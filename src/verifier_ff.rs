/// FF-верификатор: генерирует SMT-LIB2 с теорией QF_FF (конечные поля)
/// и вызывает cvc5 напрямую как подпроцесс.
///
/// Теория QF_FF использует базисы Грёбнера (библиотека CoCoALib внутри cvc5)
/// для решения полиномиальных систем над конечным полем — это тот же подход,
/// что использует Veridise Picus для верификации production-кода RISC Zero.
///
/// Ключевое преимущество перед QF_NIA: произведение quot·denom в конечном поле
/// — это нативная операция для базисов Грёбнера, а не неразрешимая задача
/// нелинейной целочисленной арифметики. Лимбная декомпозиция (4 кросс-
/// произведения U16×U16) решается за секунды вместо тайм-аута.

use crate::ir::{InstructionSpec, IrExpr, IrConstraint, VarType};
use crate::verifier::VerifyResult;
use std::collections::HashSet;
use std::io::Write;
use std::process::Command;

/// Простое число поля BabyBear.
const BABYBEAR_P: u64 = 2013265921;

pub fn verify_determinism(spec: &InstructionSpec, cvc5_path: &str) -> VerifyResult {
    let start = std::time::Instant::now();
    let nv = spec.inputs.len() + spec.outputs.len() + spec.internals.len();
    let nc = spec.constraints.len();
    match verify_inner(spec, cvc5_path) {
        Ok(det) => VerifyResult {
            name: spec.name.clone(), deterministic: Some(det),
            time_ms: start.elapsed().as_millis(), error: None,
            num_vars: nv, num_constraints: nc,
        },
        Err(e) => VerifyResult {
            name: spec.name.clone(), deterministic: None,
            time_ms: start.elapsed().as_millis(), error: Some(e),
            num_vars: nv, num_constraints: nc,
        },
    }
}

fn verify_inner(spec: &InstructionSpec, cvc5_path: &str) -> Result<bool, String> {
    if spec.outputs.is_empty() {
        return Err("No outputs to check".into());
    }

    let smt2 = generate_smt2(spec)?;

    let mut tmp = tempfile::NamedTempFile::new()
        .map_err(|e| format!("tempfile: {}", e))?;
    tmp.write_all(smt2.as_bytes())
        .map_err(|e| format!("write: {}", e))?;

    let output = Command::new(cvc5_path)
        .arg("--lang").arg("smt2")
        .arg("--tlimit").arg("120000")
        .arg("--ff-solver=split")
        .arg("--ff-field-polys")
        .arg("--ff-elim-disjunctive-bit")
        .arg(tmp.path())
        .output()
        .map_err(|e| format!("cvc5: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let result = stdout.trim();
    if result == "unsat" {
        Ok(true)
    } else if result == "sat" {
        Ok(false)
    } else if result == "unknown" {
        Err("Unknown (timeout or incomplete)".into())
    } else {
        Err(format!("cvc5: {} {}", result, stderr.trim()))
    }
}

/// Генерирует полный SMT-LIB2 скрипт с теорией QF_FF для dual-instance модели.
fn generate_smt2(spec: &InstructionSpec) -> Result<String, String> {
    let mut s = String::with_capacity(8192);

    // Если есть Call-constraints (UF-абстракция), нужна логика QF_UFFF.
    let has_calls = spec.constraints.iter().any(|c| matches!(c, IrConstraint::Call { .. }));
    let logic = if has_calls { "QF_UFFF" } else { "QF_FF" };
    s.push_str(&format!("(set-logic {})\n", logic));
    s.push_str(&format!("(define-sort F () (_ FiniteField {}))\n", BABYBEAR_P));

    let all_vars: Vec<_> = spec.inputs.iter()
        .chain(spec.outputs.iter())
        .chain(spec.internals.iter())
        .collect();

    // Объявляем переменные двух экземпляров
    for v in &all_vars {
        let safe = v.name.replace('.', "_");
        s.push_str(&format!("(declare-const {}_1 F)\n", safe));
        s.push_str(&format!("(declare-const {}_2 F)\n", safe));
    }

    // Range constraints.
    // В QF_FF нет нативных неравенств, поэтому используем полиномиальные тождества:
    //   Bit:  x*(x-1) = 0   → x ∈ {0, 1}
    //   Twit: x*(x-1)*(x-2)*(x-3) = 0  → x ∈ {0, 1, 2, 3}
    //   U8:   bit-decomposition (8 бит) — только для internal переменных
    //   U16:  bit-decomposition (16 бит) — только для internal переменных
    //
    // Bit-decomposition для входов НЕ добавляем: входные переменные ограничены
    // вызывающим кодом, а для standalone-верификации компонента входы свободны.
    // Для internal переменных (NondetU16Reg, NondetU8Reg) range гарантирует
    // корректность полевой арифметики.
    // Range constraints.
    //   Bit:  x*(x-1) = 0
    //   Twit: x*(x-1)*(x-2)*(x-3) = 0
    //   U8/U16-internal: bit-decomposition (только для NondetU*Reg значений,
    //   prover-guesses — им нужен range, иначе в поле найдётся множество
    //   валидных значений; входы и выходы ограничены контекстом).
    let internal_names: HashSet<&str> = spec.internals.iter()
        .map(|v| v.name.as_str()).collect();

    for v in &all_vars {
        let is_internal = internal_names.contains(v.name.as_str());
        for suffix in &["_1", "_2"] {
            let vn = format!("{}{}", v.name.replace('.', "_"), suffix);
            match v.vtype {
                VarType::Bit => {
                    s.push_str(&format!(
                        "(assert (= (ff.mul {} (ff.add {} (ff.neg (as ff1 F)))) (as ff0 F)))\n",
                        vn, vn
                    ));
                }
                VarType::Twit => {
                    let one = "(as ff1 F)";
                    let two = "(ff.add (as ff1 F) (as ff1 F))";
                    let three = "(ff.add (as ff1 F) (ff.add (as ff1 F) (as ff1 F)))";
                    s.push_str(&format!(
                        "(assert (= (ff.mul (ff.mul (ff.mul {} (ff.add {} (ff.neg {}))) (ff.add {} (ff.neg {}))) (ff.add {} (ff.neg {}))) (as ff0 F)))\n",
                        vn, vn, one, vn, two, vn, three
                    ));
                }
                VarType::U8 if is_internal => {
                    emit_range_bits(&mut s, &vn, 8);
                }
                VarType::U16 if is_internal => {
                    emit_range_bits(&mut s, &vn, 16);
                }
                _ => {}
            }
        }
    }

    // Одинаковые входы
    for inp in &spec.inputs {
        let safe = inp.name.replace('.', "_");
        s.push_str(&format!("(assert (= {}_1 {}_2))\n", safe, safe));
    }

    // UF-объявления для Call-constraints
    let mut declared_ufs: HashSet<String> = HashSet::new();
    for c in &spec.constraints {
        if let IrConstraint::Call { component, args, outputs } = c {
            for (fname, _) in outputs {
                let uf_name = format!("{}_{}", component, fname.replace('.', "_"));
                if declared_ufs.insert(uf_name.clone()) {
                    let arg_sorts: Vec<&str> = args.iter().map(|_| "F").collect();
                    s.push_str(&format!(
                        "(declare-fun {} ({}) F)\n",
                        uf_name,
                        arg_sorts.join(" ")
                    ));
                }
            }
        }
    }

    // Constraints для обоих экземпляров
    for c in &spec.constraints {
        emit_constraint(&mut s, c, "_1")?;
        emit_constraint(&mut s, c, "_2")?;
    }

    // Хотя бы один выход различается
    if spec.outputs.len() == 1 {
        let safe = spec.outputs[0].name.replace('.', "_");
        s.push_str(&format!(
            "(assert (not (= {}_1 {}_2)))\n",
            safe, safe
        ));
    } else {
        s.push_str("(assert (or\n");
        for out in &spec.outputs {
            let safe = out.name.replace('.', "_");
            s.push_str(&format!("  (not (= {}_1 {}_2))\n", safe, safe));
        }
        s.push_str("))\n");
    }

    s.push_str("(check-sat)\n");
    Ok(s)
}

/// Кодирует range constraint x ∈ [0, 2^n - 1] через битовое разложение:
///   x = Σ b_i · 2^i,  b_i · (b_i - 1) = 0  для i = 0..n-1.
/// Каждый бит — свежая переменная. Это стандартный подход в QF_FF.
fn emit_range_bits(s: &mut String, var_name: &str, bits: u32) {
    let mut sum_parts: Vec<String> = Vec::new();
    for i in 0..bits {
        let bit = format!("{}_rb{}", var_name, i);
        s.push_str(&format!("(declare-const {} F)\n", bit));
        // b_i ∈ {0, 1}
        s.push_str(&format!(
            "(assert (= (ff.mul {} (ff.add {} (ff.neg (as ff1 F)))) (as ff0 F)))\n",
            bit, bit
        ));
        let power = 1u64 << i;
        sum_parts.push(format!("(ff.mul {} (as ff{} F))", bit, power));
    }
    // x = sum of b_i * 2^i
    let mut sum = sum_parts[0].clone();
    for part in &sum_parts[1..] {
        sum = format!("(ff.add {} {})", sum, part);
    }
    s.push_str(&format!("(assert (= {} {}))\n", var_name, sum));
}

/// Генерирует assert для одного constraint с заданным суффиксом (_1 или _2).
fn emit_constraint(s: &mut String, c: &IrConstraint, suffix: &str) -> Result<(), String> {
    match c {
        IrConstraint::Eq { lhs, rhs, .. } => {
            let l = emit_expr(lhs, suffix);
            let r = emit_expr(rhs, suffix);
            s.push_str(&format!("(assert (= {} {}))\n", l, r));
            Ok(())
        }
        IrConstraint::IsZero { result, expr } => {
            let r = format!("{}{}", result.replace('.', "_"), suffix);
            let e = emit_expr(expr, suffix);
            // result = 1 ↔ expr = 0.
            // Кодируем: (expr = 0 ∧ result = 1) ∨ (expr ≠ 0 ∧ result = 0).
            // В QF_FF «≠» — это (not (= ...)).
            s.push_str(&format!(
                "(assert (or (and (= {} (as ff0 F)) (= {} (as ff1 F))) (and (not (= {} (as ff0 F))) (= {} (as ff0 F)))))\n",
                e, r, e, r
            ));
            Ok(())
        }
        IrConstraint::Call { component, args, outputs } => {
            let arg_strs: Vec<String> = args.iter()
                .map(|a| emit_expr(a, suffix))
                .collect();
            let args_joined = arg_strs.join(" ");
            for (fname, vname) in outputs {
                let uf_name = format!("{}_{}", component, fname.replace('.', "_"));
                let var = format!("{}{}", vname.replace('.', "_"), suffix);
                s.push_str(&format!(
                    "(assert (= {} ({} {})))\n",
                    var, uf_name, args_joined
                ));
            }
            Ok(())
        }
    }
}

/// Генерирует SMT-LIB2 выражение для IrExpr в теории FF.
fn emit_expr(expr: &IrExpr, suffix: &str) -> String {
    match expr {
        IrExpr::Const(n) => {
            if *n >= 0 {
                format!("(as ff{} F)", n)
            } else {
                // Отрицательная константа: ff.neg
                format!("(ff.neg (as ff{} F))", -n)
            }
        }
        IrExpr::Var(name) => {
            format!("{}{}", name.replace('.', "_"), suffix)
        }
        IrExpr::Add(a, b) => {
            format!("(ff.add {} {})", emit_expr(a, suffix), emit_expr(b, suffix))
        }
        IrExpr::Sub(a, b) => {
            format!("(ff.add {} (ff.neg {}))", emit_expr(a, suffix), emit_expr(b, suffix))
        }
        IrExpr::Mul(a, b) => {
            format!("(ff.mul {} {})", emit_expr(a, suffix), emit_expr(b, suffix))
        }
        IrExpr::Div(a, b) => {
            // Полевое деление a/b = a * b^(-1). В SMT-LIB FF нет деления;
            // но в IR деление уже раскрыто в exact_div constraint (q*b = a),
            // так что сюда мы не должны попадать. На всякий случай — ff.mul.
            format!("(ff.mul {} {})", emit_expr(a, suffix), emit_expr(b, suffix))
        }
    }
}
