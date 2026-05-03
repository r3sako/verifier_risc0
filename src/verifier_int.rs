/// Int-верификатор: альтернатива BV-варианту для случаев, когда теория
/// QF_NIA лучше подходит для задачи. В частности, для умножителя из mult.zir
/// — байтовые произведения там лучше решаются интервальной нелинейной
/// арифметикой, чем bit-blasting'ом 32-битных умножений в QF_BV.
///
/// Функционально модель та же: dual-instance на одинаковых входах,
/// проверка что выходы могут различаться. UNSAT = детерминирован.
///
/// Деление в IR трактуется как «существует q: q·b = a» (полевая семантика
/// Zirgen), это уже отражено в IR-уровне в виде exact_div constraints.

use smtlib::backend::cvc5_binary::Cvc5Binary;
use smtlib::funs::Fun;
use smtlib::terms::Dynamic;
use smtlib::{Int, Solver, Storage, SatResultWithModel, prelude::*};

use crate::ir::{InstructionSpec, IrExpr, IrConstraint};
use crate::verifier::VerifyResult;
use std::collections::HashMap;

/// Кэш объявленных UF: (component_name, field_name) → Fun
type UfCache<'st> = HashMap<(String, String), Fun<'st>>;

pub fn verify_determinism(spec: &InstructionSpec) -> VerifyResult {
    let start = std::time::Instant::now();
    let nv = spec.inputs.len() + spec.outputs.len() + spec.internals.len();
    let nc = spec.constraints.len();
    match verify_inner(spec) {
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

fn verify_inner(spec: &InstructionSpec) -> Result<bool, String> {
    if spec.outputs.is_empty() {
        return Err("No outputs to check".into());
    }

    let st = Storage::new();
    let backend = Cvc5Binary::new("./scripts/cvc5-quiet").map_err(|e| format!("cvc5: {}", e))?;
    let mut solver = Solver::new(&st, backend).map_err(|e| format!("solver: {}", e))?;
    // Таймаут задаётся в обёртке cvc5-quiet через --tlimit-per — set_timeout()
    // в smtlib-rs 0.3 не реализован для cvc5-ответов.
    let _ = &mut solver;

    let all_vars: Vec<_> = spec.inputs.iter()
        .chain(spec.outputs.iter())
        .chain(spec.internals.iter())
        .collect();

    // Создаём Int-переменные для двух экземпляров
    let mut vars1: HashMap<String, Int> = HashMap::new();
    let mut vars2: HashMap<String, Int> = HashMap::new();

    for v in &all_vars {
        let n1: &'static str = Box::leak(format!("{}_1", v.name.replace('.', "_")).into_boxed_str());
        let n2: &'static str = Box::leak(format!("{}_2", v.name.replace('.', "_")).into_boxed_str());
        vars1.insert(v.name.clone(), *Int::new_const(&st, n1));
        vars2.insert(v.name.clone(), *Int::new_const(&st, n2));
    }

    // Range constraints (нативные неравенства Int — тут как раз сила QF_NIA)
    for v in &all_vars {
        let (mn, mx) = v.vtype.range();
        solver.assert(vars1[&v.name].ge(mn) & vars1[&v.name].le(mx))
            .map_err(|e| format!("range: {}", e))?;
        solver.assert(vars2[&v.name].ge(mn) & vars2[&v.name].le(mx))
            .map_err(|e| format!("range: {}", e))?;
    }

    // Одинаковые входы у обоих экземпляров
    for inp in &spec.inputs {
        solver.assert(vars1[&inp.name]._eq(vars2[&inp.name]))
            .map_err(|e| format!("eq: {}", e))?;
    }

    // Заранее объявляем все UF (uninterpreted functions) — по одной на каждое
    // (component, output_field) встретившееся в Call-constraint'ах. Эти UF
    // расшариваются между двумя экземплярами; SMT функциональность даёт
    // «same args → same outputs», что и есть лемма из независимой верификации.
    let mut ufs: UfCache = HashMap::new();
    for c in &spec.constraints {
        if let IrConstraint::Call { component, args, outputs } = c {
            for (fname, _vname) in outputs {
                let key = (component.clone(), fname.clone());
                if !ufs.contains_key(&key) {
                    let arg_sorts = vec![Int::sort(); args.len()];
                    let f = Fun::new(
                        &st,
                        format!("{}__{}", component, fname),
                        arg_sorts,
                        Int::sort(),
                    );
                    solver.declare_fun(&f).map_err(|e| format!("declare_fun: {}", e))?;
                    ufs.insert(key, f);
                }
            }
        }
    }

    // Все constraints применяем к обоим экземплярам
    for c in &spec.constraints {
        add_constraint(&st, &mut solver, c, &vars1, &ufs)?;
        add_constraint(&st, &mut solver, c, &vars2, &ufs)?;
    }

    // Хотя бы один выход различается?
    let mut diffs = Vec::new();
    for out in &spec.outputs {
        diffs.push(vars1[&out.name]._neq(vars2[&out.name]));
    }
    let mut disj = diffs[0];
    for d in &diffs[1..] { disj = disj | *d; }
    solver.assert(disj).map_err(|e| format!("diff: {}", e))?;

    match solver.check_sat_with_model().map_err(|e| format!("solve: {}", e))? {
        SatResultWithModel::Unsat => Ok(true),
        SatResultWithModel::Sat(_) => Ok(false),
        SatResultWithModel::Unknown => Err("Unknown".into()),
    }
}

fn add_constraint<'st>(
    st: &'st Storage,
    solver: &mut Solver<'st, Cvc5Binary>,
    constraint: &IrConstraint,
    vars: &HashMap<String, Int<'st>>,
    ufs: &UfCache<'st>,
) -> Result<(), String> {
    match constraint {
        IrConstraint::Eq { lhs, rhs, .. } => {
            let l = build_expr(lhs, vars, st);
            let r = build_expr(rhs, vars, st);
            solver.assert(l._eq(r)).map_err(|e| format!("eq: {}", e))
        }
        IrConstraint::IsZero { result, expr } => {
            let r = vars.get(result)
                .ok_or(format!("IsZero var '{}' not found", result))?;
            let e = build_expr(expr, vars, st);
            solver.assert(
                (e._eq(0i64) & r._eq(1i64)) | (e._neq(0i64) & r._eq(0i64))
            ).map_err(|e| format!("iszero: {}", e))
        }
        IrConstraint::Call { component, args, outputs } => {
            // Применяем UF к args этого экземпляра. Один и тот же символ UF
            // в двух экземплярах с одинаковыми args → SMT-функциональность
            // гарантирует одинаковый output. Это и есть «лемма из независимой
            // верификации компонента».
            let arg_dyns: Vec<Dynamic> = args.iter()
                .map(|a| Dynamic::from(build_expr(a, vars, st)))
                .collect();
            for (fname, vname) in outputs {
                let f = ufs.get(&(component.clone(), fname.clone()))
                    .ok_or(format!("UF not declared: {}.{}", component, fname))?;
                let call_term = f.call(&arg_dyns)
                    .map_err(|e| format!("UF call: {}", e))?;
                let out_var = vars.get(vname)
                    .ok_or(format!("output var '{}' not found", vname))?;
                let out_dyn: Dynamic = (*out_var).into();
                solver.assert(out_dyn._eq(call_term))
                    .map_err(|e| format!("UF eq: {}", e))?;
            }
            Ok(())
        }
    }
}

fn build_expr<'st>(expr: &IrExpr, vars: &HashMap<String, Int<'st>>, st: &'st Storage) -> Int<'st> {
    match expr {
        IrExpr::Const(n) => {
            // smtlib-rs 0.3 не даёт прямого Int-литерала; делаем через
            // арифметический трюк: first - first + n = n.
            if let Some((&_, &first_var)) = vars.iter().next() {
                first_var - first_var + *n
            } else {
                let dummy = *Int::new_const(st, "__zero");
                dummy - dummy + *n
            }
        }
        IrExpr::Var(name) => {
            if let Some(&v) = vars.get(name) { v }
            else {
                eprintln!("  [warn] Variable '{}' not found", name);
                if let Some((&_, &first_var)) = vars.iter().next() {
                    first_var - first_var
                } else {
                    *Int::new_const(st, "__zero")
                }
            }
        }
        IrExpr::Add(a, b) => build_expr(a, vars, st) + build_expr(b, vars, st),
        IrExpr::Sub(a, b) => build_expr(a, vars, st) - build_expr(b, vars, st),
        IrExpr::Mul(a, b) => build_expr(a, vars, st) * build_expr(b, vars, st),
        IrExpr::Div(a, b) => build_expr(a, vars, st) / build_expr(b, vars, st),
    }
}
