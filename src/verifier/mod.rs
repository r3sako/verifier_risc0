/// Верификатор: строит dual-instance SMT-модель из InstructionSpec
/// и запускает cvc5 через smtlib-rs.
///
/// Используется теория QF_BV (BitVec шириной 32 бита) — это правильная теория
/// для битовых операций RISC Zero. Все наши значения умещаются в 32 бита:
///   Bit  ∈ [0, 1]
///   Twit ∈ [0, 3]
///   U16  ∈ [0, 65535]   (2^16-1)
///   Val  ∈ [0, 2013265920]  (~2^31, поле BabyBear)
/// Произведения двух Val в спецификациях u32.zir не встречаются;
/// максимум — Val * 0x10000 ≤ 2^32-1, что точно укладывается в 32 бита.
/// QF_BV битблэстит арифметику и идеально решает задачу uniqueness
/// битового разложения, на которой QF_NIA (целые) зависает.

use smtlib::backend::cvc5_binary::Cvc5Binary;
use smtlib::theories::fixed_size_bit_vectors::BitVec;
use smtlib::{Solver, Storage, SatResultWithModel, terms::{Sorted, StaticSorted}};

use crate::ir::{InstructionSpec, IrExpr, IrConstraint};
use std::collections::HashMap;

/// Ширина битового вектора. 32 бита достаточно для всех значений в u32.zir.
type BV<'st> = BitVec<'st, 32>;

#[derive(Debug)]
pub struct VerifyResult {
    pub name: String,
    pub deterministic: Option<bool>,
    pub time_ms: u128,
    pub error: Option<String>,
    pub num_vars: usize,
    pub num_constraints: usize,
}

pub fn verify_determinism(spec: &InstructionSpec) -> VerifyResult {
    let start = std::time::Instant::now();
    match verify_inner(spec) {
        Ok(det) => VerifyResult {
            name: spec.name.clone(), deterministic: Some(det),
            time_ms: start.elapsed().as_millis(), error: None,
            num_vars: spec.inputs.len() + spec.outputs.len() + spec.internals.len(),
            num_constraints: spec.constraints.len(),
        },
        Err(e) => VerifyResult {
            name: spec.name.clone(), deterministic: None,
            time_ms: start.elapsed().as_millis(), error: Some(e),
            num_vars: spec.inputs.len() + spec.outputs.len() + spec.internals.len(),
            num_constraints: spec.constraints.len(),
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

    // Создаём BV-переменные для двух экземпляров
    let mut vars1: HashMap<String, BV> = HashMap::new();
    let mut vars2: HashMap<String, BV> = HashMap::new();

    for v in &all_vars {
        let n1: &'static str = Box::leak(format!("{}_1", v.name.replace('.', "_")).into_boxed_str());
        let n2: &'static str = Box::leak(format!("{}_2", v.name.replace('.', "_")).into_boxed_str());
        vars1.insert(v.name.clone(), BV::new_const(&st, n1).into());
        vars2.insert(v.name.clone(), BV::new_const(&st, n2).into());
    }

    // Range constraints: 0 ≤ var ≤ max (для unsigned BV нижняя граница автоматически).
    for v in &all_vars {
        let (_, mx) = v.vtype.range();
        let max_lit = bv_const(&st, mx);
        solver.assert(vars1[&v.name].bvule(max_lit))
            .map_err(|e| format!("range: {}", e))?;
        solver.assert(vars2[&v.name].bvule(max_lit))
            .map_err(|e| format!("range: {}", e))?;
    }

    // Одинаковые входы у обоих экземпляров
    for inp in &spec.inputs {
        solver.assert(vars1[&inp.name]._eq(vars2[&inp.name]))
            .map_err(|e| format!("eq: {}", e))?;
    }

    // Все constraints применяем к обоим экземплярам
    for c in &spec.constraints {
        add_constraint(&st, &mut solver, c, &vars1)?;
        add_constraint(&st, &mut solver, c, &vars2)?;
    }

    // Может ли хоть один выход различаться?
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

/// Создаёт BV<32>-литерал из i64.
fn bv_const<'st>(st: &'st Storage, n: i64) -> BV<'st> {
    BV::new(st, n)
}

fn add_constraint<'st>(
    st: &'st Storage,
    solver: &mut Solver<'st, Cvc5Binary>,
    constraint: &IrConstraint,
    vars: &HashMap<String, BV<'st>>,
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
            let zero = bv_const(st, 0);
            let one = bv_const(st, 1);
            // result = 1 ↔ expr = 0
            solver.assert(
                (e._eq(zero) & r._eq(one)) | (e._neq(zero) & r._eq(zero))
            ).map_err(|e| format!("iszero: {}", e))
        }
        IrConstraint::Call { .. } => {
            // BV-верификатор не поддерживает UF-абстракцию.
            // Используйте Int-верификатор (verify-int) для модульной верификации.
            Err("Call constraint not supported in BV verifier (use verify-int)".into())
        }
    }
}

fn build_expr<'st>(expr: &IrExpr, vars: &HashMap<String, BV<'st>>, st: &'st Storage) -> BV<'st> {
    match expr {
        IrExpr::Const(n) => bv_const(st, *n),
        IrExpr::Var(name) => {
            if let Some(&v) = vars.get(name) { v }
            else {
                eprintln!("  [warn] Variable '{}' not found", name);
                bv_const(st, 0)
            }
        }
        IrExpr::Add(a, b) => build_expr(a, vars, st) + build_expr(b, vars, st),
        // bvsub в smtlib-rs не экспортирован; используем эквивалент: a - b == a + (-b).
        IrExpr::Sub(a, b) => build_expr(a, vars, st) + (-build_expr(b, vars, st)),
        IrExpr::Mul(a, b) => build_expr(a, vars, st) * build_expr(b, vars, st),
        IrExpr::Div(a, b) => build_expr(a, vars, st) / build_expr(b, vars, st),
    }
}
