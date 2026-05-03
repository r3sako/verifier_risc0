/// IR: полное промежуточное представление с инлайнингом компонентов.
///
/// Ключевая идея: Value может быть скаляром, структурой (ValU32)
/// или массивом бит (ToBits). При вызове компонента мы инлайним
/// его тело, подставляя аргументы, и собираем все ограничения.

use crate::parser::ast::*;
use std::collections::HashMap;

// ====================== Типы ======================

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VarType { U32, U16, U8, Bit, Twit, Val }

impl VarType {
    pub fn range(&self) -> (i64, i64) {
        match self {
            VarType::U32  => (0, 4294967295),
            VarType::U16  => (0, 65535),
            VarType::U8   => (0, 255),
            VarType::Bit  => (0, 1),
            VarType::Twit => (0, 3),
            VarType::Val  => (0, 2013265920),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Var { pub name: String, pub vtype: VarType }

/// IR-выражение
#[derive(Debug, Clone)]
pub enum IrExpr {
    Const(i64),
    Var(String),
    Add(Box<IrExpr>, Box<IrExpr>),
    Sub(Box<IrExpr>, Box<IrExpr>),
    Mul(Box<IrExpr>, Box<IrExpr>),
    Div(Box<IrExpr>, Box<IrExpr>),
}

/// Ограничение
#[derive(Debug, Clone)]
pub enum IrConstraint {
    /// lhs = rhs
    Eq { lhs: IrExpr, rhs: IrExpr, tag: String },
    /// result = (expr == 0 ? 1 : 0)
    IsZero { result: String, expr: IrExpr },
    /// Символический вызов уже-верифицированного компонента (UF-абстракция).
    /// Для каждого выходного поля будет объявлена uninterpreted function от
    /// args, и output-переменная приравнена к её значению. SMT функциональность
    /// (same args → same value) даёт «одинаковые входы → одинаковые выходы»
    /// без раскрытия body — это лемма из независимой верификации компонента.
    Call {
        component: String,
        args: Vec<IrExpr>,
        outputs: Vec<(String, String)>, // (имя_поля, имя_переменной)
    },
}

/// Спецификация инструкции — всё что нужно для верификации
#[derive(Debug, Clone)]
pub struct InstructionSpec {
    pub name: String,
    pub source_line: usize,
    pub inputs: Vec<Var>,
    pub outputs: Vec<Var>,
    pub internals: Vec<Var>,
    pub constraints: Vec<IrConstraint>,
}

// ====================== Value ======================

/// Значение, возвращаемое выражением при evaluation.
/// Может быть скаляром, структурой (ValU32) или массивом бит.
#[derive(Debug, Clone)]
pub enum Value {
    Expr(IrExpr),
    Struct(HashMap<String, Value>),
    BitArray(Vec<IrExpr>),
}

impl Value {
    fn to_expr(&self) -> IrExpr {
        match self {
            Value::Expr(e) => e.clone(),
            _ => panic!("Expected scalar value, got {:?}", self),
        }
    }

    fn field(&self, name: &str) -> Option<&Value> {
        match self {
            Value::Struct(fields) => fields.get(name),
            _ => None,
        }
    }

    fn make_struct(pairs: Vec<(&str, Value)>) -> Value {
        let mut m = HashMap::new();
        for (k, v) in pairs { m.insert(k.to_string(), v); }
        Value::Struct(m)
    }
}

// ====================== ComponentDB ======================

pub struct ComponentDB {
    components: HashMap<String, ComponentDef>,
    /// extern-функции: имя → имя возвращаемого типа (имя другого компонента-структуры).
    /// При вызове `f(args...)` где f — extern, создаётся struct из свежих переменных
    /// по форме return_type. Это prover-side hint, его значения никак не constraint'ятся.
    externs: HashMap<String, String>,
    /// Имена компонентов, чьи вызовы НЕ инлайнятся в IR — заменяются на
    /// `IrConstraint::Call`. Полезно для модульной верификации: если компонент
    /// уже доказан детерминированным независимо, в композите можно использовать
    /// его как UF (uninterpreted function) и сэкономить тысячи constraint'ов.
    abstract_list: std::collections::HashSet<String>,
}

impl ComponentDB {
    pub fn new(items: &[Item]) -> Self {
        let mut m = HashMap::new();
        let mut e = HashMap::new();
        for it in items {
            match it {
                Item::Component(c) => { m.insert(c.name.clone(), c.clone()); }
                Item::Extern { name, return_type } => { e.insert(name.clone(), return_type.clone()); }
                Item::Import(_) => {}
            }
        }
        ComponentDB { components: m, externs: e, abstract_list: Default::default() }
    }

    /// Установить список компонентов, верификация которых будет использовать
    /// функциональную абстракцию (UF) вместо полного раскрытия.
    pub fn set_abstract(&mut self, names: &[&str]) {
        self.abstract_list = names.iter().map(|s| s.to_string()).collect();
    }

    pub fn names(&self) -> Vec<String> {
        let mut n: Vec<_> = self.components.keys().cloned().collect();
        n.sort(); n
    }

    pub fn lower(&self, name: &str) -> Result<InstructionSpec, String> {
        let comp = self.components.get(name)
            .ok_or(format!("Component '{}' not found", name))?;

        let mut spec = InstructionSpec {
            name: name.into(), source_line: comp.source_line,
            inputs: vec![], outputs: vec![], internals: vec![],
            constraints: vec![],
        };

        let mut ctx = LowerCtx::new(&self.components, &self.externs, &self.abstract_list);

        // Создаём входы из параметров и привязываем их как Value
        for (pname, ptype) in &comp.params {
            if ptype == "ValU32" || ptype == "DenormedValU32" {
                let low_name = format!("{}.low", pname);
                let high_name = format!("{}.high", pname);
                spec.inputs.push(Var { name: low_name.clone(), vtype: VarType::U16 });
                spec.inputs.push(Var { name: high_name.clone(), vtype: VarType::U16 });

                let val = Value::make_struct(vec![
                    ("low",  Value::Expr(IrExpr::Var(low_name))),
                    ("high", Value::Expr(IrExpr::Var(high_name))),
                ]);
                ctx.bind(pname, val);
            } else if let Some(comp_def) = self.components.get(ptype.as_str()) {
                // Параметр имеет тип пользовательского component — разворачиваем
                // его public-биндинги как поля структуры (MultiplySettings и т.п.).
                let pub_fields: Vec<String> = comp_def.body.iter().filter_map(|s| {
                    if let Stmt::Binding { is_public: true, name, .. } = s {
                        Some(name.clone())
                    } else { None }
                }).collect();
                if !pub_fields.is_empty() {
                    let mut fields = HashMap::new();
                    for fname in &pub_fields {
                        let full = format!("{}.{}", pname, fname);
                        spec.inputs.push(Var { name: full.clone(), vtype: VarType::Val });
                        fields.insert(fname.clone(), Value::Expr(IrExpr::Var(full)));
                    }
                    ctx.bind(pname, Value::Struct(fields));
                } else {
                    spec.inputs.push(Var { name: pname.clone(), vtype: VarType::Val });
                    ctx.bind(pname, Value::Expr(IrExpr::Var(pname.clone())));
                }
            } else if ptype == "U32" {
                // U32 — одна Int-переменная в диапазоне [0, 2^32-1].
                // Удобно для алгоритмов вроде деления, где разложение на лимбы
                // давало бы 4 произведения U16×U16 в одном уравнении и QF_NIA
                // не справляется. Эквивалентно flat-представлению `low + 2^16*high`.
                spec.inputs.push(Var { name: pname.clone(), vtype: VarType::U32 });
                ctx.bind(pname, Value::Expr(IrExpr::Var(pname.clone())));
            } else {
                // Скалярный тип (Val, U16, и пр.)
                spec.inputs.push(Var { name: pname.clone(), vtype: VarType::Val });
                ctx.bind(pname, Value::Expr(IrExpr::Var(pname.clone())));
            }
        }

        // Обрабатываем тело
        let result = ctx.process_body(&comp.body, &mut spec, "")?;

        // Если тело вернуло структуру/значение — это выходы
        if let Some(val) = result {
            ctx.extract_outputs(&val, "result", &mut spec);
        }

        Ok(spec)
    }
}

// ====================== LowerCtx ======================

struct LowerCtx<'a> {
    components: &'a HashMap<String, ComponentDef>,
    externs: &'a HashMap<String, String>,
    abstract_list: &'a std::collections::HashSet<String>,
    bindings: HashMap<String, Value>,
    counter: usize,
    /// Текущий guard для Eq-constraint'ов (когда мы внутри ветки major mux).
    /// Если Some(g), каждый emitted Eq оборачивается в `g * lhs = g * rhs` —
    /// семантика Zirgen: ветка активна только при g = 1.
    current_guard: Option<IrExpr>,
}

impl<'a> LowerCtx<'a> {
    fn new(
        components: &'a HashMap<String, ComponentDef>,
        externs: &'a HashMap<String, String>,
        abstract_list: &'a std::collections::HashSet<String>,
    ) -> Self {
        LowerCtx { components, externs, abstract_list,
                   bindings: HashMap::new(), counter: 0,
                   current_guard: None }
    }

    /// Оборачивает constraint `lhs = rhs` текущим guard'ом (если есть):
    /// возвращает `(g·lhs, g·rhs)`. Семантика: при g=0 → 0=0, при g=1 → lhs=rhs.
    fn maybe_guard(&self, lhs: IrExpr, rhs: IrExpr) -> (IrExpr, IrExpr) {
        if let Some(g) = &self.current_guard {
            (
                IrExpr::Mul(Box::new(g.clone()), Box::new(lhs)),
                IrExpr::Mul(Box::new(g.clone()), Box::new(rhs)),
            )
        } else {
            (lhs, rhs)
        }
    }

    fn fresh(&mut self, prefix: &str, name: &str) -> String {
        self.counter += 1;
        if prefix.is_empty() {
            format!("{}_{}", name, self.counter)
        } else {
            format!("{}_{}_{}", prefix, name, self.counter)
        }
    }

    fn bind(&mut self, name: &str, val: Value) {
        self.bindings.insert(name.to_string(), val);
    }

    /// Извлечь выходы из возвращаемого значения
    fn extract_outputs(&self, val: &Value, prefix: &str, spec: &mut InstructionSpec) {
        match val {
            Value::Expr(e) => {
                let name = prefix.to_string();
                spec.outputs.push(Var { name: name.clone(), vtype: VarType::Val });
                spec.constraints.push(IrConstraint::Eq {
                    lhs: IrExpr::Var(name), rhs: e.clone(),
                    tag: format!("output_{}", prefix),
                });
            }
            Value::Struct(fields) => {
                for (fname, fval) in fields {
                    let full = format!("{}.{}", prefix, fname);
                    match fval {
                        Value::Expr(e) => {
                            spec.outputs.push(Var { name: full.clone(), vtype: VarType::U16 });
                            spec.constraints.push(IrConstraint::Eq {
                                lhs: IrExpr::Var(full.clone()), rhs: e.clone(),
                                tag: format!("output_{}", full),
                            });
                        }
                        _ => self.extract_outputs(fval, &full, spec),
                    }
                }
            }
            _ => {}
        }
    }

    /// Обработать тело компонента, вернуть последнее значение
    fn process_body(&mut self, stmts: &[Stmt], spec: &mut InstructionSpec, prefix: &str)
        -> Result<Option<Value>, String>
    {
        let mut last_val = None;

        for stmt in stmts {
            match stmt {
                Stmt::Binding { is_public, name, value } => {
                    let val = self.eval_expr(value, spec, prefix)?;

                    // Для Reg: создаём переменную + constraint
                    let val = if let Expr::Call { name: fn_name, .. } = value {
                        if fn_name == "Reg" || fn_name == "U16Reg" {
                            let vt = if fn_name == "U16Reg" { VarType::U16 } else { VarType::Val };
                            let vname = self.fresh(prefix, name);
                            spec.internals.push(Var { name: vname.clone(), vtype: vt });
                            spec.constraints.push(IrConstraint::Eq {
                                lhs: IrExpr::Var(vname.clone()),
                                rhs: val.to_expr(),
                                tag: format!("reg_{}", name),
                            });
                            Value::Expr(IrExpr::Var(vname))
                        } else { val }
                    } else { val };

                    if *is_public {
                        // Public binding: на верхнем уровне (prefix="") — выход компонента,
                        // внутри инлайна — обычная внутренняя переменная (станет полем
                        // возвращаемой структуры).
                        match &val {
                            Value::Expr(_) => {
                                let vname = self.fresh(prefix, name);
                                let vt = self.guess_type(value);
                                if prefix.is_empty() {
                                    spec.outputs.push(Var { name: vname.clone(), vtype: vt });
                                } else {
                                    spec.internals.push(Var { name: vname.clone(), vtype: vt });
                                }
                                spec.constraints.push(IrConstraint::Eq {
                                    lhs: IrExpr::Var(vname.clone()),
                                    rhs: val.to_expr(),
                                    tag: format!("public_{}", name),
                                });
                                self.bind(name, Value::Expr(IrExpr::Var(vname)));
                            }
                            Value::Struct(_) => {
                                // Структурный public-биндинг (например, outLow := ValU32(...)).
                                // Только на верхнем уровне разворачиваем поля в выходы.
                                if prefix.is_empty() {
                                    self.extract_outputs(&val, name, spec);
                                }
                                self.bind(name, val);
                            }
                            _ => { self.bind(name, val); }
                        }
                    } else {
                        self.bind(name, val);
                    }
                    last_val = None;
                }
                Stmt::Constraint { lhs, rhs } => {
                    let l = self.eval_expr(lhs, spec, prefix)?.to_expr();
                    let r = self.eval_expr(rhs, spec, prefix)?.to_expr();
                    let (l, r) = self.maybe_guard(l, r);
                    spec.constraints.push(IrConstraint::Eq {
                        lhs: l, rhs: r, tag: "constraint".into(),
                    });
                    last_val = None;
                }
                Stmt::Mux { guards, branches } => {
                    // Каждая ветка обрабатывается с current_guard = соответствующее
                    // guard-выражение. constraints внутри умножаются на guard:
                    //   `lhs = rhs` под guard g → `g * lhs = g * rhs`.
                    // При g = 0 это 0 = 0 (тривиально), при g = 1 это оригинал.
                    let saved_guard = self.current_guard.clone();
                    for (g_expr, branch) in guards.iter().zip(branches.iter()) {
                        let g_ir = self.eval_expr(g_expr, spec, prefix)?.to_expr();
                        // Если уже под guard — комбинируем умножением.
                        let new_guard = match &saved_guard {
                            Some(outer) => IrExpr::Mul(
                                Box::new(outer.clone()),
                                Box::new(g_ir),
                            ),
                            None => g_ir,
                        };
                        self.current_guard = Some(new_guard);
                        self.process_body(branch, spec, prefix)?;
                    }
                    self.current_guard = saved_guard;
                    last_val = None;
                }
                Stmt::ExprStmt(expr) => {
                    last_val = Some(self.eval_expr(expr, spec, prefix)?);
                }
            }
        }
        Ok(last_val)
    }

    /// Вычислить выражение → Value
    fn eval_expr(&mut self, expr: &Expr, spec: &mut InstructionSpec, prefix: &str)
        -> Result<Value, String>
    {
        match expr {
            Expr::IntLit(n) => Ok(Value::Expr(IrExpr::Const(*n as i64))),

            Expr::Ident(name) => {
                if let Some(v) = self.bindings.get(name) {
                    Ok(v.clone())
                } else {
                    Ok(Value::Expr(IrExpr::Var(name.clone())))
                }
            }

            Expr::Field { object, field } => {
                let obj = self.eval_expr(object, spec, prefix)?;
                if let Some(fval) = obj.field(field) {
                    Ok(fval.clone())
                } else {
                    // Fallback: может быть binding по полному имени
                    if let Expr::Ident(oname) = object.as_ref() {
                        let full = format!("{}.{}", oname, field);
                        if let Some(v) = self.bindings.get(&full) {
                            return Ok(v.clone());
                        }
                        Ok(Value::Expr(IrExpr::Var(full)))
                    } else {
                        Err(format!("Cannot access field '{}' on non-struct", field))
                    }
                }
            }

            Expr::BinOp { op, lhs, rhs } => {
                let l = self.eval_expr(lhs, spec, prefix)?.to_expr();
                let r = self.eval_expr(rhs, spec, prefix)?.to_expr();
                let result = match op {
                    Op::Add => IrExpr::Add(Box::new(l), Box::new(r)),
                    Op::Sub => IrExpr::Sub(Box::new(l), Box::new(r)),
                    Op::Mul => IrExpr::Mul(Box::new(l), Box::new(r)),
                    // Деление в Zirgen — полевое (умножение на инверс).
                    // Моделируем как «существует q: q·b = a» (точное деление).
                    // Эквивалентно полевой семантике, когда b ≠ 0; автоматически
                    // отсеивает случаи, когда a не делится нацело на b.
                    Op::Div => {
                        // Const-fold: 0/b = 0, c/d = c/d (когда оба константы и b≠0).
                        // Это убирает мусорные переменные из hint-выражений
                        // вида `(x & MASK) / DIVISOR` (BitAnd→0, /b → 0).
                        match (&l, &r) {
                            (IrExpr::Const(0), _) => IrExpr::Const(0),
                            (IrExpr::Const(a_v), IrExpr::Const(b_v)) if *b_v != 0 => {
                                IrExpr::Const(a_v / b_v)
                            }
                            _ => {
                                let qname = self.fresh(prefix, "div");
                                spec.internals.push(Var { name: qname.clone(), vtype: VarType::Val });
                                spec.constraints.push(IrConstraint::Eq {
                                    lhs: IrExpr::Mul(
                                        Box::new(IrExpr::Var(qname.clone())),
                                        Box::new(r.clone()),
                                    ),
                                    rhs: l.clone(),
                                    tag: "exact_div".into(),
                                });
                                IrExpr::Var(qname)
                            }
                        }
                    }
                    Op::BitAnd => {
                        // BitAnd в hint-выражениях (NondetReg аргументы) — не constraint
                        // Создаём placeholder, он будет проигнорирован
                        IrExpr::Const(0)
                    }
                };
                Ok(Value::Expr(result))
            }

            Expr::Call { name, args, type_args } => {
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a, spec, prefix))
                    .collect::<Result<Vec<_>, _>>()?;

                self.inline_call(name, &arg_vals, type_args, spec, prefix)
            }

            Expr::For { var, start, end, body } => {
                // Генерируем массив выражений
                let mut results = Vec::new();
                for i in *start..*end {
                    self.bind(var, Value::Expr(IrExpr::Const(i as i64)));
                    let val = self.eval_expr(body, spec, prefix)?;
                    results.push(val.to_expr());
                }
                Ok(Value::BitArray(results))
            }

            Expr::Index { object, index } => {
                let obj = self.eval_expr(object, spec, prefix)?;
                let idx = self.eval_expr(index, spec, prefix)?;
                match (&obj, &idx) {
                    (Value::BitArray(arr), Value::Expr(IrExpr::Const(i))) => {
                        Ok(Value::Expr(arr[*i as usize].clone()))
                    }
                    _ => Err("Index: expected BitArray[Const]".into()),
                }
            }
        }
    }

    /// Инлайнить вызов компонента
    fn inline_call(&mut self, name: &str, args: &[Value], type_args: &[u64],
                    spec: &mut InstructionSpec, prefix: &str)
        -> Result<Value, String>
    {
        match name {
            // ---- Конструкторы структур ----
            "ValU32" | "DenormedValU32" => {
                Ok(Value::make_struct(vec![
                    ("low",  args[0].clone()),
                    ("high", args[1].clone()),
                ]))
            }

            // ---- Nondeterministic регистры: создаём переменную, игнорируем hint ----
            "NondetReg" => {
                let vname = self.fresh(prefix, "nd");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Val });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "NondetU16Reg" => {
                let vname = self.fresh(prefix, "u16");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::U16 });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "NondetU32Reg" => {
                // U32-диапазон [0, 2^32-1] — для прямой формулировки 32-битных
                // алгоритмов (например, деление через q·d + r = n) без
                // лимбной декомпозиции. cvc5 NIA в одной переменной справляется
                // намного лучше, чем в паре лимбов.
                let vname = self.fresh(prefix, "u32");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::U32 });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "NondetU8Reg" => {
                let vname = self.fresh(prefix, "u8");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::U8 });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "NondetBitReg" => {
                let vname = self.fresh(prefix, "bit");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Bit });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "NondetTwitReg" | "NondetFakeTwitReg" => {
                let vname = self.fresh(prefix, "twit");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Twit });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            // FakeTwitReg(expr) — constrained reg с диапазоном [0, 3] и привязкой = expr
            "FakeTwitReg" => {
                let vname = self.fresh(prefix, "ftwit");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Twit });
                spec.constraints.push(IrConstraint::Eq {
                    lhs: IrExpr::Var(vname.clone()),
                    rhs: args[0].to_expr(),
                    tag: "fake_twit_reg".into(),
                });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }

            // ---- Constrained регистры: переменная + constraint ----
            "Reg" => {
                // Reg(expr): prover выбирает значение, но оно должно = expr
                // Возвращаем само выражение (constraint добавится при binding)
                Ok(args[0].clone())
            }
            "U16Reg" => {
                // U16Reg(expr): как Reg но с range [0, 65535]
                let vname = self.fresh(prefix, "u16r");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::U16 });
                spec.constraints.push(IrConstraint::Eq {
                    lhs: IrExpr::Var(vname.clone()),
                    rhs: args[0].to_expr(),
                    tag: "u16reg".into(),
                });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }
            "U32Reg" => {
                // U32Reg(expr): свежая single-Int переменная в диапазоне [0, 2^32-1]
                // с constraint = expr. Удобно для введения flat-форм 32-битных чисел
                // в нелинейных уравнениях — cvc5 NIA решает product двух U32-vars
                // намного быстрее, чем эквивалентное (low+65536*high)*(low+65536*high).
                let vname = self.fresh(prefix, "u32r");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::U32 });
                let (lhs, rhs) = self.maybe_guard(IrExpr::Var(vname.clone()), args[0].to_expr());
                spec.constraints.push(IrConstraint::Eq {
                    lhs, rhs, tag: "u32reg".into(),
                });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }

            // ---- IsZero (алиас Isz): result = (expr == 0 ? 1 : 0) ----
            "IsZero" | "Isz" => {
                let vname = self.fresh(prefix, "iz");
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Bit });
                spec.constraints.push(IrConstraint::IsZero {
                    result: vname.clone(),
                    expr: args[0].to_expr(),
                });
                Ok(Value::Expr(IrExpr::Var(vname)))
            }

            // ---- BitwiseAndU16: точная семантика Zirgen ----
            //   bits_x := ToBits<16>(x);   x = FromBits<16>(bits_x);
            //   bits_y := ToBits<16>(y);   y = FromBits<16>(bits_y);
            //   bits_r := for i:0..16 { bits_x[i] * bits_y[i] };
            //   r := FromBits<16>(bits_r);
            // Произведение двух бит {0,1} ∈ {0,1} и совпадает с AND.
            "BitwiseAndU16" => {
                let x_expr = args[0].to_expr();
                let y_expr = args[1].to_expr();

                let mut x_sum = IrExpr::Const(0);
                let mut y_sum = IrExpr::Const(0);
                let mut r_sum = IrExpr::Const(0);

                for i in 0..16u32 {
                    let power = 1i64 << i;

                    let xb = self.fresh(prefix, &format!("xb{}", i));
                    spec.internals.push(Var { name: xb.clone(), vtype: VarType::Bit });
                    let yb = self.fresh(prefix, &format!("yb{}", i));
                    spec.internals.push(Var { name: yb.clone(), vtype: VarType::Bit });

                    // bits_r[i] = bits_x[i] * bits_y[i]   ← как в Zirgen
                    let rb_expr = IrExpr::Mul(
                        Box::new(IrExpr::Var(xb.clone())),
                        Box::new(IrExpr::Var(yb.clone())),
                    );

                    let x_term = IrExpr::Mul(Box::new(IrExpr::Var(xb)),  Box::new(IrExpr::Const(power)));
                    let y_term = IrExpr::Mul(Box::new(IrExpr::Var(yb)),  Box::new(IrExpr::Const(power)));
                    let r_term = IrExpr::Mul(Box::new(rb_expr),          Box::new(IrExpr::Const(power)));

                    x_sum = if i == 0 { x_term } else { IrExpr::Add(Box::new(x_sum), Box::new(x_term)) };
                    y_sum = if i == 0 { y_term } else { IrExpr::Add(Box::new(y_sum), Box::new(y_term)) };
                    r_sum = if i == 0 { r_term } else { IrExpr::Add(Box::new(r_sum), Box::new(r_term)) };
                }

                // x = FromBits<16>(bits_x), y = FromBits<16>(bits_y)
                spec.constraints.push(IrConstraint::Eq { lhs: x_expr, rhs: x_sum, tag: "tobits_x".into() });
                spec.constraints.push(IrConstraint::Eq { lhs: y_expr, rhs: y_sum, tag: "tobits_y".into() });

                // r := FromBits<16>(bits_r) — материализуем результат как U16-переменную
                let result_name = self.fresh(prefix, "and16");
                spec.internals.push(Var { name: result_name.clone(), vtype: VarType::U16 });
                spec.constraints.push(IrConstraint::Eq {
                    lhs: IrExpr::Var(result_name.clone()), rhs: r_sum, tag: "and_result".into(),
                });

                Ok(Value::Expr(IrExpr::Var(result_name)))
            }

            // ---- ToBits/FromBits: when reached directly, use bit decomposition ----
            "ToBits" => {
                let n = type_args.first().copied().unwrap_or(16) as usize;
                let input = args[0].to_expr();
                let mut bits = Vec::new();
                let mut sum = IrExpr::Const(0);

                for i in 0..n {
                    let bname = self.fresh(prefix, &format!("b{}", i));
                    spec.internals.push(Var { name: bname.clone(), vtype: VarType::Bit });
                    bits.push(IrExpr::Var(bname.clone()));

                    let power = 1i64 << i;
                    let term = IrExpr::Mul(
                        Box::new(IrExpr::Var(bname)),
                        Box::new(IrExpr::Const(power)),
                    );
                    sum = if i == 0 { term } else { IrExpr::Add(Box::new(sum), Box::new(term)) };
                }

                spec.constraints.push(IrConstraint::Eq {
                    lhs: input, rhs: sum,
                    tag: "tobits_decompose".into(),
                });

                Ok(Value::BitArray(bits))
            }

            "FromBits" => {
                let bits = match &args[0] {
                    Value::BitArray(b) => b.clone(),
                    _ => return Err("FromBits: expected BitArray".into()),
                };
                let mut sum = IrExpr::Const(0);
                for (i, bit) in bits.iter().enumerate() {
                    let power = 1i64 << i;
                    let term = IrExpr::Mul(
                        Box::new(bit.clone()),
                        Box::new(IrExpr::Const(power)),
                    );
                    sum = if i == 0 { term } else { IrExpr::Add(Box::new(sum), Box::new(term)) };
                }
                Ok(Value::Expr(sum))
            }

            // ---- Пользовательские компоненты: инлайнинг (или UF-абстракция) ----
            _ => {
                // extern-функции: prover-side hint. Возвращает структуру по
                // форме return_type — поля становятся свежими переменными,
                // никак не constraint'ятся (как и должно быть для hints).
                if let Some(ret_type) = self.externs.get(name).cloned() {
                    return self.fresh_struct_for_type(&ret_type, prefix);
                }
                // UF-абстракция: компонент в abstract_list — не инлайним body,
                // создаём fresh-переменные для public-полей и Call-constraint.
                // SMT-функциональность даст «same args → same outputs».
                if self.abstract_list.contains(name) {
                    if let Some(comp) = self.components.get(name).cloned() {
                        return self.abstract_call(&comp, name, args, spec, prefix);
                    }
                }
                if let Some(comp) = self.components.get(name).cloned() {
                    let sub_prefix = if prefix.is_empty() {
                        name.to_lowercase()
                    } else {
                        format!("{}_{}", prefix, name.to_lowercase())
                    };

                    // Сохраняем старые bindings
                    let saved_bindings = self.bindings.clone();

                    // Привязываем параметры к аргументам
                    for (i, (pname, _ptype)) in comp.params.iter().enumerate() {
                        if i < args.len() {
                            self.bind(pname, args[i].clone());
                        }
                    }

                    // Обрабатываем тело
                    let result = self.process_body(&comp.body, spec, &sub_prefix)?;

                    // Собираем public bindings как поля структуры
                    let mut fields = HashMap::new();
                    for stmt in &comp.body {
                        if let Stmt::Binding { is_public: true, name: bname, .. } = stmt {
                            if let Some(val) = self.bindings.get(bname) {
                                fields.insert(bname.clone(), val.clone());
                            }
                        }
                    }

                    // Восстанавливаем bindings
                    self.bindings = saved_bindings;

                    // Возвращаем: если есть return value, оборачиваем с public полями
                    match result {
                        Some(Value::Struct(mut s)) => {
                            // Мержим public поля
                            for (k, v) in fields { s.entry(k).or_insert(v); }
                            Ok(Value::Struct(s))
                        }
                        Some(val) => {
                            if fields.is_empty() {
                                Ok(val)
                            } else {
                                // Return value + public поля → struct
                                let mut s = fields;
                                s.insert("_value".to_string(), val);
                                Ok(Value::Struct(s))
                            }
                        }
                        None => {
                            if fields.is_empty() {
                                Ok(Value::Expr(IrExpr::Const(0)))
                            } else {
                                Ok(Value::Struct(fields))
                            }
                        }
                    }
                } else {
                    Err(format!("Unknown component: {}", name))
                }
            }
        }
    }

    /// Создаёт Value::Struct (или Value::Expr для скаляров) свежих переменных
    /// согласно типу — используется для extern-возвратов (prover-hint).
    /// Эти переменные нигде не constraint'ятся: их значения свободны.
    fn fresh_struct_for_type(&mut self, ty: &str, prefix: &str) -> Result<Value, String> {
        if ty == "ValU32" || ty == "DenormedValU32" {
            let low_name  = self.fresh(prefix, "ext_low");
            let high_name = self.fresh(prefix, "ext_high");
            // extern hints — это произвольные значения от prover'а; ставим Val-диапазон.
            // Для DoDiv это ок: их значения попадают в NondetReg/NondetU16Reg, которые
            // создают СОБСТВЕННЫЕ properly-ranged переменные.
            return Ok(Value::make_struct(vec![
                ("low",  Value::Expr(IrExpr::Var(low_name))),
                ("high", Value::Expr(IrExpr::Var(high_name))),
            ]));
        }
        if let Some(comp_def) = self.components.get(ty).cloned() {
            // Пользовательский тип-структура: каждое public-поле становится
            // свежей переменной (или вложенной структурой, если поле — тоже
            // структурный тип). Тип определяем по RHS биндинга:
            //  - `ValU32(...)` / `DenormedValU32(...)` → struct (low, high)
            //  - `Ident(p)` где p — параметр типа ValU32 → struct
            //  - иначе скаляр
            let mut fields = HashMap::new();
            for stmt in &comp_def.body {
                if let Stmt::Binding { is_public: true, name: fname, value } = stmt {
                    let inferred_type: Option<String> = match value {
                        Expr::Call { name: ctor, .. }
                            if ctor == "ValU32" || ctor == "DenormedValU32" => Some(ctor.clone()),
                        Expr::Ident(pname) => {
                            comp_def.params.iter()
                                .find(|(n, _)| n == pname)
                                .map(|(_, t)| t.clone())
                        }
                        _ => None,
                    };
                    let field_value = match inferred_type {
                        Some(t) if t == "ValU32" || t == "DenormedValU32" => {
                            self.fresh_struct_for_type(&t, prefix)?
                        }
                        Some(t) if self.components.contains_key(&t) => {
                            self.fresh_struct_for_type(&t, prefix)?
                        }
                        _ => Value::Expr(IrExpr::Var(self.fresh(prefix, fname))),
                    };
                    fields.insert(fname.clone(), field_value);
                }
            }
            return Ok(Value::Struct(fields));
        }
        // Скаляр (Val и т.п.) — одна свежая переменная.
        Ok(Value::Expr(IrExpr::Var(self.fresh(prefix, "ext"))))
    }

    /// UF-абстракция вызова компонента: создаём свежие переменные для каждого
    /// public-поля и единый IrConstraint::Call. Body не раскрываем — за счёт
    /// функциональности UF в SMT (same args → same outputs) композиция получает
    /// нужное «лемма-from-independent-verification» свойство.
    fn abstract_call(
        &mut self,
        comp: &ComponentDef,
        name: &str,
        args: &[Value],
        spec: &mut InstructionSpec,
        prefix: &str,
    ) -> Result<Value, String> {
        // 1) Уплощаем аргументы согласно типам параметров.
        //    ValU32 / DenormedValU32 → 2 IrExpr (low, high)
        //    user-component-type     → по числу public-полей
        //    скалярный тип           → 1 IrExpr
        let mut flat_args: Vec<IrExpr> = Vec::new();
        for (i, (_pname, ptype)) in comp.params.iter().enumerate() {
            if i >= args.len() {
                return Err(format!("abstract {}: param {} out of args", name, i));
            }
            let arg = &args[i];
            if ptype == "ValU32" || ptype == "DenormedValU32" {
                flat_args.push(arg.field("low").ok_or("missing .low")?.to_expr());
                flat_args.push(arg.field("high").ok_or("missing .high")?.to_expr());
            } else if let Some(comp_def) = self.components.get(ptype.as_str()) {
                for stmt in &comp_def.body {
                    if let Stmt::Binding { is_public: true, name: fname, .. } = stmt {
                        let v = arg.field(fname)
                            .ok_or(format!("missing field {} on {}", fname, ptype))?;
                        flat_args.push(v.to_expr());
                    }
                }
            } else {
                flat_args.push(arg.to_expr());
            }
        }
        // 2) Public-биндинги этого компонента (имя + RHS-выражение для определения формы).
        let pub_bindings: Vec<(String, Expr)> = comp.body.iter().filter_map(|s| {
            if let Stmt::Binding { is_public: true, name, value } = s {
                Some((name.clone(), value.clone()))
            } else { None }
        }).collect();
        if pub_bindings.is_empty() {
            return Err(format!("abstract {}: no public outputs", name));
        }
        // 3) Свежие internal-переменные на каждое поле.
        //    Если public-биндинг — это `ValU32(...)` / `DenormedValU32(...)`,
        //    разворачиваем в две UF (low + high), чтобы вызывающие, ожидающие
        //    struct-форму, могли честно делать .low/.high.
        let mut struct_fields: HashMap<String, Value> = HashMap::new();
        let mut output_pairs: Vec<(String, String)> = Vec::new();
        for (fname, value) in &pub_bindings {
            let is_struct_output = matches!(value,
                Expr::Call { name: ctor, .. } if ctor == "ValU32" || ctor == "DenormedValU32"
            );
            if is_struct_output {
                let low_name  = self.fresh(prefix, &format!("{}_{}_low", name.to_lowercase(), fname));
                let high_name = self.fresh(prefix, &format!("{}_{}_high", name.to_lowercase(), fname));
                spec.internals.push(Var { name: low_name.clone(),  vtype: VarType::U16 });
                spec.internals.push(Var { name: high_name.clone(), vtype: VarType::U16 });
                struct_fields.insert(fname.clone(), Value::make_struct(vec![
                    ("low",  Value::Expr(IrExpr::Var(low_name.clone()))),
                    ("high", Value::Expr(IrExpr::Var(high_name.clone()))),
                ]));
                // Кодируем в Call-сообщении: имя поля с суффиксом ".low" / ".high".
                output_pairs.push((format!("{}.low",  fname), low_name));
                output_pairs.push((format!("{}.high", fname), high_name));
            } else {
                let vname = self.fresh(prefix, &format!("{}_{}", name.to_lowercase(), fname));
                spec.internals.push(Var { name: vname.clone(), vtype: VarType::Val });
                struct_fields.insert(fname.clone(), Value::Expr(IrExpr::Var(vname.clone())));
                output_pairs.push((fname.clone(), vname));
            }
        }
        // 4) Записываем Call-constraint, который верификатор превратит в declare-fun + asserts.
        spec.constraints.push(IrConstraint::Call {
            component: name.to_string(),
            args: flat_args,
            outputs: output_pairs,
        });
        Ok(Value::Struct(struct_fields))
    }

    fn guess_type(&self, expr: &Expr) -> VarType {
        match expr {
            Expr::Call { name, .. } => match name.as_str() {
                "NondetU16Reg"|"U16Reg" => VarType::U16,
                "NondetBitReg" => VarType::Bit,
                "NondetTwitReg" => VarType::Twit,
                "Reg" => VarType::Val,
                "IsZero" => VarType::Bit,
                _ => VarType::Val,
            },
            _ => VarType::Val,
        }
    }
}
