use std::fmt;

#[derive(Debug, Clone)]
pub enum Item {
    Import(String),
    Component(ComponentDef),
    /// `extern NAME(params...) : RETTYPE;` — внешняя prover-функция (hint).
    /// Семантика для верификатора: имя, число аргументов и тип возвращаемого
    /// значения (тип параметров нерелевантен — args не constraint'ятся).
    Extern { name: String, return_type: String },
}

#[derive(Debug, Clone)]
pub struct ComponentDef {
    pub name: String,
    pub type_params: Vec<(String, String)>,
    pub params: Vec<(String, String)>,  // (name, type)
    pub body: Vec<Stmt>,
    pub source_line: usize,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Binding { is_public: bool, name: String, value: Expr },
    Constraint { lhs: Expr, rhs: Expr },
    ExprStmt(Expr),
    /// Multi-way major mux Zirgen: `[g1, g2, ...] -> ({block1}, {block2}, ...);`.
    /// Семантика: каждая constraint в branch i имеет вид g_i * lhs = g_i * rhs.
    /// Если g_i = 0, constraint тривиален (0=0); если g_i = 1, активен оригинал.
    /// Сумма guards = 1 и каждый — бит (структурно обеспечивается NondetBitReg
    /// + явным "хвостом" 1 - g1 - g2 - ...).
    Mux { guards: Vec<Expr>, branches: Vec<Vec<Stmt>> },
}

#[derive(Debug, Clone)]
pub enum Expr {
    IntLit(u64),
    Ident(String),
    Field { object: Box<Expr>, field: String },
    BinOp { op: Op, lhs: Box<Expr>, rhs: Box<Expr> },
    Call { name: String, type_args: Vec<u64>, args: Vec<Expr> },
    Index { object: Box<Expr>, index: Box<Expr> },
    For { var: String, start: u64, end: u64, body: Box<Expr> },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op { Add, Sub, Mul, Div, BitAnd }

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self { Op::Add=>write!(f,"+"), Op::Sub=>write!(f,"-"), Op::Mul=>write!(f,"*"), Op::Div=>write!(f,"/"), Op::BitAnd=>write!(f,"&") }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::IntLit(n) => write!(f, "{}", n),
            Expr::Ident(s) => write!(f, "{}", s),
            Expr::Field { object, field } => write!(f, "{}.{}", object, field),
            Expr::BinOp { op, lhs, rhs } => write!(f, "({} {} {})", lhs, op, rhs),
            Expr::Call { name, type_args, args } => {
                write!(f, "{}", name)?;
                if !type_args.is_empty() { write!(f, "<{}>", type_args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(","))?; }
                write!(f, "({})", args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "))
            }
            Expr::Index { object, index } => write!(f, "{}[{}]", object, index),
            Expr::For { var, start, end, body } => write!(f, "for {}:{}..{}{{{}}}", var, start, end, body),
        }
    }
}
