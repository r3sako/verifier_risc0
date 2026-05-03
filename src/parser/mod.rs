pub mod ast;
pub mod lexer;

use ast::*;
use lexer::{Token, tokenize};

pub struct Parser { tokens: Vec<lexer::SpannedToken>, pos: usize }

impl Parser {
    pub fn parse_file(source: &str) -> Result<Vec<Item>, String> {
        let tokens = tokenize(source)?;
        let mut p = Parser { tokens, pos: 0 };
        p.items()
    }

    fn peek(&self) -> &Token { &self.tokens[self.pos].token }
    fn line(&self) -> usize { self.tokens[self.pos].line }
    fn advance(&mut self) -> Token { let t=self.tokens[self.pos].token.clone(); self.pos+=1; t }

    fn expect(&mut self, e: &Token) -> Result<(), String> {
        if std::mem::discriminant(self.peek())==std::mem::discriminant(e) { self.advance(); Ok(()) }
        else { Err(format!("Expected {:?}, got {:?} line {}", e, self.peek(), self.line())) }
    }
    fn ident(&mut self) -> Result<String, String> {
        if let Token::Ident(s)=self.peek().clone() { self.advance(); Ok(s) }
        else { Err(format!("Expected ident line {}", self.line())) }
    }
    fn int_lit(&mut self) -> Result<u64, String> {
        if let Token::IntLit(n)=self.peek().clone() { self.advance(); Ok(n) }
        else { Err(format!("Expected int line {}", self.line())) }
    }

    fn items(&mut self) -> Result<Vec<Item>, String> {
        let mut items=Vec::new();
        while *self.peek()!=Token::Eof {
            match self.peek() {
                // Атрибут #[ident] перед component — пропускаем
                Token::Hash => {
                    self.advance();
                    self.expect(&Token::LBracket)?;
                    let _ = self.ident()?;
                    self.expect(&Token::RBracket)?;
                }
                // test NAME { ... } — пропускаем целиком (это не component, а пример)
                Token::Test => {
                    self.advance();
                    let _ = self.ident()?;
                    self.expect(&Token::LBrace)?;
                    let mut depth = 1;
                    while depth > 0 {
                        match self.peek() {
                            Token::LBrace => { self.advance(); depth += 1; }
                            Token::RBrace => { self.advance(); depth -= 1; }
                            Token::Eof => return Err(format!("EOF in test block line {}", self.line())),
                            _ => { self.advance(); }
                        }
                    }
                }
                Token::Import => { self.advance(); let n=self.ident()?; self.expect(&Token::Semicolon)?; items.push(Item::Import(n)); }
                // extern NAME(params...) : RETTYPE;
                // Имя и return type запоминаем — нужны при вызове extern в IR
                // (возвращает структуру указанного типа со свежими переменными).
                Token::Extern => {
                    self.advance();
                    let name = self.ident()?;
                    self.expect(&Token::LParen)?;
                    // Скипаем список параметров (типы args не нужны верификатору).
                    let mut depth = 1;
                    while depth > 0 {
                        match self.peek() {
                            Token::LParen => { self.advance(); depth += 1; }
                            Token::RParen => { self.advance(); depth -= 1; }
                            Token::Eof => return Err(format!("EOF in extern '{}' line {}", name, self.line())),
                            _ => { self.advance(); }
                        }
                    }
                    self.expect(&Token::Colon)?;
                    let return_type = self.ident()?;
                    self.expect(&Token::Semicolon)?;
                    items.push(Item::Extern { name, return_type });
                }
                Token::Component => items.push(self.component()?),
                _ => return Err(format!("Unexpected {:?} line {}", self.peek(), self.line())),
            }
        }
        Ok(items)
    }

    fn component(&mut self) -> Result<Item, String> {
        let sl=self.line();
        self.expect(&Token::Component)?;
        let name=self.ident()?;
        let tp = if *self.peek()==Token::LAngle {
            self.advance();
            let mut v=Vec::new();
            loop { if *self.peek()==Token::RAngle{break;} let n=self.ident()?; self.expect(&Token::Colon)?; let t=self.ident()?; v.push((n,t)); if *self.peek()==Token::Comma{self.advance();} }
            self.expect(&Token::RAngle)?; v
        } else { vec![] };
        self.expect(&Token::LParen)?;
        let mut params=Vec::new();
        while *self.peek()!=Token::RParen { let n=self.ident()?; self.expect(&Token::Colon)?; let t=self.ident()?; params.push((n,t)); if *self.peek()==Token::Comma{self.advance();} }
        self.expect(&Token::RParen)?;
        self.expect(&Token::LBrace)?;
        let mut body=Vec::new();
        while *self.peek()!=Token::RBrace { body.push(self.stmt()?); }
        self.expect(&Token::RBrace)?;
        Ok(Item::Component(ComponentDef{name,type_params:tp,params,body,source_line:sl}))
    }

    fn stmt(&mut self) -> Result<Stmt, String> {
        // Multi-way major mux: `[g1, g2, ...] -> ({...}, {...}, ...);`
        // (открывается с LBracket на позиции statement; индексирование
        // `arr[i]` имеет место только в постфиксе на уровне выражения)
        if *self.peek() == Token::LBracket {
            return self.mux_stmt();
        }
        let is_pub = if *self.peek()==Token::Public{self.advance();true}else{false};
        if let Token::Ident(_)=self.peek() {
            let saved=self.pos;
            if let Ok(name)=self.ident() {
                // Макрос-statement: IDENT ! ( ... ) ;  — пропускаем целиком (no-op).
                // Используется для AssumeRange!, AssumeBit! и подобных в spec'ах.
                if *self.peek()==Token::Bang {
                    if is_pub { return Err(format!("'public' before macro line {}", self.line())); }
                    self.advance(); // !
                    self.expect(&Token::LParen)?;
                    let mut depth = 1;
                    while depth > 0 {
                        match self.peek() {
                            Token::LParen => { self.advance(); depth += 1; }
                            Token::RParen => { self.advance(); depth -= 1; }
                            Token::Eof => return Err(format!("EOF in macro '{}' line {}", name, self.line())),
                            _ => { self.advance(); }
                        }
                    }
                    self.expect(&Token::Semicolon)?;
                    return Ok(Stmt::ExprStmt(Expr::IntLit(0)));
                }
                if *self.peek()==Token::ColonEq {
                    self.advance(); let v=self.expr()?; self.expect(&Token::Semicolon)?;
                    return Ok(Stmt::Binding{is_public:is_pub,name,value:v});
                }
                self.pos=saved;
            }
        }
        if is_pub { return Err(format!("'public' needs binding line {}", self.line())); }
        let e=self.expr()?;
        if *self.peek()==Token::Eq { self.advance(); let r=self.expr()?; self.expect(&Token::Semicolon)?; Ok(Stmt::Constraint{lhs:e,rhs:r}) }
        else if *self.peek()==Token::Semicolon { self.advance(); Ok(Stmt::ExprStmt(e)) }
        else if *self.peek()==Token::RBrace { Ok(Stmt::ExprStmt(e)) }
        else { Err(format!("Expected ; or = line {}", self.line())) }
    }

    /// Парсит multi-way major mux:
    ///     `[g1, g2, ...] -> ({block1}, {block2}, ...);`
    /// или
    ///     `[g1, g2, ...] ->! ({block1}, {block2}, ...);`
    /// Bang-вариант (`->!`) встречается в test'ах; здесь, на уровне components,
    /// без bang. Парсим оба варианта одинаково — на верификацию это не влияет.
    fn mux_stmt(&mut self) -> Result<Stmt, String> {
        self.expect(&Token::LBracket)?;
        let mut guards = Vec::new();
        if *self.peek() != Token::RBracket {
            guards.push(self.expr()?);
            while *self.peek() == Token::Comma { self.advance(); guards.push(self.expr()?); }
        }
        self.expect(&Token::RBracket)?;
        // Стрелка: `-` `>` или `-` `>` `!`
        self.expect(&Token::Minus)?;
        self.expect(&Token::RAngle)?;
        if *self.peek() == Token::Bang { self.advance(); }
        self.expect(&Token::LParen)?;
        let mut branches: Vec<Vec<Stmt>> = Vec::new();
        if *self.peek() != Token::RParen {
            branches.push(self.block_stmts()?);
            while *self.peek() == Token::Comma {
                self.advance();
                branches.push(self.block_stmts()?);
            }
        }
        self.expect(&Token::RParen)?;
        // Точка с запятой обязательна для statement-формы
        self.expect(&Token::Semicolon)?;
        if guards.len() != branches.len() {
            return Err(format!("mux: {} guards but {} branches at line {}",
                guards.len(), branches.len(), self.line()));
        }
        Ok(Stmt::Mux { guards, branches })
    }

    /// Парсит блок statement'ов в фигурных скобках: `{ stmt; stmt; ... }`.
    fn block_stmts(&mut self) -> Result<Vec<Stmt>, String> {
        self.expect(&Token::LBrace)?;
        let mut body = Vec::new();
        while *self.peek() != Token::RBrace {
            body.push(self.stmt()?);
        }
        self.expect(&Token::RBrace)?;
        Ok(body)
    }

    fn expr(&mut self) -> Result<Expr, String> { self.additive() }

    fn additive(&mut self) -> Result<Expr, String> {
        let mut l=self.multiplicative()?;
        loop { match self.peek() {
            Token::Plus => { self.advance(); let r=self.multiplicative()?; l=Expr::BinOp{op:Op::Add,lhs:Box::new(l),rhs:Box::new(r)}; }
            Token::Minus => { self.advance(); let r=self.multiplicative()?; l=Expr::BinOp{op:Op::Sub,lhs:Box::new(l),rhs:Box::new(r)}; }
            _ => break,
        }}
        Ok(l)
    }

    fn multiplicative(&mut self) -> Result<Expr, String> {
        let mut l=self.bitwise()?;
        loop { match self.peek() {
            Token::Star => { self.advance(); let r=self.bitwise()?; l=Expr::BinOp{op:Op::Mul,lhs:Box::new(l),rhs:Box::new(r)}; }
            Token::Slash => { self.advance(); let r=self.bitwise()?; l=Expr::BinOp{op:Op::Div,lhs:Box::new(l),rhs:Box::new(r)}; }
            _ => break,
        }}
        Ok(l)
    }

    fn bitwise(&mut self) -> Result<Expr, String> {
        let mut l=self.postfix()?;
        loop { if *self.peek()==Token::Ampersand { self.advance(); let r=self.postfix()?; l=Expr::BinOp{op:Op::BitAnd,lhs:Box::new(l),rhs:Box::new(r)}; } else { break; } }
        Ok(l)
    }

    fn postfix(&mut self) -> Result<Expr, String> {
        let mut e=self.primary()?;
        loop { match self.peek() {
            Token::Dot => { self.advance(); let f=self.ident()?; e=Expr::Field{object:Box::new(e),field:f}; }
            Token::LBracket => { self.advance(); let i=self.expr()?; self.expect(&Token::RBracket)?; e=Expr::Index{object:Box::new(e),index:Box::new(i)}; }
            _ => break,
        }}
        Ok(e)
    }

    fn primary(&mut self) -> Result<Expr, String> {
        match self.peek().clone() {
            Token::IntLit(n) => { self.advance(); Ok(Expr::IntLit(n)) }
            Token::LParen => { self.advance(); let e=self.expr()?; self.expect(&Token::RParen)?; Ok(e) }
            Token::For => {
                self.advance(); let v=self.ident()?; self.expect(&Token::Colon)?;
                let s=self.int_lit()?; self.expect(&Token::DotDot)?; let end=self.int_lit()?;
                self.expect(&Token::LBrace)?; let b=self.expr()?; self.expect(&Token::RBrace)?;
                Ok(Expr::For{var:v,start:s,end,body:Box::new(b)})
            }
            Token::Ident(name) => {
                self.advance();
                if *self.peek()==Token::LAngle {
                    self.advance(); let ta=self.int_lit()?; self.expect(&Token::RAngle)?;
                    self.expect(&Token::LParen)?; let a=self.args()?; self.expect(&Token::RParen)?;
                    Ok(Expr::Call{name,type_args:vec![ta],args:a})
                } else if *self.peek()==Token::LParen {
                    self.advance(); let a=self.args()?; self.expect(&Token::RParen)?;
                    Ok(Expr::Call{name,type_args:vec![],args:a})
                } else { Ok(Expr::Ident(name)) }
            }
            _ => Err(format!("Unexpected {:?} in expr line {}", self.peek(), self.line())),
        }
    }

    fn args(&mut self) -> Result<Vec<Expr>, String> {
        let mut a=Vec::new();
        if *self.peek()==Token::RParen { return Ok(a); }
        a.push(self.expr()?);
        while *self.peek()==Token::Comma { self.advance(); a.push(self.expr()?); }
        Ok(a)
    }
}
