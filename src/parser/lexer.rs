#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Component, Import, Public, For, Test, Extern,
    Ident(String), IntLit(u64),
    LParen, RParen, LBrace, RBrace, LBracket, RBracket, LAngle, RAngle,
    Colon, ColonEq, Semicolon, Comma, Dot, DotDot, Eq,
    Plus, Minus, Star, Slash, Ampersand,
    Hash, Bang,
    Eof,
}

pub struct SpannedToken { pub token: Token, pub line: usize }

pub fn tokenize(input: &str) -> Result<Vec<SpannedToken>, String> {
    let chars: Vec<char> = input.chars().collect();
    let (mut pos, mut line) = (0, 1);
    let mut tokens = Vec::new();

    loop {
        // skip whitespace + comments (line // и block /* */)
        loop {
            while pos < chars.len() && chars[pos].is_whitespace() { if chars[pos]=='\n'{line+=1;} pos+=1; }
            if pos+1 < chars.len() && chars[pos]=='/' && chars[pos+1]=='/' {
                while pos < chars.len() && chars[pos]!='\n' { pos+=1; }
                continue;
            }
            if pos+1 < chars.len() && chars[pos]=='/' && chars[pos+1]=='*' {
                pos += 2;
                while pos+1 < chars.len() && !(chars[pos]=='*' && chars[pos+1]=='/') {
                    if chars[pos]=='\n' { line += 1; }
                    pos += 1;
                }
                if pos+1 < chars.len() { pos += 2; } // съесть */
                continue;
            }
            break;
        }
        if pos >= chars.len() { tokens.push(SpannedToken{token:Token::Eof,line}); break; }

        let ln = line;
        let c = chars[pos]; pos += 1;
        let token = match c {
            '(' => Token::LParen, ')' => Token::RParen,
            '{' => Token::LBrace, '}' => Token::RBrace,
            '[' => Token::LBracket, ']' => Token::RBracket,
            '<' => Token::LAngle, '>' => Token::RAngle,
            ';' => Token::Semicolon, ',' => Token::Comma,
            '+' => Token::Plus, '-' => Token::Minus,
            '*' => Token::Star, '/' => Token::Slash, '&' => Token::Ampersand,
            '#' => Token::Hash, '!' => Token::Bang,
            ':' => if pos<chars.len()&&chars[pos]=='=' { pos+=1; Token::ColonEq } else { Token::Colon },
            '.' => if pos<chars.len()&&chars[pos]=='.' { pos+=1; Token::DotDot } else { Token::Dot },
            '=' => Token::Eq,
            '0' if pos<chars.len()&&(chars[pos]=='x'||chars[pos]=='X') => {
                pos+=1; let mut h=String::new();
                while pos<chars.len()&&chars[pos].is_ascii_hexdigit() { h.push(chars[pos]); pos+=1; }
                Token::IntLit(u64::from_str_radix(&h,16).map_err(|e|format!("hex: {}",e))?)
            }
            c if c.is_ascii_digit() => {
                let mut n=String::from(c);
                while pos<chars.len()&&chars[pos].is_ascii_digit() { n.push(chars[pos]); pos+=1; }
                Token::IntLit(n.parse().map_err(|e|format!("int: {}",e))?)
            }
            c if c.is_ascii_alphabetic()||c=='_' => {
                let mut id=String::from(c);
                while pos<chars.len()&&(chars[pos].is_ascii_alphanumeric()||chars[pos]=='_') { id.push(chars[pos]); pos+=1; }
                match id.as_str() {
                    "component"=>Token::Component, "import"=>Token::Import,
                    "public"=>Token::Public, "for"=>Token::For,
                    "test"=>Token::Test, "extern"=>Token::Extern,
                    _ => Token::Ident(id),
                }
            }
            _ => return Err(format!("Unexpected '{}' at line {}", c, ln)),
        };
        tokens.push(SpannedToken{token, line: ln});
    }
    Ok(tokens)
}
