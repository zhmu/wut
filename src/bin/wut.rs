extern crate wut;

use std::fs::File;
use wut::stream::{CharStream, FileStream};

#[derive(Debug,Clone,PartialEq)]
enum Token {
    Plus,
    Minus,
    Star,
    Slash,
    Semicolon,
    Equals,
    IntLiteral(i32),
    EndOfStream,
    Int,
    Identifier(String),
}

#[derive(Debug,PartialEq)]
enum AstOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Assign,
}

#[derive(Debug,PartialEq)]
enum AstNode {
    BinaryOp(AstOp, Box<AstNode>, Box<AstNode>),
    IntegerLiteral(i32),
    LValueIdentifier(String),
    DeclareVariable(String),
}

fn get_token_operator_precedence(t: &Token) -> Result<i32, WutError> {
    match t {
        Token::Plus => { Ok(10) },
        Token::Minus => { Ok(10) },
        Token::Star => { Ok(20) },
        Token::Slash => { Ok(20) },
        _ => { Err(WutError::UnexpectedToken(t.clone())) },
    }
}

fn is_alpha(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn scan_int(is: &mut dyn CharStream) -> i32 {
    let mut result: i32 = 0;
    loop {
        match is.next() {
            Some(ch) => {
                if !is_digit(ch) {
                    is.put_front(ch);
                    break
                }

                result = result * 10 + (ch as i32 - '0' as i32);
            },
            None => { break }
        }
    }
    result
}

fn scan_ident(is: &mut dyn CharStream) -> String {
    let mut result = String::new();
    loop {
        match is.next() {
            Some(ch) => {
                if !is_digit(ch) && !is_alpha(ch) && ch != '_' {
                    is.put_front(ch);
                    break
                }

                result.push(ch);
            },
            None => { break }
        }
    }
    result
}

fn get_token_from_ident(ident: &str) -> Result<Token, WutError> {
    if ident == "int" {
        return Ok(Token::Int)
    }
    Ok(Token::Identifier(ident.to_string()))
}

fn scan(is: &mut dyn CharStream) -> Result<Token, WutError> {
    match is.skip() {
        Some(ch) => {
            return match ch {
                '+' => { Ok(Token::Plus) },
                '-' => { Ok(Token::Minus) },
                '*' => { Ok(Token::Star) },
                '/' => { Ok(Token::Slash) },
                ';' => { Ok(Token::Semicolon) },
                '=' => { Ok(Token::Equals) },
                _ => {
                    if is_digit(ch) {
                        is.put_front(ch);
                        let i = scan_int(is);
                        return Ok(Token::IntLiteral(i))
                    } else if is_alpha(ch) || ch == '_' {
                        is.put_front(ch);
                        let id = scan_ident(is);
                        return get_token_from_ident(&id)
                    }
                    Err(WutError::UnexpectedChar(ch))
                }
            }
        },
        None => { Ok(Token::EndOfStream) },
    }
}

fn match_token_and_scan<F>(is: &mut dyn CharStream, t: &Token, msg: &str, func: F) -> Result<Token, WutError>
    where F: FnOnce(&Token) -> bool
{
    if !func(t) {
        return Err(WutError::Mismatch(msg.to_string()));
    }
    scan(is)
}

fn match_ident(is: &mut dyn CharStream, t: &Token) -> Result<(String, Token), WutError> {
    let next_token = match_token_and_scan(is, t, "expected identifier", |t| matches!(*t, Token::Identifier{..}))?;

    return match t {
        Token::Identifier(ref id) => { Ok((id.to_string(), next_token)) },
        _ => { unreachable!() }
    };
}

fn match_semicolon(is: &mut dyn CharStream, t: &Token) -> Result<Token, WutError> {
    match_token_and_scan(is, t, "expected ';'", |t| *t == Token::Semicolon)
}

fn var_declaration(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let ident = match_token_and_scan(is, t, "expected 'Int'", |t| *t == Token::Int)?;
    let (ident, t) = match_ident(is, &ident)?;
    let t = match_semicolon(is, &t)?;

    let node = AstNode::DeclareVariable(ident);
    Ok((node, t))
}

fn assignment(is: &mut dyn CharStream, ident: &Token) -> Result<(AstNode, Token), WutError> {
    let (ident, t) = match_ident(is, ident)?;

    let t = match_token_and_scan(is, &t, "expected '='", |t| *t == Token::Equals)?;
    let (left, t) = binexpr(is, &t, 0, 0)?;
    let t = match_semicolon(is, &t)?;

    let right = AstNode::LValueIdentifier(ident.to_string());

    let node = AstNode::BinaryOp(AstOp::Assign, Box::new(left), Box::new(right));
    Ok((node, t))
}

fn statements(is: &mut dyn CharStream) -> Result<Vec<AstNode>, WutError> {
    let mut result: Vec<AstNode> = Vec::new();
    let mut t = scan(is)?;
    loop {
        match t {
            Token::Int => {
                let (node, next_token) = var_declaration(is, &t)?;
                result.push(node);
                t = next_token;
            },
            Token::Identifier(_) => {
                let (node, next_token) = assignment(is, &t)?;
                result.push(node);
                t = next_token;
            },
            Token::EndOfStream => {
                return Ok(result)
            },
            t => {
                return Err(WutError::UnexpectedToken(t))
            }
        }
    }
}

#[derive(Debug,PartialEq)]
enum WutError {
    SyntaxError(Token),
    UnexpectedToken(Token),
    UnexpectedChar(char),
    Mismatch(String),
}

fn token_to_astop(t: &Token) -> Result<AstOp, WutError> {
    match t {
        Token::Plus => { Ok(AstOp::Add) },
        Token::Minus => { Ok(AstOp::Subtract) },
        Token::Star => { Ok(AstOp::Multiply) },
        Token::Slash => { Ok(AstOp::Divide) },
        _ => { Err(WutError::UnexpectedToken(t.clone())) },
    }
}


fn primary(t: &Token) -> Result<AstNode, WutError> {
    match t {
        Token::IntLiteral(i) => {
            Ok(AstNode::IntegerLiteral(*i))
        },
        Token::Identifier(id) => {
            Ok(AstNode::LValueIdentifier(id.to_string()))
        },
        _ => {
            Err(WutError::SyntaxError(t.clone()))
        }
    }
}

fn binexpr(is: &mut dyn CharStream, token: &Token, prev_token_precedence: i32, level: i32) -> Result<(AstNode, Token), WutError> {
    let mut left = primary(&token)?;

    let mut current_token = scan(is)?;
    if let Token::Semicolon = current_token {
        return Ok((left, current_token))
    }

    loop {
        let current_token_precedence = get_token_operator_precedence(&current_token)?;
        if current_token_precedence <= prev_token_precedence { break; }

        let token = scan(is)?;
        let node_op = token_to_astop(&current_token)?;
        let (right, next_token) = binexpr(is, &token, current_token_precedence, level + 1)?;
        current_token = next_token;

        left = AstNode::BinaryOp(node_op, Box::new(left), Box::new(right));
        if let Token::Semicolon = current_token {
            break;
        }
    }
    Ok((left, current_token))
}

fn main() -> Result<(), std::io::Error> {
    let f = File::open("t.c")?;
    let mut is = FileStream::new(f);
    //let mut is = StringStream::new("2 *3 + 4*5");

    let s = statements(&mut is).unwrap();
    println!("{:?}", s);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use wut::stream::StringStream;

    fn invoke_scan(s: &str) -> Result<Token, WutError> {
        let mut ss = StringStream::new(&s);
        scan(&mut ss)
    }

    fn invoke_binexpr(s: &str) -> Result<(AstNode, Token), WutError> {
        let mut ss = StringStream::new(&s);
        let t = scan(&mut ss).unwrap();
        binexpr(&mut ss, &t, 0, 0)
    }

    fn invoke_binexpr_and_get_ast(s: &str) -> AstNode {
        let n = invoke_binexpr(s).unwrap();
        assert_eq!(Token::Semicolon, n.1);
        n.0
    }

    fn invoke_statements(s: &str) -> Result<Vec<AstNode>, WutError> {
        let mut ss = StringStream::new(&s);
        statements(&mut ss)
    }

    #[test]
    fn parse_single_digit_integer_literal() {
        let ast = invoke_binexpr_and_get_ast("9;");
        assert_eq!(AstNode::IntegerLiteral(9), ast);
    }

    #[test]
    fn parse_multiple_digit_integer_literal() {
        let ast = invoke_binexpr_and_get_ast("1234;");
        assert_eq!(AstNode::IntegerLiteral(1234), ast);
    }

    #[test]
    fn parse_add_without_integer() {
        let r = invoke_binexpr("+");
        assert_eq!(Err(WutError::SyntaxError(Token::Plus)), r);
    }

    #[test]
    fn parse_add_missing_argument() {
        let r = invoke_binexpr("1+");
        assert_eq!(Err(WutError::SyntaxError(Token::EndOfStream)), r);
    }

    #[test]
    fn parse_single_add() {
        let ast = invoke_binexpr_and_get_ast("1+2;");
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Add,
                Box::new(AstNode::IntegerLiteral(1)),
                Box::new(AstNode::IntegerLiteral(2))
            ), ast);
    }

    #[test]
    fn parse_multiple_add() {
        let ast = invoke_binexpr_and_get_ast("1+2+3;");
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Add,
                Box::new(AstNode::BinaryOp(
                    AstOp::Add,
                    Box::new(AstNode::IntegerLiteral(1)),
                    Box::new(AstNode::IntegerLiteral(2))
                )),
                Box::new(AstNode::IntegerLiteral(3))
            ), ast);
    }

    #[test]
    fn parse_add_multiply_precedence() {
        let ast = invoke_binexpr_and_get_ast("1*2+3*4;");
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Add,
                Box::new(AstNode::BinaryOp(
                    AstOp::Multiply,
                    Box::new(AstNode::IntegerLiteral(1)),
                    Box::new(AstNode::IntegerLiteral(2))
                )),
                Box::new(AstNode::BinaryOp(
                    AstOp::Multiply,
                    Box::new(AstNode::IntegerLiteral(3)),
                    Box::new(AstNode::IntegerLiteral(4))
                )),
            ), ast);
    }

    #[test]
    fn parse_unrecognized_identifier() {
        let r = invoke_scan("foo");
        assert_eq!(Ok(Token::Identifier("foo".to_string())), r);
    }

    #[test]
    fn statement_declare_single_int() {
        let s = invoke_statements("int i;").unwrap();
        assert_eq!(1, s.len());
        assert_eq!(AstNode::DeclareVariable("i".to_string()), *s.first().unwrap());
    }

    #[test]
    fn statement_assign_var_int() {
        let s = invoke_statements("a=1;").unwrap();
        assert_eq!(1, s.len());
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Assign,
                Box::new(AstNode::IntegerLiteral(1)),
                Box::new(AstNode::LValueIdentifier("a".to_string())),
            ), *s.first().unwrap());
    }

    #[test]
    fn statement_assign_var_expr() {
        let s = invoke_statements("a=1+2;").unwrap();
        assert_eq!(1, s.len());
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Assign,
                Box::new(
                    AstNode::BinaryOp(
                        AstOp::Add,
                        Box::new(AstNode::IntegerLiteral(1)),
                        Box::new(AstNode::IntegerLiteral(2))
                    )
                ),
                Box::new(AstNode::LValueIdentifier("a".to_string())),
            ), *s.first().unwrap());
    }
}
