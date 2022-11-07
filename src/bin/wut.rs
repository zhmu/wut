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
    Assign,
    IntLiteral(i32),
    EndOfStream,
    Int,
    Identifier(String),
    Equals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    If,
    Else,
    While,
    For,
    Void,
}

#[derive(Debug,PartialEq)]
enum AstOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Assign,
    Equals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
}

#[derive(Debug,PartialEq)]
enum AstNode {
    Empty,
    Glue(Box<AstNode>, Box<AstNode>),
    BinaryOp(AstOp, Box<AstNode>, Box<AstNode>),
    If(Box<AstNode>, Box<AstNode>, Option<Box<AstNode>>),
    IntegerLiteral(i32),
    LValueIdentifier(String),
    DeclareVariable(String),
    While(Box<AstNode>, Box<AstNode>),
    Function(String, Box<AstNode>),
}

fn get_token_operator_precedence(t: &Token) -> Result<i32, WutError> {
    match t {
        Token::Plus | Token::Minus => { Ok(10) },
        Token::Star | Token::Slash => { Ok(20) },
        Token::Equals | Token::NotEquals => { Ok(30) },
        Token::LessThan | Token::GreaterThan | Token::LessEqual | Token::GreaterEqual => { Ok(40) },
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
    } else if ident == "if" {
        return Ok(Token::If)
    } else if ident == "else" {
        return Ok(Token::Else)
    } else if ident == "while" {
        return Ok(Token::While)
    } else if ident == "for" {
        return Ok(Token::For)
    } else if ident == "void" {
        return Ok(Token::Void)
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
                '{' => { Ok(Token::LeftBrace) },
                '}' => { Ok(Token::RightBrace) },
                '(' => { Ok(Token::LeftParen) },
                ')' => { Ok(Token::RightParen) },
                '=' => {
                    if let Some(ch) = is.next() {
                        if ch == '=' {
                            return Ok(Token::Equals)
                        }
                        is.put_front(ch);
                    }
                    Ok(Token::Assign)
                },
                '!' => {
                    if let Some(ch) = is.next() {
                        if ch == '=' {
                            return Ok(Token::NotEquals)
                        }
                        return Err(WutError::UnexpectedChar(ch))
                    }
                    Err(WutError::UnexpectedEndOfStream)
                },
                '<' => {
                    if let Some(ch) = is.next() {
                        if ch == '=' {
                            return Ok(Token::LessEqual)
                        }
                        is.put_front(ch);
                    }
                    Ok(Token::LessThan)
                },
                '>' => {
                    if let Some(ch) = is.next() {
                        if ch == '=' {
                            return Ok(Token::GreaterEqual)
                        }
                        is.put_front(ch);
                    }
                    Ok(Token::GreaterThan)
                },
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

fn match_leftbrace(is: &mut dyn CharStream, t: &Token) -> Result<Token, WutError> {
    match_token_and_scan(is, t, "expected '{'", |t| *t == Token::LeftBrace)
}

fn match_leftparen(is: &mut dyn CharStream, t: &Token) -> Result<Token, WutError> {
    match_token_and_scan(is, t, "expected '('", |t| *t == Token::LeftParen)
}

fn match_rightparen(is: &mut dyn CharStream, t: &Token) -> Result<Token, WutError> {
    match_token_and_scan(is, t, "expected ')'", |t| *t == Token::RightParen)
}

fn var_declaration(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let ident = match_token_and_scan(is, t, "expected 'Int'", |t| *t == Token::Int)?;
    let (ident, t) = match_ident(is, &ident)?;

    let node = AstNode::DeclareVariable(ident);
    Ok((node, t))
}

fn assignment(is: &mut dyn CharStream, ident: &Token) -> Result<(AstNode, Token), WutError> {
    let (ident, t) = match_ident(is, ident)?;

    let t = match_token_and_scan(is, &t, "expected '='", |t| *t == Token::Assign)?;
    let (left, t) = binexpr(is, &t, 0, 0)?;

    let right = AstNode::LValueIdentifier(ident.to_string());

    let node = AstNode::BinaryOp(AstOp::Assign, Box::new(left), Box::new(right));
    Ok((node, t))
}

fn single_statement(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    return match t {
        Token::Int => {
            var_declaration(is, &t)
        },
        Token::Identifier(_) => {
            assignment(is, &t)
        },
        Token::If => {
            if_statement(is, &t)
        },
        Token::While => {
            while_statement(is, &t)
        },
        Token::For => {
            for_statement(is, &t)
        },
        Token::EndOfStream => {
            return Err(WutError::UnexpectedEndOfStream)
        },
        t => {
            return Err(WutError::UnexpectedToken(t.clone()))
        }
    }
}

fn compound_statements(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let mut result: Option<AstNode> = None;
    let mut t = match_leftbrace(is, &t)?;

    while Token::RightBrace != t {
        let (next_node, next_token) = single_statement(is, &t)?;
        t = next_token;

        // XXX This is a bit crude: we need semicolons after assignments and
        // variable declarations (there ought to be a better way to do this)
        if let AstNode::BinaryOp(op, _, _) = &next_node {
            if *op == AstOp::Assign {
                t = match_semicolon(is, &t)?;
            }
        } else if let AstNode::DeclareVariable(_) = &next_node {
            t = match_semicolon(is, &t)?;
        }

        if result.is_some() {
            result = Some(AstNode::Glue(Box::new(result.unwrap()), Box::new(next_node)));
        } else {
            result = Some(next_node);
        }
    }

    if result.is_none() {
        result = Some(AstNode::Empty);
    }

    let next_token = scan(is)?;
    Ok((result.unwrap(), next_token))
}

fn has_comparison_operator(n: &AstNode) -> bool {
    return if let AstNode::BinaryOp(op, _, _) = n {
        return match op {
            AstOp::Equals | AstOp::NotEquals | AstOp::LessThan |
            AstOp::GreaterThan | AstOp::LessEqual | AstOp::GreaterEqual => { true },
            _ => { false }
        }
    } else {
        false
    }
}

fn if_statement(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let t = match_token_and_scan(is, &t, "expected 'if'", |t| *t == Token::If)?;
    let t = match_leftparen(is, &t)?;
    let (condition_ast, t) = binexpr(is, &t, 0, 0)?;
    let t = match_rightparen(is, &t)?;

    if !has_comparison_operator(&condition_ast) {
        return Err(WutError::Fatal("expected comparison operator".to_string()))
    }

    let (true_branch, mut next_token) = compound_statements(is, &t)?;
    let mut false_branch: Option<Box<AstNode>> = None;
    if next_token == Token::Else {
        let t = scan(is)?;
        let (node, t) = compound_statements(is, &t)?;
        false_branch = Some(Box::new(node));
        next_token = t;
    }
    let node = AstNode::If(Box::new(condition_ast), Box::new(true_branch), false_branch);
    Ok((node, next_token))
}

fn while_statement(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let t = match_token_and_scan(is, &t, "expected 'while'", |t| *t == Token::While)?;
    let t = match_leftparen(is, &t)?;
    let (condition_ast, t) = binexpr(is, &t, 0, 0)?;
    let t = match_rightparen(is, &t)?;

    if !has_comparison_operator(&condition_ast) {
        return Err(WutError::Fatal("expected comparison operator".to_string()))
    }

    let (body, next_token) = compound_statements(is, &t)?;
    let node = AstNode::While(Box::new(condition_ast), Box::new(body));
    Ok((node, next_token))
}

fn for_statement(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let t = match_token_and_scan(is, &t, "expected 'for'", |t| *t == Token::For)?;
    let t = match_leftparen(is, &t)?;
    let (prepare_ast, t) = single_statement(is, &t)?;
    let t = match_semicolon(is, &t)?;
    let (condition_ast, t) = binexpr(is, &t, 0, 0)?;
    let t = match_semicolon(is, &t)?;
    let (iteration_ast, t) = single_statement(is, &t)?;
    let t = match_rightparen(is, &t)?;

    if !has_comparison_operator(&condition_ast) {
        return Err(WutError::Fatal("expected comparison operator".to_string()))
    }

    let (body_ast, next_token) = compound_statements(is, &t)?;
    let node = AstNode::Glue(
        Box::new(prepare_ast),
        Box::new(
            AstNode::While(
                Box::new(condition_ast),
                Box::new(AstNode::Glue(
                    Box::new(body_ast),
                    Box::new(iteration_ast),
                ))
            )
        )
    );
    Ok((node, next_token))
}

fn function_declaration(is: &mut dyn CharStream, t: &Token) -> Result<(AstNode, Token), WutError> {
    let t = match_token_and_scan(is, &t, "expected 'void'", |t| *t == Token::Void)?;
    let (ident, t) = match_ident(is, &t)?;

    let t = match_leftparen(is, &t)?;
    let t = match_rightparen(is, &t)?;
    let (body_ast, next_token) = compound_statements(is, &t)?;

    let node = AstNode::Function(ident, Box::new(body_ast));
    Ok((node, next_token))
}

#[derive(Debug,PartialEq)]
enum WutError {
    SyntaxError(Token),
    UnexpectedToken(Token),
    UnexpectedChar(char),
    Mismatch(String),
    UnexpectedEndOfStream,
    Fatal(String),
}

fn token_to_astop(t: &Token) -> Result<AstOp, WutError> {
    match t {
        Token::Plus => { Ok(AstOp::Add) },
        Token::Minus => { Ok(AstOp::Subtract) },
        Token::Star => { Ok(AstOp::Multiply) },
        Token::Slash => { Ok(AstOp::Divide) },
        Token::Equals => { Ok(AstOp::Equals) },
        Token::NotEquals => { Ok(AstOp::NotEquals) },
        Token::LessThan => { Ok(AstOp::LessThan) },
        Token::GreaterThan => { Ok(AstOp::GreaterThan) },
        Token::LessEqual => { Ok(AstOp::LessEqual) },
        Token::GreaterEqual => { Ok(AstOp::GreaterEqual) },
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
    if let Token::RightParen = current_token {
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
        if let Token::RightParen = current_token {
            break;
        }
    }
    Ok((left, current_token))
}

fn main() -> Result<(), std::io::Error> {
    let f = File::open("t.c")?;
    let mut is = FileStream::new(f);
    //let mut is = StringStream::new("2 *3 + 4*5");

    let mut t = scan(&mut is).unwrap();
    loop {
        let (node, next_token) = function_declaration(&mut is, &t).unwrap();
        println!("{:?}", node);

        t = next_token;
        if Token::EndOfStream == t { break; }
    }

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

    fn invoke_statements(s: &str) -> Result<AstNode, WutError> {
        let mut ss = StringStream::new(&s);
        let t = scan(&mut ss).unwrap();
        let (node, next_token) = compound_statements(&mut ss, &t).unwrap();
        assert_eq!(Token::EndOfStream, next_token);
        Ok(node)
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
        let s = invoke_statements("{int i;}").unwrap();
        assert_eq!(AstNode::DeclareVariable("i".to_string()), s);
    }

    #[test]
    fn statement_assign_var_int() {
        let s = invoke_statements("{a=1;}").unwrap();
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Assign,
                Box::new(AstNode::IntegerLiteral(1)),
                Box::new(AstNode::LValueIdentifier("a".to_string())),
            ), s);
    }

    #[test]
    fn statement_assign_var_expr() {
        let s = invoke_statements("{a=1+2;}").unwrap();
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
            ), s);
    }

    #[test]
    fn statement_assign_var_int_twice() {
        let s = invoke_statements("{a=1;b=2;}").unwrap();
        assert_eq!(
            AstNode::Glue(
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(1)),
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                )),
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(2)),
                    Box::new(AstNode::LValueIdentifier("b".to_string())),
                ))
            ), s);
    }

    #[test]
    fn scan_assign() {
        assert_eq!(Token::Assign, invoke_scan("=").unwrap());
    }

    #[test]
    fn scan_braces() {
        assert_eq!(Token::LeftBrace, invoke_scan("{").unwrap());
        assert_eq!(Token::RightBrace, invoke_scan("}").unwrap());
    }

    #[test]
    fn scan_parens() {
        assert_eq!(Token::LeftParen, invoke_scan("(").unwrap());
        assert_eq!(Token::RightParen, invoke_scan(")").unwrap());
    }

    #[test]
    fn scan_operators() {
        assert_eq!(Token::Equals, invoke_scan("==").unwrap());
        assert_eq!(Token::NotEquals, invoke_scan("!=").unwrap());
        assert_eq!(Token::LessThan, invoke_scan("<").unwrap());
        assert_eq!(Token::LessEqual, invoke_scan("<=").unwrap());
        assert_eq!(Token::GreaterThan, invoke_scan(">").unwrap());
        assert_eq!(Token::GreaterEqual, invoke_scan(">=").unwrap());
    }

    #[test]
    fn scan_identifiers() {
        assert_eq!(Token::If, invoke_scan("if").unwrap());
        assert_eq!(Token::Else, invoke_scan("else").unwrap());
        assert_eq!(Token::While, invoke_scan("while").unwrap());
    }

    #[test]
    fn empty_statement() {
        let s = invoke_statements("{}").unwrap();
        assert_eq!(AstNode::Empty, s);
    }

    #[test]
    fn statement_if_without_else() {
        let s = invoke_statements("{if(a==1) { b=2; }}").unwrap();
        assert_eq!(
            AstNode::If(
                Box::new(AstNode::BinaryOp(
                    AstOp::Equals,
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                    Box::new(AstNode::IntegerLiteral(1)),
                )),
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(2)),
                    Box::new(AstNode::LValueIdentifier("b".to_string())),
                )),
                None
            ), s);
    }

    #[test]
    fn statement_if_with_else() {
        let s = invoke_statements("{if(a==1) { b=2; } else { c=3; }}").unwrap();
        assert_eq!(
            AstNode::If(
                Box::new(AstNode::BinaryOp(
                    AstOp::Equals,
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                    Box::new(AstNode::IntegerLiteral(1)),
                )),
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(2)),
                    Box::new(AstNode::LValueIdentifier("b".to_string())),
                )),
                Some(Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(3)),
                    Box::new(AstNode::LValueIdentifier("c".to_string())),
                ))),
            ), s);
    }

    #[test]
    fn statement_while() {
        let s = invoke_statements("{while(a < 10) { a = a + 1; }}").unwrap();
        assert_eq!(
            AstNode::While(
                Box::new(AstNode::BinaryOp(
                    AstOp::LessThan,
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                    Box::new(AstNode::IntegerLiteral(10)),
                )),
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::BinaryOp(
                        AstOp::Add,
                        Box::new(AstNode::LValueIdentifier("a".to_string())),
                        Box::new(AstNode::IntegerLiteral(1)),
                    )),
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                ))
            ), s);
    }

    #[test]
    fn statement_for() {
        let s = invoke_statements("{for(a=0; a < 5; a = a + 1) { b = b + 1; }}").unwrap();
        assert_eq!(
            AstNode::Glue(
                Box::new(AstNode::BinaryOp(
                    AstOp::Assign,
                    Box::new(AstNode::IntegerLiteral(0)),
                    Box::new(AstNode::LValueIdentifier("a".to_string())),
                )),
                Box::new(AstNode::While(
                    Box::new(AstNode::BinaryOp(
                        AstOp::LessThan,
                        Box::new(AstNode::LValueIdentifier("a".to_string())),
                        Box::new(AstNode::IntegerLiteral(5)),
                    )),
                    Box::new(AstNode::Glue(
                        Box::new(AstNode::BinaryOp(
                            AstOp::Assign,
                            Box::new(AstNode::BinaryOp(
                                AstOp::Add,
                                Box::new(AstNode::LValueIdentifier("b".to_string())),
                                Box::new(AstNode::IntegerLiteral(1)),
                            )),
                            Box::new(AstNode::LValueIdentifier("b".to_string())),
                        )),
                        Box::new(AstNode::BinaryOp(
                            AstOp::Assign,
                            Box::new(AstNode::BinaryOp(
                                AstOp::Add,
                                Box::new(AstNode::LValueIdentifier("a".to_string())),
                                Box::new(AstNode::IntegerLiteral(1)),
                            )),
                            Box::new(AstNode::LValueIdentifier("a".to_string())),
                        )),
                    ))
                ))
            ), s);
    }

    #[test]
    fn void_function() {
        let mut ss = StringStream::new("void main() { }");
        let t = scan(&mut ss).unwrap();
        let (node, next_token) = function_declaration(&mut ss, &t).unwrap();
        assert_eq!(Token::EndOfStream, next_token);
        assert_eq!(AstNode::Function("main".to_string(), Box::new(AstNode::Empty)), node);
    }
}
