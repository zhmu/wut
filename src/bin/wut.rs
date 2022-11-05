extern crate wut;

use wut::stream::{CharStream, StringStream};

#[derive(Debug,Copy,Clone,PartialEq)]
enum Token {
    Plus,
    Minus,
    Star,
    Slash,
    IntLiteral(i32),
    EndOfStream
}

#[derive(Debug,PartialEq)]
enum AstOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(Debug,PartialEq)]
enum AstNode {
    BinaryOp(AstOp, Box<AstNode>, Box<AstNode>),
    IntegerLiteral(i32),
}

fn get_token_operator_precedence(t: &Token) -> Result<i32, WutError> {
    match t {
        Token::Plus => { Ok(10) },
        Token::Minus => { Ok(10) },
        Token::Star => { Ok(20) },
        Token::Slash => { Ok(20) },
        _ => { Err(WutError::UnexpectedToken(*t)) },
    }
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

fn scan(is: &mut dyn CharStream) -> Result<Token, WutError> {
    match is.skip() {
        Some(ch) => {
            return match ch {
                '+' => { Ok(Token::Plus) },
                '-' => { Ok(Token::Minus) },
                '*' => { Ok(Token::Star) },
                '/' => { Ok(Token::Slash) },
                _ => {
                    if is_digit(ch) {
                        is.put_front(ch);
                        let i = scan_int(is);
                        return Ok(Token::IntLiteral(i))
                    }
                    Err(WutError::UnexpectedChar(ch))
                }
            }
        },
        None => { Ok(Token::EndOfStream) },
    }
}

#[derive(Debug,PartialEq)]
enum WutError {
    SyntaxError(Token),
    UnexpectedToken(Token),
    UnexpectedChar(char),
}

fn token_to_astop(t: &Token) -> Result<AstOp, WutError> {
    println!("token_to_astop t {:?}", t);
    match t {
        Token::Plus => { Ok(AstOp::Add) },
        Token::Minus => { Ok(AstOp::Subtract) },
        Token::Star => { Ok(AstOp::Multiply) },
        Token::Slash => { Ok(AstOp::Divide) },
        _ => { Err(WutError::UnexpectedToken(*t)) },
    }
}


fn primary(t: &Token) -> Result<AstNode, WutError> {
    println!("primary t {:?}", t);
    match t {
        Token::IntLiteral(i) => {
            Ok(AstNode::IntegerLiteral(*i))
        },
        _ => {
            Err(WutError::SyntaxError(*t))
        }
    }
}

fn binexpr(is: &mut dyn CharStream, token: &Token, prev_token_precedence: i32, level: i32) -> Result<(AstNode, Token), WutError> {
    println!("level {} binexpr t {:?} prev_token_precedence {}", level, token, prev_token_precedence);
    let mut left = primary(&token)?;

    let mut current_token = scan(is)?;
    if let Token::EndOfStream = current_token {
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
        if let Token::EndOfStream = current_token {
            break;
        }
    }
    Ok((left, current_token))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn invoke_binexpr(s: &str) -> Result<(AstNode, Token), WutError> {
        let mut ss = StringStream::new(&s);
        let t = scan(&mut ss).unwrap();
        binexpr(&mut ss, &t, 0, 0)
    }

    fn invoke_binexpr_and_get_ast(s: &str) -> AstNode {
        let mut ss = StringStream::new(&s);
        let t = scan(&mut ss).unwrap();
        let n = binexpr(&mut ss, &t, 0, 0).unwrap();
        assert_eq!(Token::EndOfStream, n.1);
        n.0
    }

    #[test]
    fn parse_single_digit_integer_literal() {
        let ast = invoke_binexpr_and_get_ast("9");
        assert_eq!(AstNode::IntegerLiteral(9), ast);
    }

    #[test]
    fn parse_multiple_digit_integer_literal() {
        let ast = invoke_binexpr_and_get_ast("1234");
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
        let ast = invoke_binexpr_and_get_ast("1+2");
        assert_eq!(
            AstNode::BinaryOp(
                AstOp::Add,
                Box::new(AstNode::IntegerLiteral(1)),
                Box::new(AstNode::IntegerLiteral(2))
            ), ast);
    }

    #[test]
    fn parse_multiple_add() {
        let ast = invoke_binexpr_and_get_ast("1+2+3");
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
}

fn main() -> Result<(), std::io::Error> {
    //let f = File::open("t.c")?;
    //let mut is = InputStream::new(f);
    let mut is = StringStream::new("2 *3 + 4*5");

    let t = scan(&mut is).unwrap();
    let n = binexpr(&mut is, &t, 0, 0).unwrap();
    println!("{:?}", n);

    // https://github.com/DoctorWkt/acwj/blob/master/02_Parser/Readme.md
    Ok(())
}
