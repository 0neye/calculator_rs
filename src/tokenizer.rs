// a module for tokenizing a string representation of a mathematical expression

use std::iter::Peekable;
use std::str::{Chars, FromStr};

use crate::Fraction;

const OPERATORS: [&str; 8] = ["+", "-", "*", "/", "%", "^", "!", "="];
const DELIMITERS: [&str; 3] = ["(", ")", ","];
// const FUNCTIONS: [&str; 11] = [
//     "sin", "cos", "tan", "log", "ln", "exp", "root", "floor", "ceil", "round", "abs",
// ];

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Token {
    OPERATOR(String),
    DELIMITER(String),
    //FUNCTION(String),
    IDENTIFIER(String),
    NUMBER(Fraction),
    EOE, // end of expression
}

fn is_operator(c: &char) -> bool {
    OPERATORS.contains(&c.to_string().as_str())
}

fn is_delimiter(c: &char) -> bool {
    DELIMITERS.contains(&c.to_string().as_str())
}

// fn is_function(c: &str) -> bool {
//     FUNCTIONS.contains(&c)
// }

/// Returns a list of tokens representing individual components of a math expression
pub fn get_tokens(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens: Vec<Token> = Vec::new();
    let mut chars: Peekable<Chars> = input.chars().peekable();

    // do something different depending on the current character
    while let Some(c) = chars.next() {
        if is_operator(&c) {
            tokens.push(Token::OPERATOR(c.to_string()));
        } else if is_delimiter(&c) {
            tokens.push(Token::DELIMITER(c.to_string()));
        } else if c.is_numeric() || c == '.' {
            let mut current_token = c.to_string();
            while let Some(&c) = chars.peek() {
                if c.is_numeric() || c == '.' {
                    current_token.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            tokens.push(Token::NUMBER(Fraction::from_str(&current_token).unwrap()));
        } else if c.is_alphabetic() || c == '_' {
            let mut current_token = c.to_string();
            while let Some(&c) = chars.peek() {
                if c.is_alphabetic() || c.is_numeric() || c == '_' {
                    current_token.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            // if is_function(current_token.as_str()) {
            //     tokens.push(Token::FUNCTION(current_token));
            // } else {
                tokens.push(Token::IDENTIFIER(current_token));
            //}
        } else if c.is_whitespace() {
            continue;
        } else {
            return Err(format!("Invalid character {} in input", c));
        }
    }
    tokens.push(Token::EOE);

    // The following doesn't work.
    // It's a bit more complicated to add implicit multiplication because of being able to call functions like "log2(params)" (the '2' is the issue)

    // go through and add implicit multiplication tokens between numbers and parentheses, parentheses and numbers, and parentheses and parentheses
    // let mut new_tokens: Vec<Token> = Vec::new();
    // for i in 0..tokens.len() {
    //     if i > 0 {
    //         if let Token::NUMBER(_) = tokens[i - 1] {
    //             if let Token::DELIMITER(ref d) = tokens[i] {
    //                 if d == "(" {
    //                     new_tokens.push(Token::OPERATOR("*".to_string()));
    //                 }
    //             }
    //         } else if let Token::DELIMITER(ref d) = tokens[i - 1] {
    //             if d == ")" {
    //                 if let Token::NUMBER(_) = tokens[i] {
    //                     new_tokens.push(Token::OPERATOR("*".to_string()));
    //                 } else if let Token::DELIMITER(ref d) = tokens[i] {
    //                     if d == "(" {
    //                         new_tokens.push(Token::OPERATOR("*".to_string()));
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //     tokens.push(tokens[i].clone());
    // }

    // Ok(new_tokens)
    Ok(tokens)
}
