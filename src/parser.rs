// a module for parsing a string representation of a mathematical expression

use crate::{tokenizer::Token, Fraction};

#[derive(PartialEq, Eq, Debug)]
pub enum Node<'a> {
    UniOp {
        op: String,
        child: Box<Node<'a>>,
    },
    BinOp {
        op: String,
        left: Box<Node<'a>>,
        right: Box<Node<'a>>,
    },
    Function {
        name: String,
        args: Vec<Node<'a>>,
    },
    Identifier(String),
    Number(&'a Fraction),
}

const FUNCTION_ARG_COUNT: &[(&str, usize)] = &[
    ("sin", 1),
    ("cos", 1),
    ("tan", 1),
    ("log", 2),
    ("ln", 1),
    ("exp", 1),
    ("root", 2),
    ("floor", 1),
    ("ceil", 1),
    ("round", 1),
    ("abs", 1),
];

/// Parses an expression with the given binary operators
/// Calls the given function pointer when done
fn parse_generic_bin_op<'a>(
    tokens: &'a Vec<Token>,
    pos: usize,
    ops: &[&str],
    next_func: fn(&'a Vec<Token>, usize) -> Result<(Node<'a>, usize), String>,
) -> Result<(Node<'a>, usize), String> {
    // pos is the current position in the token stream to start parsing from
    let mut new_pos = pos;
    // parse the first node in the binary operation
    let node_res = next_func(tokens, new_pos);
    let node = match node_res {
        Ok((mut node, next_pos)) => {
            new_pos = next_pos;
            // while the next token is an operator in ops, keep parsing
            while let Some(&Token::OPERATOR(ref op)) = tokens.get(new_pos) {
                if ops.contains(&op.as_str()) {
                    new_pos += 1;
                    // parse the next node in the binary operation
                    let node2_res = next_func(tokens, new_pos);
                    let node2 = match node2_res {
                        Ok((node2, next_pos)) => {
                            new_pos = next_pos;
                            node2
                        }
                        Err(e) => return Err(e),
                    };
                    // create a new node representing the binary operation
                    node = Node::BinOp {
                        op: op.to_string(),
                        left: Box::new(node),
                        right: Box::new(node2),
                    };
                } else {
                    break;
                }
            }
            node
        }
        Err(e) => return Err(e),
    };
    // return the node and the position in the token stream after parsing
    Ok((node, new_pos))
}

fn parse_assignment<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    parse_generic_bin_op(tokens, pos, &["="], parse_add_sub)
}

fn parse_add_sub<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    parse_generic_bin_op(tokens, pos, &["+", "-"], parse_mul_div)
}

fn parse_mul_div<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    parse_generic_bin_op(tokens, pos, &["*", "/"], parse_pow)
}

fn parse_pow<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    parse_generic_bin_op(tokens, pos, &["^"], parse_function)
}

fn parse_function<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    // if it's a function, parse the arguments
    if let Token::FUNCTION(name) = &tokens[pos] {
        let mut new_pos = pos + 1;
        let mut args = Vec::new();
        // if it's a number and the function is log, parse the number as the argument
        if name == "log" {
            if let Token::NUMBER(num) = &tokens[new_pos] {
                new_pos += 1;
                args.push(Node::Number(num));
            }
        }
        // or if it's the root function
        else if name == "root" {
            if let Token::NUMBER(num) = &tokens[new_pos] {
                new_pos += 1;
                args.push(Node::Number(num));
            }
        }
        // if it's parentheses, parse the arguments inside
        if Token::DELIMITER("(".to_string()) == tokens[new_pos] {
            new_pos += 1;
            let node_res = parse_expression(tokens, new_pos);
            if let Ok((node, next_pos)) = node_res {
                new_pos = next_pos;
                args.push(node);
                while Token::DELIMITER(",".to_string()) == tokens[new_pos] {
                    new_pos += 1;
                    let node_res = parse_expression(tokens, new_pos);
                    match node_res {
                        Ok((node, next_pos)) => {
                            new_pos = next_pos;
                            args.push(node);
                        }
                        Err(e) => return Err(e),
                    }
                }
                if Token::DELIMITER(")".to_string()) == tokens[new_pos] {
                    new_pos += 1;
                    // if the number of arguments is not correct, return an error
                    let arg_num = FUNCTION_ARG_COUNT
                        .iter()
                        .find(|(n, _)| *n == name)
                        .unwrap()
                        .1;
                    if args.len() != arg_num {
                        return Err(format!(
                            "Expected {} arguments for function {}",
                            arg_num, name
                        ));
                    }
                    // return the function node and the position in the token stream after parsing
                    return Ok((
                        Node::Function {
                            name: name.to_string(),
                            args,
                        },
                        new_pos,
                    ));
                } else {
                    return Err("Expected closing parenthesis".to_string());
                }
            } else {
                return node_res; // return the error
            }
        }
    }
    parse_atom(tokens, pos)
}

fn parse_atom<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    let mut new_pos = pos;
    // if it's parentheses, parse the expression inside
    if Token::DELIMITER("(".to_string()) == tokens[pos] {
        new_pos += 1;
        let node_res = parse_expression(tokens, new_pos);
        if let Ok((node, next_pos)) = node_res {
            new_pos = next_pos;
            if Token::DELIMITER(")".to_string()) == tokens[new_pos] {
                new_pos += 1;
                // if there's a factorial, return a UniOp node
                if Token::OPERATOR("!".to_string()) == tokens[new_pos] {
                    new_pos += 1;
                    return Ok((
                        Node::UniOp {
                            op: "!".to_string(),
                            child: Box::new(node),
                        },
                        new_pos,
                    ));
                }
                return Ok((node, new_pos));
            } else {
                return Err("Expected closing parenthesis".to_string());
            }
        } else {
            return node_res; // return the error
        }
    }
    // if it's an identifier, return an Identifier node
    else if let Token::IDENTIFIER(id) = &tokens[pos] {
        new_pos += 1;
        // if there's a factorial, return a UniOp node
        if Token::OPERATOR("!".to_string()) == tokens[new_pos] {
            new_pos += 1;
            return Ok((
                Node::UniOp {
                    op: "!".to_string(),
                    child: Box::new(Node::Identifier(id.to_string())),
                },
                new_pos,
            ));
        }
        return Ok((Node::Identifier(id.to_string()), new_pos));
    }
    // if it's a number, return a Number node
    else if let Token::NUMBER(n) = &tokens[pos] {
        new_pos += 1;
        // if there's a factorial, return a UniOp node
        if Token::OPERATOR("!".to_string()) == tokens[new_pos] {
            new_pos += 1;
            return Ok((
                Node::UniOp {
                    op: "!".to_string(),
                    child: Box::new(Node::Number(n)),
                },
                new_pos,
            ));
        }
        return Ok((Node::Number(n), new_pos));
    }
    // if it's a negative number, return a UniOp node
    else if Token::OPERATOR("-".to_string()) == tokens[pos] {
        new_pos += 1;
        let node_res = parse_atom(tokens, new_pos);
        match node_res {
            Ok((node, next_pos)) => {
                new_pos = next_pos;
                return Ok((
                    Node::UniOp {
                        op: "-".to_string(),
                        child: Box::new(node),
                    },
                    new_pos,
                ));
            }
            Err(e) => return Err(e),
        }
    }
    Err("Expected number or opening parenthesis".to_string())
}

/// Basically just gives parse_assignment a more understandable name
fn parse_expression<'a>(tokens: &'a Vec<Token>, pos: usize) -> Result<(Node<'a>, usize), String> {
    parse_assignment(tokens, pos)
}

/// Root of the recursive parse tree
/// Call order:
/// parse -> parse_expression
/// -> parse_assignment -> parse_add_sub
/// -> parse_mul_div -> parse_pow
/// -> parse_function -> parse_atom
pub fn parse<'a>(tokens: &'a Vec<Token>) -> Result<Node<'a>, String> {
    let pos = 0;
    match parse_assignment(&tokens, pos) {
        Ok((node, next_pos)) => {
            if next_pos == tokens.len() - 1 {
                return Ok(node);
            } else {
                return Err("Expected end of expression".to_string());
            }
        }
        Err(e) => return Err(e),
    }
}
