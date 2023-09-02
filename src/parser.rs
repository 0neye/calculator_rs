// a module for parsing a string representation of a mathematical expression

use std::rc::Rc;

use crate::{tokenizer::Token, Fraction};

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Node {
    UniOp {
        op: String,
        child: Rc<Node>,
    },
    BinOp {
        op: String,
        left: Rc<Node>,
        right: Rc<Node>,
    },
    Function {
        name: String,
        args: Vec<Node>,
    },
    Identifier(String),
    Number(Box<Fraction>),
}


/// Parses an expression with the given binary operators
/// Calls the given function pointer when done
fn parse_generic_bin_op(
    tokens: & Vec<Token>,
    pos: usize,
    ops: &[&str],
    next_func: fn(& Vec<Token>, usize) -> Result<(Node, usize), String>,
) -> Result<(Node, usize), String> {
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
                        left: Rc::new(node),
                        right: Rc::new(node2),
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

fn parse_assignment(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    parse_generic_bin_op(tokens, pos, &["="], parse_add_sub)
}

fn parse_add_sub(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    parse_generic_bin_op(tokens, pos, &["+", "-"], parse_mul_div)
}

fn parse_mul_div(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    parse_generic_bin_op(tokens, pos, &["*", "/"], parse_pow)
}

fn parse_pow(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    parse_generic_bin_op(tokens, pos, &["^"], parse_function)
}

fn parse_function(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    // if it's a function, parse the arguments
    if let Token::IDENTIFIER(name) = &tokens[pos] {
        let mut new_pos = pos + 1;
        let mut args = Vec::new();
        // // if it's a number and the function is log, parse the number as the argument
        // if name == "log" {
        //     if let Token::NUMBER(num) = &tokens[new_pos] {
        //         new_pos += 1;
        //         args.push(Node::Number(num));
        //     }
        // }
        // // or if it's the root function
        // else if name == "root" {
        //     if let Token::NUMBER(num) = &tokens[new_pos] {
        //         new_pos += 1;
        //         args.push(Node::Number(num));
        //     }
        // }
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

fn parse_atom(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
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
                        factorial_node(node)?,
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
    // if it's a variable, return an Identifier node
    else if let Token::IDENTIFIER(id) = &tokens[pos] {
        new_pos += 1;
        // if there's a factorial, return a UniOp node
        if Token::OPERATOR("!".to_string()) == tokens[new_pos] {
            new_pos += 1;
            return Ok((
                factorial_node(Node::Identifier(id.to_string()))?,
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
                factorial_node(Node::Number(Box::new(n.clone())))?,
                new_pos,
            ));
        }
        return Ok((Node::Number(Box::new(n.clone())), new_pos));
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
                        child: Rc::new(node),
                    },
                    new_pos,
                ));
            }
            Err(e) => return Err(e),
        }
    }
    Err("Expected number or opening parenthesis".to_string())
}

/// small helper func
fn factorial_node(node: Node) -> Result<Node, String> {
    Ok(Node::UniOp {
        op: "!".to_string(),
        child: Rc::new(node),
    })
}

/// Basically just gives parse_assignment a more understandable name
fn parse_expression(tokens: & Vec<Token>, pos: usize) -> Result<(Node, usize), String> {
    parse_assignment(tokens, pos)
}

/// Root of the recursive parse tree
/// Call order:
/// parse -> parse_expression
/// -> parse_assignment -> parse_add_sub
/// -> parse_mul_div -> parse_pow
/// -> parse_function -> parse_atom
pub fn parse(tokens: & Vec<Token>) -> Result<Node, String> {
    let pos = 0;
    match parse_expression(&tokens, pos) {
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
