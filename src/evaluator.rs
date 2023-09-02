use std::rc::Rc;

use crate::{calc_engine::Fraction, parser::Node};

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

#[derive(Clone)]
pub enum Symbol{
    Variable(String, Box<Fraction>),
    FunctionDef {
        name: String,
        arg_names: Vec<String>,
        body: Rc<Node>,
    }
}
#[derive(Clone)]
pub struct SymbolTable {
    symbols: Vec<Symbol>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            symbols: Vec::new(),
        }
    }


    pub fn get_variable(&self, name: &str) -> Option<&Fraction> {
        for symbol in &self.symbols {
            if let Symbol::Variable(var_name, value) = symbol {
                if var_name == name {
                    return Some(value.as_ref());
                }
            }
        }
        None
    }

    pub fn get_function(&self, name: &str) -> Option<(Vec<String>, Node)> {
        for symbol in &self.symbols {
            if let Symbol::FunctionDef { name: func_name, arg_names, body } = symbol {
                if func_name == name {
                    return Some((arg_names.to_vec(), body.as_ref().clone()));
                }
            }
        }
        None
    }

    pub fn set_variable(&mut self, name: String, value: Box<Fraction>) {
        for symbol in &mut self.symbols {
            if let Symbol::Variable(var_name, val) = symbol {
                if var_name == &name {
                    *val = value;
                    return;
                }
            }
        }
        self.symbols.push(Symbol::Variable(name, value));
    }

    pub fn set_function(&mut self, name: String, arg_names: Vec<String>, body: Rc<Node>) {
        for symbol in &mut self.symbols {
            if let Symbol::FunctionDef { name: func_name, .. } = symbol {
                if func_name == &name {
                    *symbol = Symbol::FunctionDef { name, arg_names, body };
                    return;
                }
            }
        }
        self.symbols.push(Symbol::FunctionDef { name, arg_names, body });
    }

    pub fn remove_symbol(&mut self, name: &str) {
        self.symbols.retain(|symbol| {
            match symbol {
                Symbol::Variable(var_name, _) => var_name != name,
                Symbol::FunctionDef { name: func_name, .. } => func_name != name,
            }
        });
    }
    
}

/// Evaluate a node tree representation of a math expression
pub fn evaluate(
    node: &Node,
    precision: u32,
    previous_ans: Option<&Fraction>,
    symbol_table: &mut SymbolTable,
) -> Result<Fraction, String> {
    match node {
        Node::Number(f) => Ok(*f.clone()),
        Node::UniOp { op, child } => {
            let child = evaluate(child, precision, previous_ans, symbol_table)?;
            match op.as_str() {
                "-" => Ok(-child),
                "!" => child.fact_fraction(precision),
                _ => panic!("Unknown unary operator: {}", op),
            }
        }
        Node::BinOp { op, left, right } => {
            // if the operation is assignment
            if op.as_str() == "=" {
                // for a variable assignment
                if let Node::Identifier(name) = (*left).as_ref() {
                    let value = evaluate(right, precision, previous_ans, symbol_table)?;
                    symbol_table.set_variable(name.to_string(), Box::new(value.clone()));
                    return Ok(value);
                } 
                // for a function definition
                else if let Node::Function { name, args } = (*left).as_ref() {
                    // all args must be identifiers since we're defining a function
                    let arg_names: Vec<String> = 
                    args.iter()
                        .map(|arg| {
                            if let Node::Identifier(name) = arg {
                                Ok(name.clone())
                            } else {
                                Err("Function arguments must be identifiers.".to_string())
                            }
                        })
                        .collect::<Result<_, _>>()?;
                    
                        symbol_table.set_function(name.to_string(), arg_names, right.clone());
                        return Ok(Fraction::from(0));
                        
                    } else {
                    return Err("Invalid assignment.".to_string());
                }
            }
            // else
            let left = evaluate(left, precision, previous_ans, symbol_table)?;
            let right = evaluate(right, precision, previous_ans, symbol_table)?;
            match op.as_str() {
                "+" => Ok(left.added_to(&right)),
                "-" => Ok(left.subtract(&right)),
                "*" => Ok(left.multiply(&right)),
                "/" => Ok(left.divide(&right)),
                "^" => left.pow_frac(&right, precision),
                _ => Err(format!("Unknown binary operator: {}", op)),
            }
        }
        Node::Function { name, args } => {
            let args: Vec<Fraction> = args
                .iter()
                .map(|arg| evaluate(arg, precision, previous_ans, symbol_table))
                .collect::<Result<_, _>>()?;
            
            // check for the correct number of arguments
            if FUNCTION_ARG_COUNT.iter()
                .any(|(func_name, count)| func_name == &name && args.len() != *count) {
                return Err(format!("Wrong number of arguments for function: {}", name));
            }
            
            match name.as_str() {
                "sin" => args[0].sin(precision),
                "cos" => args[0].cos(precision),
                "tan" => args[0].tan(precision),
                "log" => args[1].log(&args[0], precision),
                "ln" => args[0].ln(precision),
                "exp" => args[0].exp(precision),
                "root" => args[1].nth_root(&args[0], precision),
                "floor" => Ok(args[0].floor()),
                "ceil" => Ok(args[0].ceil()),
                "round" => Ok(args[0].round()),
                "abs" => Ok(args[0].abs()),
                // user's custom functions
                func_name => {
                    if let Some((arg_names, body)) = symbol_table.get_function(name) {
                        if args.len() != arg_names.len() {
                            return Err(format!("Wrong number of arguments for function: {}", func_name));
                        }
                        // store the arguments in a temporary symbol table
                        let mut temp_symbol_table = symbol_table.clone();
                        temp_symbol_table.remove_symbol(func_name); // prevent recursive calls
                        for (i, arg_name) in arg_names.iter().enumerate() {
                            temp_symbol_table.set_variable(arg_name.to_string(), Box::new(args[i].clone()));
                        }
                        evaluate(&body, precision, previous_ans, &mut temp_symbol_table)
                    } else {
                        return Err(format!("Unknown function: {}", name));
                    }
                }
            }
        }
        Node::Identifier(id) => match id.as_str() {
            "pi" => Ok(Fraction::pi()),
            "e" => Ok(Fraction::e()),
            "last" => match previous_ans {
                Some(f) => Ok(f.clone()),
                None => Err("No previous answer".to_string()),
            },
            _ => {
                //if it's in the symbol table, return its value
                if let Some(value) = symbol_table.get_variable(id) {
                    Ok(value.clone())
                } else {
                    Err(format!("Unknown identifier: {}", id))
                }
            }
        },
    }
}
