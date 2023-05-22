use crate::{calc_engine::Fraction, parser::Node};

pub struct SymbolTable {
    symbols: Vec<(String, Fraction)>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            symbols: Vec::new(),
        }
    }

    pub fn set(&mut self, symbol: String, value: Fraction) {
        // if the symbol already exists, replace it with the new value
        if let Some(pos) = self.symbols.iter().position(|&(ref s, _)| s == &symbol) {
            self.symbols[pos] = (symbol, value);
        }
        // otherwise, add it to the end of the list
        else {
            self.symbols.push((symbol, value));
        }
    }

    pub fn get(&self, symbol: &str) -> Option<&Fraction> {
        self.symbols
            .iter()
            .find(|&(s, _)| s == symbol)
            .map(|(_, value)| value)
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
        Node::Number(f) => Ok((*f).clone()),
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
                if let Node::Identifier(name) = (*left).as_ref() {
                    let value = evaluate(right, precision, previous_ans, symbol_table)?;
                    symbol_table.set(name.to_string(), value.clone());
                    return Ok(value);
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
                _ => Err(format!("Unknown function: {}", name)),
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
                if let Some(value) = symbol_table.get(id) {
                    Ok(value.clone())
                } else {
                    Err(format!("Unknown identifier: {}", id))
                }
            }
        },
    }
}
