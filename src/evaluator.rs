use std::rc::Rc;

use crate::{calc_engine::Fraction, calc_engine::Matrix, parser::{Node, self}, tokenizer};

const FUNCTION_ARG_COUNT: &[(&str, usize)] = &[
    // fractions
    ("sin", 1),
    ("cos", 1),
    ("tan", 1),
    ("atan", 1),
    ("log", 2),
    ("ln", 1),
    ("exp", 1),
    ("root", 2),
    ("floor", 1),
    ("ceil", 1),
    ("round", 2),
    ("abs", 1),
    // matrices
    ("det", 1),
    ("inv", 1),
    ("ref", 1),
    ("mean", 1),
    ("median", 1),
    ("mode", 1),
    ("sum", 1),
    ("prod", 1),
];
// TODO: rework how built-in functions are stored
const MATRIX_FUNCTIONS: &[&str] = &[
    "det",
    "inv",
    "ref",
    "mean",
    "median",
    "mode",
    "sum",
    "prod",
];

// functions using the calculator syntax, need to be initialized with the parser
const CUSTOM_FUNCTIONS: &[&str] = &[
    "quad(a,b,c) = [(-b + root(b^2 - 4*a*c))/(2*a), (-b - root(b^2 - 4*a*c))/(2*a)]", // quadratic formula

    "pva(r,n,pmt) = pmt * (1 - (1 + r)^-n) / r", // present value formula (annuity)
    "fva(r,n,pmt) = pmt * ((1 + r)^n - 1) / r", // future value formula (annuity)
    "pv(fv,r,n) = fv / (1+r)^n", // present value formula
    "fv(pv,r,n) = pv * (1+r)^n", // future value formula
    "pmt(pv,fv,r,n) = (pv - fv) / ((1 + r)^n - 1)", // payment formula
    "nper(pmt,r,fv) = log(fv / pmt) / log(1 + r)", // number of periods
    "pci(p,r,t,n) = p * (1 + r/n)^(n*t)", // periodic compound interest formula
    "cci(p,r,t) = p * exp(r*t)", // continuous compound interest formula
    "si(p,r,t) = p * r * t", // simple interest formula
    "comb(n,r) = n! / (r!*(n-r)!)", // combination formula
    "perm(n,r) = n! / (n-r)!", // permutation formula
];

const CUSTOM_VARS: &[&str] = &[
    "h = 100",
    "k = 1`000",
    "mill = 1`000`000",
    "bill = 1`000`000`000",
    "m = 1`000`000",
    "b = 1`000`000`000",
];

pub fn init_custom_symbols(symbol_table: &mut SymbolTable) {
    for symbol in CUSTOM_FUNCTIONS.iter().chain(CUSTOM_VARS.iter()) {
        let tokens = tokenizer::get_tokens(symbol).unwrap();
        let parsed = parser::parse(&tokens).unwrap();
        let _ = evaluate(&parsed, 20, None, symbol_table);
    }
}

#[derive(Clone)]
pub enum Symbol{
    Variable(String, Box<EvalResult>),
    FunctionDef {
        name: String,
        arg_names: Vec<String>,
        body: Rc<Node>,
        destruct: bool, // whether the function operates on each element of a matrix instead of the whole matrix
    }
}

impl Symbol {
    pub fn to_string(&self) -> String {
        match self {
            Symbol::Variable(var_name, value) => {
                format!("Variable: {} = {}", var_name, value.to_string())
            },
            Symbol::FunctionDef { name, arg_names, body, destruct } => {
                let args = arg_names.join(", ");
                format!("Function: {}({}) = {}", name, 
                    if *destruct { format!("[{}]", args) } else { args }, 
                    body.to_string())
            },
        }
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


    pub fn get_variable(&self, name: &str) -> Option<&EvalResult> {
        for symbol in &self.symbols {
            if let Symbol::Variable(var_name, value) = symbol {
                if var_name == name {
                    return Some(value.as_ref());
                }
            }
        }
        None
    }

    pub fn get_function(&self, name: &str) -> Option<(Vec<String>, Node, bool)> {
        for symbol in &self.symbols {
            if let Symbol::FunctionDef { name: func_name, arg_names, body, destruct} = symbol {
                if func_name == name {
                    return Some((arg_names.to_vec(), body.as_ref().clone(), *destruct));
                }
            }
        }
        None
    }

    pub fn set_variable(&mut self, name: String, value: Box<EvalResult>) {
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

    pub fn set_function(&mut self, name: String, arg_names: Vec<String>, body: Rc<Node>, destruct: bool) {
        for symbol in &mut self.symbols {
            if let Symbol::FunctionDef { name: func_name, .. } = symbol {
                if func_name == &name {
                    *symbol = Symbol::FunctionDef { name, arg_names, body, destruct };
                    return;
                }
            }
        }
        self.symbols.push(Symbol::FunctionDef { name, arg_names, body, destruct });
    }

    pub fn remove_symbol(&mut self, name: &str) {
        self.symbols.retain(|symbol| {
            match symbol {
                Symbol::Variable(var_name, _) => var_name != name,
                Symbol::FunctionDef { name: func_name, .. } => func_name != name,
            }
        });
    }

    pub fn get_symbol_string(&self, name: &str) -> String {
        self.symbols.iter()
            .find(|symbol| match symbol {
                Symbol::Variable(var_name, _) => var_name == name,
                Symbol::FunctionDef { name: func_name, .. } => func_name == name,
            })
            .map(|symbol| symbol.to_string())
            .unwrap_or_else(|| format!("Symbol not found: {}", name))
    }

    pub fn get_symbol_string_list(&self) -> String {
        let mut output = String::new();
        for symbol in &self.symbols {
            output.push_str(&symbol.to_string());
            output.push('\n');
        }
        output.trim_end().to_string()
    }
    
}

#[derive(Clone, Debug)]
pub enum EvalResult {
    Fraction(Fraction),
    Matrix(Matrix),
}
impl From<Fraction> for EvalResult {
    fn from(fraction: Fraction) -> Self {
        EvalResult::Fraction(fraction)
    }
}
impl From<Matrix> for EvalResult {
    fn from(matrix: Matrix) -> Self {
        EvalResult::Matrix(matrix)
    }
}
impl From<EvalResult> for Fraction {
    fn from(result: EvalResult) -> Self {
        match result {
            EvalResult::Fraction(fraction) => fraction,
            EvalResult::Matrix(_) => panic!("Can not convert matrix to fraction"),
        }
    }
}
impl From<EvalResult> for Matrix {
    fn from(result: EvalResult) -> Self {
        match result {
            EvalResult::Fraction(fraction) => Matrix::new_from_rows(vec![vec![fraction]]).unwrap(),
            EvalResult::Matrix(matrix) => matrix,
        }
    }
}

impl ToString for EvalResult {
    fn to_string(&self) -> String {
        match self {
            EvalResult::Fraction(fraction) => fraction.to_string(),
            EvalResult::Matrix(matrix) => matrix.to_string(),
        }
    }
}





/// Evaluate a node tree representation of a math expression
pub fn evaluate(
    node: &Node,
    precision: u32,
    previous_ans: Option<&EvalResult>,
    symbol_table: &mut SymbolTable,
) -> Result<EvalResult, String> {
    match node {
        Node::Number(f) => Ok((*f.clone()).into()),
        Node::Matrix(matrix) => {
            let mut evaluated_matrix = Vec::new();
            for row in matrix {
                let mut evaluated_row = Vec::new();
                for node in row {
                    let evaluated_node = evaluate(&node, precision, previous_ans, symbol_table)?;
                    if let EvalResult::Fraction(f) = evaluated_node {
                        evaluated_row.push(f);
                    } else {
                        return Err("Matrixes can not hold non-numbers".to_string());
                    }
                }
                evaluated_matrix.push(evaluated_row);
            }
            Ok(Matrix::new_from_rows(evaluated_matrix)?.into())
        },
        Node::UniOp { op, child } => {
            let child = evaluate(child, precision, previous_ans, symbol_table)?;
            Ok(match child {
                EvalResult::Fraction(f) => match op.as_str() {
                    "-" => -f,
                    "!" => f.fact_fraction(precision)?,
                    _ => panic!("Unknown unary operator: {}", op),
                }.into(),
                EvalResult::Matrix(matrix) => match op.as_str() {
                    "-" => matrix.inverse()?,
                    "!" => matrix.try_apply(&|f| f.factorial())?,
                    _ => panic!("Unknown unary operator: {}", op),
                }.into(),
            })
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
                    let mut destruct = false;
                    let arg_names: Vec<String> = 
                    args.iter()
                        .map(|arg| {
                            if let Node::Identifier(name) = arg {
                                Ok(name.clone())
                            } else if let Node::Matrix(matrix) = arg {
                                // special syntax for defining a destructive function
                                // f([x]) = ...
                                if matrix.len() == 1 && matrix[0].len() == 1 {
                                    if let Node::Identifier(name) = &matrix[0][0] {
                                        destruct = true;
                                        Ok(name.clone().replace("[", "").replace("]", ""))
                                    } else {
                                        Err("Use syntax f([x]) = ... for destructive functions.".to_string())
                                    }
                                } else {
                                    Err("Destructive functions must have a single argument.".to_string())
                                }
                            } else {
                                Err("Function arguments must be identifiers or destructured matrices.".to_string())
                            }
                        })
                        .collect::<Result<_, _>>()?;
                    
                    symbol_table.set_function(name.to_string(), arg_names, right.clone(), destruct);
                    return Ok(Fraction::zero().into());
                        
                    } else {
                    return Err("Invalid assignment.".to_string());
                }
            }
            // else
            let handle_frac = |left: Fraction, right: Fraction| -> Result<Fraction, String> {
                Ok(match op.as_str() {
                    "+" => left.added_to(&right),
                    "-" => left.subtract(&right),
                    "*" => left.multiply(&right),
                    "/" => left.divide(&right),
                    "^" => left.pow_frac(&right, precision)?,
                    _ => panic!("Unknown binary operator: {}", op),
                })
            };
            let left = evaluate(left, precision, previous_ans, symbol_table)?;
            let right = evaluate(right, precision, previous_ans, symbol_table)?;

            match (left, right) {
                (EvalResult::Fraction(f1), EvalResult::Fraction(f2)) => Ok(handle_frac(f1, f2)?.into()),
                (EvalResult::Matrix(m1), EvalResult::Matrix(m2)) => {
                    // matrix operations
                    match op.as_str() {
                        "+" => Ok(m1.add(&m2)?.into()),
                        "-" => Ok(m1.subtract(&m2)?.into()),
                        "*" => Ok(m1.multiply(&m2)?.into()),
                        "/" => Ok(m1.multiply(&m2.inverse()?)?.into()),
                        _ => Err("Invalid matrix operation.".to_string()),
                    }
                }
                (EvalResult::Fraction(f1), EvalResult::Matrix(m2)) => {
                    match op.as_str() {
                        "*" => Ok(m2.scale(&f1).into()),
                        _ => Err("Invalid operation between number and matrix. Try the other way around?".to_string()),
                    }
                }
                (EvalResult::Matrix(m1), EvalResult::Fraction(f2)) => {
                    match op.as_str() {
                        "+" => Ok(m1.try_apply(&|f| Ok(f.added_to(&f2)))?.into()),
                        "-" => Ok(m1.try_apply(&|f| Ok(f.subtract(&f2)))?.into()),
                        "*" => Ok(m1.scale(&f2).into()),
                        "/" => Ok(m1.try_apply(&|f| Ok(f.divide(&f2)))?.into()),
                        "^" => Ok(m1.try_apply(&|f| Ok(f.pow_frac(&f2, precision)?))?.into()),
                        _ => Err("Invalid operation between matrix and number.".to_string()),
                    }
                }
            }
        }
        Node::Function { name, args } => {
            // check for the correct number of arguments
            if FUNCTION_ARG_COUNT.iter()
                .any(|(func_name, count)| func_name == &name && args.len() > *count) {
                return Err(format!("Wrong number of arguments for function: {}", name));
            }

            let evaled_args: Vec<EvalResult> = args.iter().map(|arg| evaluate(arg, precision, previous_ans, symbol_table)).collect::<Result<_, _>>()?;

            let handle_custom_func = |func_name: &str, args: Vec<EvalResult>| -> Result<EvalResult, String> {
                if let Some((arg_names, body, _)) = symbol_table.get_function(name) {
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
            };

            let handle_frac_args = |args: Vec<Fraction>| -> Result<EvalResult, String> {
                Ok(match name.as_str() {
                    "sin" => args[0].sin(precision)?.into(),
                    "cos" => args[0].cos(precision)?.into(),
                    "tan" => args[0].tan(precision)?.into(),
                    "atan" => args[0].atan(precision)?.into(),
                    "asin" => args[0].asin(precision)?.into(),
                    "acos" => args[0].acos(precision)?.into(),
                    "sinh" => args[0].sinh(precision)?.into(),
                    "cosh" => args[0].cosh(precision)?.into(),
                    "tanh" => args[0].tanh(precision)?.into(),
                    "atanh" => args[0].atanh(precision)?.into(),
                    "asinh" => args[0].asinh(precision)?.into(),
                    "acosh" => args[0].acosh(precision)?.into(),
                    "log" if args.len() == 1 => args[0].log(&10u32.into(), precision)?.into(),
                    "log" if args.len() == 2 => args[1].log(&args[0], precision)?.into(),
                    "ln" => args[0].ln(precision)?.into(),
                    "exp" => args[0].exp(precision)?.into(),
                    "root" if args.len() == 1 => args[0].nth_root(&2u32.into(), precision)?.into(),
                    "root" if args.len() == 2 => args[1].nth_root(&args[0], precision)?.into(),
                    "floor" => args[0].floor().into(),
                    "ceil" => args[0].ceil().into(),
                    "round" if args.len() == 1 => args[0].round().into(),
                    "round" if args.len() == 2 => args[0].round_to_decimal(&args[1])?.into(),
                    "abs" => args[0].abs().into(),
                    // user's custom functions
                    func_name => handle_custom_func(func_name, args.iter().map(|f| EvalResult::from(f.clone())).collect())?,
                })
            };
            
            // TODO: switch destructuring feature to call-side so it can work with any function
            // for arg in args{
            //     if let Node::Matrix(matrix) = arg {
            //         if matrix.len() == 0 {return Err(format!("Empty matrix passed to function: {}", name).to_string());}
            //         // special syntax for calling a function as destructive
            //         // sin([M]) or sin([[1,2,3]]) -> calls sin on each element of matrix
                    
            //     } else {
            //         evaled_args.push(evaluate(arg, precision, previous_ans, symbol_table)?);
            //     }
            // }
            for arg in &evaled_args {
                if let EvalResult::Matrix(m) = arg {
                    if FUNCTION_ARG_COUNT.iter().any(|(func_name, _)| func_name == &name) {
                        if MATRIX_FUNCTIONS.iter().any(|func_name| func_name == &name) {
                            return match name.as_str() {
                                "det" => Ok(m.determinant()?.into()),
                                "inv" => Ok(m.inverse()?.into()),
                                "mean" => Ok(m.mean()?.into()),
                                "median" => Ok(m.median()?.into()),
                                "mode" => Ok(m.mode()?.into()),
                                "sum" => Ok(m.sum().into()),
                                "prod" => Ok(m.prod().into()),
                                //"ref" => Ok(m.row_echelon_form().into()),
                                _ => Err(format!("Matrix passed to function '{}' that is not destructive.", name)),
                            }
                        }
                        // rule out non-matrix built-in functions if a matrix was passed in
                        else {return Err(format!("Matrix passed to function '{}' that is not destructive.", name));}
                    } else if let Some((arg_names, body, destruct)) = symbol_table.get_function(name) {
                        // evaluate the function for every element of the matrix
                        if destruct && evaled_args.len() == 1 {
                            // store the arguments in a temporary symbol table
                            let mut temp_symbol_table = symbol_table.clone();
                            temp_symbol_table.remove_symbol(name); // prevent recursive calls
                            let mut res_matrix: Vec<Fraction> = Vec::new();
                            for f in m.clone() {
                                temp_symbol_table.set_variable(arg_names[0].clone(), Box::new(f.into()));
                                res_matrix.push(evaluate(&body, precision, previous_ans, &mut temp_symbol_table)?.into());
                            }
                            return Ok(Matrix::new_from_data(m.rows(), m.cols(), res_matrix)?.into());
                        }
                    }
                }        
            }

            // if they're all fractions
            if evaled_args.iter().all(|arg| matches!(arg, EvalResult::Fraction(_))) {
                Ok(handle_frac_args(evaled_args.iter().map(|f| f.clone().into()).collect())?.into())
            } else {
                handle_custom_func(name, evaled_args)
            }
        },
        Node::Identifier(id) => match id.as_str() {
            "pi" => Ok(Fraction::pi().clone().into()),
            "e" => Ok(Fraction::e().clone().into()),
            "last" => match previous_ans {
                Some(f) => Ok(f.clone().into()),
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
        }
    }
}