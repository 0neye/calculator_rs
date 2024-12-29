pub mod calc_engine;
pub mod evaluator;
pub mod parser;
pub mod tokenizer;

use evaluator::SymbolTable;
use evaluator::EvalResult;
use fieri::{
    completion::{create, CompletionParamBuilder},
    Client, Error,
};
use std::{env, io::{BufRead, Write}};

//use std::fs::File;
use calc_engine::Fraction;
//use calc_engine::Matrix;
use std::io;

/// Evaluates an expresion and returns the result of the calculation
fn evaluate_expr(
    input: String,
    precision: u32,
    previous_ans: Option<&EvalResult>,
    symbol_table: &mut SymbolTable
) -> Result<EvalResult, String> {
    let token_res = tokenizer::get_tokens(&input);
    if let Ok(tokens) = token_res {
        //dbg!(&tokens);
        let parsed = parser::parse(&tokens);
        if let Ok(parsed) = parsed {
            //dbg!(&parsed);
            //let start_time = std::time::Instant::now();
            let evaluated = evaluator::evaluate(&parsed, precision, previous_ans, symbol_table);
            //let end_time = std::time::Instant::now();
            //println!("Time: {}ms", end_time.duration_since(start_time).as_millis());
            if let Ok(evaluated) = evaluated {
                Ok(match evaluated {
                    EvalResult::Fraction(f) => f.rounded_if_close().into(),
                    EvalResult::Matrix(m) => m.into(),
                })
            } else {
                Err(format!("invalid input: {}", evaluated.unwrap_err()))
            }
        } else {
            Err(format!("invalid input: {}", parsed.unwrap_err()))
        }
    } else {
        Err(format!("invalid input: {}", token_res.unwrap_err()))
    }
}

fn get_fmt_function(fmt: &str) -> fn(&Fraction, u32) -> String {
    match fmt {
        "decimal" | "d" => Fraction::to_string_decimal,
        "fraction" | "f" => Fraction::to_string_p,
        "mixed" | "m" => Fraction::to_string_mixed,
        "scientific" | "s" => Fraction::to_string_scientific,
        _ => panic!("Invalid format option: {}", fmt),
    }
}

/// Reads the API key from the .env file very crudely. Doesn't even work when run from the command line.
fn get_api_key() -> Result<String, String> {
    //read from .env file in this or parent directorys
    let mut api_key = String::new();
    let mut file = std::fs::File::open(".env");
    if file.is_err() {
        file = std::fs::File::open("../.env");
    }
    if file.is_err() {
        file = std::fs::File::open("../../.env");
    }
    if file.is_err() {
        file = std::fs::File::open("../../../.env");
    }
    if file.is_err() {
        return Err("No .env file found".to_string());
    }
    let file = file.unwrap();
    let lines = std::io::BufReader::new(file).lines();
    for line in lines {
        let line = line.unwrap();
        if line.starts_with("OPENAI_API_KEY") {
            api_key = line.split("=").collect::<Vec<&str>>()[1].to_string();
        }
    }

    if api_key.is_empty() {
        Err("API_KEY not found in .env file".to_string())
    } else {
        Ok(api_key)
    }
}

/// Uses OpenAI API to evaluate a query into an expression
async fn evaluate_query(query: String) -> Result<String, Error> {
    let key = match get_api_key() {
        Ok(key) => key,
        Err(err) => {
            println!("{}", err);
            return Ok("".to_string());
        }
    };

    let client = Client::new(key);
    let prompt = format!(
"Usage: [expression] [options]

    Expression syntax:
        operators: +, -, *, /, ^, !
        parentheses: (, )
        base functions: sin, cos, tan, root, exp, ln, log, floor, ceil, round, abs
        constants: pi, e
        last answer: 'last'
        assignment: '=' (variable names can not have numbers)

    Options:
        --f  [format]            Set the display format for the answer
                                Options: decimal (d), fraction (f), mixed (m), scientific (s)
                                Default: decimal
        --p  [precision]         Set the precision for the answer and all intermediate calculations
                                Default: 500
        --fp [format-precision]  Set the precision for just the formatted answer
                                Default: 35
        --h  [handheld-mode]     Toggles teh behavior of inserting your last answer at the beginning of the expression
                                Default: false
        --q  [query]             Use OpenAI api to evaluate a query into an expression
        --help                  Display this help menu
        --help [name] | 'all'   Display info on the given function or variable

    Examples:
        'log(2.1, pi) + 2^3'
        'x = 1/2 + 1/3'
        'root(2, 3)'
        'e^pi' or 'exp(pi)'
        'sin(pi/2)'
        'test = last + 1/2'
        'f(x) = x^2 + 2x - 5'
        'f(45)'

Additional Functions and Constants:

Function: quad(a, b, c) = [(-b + root(b ^ 2 - 4 * a * c)) / 2 * a, (-b - root(b ^ 2 - 4 * a * c)) / 2 * a]
Function: pva(r, n, pmt) = pmt * (1 - (1 + r) ^ -n) / r
Function: fva(r, n, pmt) = pmt * ((1 + r) ^ n - 1) / r
Function: pv(fv, r, n) = fv / (1 + r) ^ n
Function: fv(pv, r, n) = pv * (1 + r) ^ n
Function: pmt(pv, fv, r, n) = (pv - fv) / ((1 + r) ^ n - 1)
Function: nper(pmt, r, fv) = log(fv / pmt) / log(1 + r)
Function: pci(p, r, t, n) = p * (1 + r / n) ^ (n * t)
Function: cci(p, r, t) = p * exp(r * t)
Function: si(p, r, t) = p * r * t
Function: comb(n, r) = n! / r! * (!n - r)
Function: perm(n, r) = n! / (!n - r)
Function: sinh(x) = (exp(x) - exp(-x)) / 2
Function: cosh(x) = (exp(x) + exp(-x)) / 2
Function: tanh(x) = sinh(x) / cosh(x)
Function: asinh(x) = ln(x + root(x ^ 2 + 1))
Function: acosh(x) = ln(x + root(x ^ 2 - 1))
Function: atanh(x) = 1/2 * ln((1 + x) / (1 - x))
Function: asin(x) = atan(x / root(1 - x ^ 2))
Function: acos(x) = atan(root(1 - x ^ 2) / x)
Variable: h = 100
Variable: k = 1000
Variable: mill = 1000000
Variable: bill = 1000000000
Variable: m = 1000000
Variable: b = 1000000000

Syntax Notes:
- Commas in numbers are not supported. Replace them with backticks.
- Implicit multiplication is supported, but only use it with the provided constants for clarity (like k for thousand).
- Matrices have limited support. Destructive functions can be declared like 'abs_all([x]) = abs(x)' and will apply to all values in an input matrix.

Below is the query:
<QUERY>
{}
</QUERY>
", query.trim()
    );
    let params = CompletionParamBuilder::new("text-davinci-003")
        .prompt(prompt)
        .max_tokens(35)
        .temperature(0.4)
        .top_p(1.0)
        .frequency_penalty(0.0)
        .presence_penalty(0.0)
        .build()?;

    let response = create(&client, &params).await?.choices[0]
        .text
        .as_ref()
        .unwrap()
        .trim()
        .to_string();

    Ok(response)
}

// the help menu
fn help_menu() {
    println!(
        "
    Usage: [expression] [options]

        Expression syntax:
            operators: +, -, *, /, ^, !
            parentheses: (, )
            base functions: sin, cos, tan, root, exp, ln, log, floor, ceil, round, abs
            constants: pi, e
            last answer: 'last'
            assignment: '=' (variable names can not have numbers)

        Options:
            --f  [format]            Set the display format for the answer
                                    Options: decimal (d), fraction (f), mixed (m), scientific (s)
                                    Default: decimal
            --p  [precision]         Set the precision for the answer and all intermediate calculations
                                    Default: 500
            --fp [format-precision]  Set the precision for just the formatted answer
                                    Default: 35
            --h  [handheld-mode]     Toggles teh behavior of inserting your last answer at the beginning of the expression
                                    Default: false
            --q  [query]             Use OpenAI api to evaluate a query into an expression
            --help                  Display this help menu
            --help [name] | 'all'   Display info on the given function or variable

        Examples:
            'log(2.1, pi) + 2^3'
            'x = 1/2 + 1/3'
            'root(2, 3)'
            'e^pi' or 'exp(pi)'
            'sin(pi/2)'
            'test = last + 1/2'
            'f(x) = x^2 + 2x - 5'
            'f(45)'
            "
    );
}

enum CliArgument {
    Format(String),       // format type
    Precision(u32),       // precision for all calculations
    FormatPrecision(u32), // precision used when formatting the answer
    HandheldMode,   // whether to insert the last answer at the beginning
    Query(String),        // query to AI
}
const MINIMUM_PRECISION: u32 = 10;
const FMT_OPTIONS: [&str; 8] = [
    "decimal",
    "fraction",
    "mixed",
    "scientific",
    "d",
    "f",
    "m",
    "s",
];

/// Parses command line arguments and returns the parsed values
fn evaluate_arguments(args: Vec<String>, symbol_table: &SymbolTable) -> Result<(String, Option<Vec<CliArgument>>), String> {
    let mut input = String::new();
    let mut new_args: Vec<CliArgument> = Vec::new();
    let mut iter = args.iter().enumerate();
    while let Some((i, arg)) = iter.next() {

        // check for the help flag and variations
        if arg == "--help" && i + 1 < args.len() {
            let this_name = args[i + 1].to_string();
            if this_name == "all" {
                println!("{}", symbol_table.get_symbol_string_list());
                return Err("".to_string());
            }
            else if !symbol_table.get_symbol_string(&this_name).is_empty() {
                println!("{}", symbol_table.get_symbol_string(&this_name));
                return Err("".to_string());
            }
            return Err(format!("Unknown function or variable: {}", this_name));
        } 
        if arg == "--help" {
            help_menu();
            return Err("".to_string());
        }

        // check for the format flag
        if arg == "--f" && i + 1 < args.len() {
            // get the format option
            let this_fmt = args[i + 1].to_string();
            // check if the option is valid
            if !FMT_OPTIONS.contains(&this_fmt.as_str()) {
                return Err(format!("Invalid format option: {}", this_fmt));
            }
            // if valid, set the new format
            new_args.push(CliArgument::Format(this_fmt));
            // skip the next argument
            iter.next();
        }
        // check for the precision flag
        else if arg == "--p" && i + 1 < args.len() {
            let this_precision = args[i + 1].to_string();
            if let Ok(this_precision) = this_precision.parse::<u32>() {
                // check if the precision is valid
                if this_precision < MINIMUM_PRECISION {
                    return Err(format!("Precision must be at least {}", MINIMUM_PRECISION));
                }
                // if valid, set the new precision
                new_args.push(CliArgument::Precision(this_precision));
            } else {
                return Err(format!("Invalid precision: {}", this_precision));
            }
            iter.next();
        }
        
        // check for format precision flag
        else if arg == "--fp" && i + 1 < args.len() {
            let this_precision = args[i + 1].to_string();
            if let Ok(this_precision) = this_precision.parse::<u32>() {
                // check if the precision is valid
                if this_precision <= 0 {
                    return Err(format!("Format precision must be greater than 0"));
                }
                // if valid, set the new precision
                new_args.push(CliArgument::FormatPrecision(this_precision));
            } else {
                return Err(format!("Invalid format precision: {}", this_precision));
            }
            iter.next();
        }
        // check for handheld mode flag
        else if arg == "--h" {
            new_args.push(CliArgument::HandheldMode); // true in this case means to toggle the flag
            iter.next();
        }
        // check for the query flag
        else if arg == "--q" && i + 1 < args.len() {
            // a query is multiple words, so loop until the next flag
            let mut this_query = String::new();
            while let Some((_, arg)) = iter.next() {
                if arg.starts_with("--") {
                    iter.next_back();
                    break;
                }
                this_query.push_str(arg);
                this_query.push(' ');
            }
            new_args.push(CliArgument::Query(this_query));
            iter.next();
        } else {
            // if not a flag, add it to the input string
            input.push_str(arg);
            input.push(' ');
        }
    }
    if new_args.is_empty() {
        Ok((input, None))
    } else {
        Ok((input, Some(new_args)))
    }
}


//main
#[tokio::main]
async fn main() {
    // settings (defaults)
    let mut display_fmt: String = "decimal".to_string();
    let mut calc_precision: u32 = 500;
    let mut fmt_precision: u32 = 35;
    let mut handheld_mode = false;
    let mut symbol_table: SymbolTable = SymbolTable::new();
    evaluator::init_custom_symbols(&mut symbol_table);
    //println!("{}", symbol_table.get_symbol_string_list());

    // get command line arguments
    let args: Vec<String> = env::args().collect();
    // if there are no arguments, start the REPL
    if args.len() == 1 {
        let mut previous_ans: EvalResult = Fraction::zero().into();
        let mut answer_str = String::new();
        loop {
            // get input
            let mut input = String::new();
            if handheld_mode {
                print!("Calc >> {}", answer_str);
            } else {
                print!("Calc >> ");
            }
            io::stdout().flush().unwrap();
            io::stdin().read_line(&mut input).unwrap();
            if input.trim() == "q" {
                break;
            }

            // evaluate the arguments, setting the display format and precision to the default values
            // if the user provided any flags, they will overwrite the defaults
            match evaluate_arguments(input.split_whitespace().map(|s| s.to_string()).collect(), &symbol_table) {
                Ok((new_input, Some(new_args))) => {
                    let mut ai_gen_expr = String::new();
                    for arg in new_args {
                        match arg {
                            CliArgument::Format(fmt) => display_fmt = fmt,
                            CliArgument::Precision(precision) => calc_precision = precision,
                            CliArgument::FormatPrecision(precision) => fmt_precision = precision,
                            CliArgument::HandheldMode => handheld_mode = !handheld_mode,
                            CliArgument::Query(query) => {
                                // get the ai response and set the input to it
                                ai_gen_expr = evaluate_query(query).await.unwrap_or("".to_string());
                                println!("Generated expression: {}", ai_gen_expr)
                            }
                        }
                    }
                    if ai_gen_expr != "" {
                        input = ai_gen_expr;
                    } else {
                        input = new_input;
                    }
                }
                Ok((new_input, None)) => input = new_input,
                Err(err) => {
                    // if there was an error, print it and continue
                    println!("{}", err);
                    continue;
                }
            };

            if handheld_mode {
                // if it's empty (just hit enter) clear the answer string
                if input.trim().is_empty() {
                    answer_str = String::new();
                    continue;
                } else if !answer_str.is_empty() { // else insert the answer in the front of the expression
                    input = format!("({}) {}", previous_ans.to_string(), input);
                }
            } else {
                answer_str = String::new();
            }

            //dbg!(&input);
            //dbg!(&handheld_mode);

            // evaluate input
            if input == "".to_string() {
                continue;
            }

            let result = evaluate_expr(
                input,
                calc_precision,
                Some(&previous_ans),
                &mut symbol_table,
            );
            if let Ok(result) = result {
                previous_ans = result;
                answer_str = match previous_ans.clone() {
                    EvalResult::Fraction(f) => get_fmt_function(&display_fmt)(&f, fmt_precision),
                    EvalResult::Matrix(m) => m.to_string_fmt(get_fmt_function(&display_fmt), fmt_precision),
                };
                println!("\n> {}\n", answer_str);
            } else {
                println!("{}", result.unwrap_err());
            }
        }
    }
    // if there are arguments, evaluate the expression once
    else {
        // parse the command line arguments into a string

        // evaluate the arguments, setting the display format and precision to the default values
        // if the user provided any flags, they will overwrite the defaults
        let mut input = args[1].to_string();

        match evaluate_arguments(args[1..].iter().map(|s| s.to_string()).collect(), &symbol_table) {
            Ok((new_input, Some(new_args))) => {
                for arg in new_args {
                    match arg {
                        CliArgument::Format(fmt) => display_fmt = fmt,
                        CliArgument::Precision(precision) => calc_precision = precision,
                        CliArgument::FormatPrecision(precision) => fmt_precision = precision,
                        CliArgument::HandheldMode => handheld_mode = !handheld_mode, // does nothing in this case
                        CliArgument::Query(query) => {
                            // get the ai response and set the input to it
                            input = evaluate_query(query).await.unwrap_or("".to_string());
                            println!("Generated expression: {}", input)
                        }
                    }
                }
                input = new_input;
            }
            Ok((new_input, None)) => input = new_input,
            Err(err) => {
                // if there was an error, print it and exit
                println!("{}", err);
                return;
            }
        };

        // evaluate input
        if input == "".to_string() {
            return;
        }

        let result = evaluate_expr(input, calc_precision, None, &mut symbol_table);
        if let Ok(result) = result {
            let str = match result {
                EvalResult::Fraction(f) => get_fmt_function(&display_fmt)(&f, fmt_precision),
                EvalResult::Matrix(m) => m.to_string_fmt(get_fmt_function(&display_fmt), fmt_precision),
            };
            println!("\n> {}\n", str);
        } else {
            println!("{}", result.unwrap_err());
        }
    }
}
