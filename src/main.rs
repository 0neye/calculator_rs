pub mod calc_engine;
pub mod evaluator;
pub mod parser;
pub mod tokenizer;

use std::env;
//use std::fs::File;
use crate::calc_engine::Fraction;
use std::io;

fn evaluate_expr(
    input: String,
    precision: u32,
    previous_ans: Option<&Fraction>,
) -> Result<Fraction, String> {
    let token_res = tokenizer::get_tokens(&input);
    if let Ok(tokens) = token_res {
        //println!("\ntokens = {:?}", tokens);
        let parsed = parser::parse(&tokens);
        if let Ok(parsed) = parsed {
            //println!("parsed = {:?}", parsed);
            let evaluated = evaluator::evaluate(&parsed, precision, previous_ans);
            if let Ok(evaluated) = evaluated {
                Ok(evaluated.rounded_if_close())
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

// the help menu
fn help_menu() {
    println!(
        "
    Usage: [expression] [options]

        Expression syntax:
            operators: +, -, *, /, ^
            parentheses: (, )
            functions: sin, cos, tan, root, exp, ln, log, floor, ceil, round, abs
            constants: pi, e
            last answer: 'last'

        Options:
            --f [format]    Set the display format for the answer
                            Options: decimal (d), fraction (f), mixed (m), scientific (s)
                            Default: decimal
            --p [precision] Set the precision for the answer and all intermediate calculations
                            Default: 500
            help            Display this help menu

        Examples:
            'log2.1(pi) + 2^3' or 'log(2.1, pi) + 2^3'
            '1/2 + 1/3'
            'root(2, 3)' or 'root2(3)'
            'e^pi' or 'exp(pi)'
            'sin(pi/2)'
            'last + 1/2'"
    );
}

//main
fn main() {
    // settings
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
    let mut display_fmt: String = "decimal".to_string();
    let mut calc_precision: u32 = 500;
    const MINIMUM_PRECISION: u32 = 10;

    fn evaluate_arguments(
        args: Vec<String>,
        current_display_fmt: String,
        current_precision: u32,
    ) -> Result<(String, String, u32), String> {
        let mut input = String::new();
        let mut iter = args.iter().enumerate();
        let mut new_fmt = current_display_fmt; // default
        let mut new_precision = current_precision; // default
        while let Some((i, arg)) = iter.next() {
            // check for the help flag
            if arg == "help" {
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
                new_fmt = this_fmt;
                // skip the next argument
                iter.next();
            // check for the precision flag
            } else if arg == "--p" && i + 1 < args.len() {
                let this_precision = args[i + 1].to_string();
                if let Ok(this_precision) = this_precision.parse::<u32>() {
                    if this_precision < MINIMUM_PRECISION {
                        return Err(format!("Precision must be at least {}", MINIMUM_PRECISION));
                    }
                    new_precision = this_precision;
                } else {
                    return Err(format!("Invalid precision: {}", this_precision));
                }
                iter.next();
            } else {
                // if not a flag, add it to the input string
                input.push_str(arg);
                input.push(' ');
            }
        }
        Ok((input, new_fmt, new_precision))
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

    // get command line arguments
    let args: Vec<String> = env::args().collect();
    // if there are no arguments, start the REPL
    if args.len() == 1 {
        let mut previous_ans: Fraction = Fraction::from(0);
        loop {
            // get input
            let mut input = String::new();
            println!("Enter an expression (q to quit):");
            io::stdin().read_line(&mut input).unwrap();
            if input.trim() == "q" {
                break;
            }

            // evaluate the arguments, setting the display format and precision to the default values
            // if the user provided any flags, they will overwrite the defaults
            (input, display_fmt, calc_precision) = match evaluate_arguments(
                input.split_whitespace().map(|s| s.to_string()).collect(),
                display_fmt.clone(),
                calc_precision,
            ) {
                Ok((input, display_fmt, calc_precision)) => {
                    // trim the input string and return it
                    (input.trim().to_string(), display_fmt, calc_precision)
                }
                Err(err) => {
                    // if there was an error, print it and continue
                    println!("{}", err);
                    continue;
                }
            };

            // evaluate input
            if input == "".to_string() {
                continue;
            }

            let result = evaluate_expr(input, calc_precision, Some(&previous_ans));
            if let Ok(result) = result {
                println!(
                    "\nAnswer: {}\n",
                    get_fmt_function(&display_fmt)(&result, calc_precision)
                );
                previous_ans = result;
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
        let (input, display_fmt, calc_precision) = match evaluate_arguments(
            args[1..].iter().map(|s| s.to_string()).collect(),
            display_fmt,
            calc_precision,
        ) {
            Ok((input, display_fmt, calc_precision)) => {
                // trim the input string and return it
                (input.trim().to_string(), display_fmt, calc_precision)
            }
            Err(err) => {
                // if there was an error, print it and return
                println!("{}", err);
                return;
            }
        };

        // evaluate input
        if input == "".to_string() {
            return;
        }

        let result = evaluate_expr(input, calc_precision, None);
        if let Ok(result) = result {
            println!(
                "{}",
                get_fmt_function(&display_fmt)(&result, calc_precision)
            );
        } else {
            println!("{}", result.unwrap_err());
        }
    }
}
