use crate::{calc_engine::Fraction, parser::Node};

pub fn evaluate(
    node: &Node,
    precision: u32,
    previous_ans: Option<&Fraction>,
) -> Result<Fraction, String> {
    match node {
        Node::Number(f) => Ok((*f).clone()),
        Node::UniOp { op, child } => {
            let child = evaluate(child, precision, previous_ans)?;
            match op.as_str() {
                "-" => Ok(-child),
                "!" => child.factorial(),
                _ => panic!("Unknown unary operator: {}", op),
            }
        }
        Node::BinOp { op, left, right } => {
            let left = evaluate(left, precision, previous_ans)?;
            let right = evaluate(right, precision, previous_ans)?;
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
                .map(|arg| evaluate(arg, precision, previous_ans))
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
            _ => Err(format!("Unknown identifier: {}", id)),
        },
    }
}
