use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;
//use std::time::Instant;

use malachite::num::arithmetic::traits::{Abs, Ceiling, Floor, Mod, Pow, Reciprocal};
use malachite::num::conversion::string::options::ToSciOptions;
use malachite::num::conversion::traits::ToSci;
use malachite::num::logic::traits::SignificantBits;
//use malachite::rounding_modes::RoundingMode;
use malachite::{self, Integer, Natural, Rational};

//wrapper
#[derive(PartialEq, Eq, PartialOrd, Debug, Clone)]
pub struct Fraction {
    value: Rational,
}

//implementing the Fraction struct
impl Fraction {
    /// The constant pi.
    pub fn pi() -> Fraction {
        Fraction::parse_decimal(
            "3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566"
        )
        .unwrap()
    }

    /// The natural logarithm of 10.
    fn ln10() -> Fraction {
        Fraction::parse_decimal(
            "2.3025850929940456840179914546843642076011014886287729760333279009675726096773524802359972050895982983419677840422862486334095254650828067566662873690987816894829072083255546808437998948262331985283935053089653777326288461633662222876982198867465436674744042432743651550489343149393914796194044002221051017141748003688084012647080685567743216228355220114804663715659121373450747856947683463616792101806445070648000277502684916746550586856935673420670581136429224554405758925724208241314695689016758940256776311356919292"
        )
        .unwrap()
    }

    /// The constant e.
    pub fn e() -> Fraction {
        Fraction::parse_decimal(
            "2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307381323286279434907632338298807531952510190115738341879307021540891499348841675092447614606680822648001684774118537423454424371075390777449920695517027618386062613313845830007520449338265602976067371132007093287091274437470472306969772093101416928368190255151086574637721112523897844250569536967707854499699679468644549059879316368892300987931277361782154249992"
        )
        .unwrap()
    }

    //new
    pub fn new(numerator: i64, denominator: i64) -> Fraction {
        Fraction {
            value: Rational::from_integers(Integer::from(numerator), Integer::from(denominator)),
        }
    }

    //new from big ints
    pub fn new_from_big_ints(numerator: &Integer, denominator: &Integer) -> Fraction {
        Fraction {
            value: Rational::from_integers(numerator.clone(), denominator.clone()),
        }
    }

    //new from big natural
    pub fn new_from_big_naturals(numerator: &Natural, denominator: &Natural) -> Fraction {
        Fraction {
            value: Rational::from_naturals(numerator.clone(), denominator.clone()),
        }
    }

    //Parses a string in any form.
    pub fn parse(s: &str) -> Option<Fraction> {
        if s.contains('.') {
            return Fraction::parse_decimal(s);
        }
        match Rational::from_str(s) {
            Ok(r) => Some(Fraction { value: r }),
            Err(_) => None,
        }
    }

    /// Parses a string in decimal form.
    pub fn parse_decimal(s: &str) -> Option<Fraction> {
        // if the string is empty
        if s.is_empty() {
            return None;
        }
        // if there is a decimal point
        if s.contains('.') {
            // get the index of the decimal point
            let index = s.find('.').unwrap();
            // get the length of the string
            let length = s.len();
            // get the number of digits after the decimal point
            let digits_after_decimal = length - index - 1;
            // get the numerator
            let numerator = Integer::from_str(&s.replace('.', "")).unwrap();
            // get the denominator
            let denominator = Integer::from(10).pow(digits_after_decimal as u64);
            // return the fraction
            Some(Fraction::new_from_big_ints(&numerator, &denominator))
        } else {
            // if there is no decimal point
            // get the numerator
            let numerator = Integer::from_str(s).unwrap();
            // get the denominator
            let denominator = Integer::from(1);
            // return the fraction
            Some(Fraction::new_from_big_ints(&numerator, &denominator))
        }
    }

    // add
    pub fn added_to(&self, other: &Fraction) -> Fraction {
        Fraction {
            value: (&self.value).add(&other.value),
        }
    }

    pub fn add_assign(&mut self, other: &Fraction) {
        self.value.add_assign(&other.value);
    }

    // subtract
    pub fn subtract(&self, other: &Fraction) -> Fraction {
        Fraction {
            value: (&self.value).sub(&other.value),
        }
    }

    pub fn sub_assign(&mut self, other: &Fraction) {
        self.value.sub_assign(&other.value);
    }

    // multiply
    pub fn multiply(&self, other: &Fraction) -> Fraction {
        Fraction {
            value: (&self.value).mul(&other.value),
        }
    }

    pub fn mul_assign(&mut self, other: &Fraction) {
        self.value.mul_assign(&other.value);
    }

    // divide
    pub fn divide(&self, other: &Fraction) -> Fraction {
        Fraction {
            value: (&self.value).div(&other.value),
        }
    }

    pub fn div_assign(&mut self, other: &Fraction) {
        self.value.div_assign(&other.value);
    }

    // negate
    pub fn negate(&self) -> Fraction {
        Fraction {
            value: -(&self.value),
        }
    }

    // clone
    pub fn clone(&self) -> Fraction {
        Fraction {
            value: self.value.clone(),
        }
    }

    // numer
    pub fn numer(&self) -> &Natural {
        self.value.numerator_ref()
    }

    // denom
    pub fn denom(&self) -> &Natural {
        self.value.denominator_ref()
    }

    /// Gets the integer part of a Fraction.
    pub fn trunc(&self) -> Fraction {
        Fraction {
            value: if self > &Fraction::from(0) {
                (&self.value).floor().into()
            } else {
                (&self.value).ceiling().into()
            },
        }
    }

    /// Gets the fractional part of a Fraction.
    pub fn fract(&self) -> Fraction {
        Fraction {
            value: Rational::from_naturals_ref(&(self.numer().mod_op(self.denom())), self.denom()),
        }
    }

    /// Rounds towards negative infinity.
    pub fn floor(&self) -> Fraction {
        Fraction {
            value: (&self.value).floor().into(),
        }
    }

    /// Rounds towards positive infinity.
    pub fn ceil(&self) -> Fraction {
        Fraction {
            value: (&self.value).ceiling().into(),
        }
    }

    /// Rounds to the nearest integer.
    pub fn round(&self) -> Fraction {
        //to round a number, we add 0.5 and then truncate
        let sign = if self.value < 0.0 { -1 } else { 1 };
        self.abs()
            .added_to(&Fraction::parse("0.5").unwrap())
            .multiply(&Fraction::from(sign))
            .trunc()
    }

    /// Gets the absolute value of a Fraction.
    pub fn abs(&self) -> Fraction {
        Fraction {
            value: (&self.value).abs(),
        }
    }

    // recip
    pub fn recip(&self) -> Fraction {
        Fraction {
            value: (&self.value).reciprocal(),
        }
    }

    /// gets e ^ x where both are Fractions. <br>
    /// Uses a taylor series: https://github.com/microsoft/calculator/blob/master/src/CalcManager/Ratpack/exp.cpp
    //             |sum of    /              self  \
    // 1 + self +  |i=1 to   | lastTerm  *  ------- |
    //             |i=1000    \        i-1    i+1  /
    //
    // lastTerm = self      stop when the terms are adding less than "STOP_AFTER"
    //         0
    pub fn exp(&self, precision: u32) -> Result<Fraction, String> {
        //println!("exp({})", self.to_string());
        // if numerator is 0
        if self.value == 0.0 {
            //return 1
            return Ok(Fraction::from(1));
        }
        // if it's negative
        if self.value < 0.0 {
            //return 1 / (e ^ -x)
            return Ok(Fraction::from(1).divide(&self.negate().exp(precision)?));
        }
        // if the input is too large
        if self.value > 5000000.0 {
            return Err(format!(
                "Can't take the exp of a number greater than 5,000,000. {} is greater than that.",
                self.to_string_decimal(20)
            ));
        }

        // split the fraction into integer and fractional parts
        let binding = self.trunc(); //temp
        let int_part = binding.numer();
        let exp_int_part = Fraction::e().pow_nat(int_part, precision)?;
        let scaled = self.fract();

        // when the value is exactly a whole number
        if scaled == Fraction::from(0) {
            return Ok(exp_int_part.trimed(precision));
        }
        // when it has a fractional part as well
        else if int_part != &0 {
            return Ok(scaled
                .exp(precision)?
                .multiply(&exp_int_part)
                .trimed(precision));
        }

        const MAX_LOOP_TIMES: u32 = 1000;
        let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
            &Integer::from(1),
            &Integer::from(precision).pow(precision as u64 / 10),
        );

        // initialize the last term and the sum
        let mut last_term = self.trimed(precision);
        let mut sum = Fraction::from(1).added_to(&last_term);

        // iterate until the last term is small enough
        for i in 1..MAX_LOOP_TIMES {
            // calculate the value of the current term
            let this_term = last_term
                .multiply(&self.divide(&Fraction::from(i + 1)))
                .trimed(precision);

            // add the term to the sum
            sum.add_assign(&this_term);

            // check if the term is small enough
            if this_term < STOP_AFTER {
                break;
            }

            // update the last term
            last_term = this_term;

            // trim the sum to the desired precision
            sum.trim(precision);
        }
        Ok(sum)
    }

    /// Gets the natural logarithm of a Fraction. <br>
    /// Uses arctanh taylor series: https://en.wikipedia.org/wiki/Logarithm#Calculation
    //     |sum of      1       /  self-1  \ 2i+1
    // 2 * |i=0 to    ------ * |  --------  |
    //     |i=500      2i+1     \  self+1  /
    // stop when the terms are adding less than "STOP_AFTER"
    pub fn ln(&self, precision: u32) -> Result<Fraction, String> {
        // if it's  0
        if self.value == 0.0 {
            return Err(format!("Can't take the ln of 0"));
        }
        // if it's 1
        else if self.value == 1.0 {
            //return 0
            return Ok(Fraction::from(0));
        }
        // if it's negative, recurse
        else if self.value < 0.0 {
            //return -ln(-x)
            return Ok(self.negate().ln(precision)?.negate());
        }

        // break frac into a * 10^b or do Ln(a) + b * Ln(10) where b is the power of 10 to get a < 10
        let mut frac = self.clone();
        let mut b = 0;
        if frac > Fraction::ln10() {
            b = num_decimal_digits(frac.trunc().numer()) as i64 - 2;
            if b < 0 {
                b = 0;
            }
            frac.div_assign(&Fraction::from(&Integer::from(10).pow(b as u64)));
        }
        frac.trim(precision);

        const MAX_LOOP_TIMES: u32 = 500;
        let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
            &Integer::from(1),
            &Integer::from(precision).pow(precision as u64 / 10),
        );

        // calculate the value of (frac - 1) / (frac + 1)
        let num_1_less_over_1_more = ((frac.clone() - Fraction::from(1))
            / (frac.clone() + Fraction::from(1)))
        .trimed(precision);

        // initialize the sum to 0
        let mut sum = Fraction::from(0);

        // iterate until the last term is small enough
        for i in 0..MAX_LOOP_TIMES {
            // calculate the value of the current term
            let this_term = num_1_less_over_1_more
                .pow(&Integer::from(2 * i + 1), precision)?
                .divide(&Fraction::from(2 * i + 1));

            // add the term to the sum
            sum.add_assign(&this_term);

            // check if the term is small enough
            if this_term < STOP_AFTER {
                break;
            }

            // trim the sum to the desired precision
            sum.trim(precision);
        }
        // scale back up
        let result = sum * Fraction::from(2) + Fraction::from(b).multiply(&Fraction::ln10());

        Ok(result.trimed(precision))
    }

    /// Gets the sine of a Fraction. <br>
    /// Uses a taylor series.
    //         |sum of    /               -(self^2)    \
    // self +  |i=1 to   | lastTerm  *  --------------- |
    //         |i=500     \       i-1     2*i*(2*i+1)  /
    //
    // lastTerm = self      stop when the terms are adding less than "STOP_AFTER"
    //         0
    pub fn sin(&self, precision: u32) -> Result<Fraction, String> {
        let pi2 = &(Fraction::pi() * Fraction::from(2));

        //scale within abs of 2 pi
        let mut scaled = self.clone();

        //if self > pi2
        if self > pi2 {
            //self - (self / pi2).trunc() * pi2
            scaled = self.subtract(&self.divide(&pi2).trunc().multiply(&pi2));

        //if self < -pi2
        } else if self < &-pi2.clone() {
            //self + (self.abs() / pi2).trunc() * pi2
            scaled = self.added_to(&Fraction::abs(self).divide(&pi2).trunc().multiply(&pi2));
        }
        scaled.trim(precision);

        const MAX_LOOP_TIMES: i64 = 500;
        let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
            &Integer::from(1),
            &Integer::from(precision).pow(precision as u64 / 10),
        );

        // initialize the last term and the sum
        let mut last_term = scaled.clone();
        let mut sum = scaled.clone();

        // iterate until the last term is small enough
        for i in 1..MAX_LOOP_TIMES {
            // calculate the value of the current term
            let this_term = last_term
                .multiply(
                    &(-scaled.clone().pow(&Integer::from(2), precision)?)
                        .divide(&Fraction::from(2 * i * (2 * i + 1))),
                )
                .trimed(precision);

            // add this term to the sum
            sum = sum.added_to(&this_term);

            // check if the term is small enough
            if this_term.abs() < STOP_AFTER {
                break;
            }

            // update the last term
            last_term = this_term;

            // trim the sum to the required precision
            sum.trim(precision);
        }
        Ok(sum)
    }

    /// Gets the cosine of a Fraction. <br>
    /// Uses sine and shifts the input by pi/2.
    pub fn cos(&self, precision: u32) -> Result<Fraction, String> {
        Ok((self.added_to(&Fraction::pi().divide(&Fraction::from(2)))).sin(precision)?)
    }

    /// Gets the tangent of a Fraction. <br>
    /// Uses sine and cosine.
    pub fn tan(&self, precision: u32) -> Result<Fraction, String> {
        Ok(self.sin(precision)?.divide(&self.cos(precision)?))
    }

    /// Takes a Fraction to an integer power.
    pub fn pow(&self, exponent: &Integer, precision: u32) -> Result<Fraction, String> {
        // if the exponent is 0 or 1
        if exponent == &0 {
            return Ok(Fraction::from(1));
        } else if exponent == &Integer::from(1) {
            return Ok(self.clone());
        }
        // if the exponent is negative
        else if exponent < &0 {
            //return the inverse of the fraction to the power of the absolute value of the exponent
            return Ok(self.pow(&exponent.abs(), precision)?.recip());
        }

        // exponentiation by squaring
        // https://en.wikipedia.org/wiki/Exponentiation_by_squaring
        // initialize the result
        let mut result = Fraction::from(1);

        // clone the fraction
        let mut frac = self.clone();

        // get the exponent as a u32
        if let Ok(mut exp) = u32::try_from(exponent) {
            // while the exponent is greater than 0
            while exp > 0 {
                // if the exponent is odd
                if exp % 2 == 1 {
                    // multiply the result by the fraction
                    result.mul_assign(&frac);
                }

                // square the fraction
                frac = frac.multiply(&frac);

                // trim the result and fraction
                result.trim(precision);
                frac.trim(precision);

                // divide the exponent by 2
                exp /= 2;
            }
            // return the trimed result
            Ok(result.trimed(precision))
        } else {
            // uses x^y = e^(y*ln(x))
            Ok(self
                .ln(precision)?
                .multiply(&Fraction::from(exponent))
                .exp(precision)?)
        }
    }

    fn pow_nat(&self, exponent: &Natural, precision: u32) -> Result<Fraction, String> {
        Ok(self.pow(&Integer::from(exponent), precision)?)
    }

    /// Gets the nth root of a Fraction. <br>
    /// Uses nth root of x = e^(Ln(x)/n).
    pub fn nth_root(&self, n: &Fraction, precision: u32) -> Result<Fraction, String> {
        Ok(self.ln(precision)?.divide(n).exp(precision)?)
    }

    /// Takes one Fraction to the power of another Fraction. <br>
    pub fn pow_frac(&self, exponent: &Fraction, precision: u32) -> Result<Fraction, String> {
        let p_less = precision / 5;

        if exponent.value == 0.0 {
            //return 1
            return Ok(Fraction::from(1));
        }
        if self.value == 0.0 {
            //return 0
            return Ok(Fraction::from(0));
        }
        if exponent.value < 0.0 {
            //return 1 / x ^ -n
            return Ok(self.pow_frac(&-exponent.clone(), precision)?.recip());
        }
        if self == &Fraction::e() {
            //return e ^ n
            return Ok(exponent.exp(precision)?);
        }

        // if the exponent is a whole number
        if exponent.denom() == &Natural::from(1u8) {
            //return x ^ n
            return Ok(self.pow(&exponent.numer().into(), precision)?);
        }

        // exponents with int parts can be split into that and a fractional part for faster processing

        let int_part = exponent.numer() / exponent.denom();
        //dbg!(&int_part);
        let frac_part = exponent.fract().trimed(p_less);
        //dbg!(&frac_part.to_string_decimal());
        let this_is_neg = self.value < 0.0;

        // if there are no real roots (can't take an even root of a negative number)
        if this_is_neg && frac_part.denom() % &Natural::from(2u8) == 0u8 {
            return Err(format!(
                "Can't take an even root of {} because it is negative",
                self.to_string_decimal(20)
            ));
        }

        // if the fraction is negative
        if this_is_neg {
            //return -(-x) ^ n
            return Ok(-(-self.clone()).pow_frac(exponent, precision)?);
        }

        // main calculation
        // fractional powers = the denominator-th root of the number to the power of the numerator (or reversed)
        // x ^ (a/b) = ((x ^ a) ^ (1/b))   or
        // x ^ (a/b) = bth_root(x) ^ a
        let int_part = self.pow_nat(&int_part, precision)?;
        //dbg!(&int_part.to_string_decimal());
        let frac_part = self
            .nth_root(&Fraction::from(frac_part.denom()), precision)?
            .pow_nat(frac_part.numer(), precision)?;
        //dbg!(&frac_part.to_string_decimal());
        Ok(int_part.multiply(&frac_part).trimed(precision))
    }

    /// Takes the arbitrary-base log of a Fraction. <br>
    /// Uses x = e^(Ln(x)/n).
    pub fn log(&self, base: &Fraction, precision: u32) -> Result<Fraction, String> {
        Ok(self
            .ln(precision)?
            .divide(&base.ln(precision)?)
            .trimed(precision))
    }

    /// Gets the factorial of an integer in Fraction form.
    pub fn factorial(&self) -> Result<Fraction, String> {
        if self.value < 0.0 {
            return Err(format!(
                "Can't take the factorial of {}",
                self.to_string_decimal(20)
            ));
        }
        if self.denom() != &Natural::from(1u8) {
            return Err(format!(
                "Can't take the factorial of {} because it is not an integer",
                self.to_string_decimal(20)
            ));
        }
        let mut result = Fraction::from(1);
        let mut i = Fraction::from(1);
        while i <= *self {
            result.mul_assign(&i);
            i.add_assign(&Fraction::from(1));
        }
        Ok(result)
    }

    /// Trims a fraction to a certain number of digits (where the min(numer, denom) becomes that number of digits long).
    #[inline]
    fn trim(&mut self, trim_to: u32) {
        // get the number of decimal digits in the numerator and denominator
        let numer_len = num_decimal_digits(self.numer());
        let denom_len = num_decimal_digits(self.denom());
        // if both are larger than the desired number of digits, scale both down
        if numer_len > trim_to && denom_len > trim_to {
            //determine the amount to scale down by
            let scaler = numer_len.min(denom_len) - trim_to;
            //scale both down by the same amount
            self.value.mutate_numerator_and_denominator(|x, y| {
                x.div_assign(&Natural::from(10u8).pow(scaler as u64));
                y.div_assign(&Natural::from(10u8).pow(scaler as u64));
            });
        }
    }

    /// Returns a new fraction that is the same as the original but trimmed to a certain number of digits (where the min(numer, denom) becomes that number of digits long).
    fn trimed(&self, trim_to: u32) -> Fraction {
        let mut new = self.clone();
        new.trim(trim_to);
        new
    }

    /// Rounds a Fraction in-place if it's extremely close to the next integer that's not 0.
    pub fn round_if_close(&mut self) {
        if self.trunc().value == 0.0 {
            return;
        }
        let distance = Fraction::parse_decimal("0.00000000000000000000000001").unwrap();
        let frac_part = self.fract();
        // if the fraction is less than the distance from the nearest integer
        if frac_part < distance || frac_part > (Fraction::from(1) - distance) {
            self.value = self.round().value;
        }
    }

    /// Returns a new Fraction that is the same as the original but rounded if it's extremely close to the next integer that's not 0.
    pub fn rounded_if_close(&self) -> Fraction {
        let mut new = self.clone();
        new.round_if_close();
        new
    }

    /// Returns a string representation of the fraction in decimal form.
    pub fn to_string_decimal(&self, precision: u32) -> String {
        let mut options = ToSciOptions::default();
        options.set_size_complete();
        if self.value.fmt_sci_valid(options) {
            self.value.to_sci_with_options(options).to_string()
        } else {
            let mut res = String::new();
            if self < &Fraction::from(0) {
                res += "-";
            }
            res += &self.trunc().numer().to_string();
            options = ToSciOptions::default();
            options.set_precision(precision as u64);
            if !self.value.fmt_sci_valid(options) {
                options.set_precision(50);
            }
            if self.value.fmt_sci_valid(options) {
                res.push_str(
                    &self
                        .fract()
                        .abs()
                        .value
                        .to_sci_with_options(options)
                        .to_string()[1..],
                );
            } else {
                // if it's still not valid, use mixed number notation
                return self.to_string_mixed(precision);
            }
            res
        }
    }

    /// Returns a string representation of the fraction in mixed number form.
    pub fn to_string_mixed(&self, precision: u32) -> String {
        let mut res = String::new();
        if self < &Fraction::from(0) {
            res += "-";
        }
        res += &self.trunc().numer().to_string();
        res.push_str(" ");
        res += &self.fract().abs().trimed(precision).to_string();
        res
    }

    /// Returns a string representation of the fraction in scientific notation.
    pub fn to_string_scientific(&self, precision: u32) -> String {
        // the difference from to_string_decimal is that it will always use scientific notation to 50 decimal places
        let mut options = ToSciOptions::default();
        options.set_precision(precision as u64);
        if self.value.fmt_sci_valid(options) {
            return self.value.to_sci_with_options(options).to_string();
        }
        options.set_precision(50);
        if self.value.fmt_sci_valid(options) {
            self.value.to_sci_with_options(options).to_string()
        } else {
            // if it's still not valid, use mixed number notation
            self.to_string_mixed(precision)
        }
    }

    /// Returns a string representation of the fraction in fraction form.
    pub fn to_string_p(&self, precision: u32) -> String {
        format!("{}", self.trimed(precision).value)
    }
}

//FromStr trait implementation
impl FromStr for Fraction {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Fraction::parse(s).ok_or(())
    }
}
//from i64
impl From<i64> for Fraction {
    fn from(n: i64) -> Fraction {
        Fraction::new(n, 1)
    }
}
//from i32
impl From<i32> for Fraction {
    fn from(n: i32) -> Fraction {
        Fraction::new(n as i64, 1)
    }
}
//from u64
impl From<u64> for Fraction {
    fn from(n: u64) -> Fraction {
        Fraction::new(n as i64, 1)
    }
}
//from u32
impl From<u32> for Fraction {
    fn from(n: u32) -> Fraction {
        Fraction::new(n as i64, 1)
    }
}
//from Integer
impl From<&Integer> for Fraction {
    fn from(n: &Integer) -> Fraction {
        Fraction::new_from_big_ints(n, &Integer::from(1))
    }
}
//from Natural
impl From<&Natural> for Fraction {
    fn from(n: &Natural) -> Fraction {
        Fraction::new_from_big_ints(&Integer::from(n), &Integer::from(1))
    }
}
//from Rational
impl From<&Rational> for Fraction {
    fn from(n: &Rational) -> Fraction {
        Fraction { value: n.clone() }
    }
}

//operator overloading

//add
impl std::ops::Add for Fraction {
    type Output = Fraction;
    fn add(self, other: Fraction) -> Fraction {
        self.added_to(&other)
    }
}
impl std::ops::Add for &Fraction {
    type Output = Fraction;
    fn add(self, other: &Fraction) -> Fraction {
        self.added_to(other)
    }
}
impl std::ops::AddAssign for Fraction {
    fn add_assign(&mut self, other: Fraction) {
        *self = self.added_to(&other);
    }
}

//subtract
impl std::ops::Sub for Fraction {
    type Output = Fraction;
    fn sub(self, other: Fraction) -> Fraction {
        self.subtract(&other)
    }
}
impl std::ops::Sub for &Fraction {
    type Output = Fraction;
    fn sub(self, other: &Fraction) -> Fraction {
        self.subtract(other)
    }
}
impl std::ops::SubAssign for Fraction {
    fn sub_assign(&mut self, other: Fraction) {
        *self = self.subtract(&other);
    }
}

//multiply
impl std::ops::Mul for Fraction {
    type Output = Fraction;
    fn mul(self, other: Fraction) -> Fraction {
        self.multiply(&other)
    }
}
impl std::ops::Mul for &Fraction {
    type Output = Fraction;
    fn mul(self, other: &Fraction) -> Fraction {
        self.multiply(other)
    }
}
impl std::ops::MulAssign for Fraction {
    fn mul_assign(&mut self, other: Fraction) {
        self.value *= other.value;
    }
}

//divide
impl std::ops::Div for Fraction {
    type Output = Fraction;
    fn div(self, other: Fraction) -> Fraction {
        self.divide(&other)
    }
}
impl std::ops::Div for &Fraction {
    type Output = Fraction;
    fn div(self, other: &Fraction) -> Fraction {
        self.divide(other)
    }
}
impl std::ops::DivAssign for Fraction {
    fn div_assign(&mut self, other: Fraction) {
        self.value /= other.value;
    }
}

impl std::ops::Neg for Fraction {
    type Output = Fraction;
    fn neg(self) -> Fraction {
        Fraction::from(&(&self.value).neg())
    }
}
//negate by reference
impl std::ops::Neg for &Fraction {
    type Output = Fraction;
    fn neg(self) -> Fraction {
        Fraction::from(&(&self.value).neg())
    }
}
//std::fmt::Display
impl std::fmt::Display for Fraction {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// Gets the number of decimal digits in a number. <br>
/// Uses: number of decimal digits ~= floor( self.num_bytes * log(256) ) + 1
#[inline]
fn num_decimal_digits(num: &Natural) -> u32 {
    ((num.significant_bits() as f64 / 8.0) * 2.408_239_965_311_849_6 + 1.0) as u32
}

// old code

// fn e_sqrt() -> Fraction {
//     Fraction::parse_decimal("1.64872127070012814684865078781416357165377610071014801157507931164066102119421560863277652005636664300286663775630779700467116697521960915984097145249005979692942265909840391471994846465948924489686890533641846572084106665685980008892498121171228737521497219").unwrap()
// }

// fn log2_10() -> Fraction {
//     Fraction::parse_decimal("3.32192809488736234787031942948939017586483139302458061205475639581593477660862521585013974335937015509965737171025025182682409698426352688827530277299865539385195135265750556864301760919002489166694143337401190312418737510971586646754017918965580673583077968").unwrap()
// }

// pub fn ln_attempt(&self) -> Result<Fraction, String> {
//     const precision: u32 = 500;
//     // if it's 0
//     if self.value == 0.0 {
//         return Err("Can't take the ln of 0".to_string());
//     }
//     // if it's 1
//     else if self.value == 1.0 {
//         //return 0
//         return Ok(Fraction::from(0));
//     }
//     // if it's negative, recurse
//     else if self.value < 0.0 {
//         return Ok(-(self.abs().ln()?));
//     }

//     let mut frac = self.clone();
//     // scaling factors
//     let scale_big: Fraction = if self.value > 1.0 {
//         let int_power = (num_decimal_digits(frac.trunc().numer()) - 1) as u64;
//         frac = frac.divide(&Fraction::from(&Integer::from(10).pow(int_power)));
//         Fraction::from(int_power as i64)
//             .multiply(&Fraction::ln2())
//             .multiply(&Fraction::log2_10())
//     } else {
//         Fraction::from(0)
//     };
//     // scale frac between 1 and e^(1/2)
//     let mut scale_small = 0;
//     while frac > Fraction::e_sqrt() {
//         frac.div_assign(&Fraction::e_sqrt());
//         scale_small += 1;
//     }

//     const MAX_LOOP_TIMES: i64 = 500;
//     let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
//         &Integer::from(1),
//         &Integer::from(PRECISION).pow(PRECISION as u64 / 10),
//     );

//     let mut sum = frac.clone();
//     let mut last_term = frac.clone();
//     for i in 0..MAX_LOOP_TIMES {
//         let this_term = last_term.multiply(
//             &Fraction::from(i)
//                 .multiply(&Fraction::from(1).subtract(&frac))
//                 .divide(&Fraction::from(i + 1)),
//         );

//         sum = sum.added_to(&this_term);

//         if this_term < STOP_AFTER {
//             break;
//         }
//         println!("{}: {}", i, this_term.to_string_decimal());
//         last_term = this_term;
//         sum.trim(PRECISION);
//     }
//     Ok(sum
//         .added_to(&scale_big)
//         .added_to(&Fraction::from(scale_small).divide(&Fraction::from(2)))
//         .trimed(PRECISION))
// }

// fn trim_old(&mut self, trim_to: i32) {
//     //print!("Fraction before trim: {:?}", self);
//     //if the fraction is negative
//     let is_neg = self.numer() < &Integer::from(0);
//     //get the numerator and denominator
//     let mut numer = self.numer().abs().to_string();
//     let mut denom = self.denom().to_string();
//     if numer.len() > trim_to as usize && denom.len() > trim_to as usize {
//         let scaler = numer.clone().len().min(denom.clone().len()) - trim_to as usize;
//         //trim the difference off the back of both the numerator and denominator
//         numer = numer[0..numer.len() - scaler].to_string();
//         denom = denom[0..denom.len() - scaler].to_string();
//     } else {
//         return;
//     }
//     //set the numerator and denominator
//     self.value = Rational::new(
//         Integer::from_str(&((if is_neg { "-" } else { "" }).to_string() + &numer)).unwrap(),
//         Integer::from_str(&denom).unwrap(),
//     );
//     //println!("Fraction after trim: {:?}", self);
// }

// fn trimed_old(&self, trim_to: i32) -> Fraction {
//     let mut new = self.clone();
//     new.trim_old(trim_to);
//     new
// }

//for exp function
//break into smaller chunks using power rules
// if self > &Fraction::from(150) {
//     let divisor =
//         i64::try_from(self.divide(&Fraction::from(150)).trunc().numer()).unwrap() + 1;
//     //return (e ^ (x / divisor))^divisor
//     // println!(
//     //     "scaled for exp: {}",
//     //     self.divide(&Fraction::new(divisor, 1))
//     // );
//     return (self.divide(&Fraction::new(divisor, 1)).exp()).pow(&Integer::from(divisor));
//     //return self.divide(&Fraction::from(2)).exp().pow(&Integer::from(2));
// }
