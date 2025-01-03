use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;
use std::sync::OnceLock;

use malachite::num::arithmetic::traits::{Abs, Ceiling, Floor, Mod, Pow, Reciprocal};
use malachite::num::conversion::string::options::ToSciOptions;
use malachite::num::conversion::traits::ToSci;
use malachite::num::logic::traits::SignificantBits;

use malachite::{self, Integer, Natural, Rational};

//TODO: make "num!" macro

static INT_ONE: Integer = Integer::const_from_signed(1i64);
static INT_TWO: Integer = Integer::const_from_signed(2i64);
static FRAC_ONE: Fraction = Fraction::const_new(Rational::const_from_signed(1i64));
static FRAC_TWO: Fraction = Fraction::const_new(Rational::const_from_signed(2i64));

//wrapper
#[derive(PartialEq, Eq, PartialOrd, Debug, Clone, Hash, Ord)]
pub struct Fraction {
    value: Rational,
}

impl Fraction {
    #[inline(always)]
    /// The constant pi.
    pub fn pi() -> &'static Fraction {
        // Fraction::parse_decimal(
        //     "3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566"
        // ).unwrap()

        static PI: OnceLock<Fraction> = OnceLock::new();
        PI.get_or_init(|| {
        Fraction {
            value: Rational::from_naturals(
            Natural::from_limbs_asc(&[16015526629650925843, 3937736330497040659, 1060430482972443683, 10399108037880605619, 8722342527738386168, 12348386842194014499, 10456888439762154316, 6123312802475432784, 14473133155955814955, 3316851539658346146, 4008975686485604611, 13665342900331867789, 7367028535400513886, 10468695547307308229, 2523222716210950042, 14739891572339476236, 15103922911250320823, 12045249174508056803, 14932924909784619909, 14133008778476973700, 3030420747556997008, 9964611091800904359, 
                2367976803570382958, 1146080508054429785, 15454708050572990171, 1573771280965505516, 19151689505232501]), 
            Natural::from_limbs_asc(&[0, 0, 0, 0, 0, 0, 0, 0, 2947876186379141968, 17611692736084186179, 16707293993252985750, 18191887369100043212, 1010066148020621545, 13508309527881721771, 4120948427896168217, 5472735846129317792, 13926463604134851517, 14498716182408168085, 10592146117519359629, 16862044634572918105, 1854757136523561851, 781532325147078541, 5377723743440681581, 3403405907508723356, 11251568871083062745, 12898162146947153281, 6096172106637855])
            )
        }
        })
    }

    #[inline(always)]
    /// The natural logarithm of 10.
    pub fn ln10() -> &'static Fraction {
        // Fraction::parse_decimal(
        //     "2.3025850929940456840179914546843642076011014886287729760333279009675726096773524802359972050895982983419677840422862486334095254650828067566662873690987816894829072083255546808437998948262331985283935053089653777326288461633662222876982198867465436674744042432743651550489343149393914796194044002221051017141748003688084012647080685567743216228355220114804663715659121373450747856947683463616792101806445070648000277502684916746550586856935673420670581136429224554405758925724208241314695689016758940256776311356919292"
        // ).unwrap()
        static LN10: OnceLock<Fraction> = OnceLock::new();
        LN10.get_or_init(||
        Fraction{
            value: Rational::from_naturals(
            Natural::from_limbs_asc(&[6546201492431733631, 15167238648806427950, 7721200715290770806, 12989992052497708677, 17430463276391498161, 8775086792721659178, 5949444383504965489, 
                10501986357334362890, 15183387476595612190, 12374549391725404527, 1658246278310302591, 10447985775721052970, 7985866247887334149, 15794301743557623427, 14631767923104774157, 4178365717037319257, 6993080803111291073, 4067443610771871882, 2024493715143330430, 14456267422202451365, 4705301256809828273, 15445175022013487437, 17499162475290393377, 1877428196517740830, 3023116865352080502, 3204975913097886827, 7018477508535217]),
            Natural::from_limbs_asc(&[0, 0, 0, 0, 0, 0, 0, 0, 10697310130044346792, 8805846368042093089, 8353646996626492875, 18319315721404797414, 9728405110865086580, 15977526800795636693, 2060474213948084108, 11959739959919434704, 16186603838922201566, 16472730128058859850, 14519445095614455622, 17654394354141234860, 10150750605116556733, 9614138199428315078, 2688861871720340790, 10925074990609137486, 14849156472396307180, 15672453110328352448, 3048086053318927]),
            )
        })
    }

    #[inline(always)]
    /// The constant e.
    pub fn e() -> &'static Fraction {
        // Fraction::parse_decimal(
        //     "2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307381323286279434907632338298807531952510190115738341879307021540891499348841675092447614606680822648001684774118537423454424371075390777449920695517027618386062613313845830007520449338265602976067371132007093287091274437470472306969772093101416928368190255151086574637721112523897844250569536967707854499699679468644549059879316368892300987931277361782154249992"
        // ).unwrap()
        static E: OnceLock<Fraction> = OnceLock::new();
        E.get_or_init(||
        Fraction {
            value: Rational::from_naturals(
            Natural::from_limbs_asc(&[11155792792291367137, 14843241099458555859, 9742054270963091109, 18428450497896879634, 681035353230862522, 14722925718561622299, 18207354264394167359, 14946518255153698470, 10783921601857590754, 7588981783146609963, 6696430093574571002, 8817351515305176225, 16863360264972537834, 16585578783233878458, 618057755987732159, 1589857981829012990, 14936706098823532224, 5425205516425713948, 9421205131929569441, 11389270005369564276, 16054835044392251151, 4220083976976521050, 15484145799462589151, 16154542886189831893, 6969920245932685420, 385256868788853586, 4142778465158145]),
            Natural::from_limbs_asc(&[0, 0, 0, 0, 0, 0, 0, 0, 14572027101876949204, 13626295220875822352, 4176823498313246437, 9159657860702398707, 14087574592287319098, 7988763400397818346, 1030237106974042054, 5979869979959717352, 8093301919461100783, 8236365064029429925, 7259722547807227811, 18050569213925393238, 5075375302558278366, 4807069099714157539, 1344430935860170395, 5462537495304568743, 7424578236198153590, 17059598592018952032, 1524043026659463])
            )
        })
    }

    //new
    pub fn new(numerator: i64, denominator: i64) -> Fraction {
        Fraction {
            value: Rational::from_integers(Integer::from(numerator), Integer::from(denominator)),
        }
    }

    pub const fn const_new(frac: Rational) -> Fraction {
        Fraction { value: frac }
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

    /// Parses a string in any (non-scientific) form
    pub fn parse(s: &str) -> Option<Fraction> {
        if s.contains('.') {
            return Fraction::parse_decimal(s);
        }
        match Rational::from_str(s) {
            Ok(r) => Some(Fraction { value: r }),
            Err(_) => None,
        }
    }

    /// Parses a string in decimal form
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
            // get the numerator (the number without the decimal point)
            let numerator = Integer::from_str(&s.replace('.', "")).unwrap();
            // get the denominator (10^number of places after the decimal)
            let denominator = Integer::from(10).pow(digits_after_decimal as u64);
            // return the fraction (it is automatically simplified)
            Some(Fraction::new_from_big_ints(&numerator, &denominator))
        } else {
            // if there is no decimal point
            // get the numerator
            let numerator = Integer::from_str(s).unwrap();
            // get the denominator
            let denominator = &INT_ONE;
            // return the fraction
            Some(Fraction::new_from_big_ints(&numerator, &denominator))
        }
    }

    pub fn zero() -> Fraction {
        Fraction {
            value: Rational::from(0),
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

    /// Negates a fraction
    pub fn negate(&self) -> Fraction {
        Fraction {
            value: -(&self.value),
        }
    }

    /// Clones a fraction
    pub fn clone(&self) -> Fraction {
        Fraction {
            value: self.value.clone(),
        }
    }

    /// Numerator
    pub fn numer(&self) -> &Natural {
        self.value.numerator_ref()
    }

    /// Denominator
    pub fn denom(&self) -> &Natural {
        self.value.denominator_ref()
    }

    /// Gets the integer part of a Fraction
    pub fn trunc(&self) -> Fraction {
        Fraction {
            value: if self > &Fraction::zero() {
                (&self.value).floor().into()
            } else {
                (&self.value).ceiling().into()
            },
        }
    }

    /// Gets the fractional part of a Fraction
    pub fn fract(&self) -> Fraction {
        let is_neg = self.value < 0.0;
        Fraction {
            value: Rational::from_naturals_ref(&(self.numer().mod_op(self.denom())), self.denom()),
        }
        .multiply(&Fraction::from(if is_neg { -1 } else { 1 }))
    }

    /// Rounds towards negative infinity
    pub fn floor(&self) -> Fraction {
        Fraction {
            value: (&self.value).floor().into(),
        }
    }

    /// Rounds towards positive infinity
    pub fn ceil(&self) -> Fraction {
        Fraction {
            value: (&self.value).ceiling().into(),
        }
    }

    /// Rounds to the nearest integer
    pub fn round(&self) -> Fraction {
        //to round a number, we add 0.5 and then truncate
        let sign = if self.value < 0.0 { -1 } else { 1 };
        self.abs()
            .added_to(&Fraction::parse("0.5").unwrap())
            .multiply(&Fraction::from(sign))
            .trunc()
    }

    /// Rounds to the provided decimal place
    pub fn round_to_decimal(&self, place: &Fraction) -> Result<Fraction, String> {
        if place.value < 0 {
            return Err(format!("Cannot round to a negative decimal place: {}", place.to_string_decimal(10)));
        } else if place.denom() != &Natural::from(1u8) {
            return Err(format!("Cannot round to a non-integer decimal place: {}", place.to_string_decimal(10)));
        }
        let factor = Fraction::from(10u32).pow_frac(place, 10).unwrap();
        let rounded = (self.multiply(&factor)).round();
        Ok(rounded.divide(&factor))
    }

    /// Gets the absolute value of a Fraction
    pub fn abs(&self) -> Fraction {
        Fraction {
            value: (&self.value).abs(),
        }
    }

    /// Gets the reciprocal of a Fraction
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
            return Ok(FRAC_ONE.clone());
        }
        // if it's negative
        if self.value < 0.0 {
            //return 1 / (e ^ -x)
            return Ok(FRAC_ONE.divide(&self.negate().exp(precision)?));
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
        if scaled == Fraction::zero() {
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
            &INT_ONE,
            &Integer::from(precision).pow(precision as u64 / 10),
        );

        // initialize the last term and the sum
        let mut last_term = self.trimed(precision);
        let mut sum = FRAC_ONE.added_to(&last_term);

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
            return Ok(Fraction::zero());
        }
        // if it's negative, recurse
        else if self.value < 0.0 {
            //return -ln(-x)
            return Ok(self.negate().ln(precision)?.negate());
        }
        // if it's less than 1, recurse; required to keep accuracy high
        else if self.value < 1.0 {
            //return -ln(1/x)
            return Ok(self.recip().ln(precision)?.negate());
        }

        // break frac into a * 10^b or do Ln(a) + b * Ln(10) where b is the power of 10 to get a < ln10
        let mut frac = self.clone();
        let mut b = 0;
        if frac > *Fraction::ln10() {
            b = num_decimal_digits(frac.trunc().numer()) as i64 - 2;
            if b < 0 {
                b = 0;
            }
            frac.div_assign(&Fraction::from(&Integer::from(10).pow(b as u64)));
        }
        frac.trim(precision);

        const MAX_LOOP_TIMES: u32 = 500;
        let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
            &INT_ONE,
            &Integer::from(precision).pow(precision as u64 / 10),
        );

        // calculate the value of (frac - 1) / (frac + 1)
        let num_1_less_over_1_more = ((frac.clone().subtract(&FRAC_ONE))
            / (frac.clone().added_to(&FRAC_ONE)))
        .trimed(precision);

        // initialize the sum to 0
        let mut sum = Fraction::zero();

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
        let result = (sum.multiply(&FRAC_TWO)).added_to(&Fraction::from(b).multiply(&Fraction::ln10()));

        Ok(result.trimed(precision))
    }

    /// Takes the arbitrary-base log of a Fraction. <br>
    /// Uses x = e^(Ln(x)/n).
    pub fn log(&self, base: &Fraction, precision: u32) -> Result<Fraction, String> {
        Ok(
            self
            .ln(precision)?
            .divide(&base.ln(precision)?)
            .trimed(precision)
        )
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
        let pi2 = &Fraction::pi().multiply(&FRAC_TWO);

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
            &INT_ONE,
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
                    &(-scaled.clone().pow(&INT_TWO, precision)?)
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
        Ok((self.added_to(&Fraction::pi().divide(&FRAC_TWO))).sin(precision)?)
    }

    /// Gets the tangent of a Fraction. <br>
    /// Uses sine and cosine.
    pub fn tan(&self, precision: u32) -> Result<Fraction, String> {
        Ok(self.sin(precision)?.divide(&self.cos(precision)?))
    }

    /// Gets the arctangent of a Fraction <br>
    /// Uses taylor series from https://github.com/microsoft/calculator/blob/main/src/CalcManager/Ratpack/itrans.cpp
    //    n
    //   ___                                                   2
    //   \  ]                                            (2j)*X (-1^j)
    //    \   thisterm  ; where thisterm   = thisterm  * ---------
    //    /           j                 j+1          j   (2j+2)
    //   /__]
    //   j=0
    //
    //   thisterm  = X ;  and stop when thisterm < precision used.
    //           0                              n
    //
    //   If abs(x) > 0.9 then an alternate form is used
    //      atan(x) = 2 * atan((√(1 + x²) - 1) / x)
    //
    //   And if abs(x) > 1.0 then this form is used.
    //   pi/2 - atan(1/x)
    // Changed slightly from the microsoft implementation
    // https://en.wikipedia.org/wiki/Horner's_method
    pub fn atan(&self, precision: u32) -> Result<Fraction, String> {
        if self.value < 0.0 {
            return Ok(Self::atan(&self.negate(), precision)?.negate());
        }

        if self.value > 1 {
            return Ok(Self::pi()
                .divide(&FRAC_TWO)
                .subtract(&Self::atan(&self.recip(), precision)?));
        }

        if self.value > 0.9 {
            let x_squared = self.multiply(self).trimed(precision);
            let inner = x_squared.added_to(&FRAC_ONE).nth_root(&FRAC_TWO, precision)?
                .subtract(&FRAC_ONE)
                .divide(self);
            let res = Ok((&Self::atan(&inner, precision)?).multiply(&FRAC_TWO).trimed(precision));
            return res
        }

        const MAX_LOOP_TIMES: i64 = 500;
        let STOP_AFTER: Fraction = Self::new_from_big_ints(
            &INT_ONE,
            &Integer::from(10).pow(precision as u64 + 5),
        );

        let mut sum = Fraction::zero();
        let mut term = self.clone();

        for n in 1..=MAX_LOOP_TIMES {
            sum = sum.added_to(&term.divide(&Fraction::from(2 * n - 1)));
            term = term.negate().multiply(&self).multiply(self);
            term.trim(precision);
            sum.trim(precision);

            if term.abs() < STOP_AFTER {
                break;
            }
        }

        sum.trim(precision);

        Ok(sum)
    }

    /// Gets the arcsine of a Fraction
    /// uses asin(x) = 2atan(x/sqrt(1-x^2))
    pub fn asin(&self, precision: u32) -> Result<Fraction, String> {
        if self.abs() > FRAC_ONE {
            return Err("Absolute value of input to asin must be less than or equal to 1".to_string());
        }

        Ok(
            Self::atan(
                &self.divide(
                    &FRAC_ONE.subtract(&self.pow(&INT_TWO, precision)?).nth_root(&FRAC_TWO, precision)?), precision)?
            .multiply(&FRAC_TWO)
        )
    }

    /// Gets the arccosine of a Fraction
    /// uses acos(x) = pi/2 - asin(x)
    pub fn acos(&self, precision: u32) -> Result<Fraction, String> {
        if self.abs() > FRAC_ONE {
            return Err("Absolute value of input to acos must be less than or equal to 1".to_string());
        }

        Ok(
            Self::pi().divide(&FRAC_TWO).subtract(&self.asin(precision)?)
        )
    }

    /// Gets the hyperbolic sine of a Fraction
    /// uses sinh(x) = (e^x - e^-x) / 2
    pub fn sinh(&self, precision: u32) -> Result<Fraction, String> {
        Ok(
            (self.exp(precision)? - (-self).exp(precision)?) / FRAC_TWO.clone()
        )
    }

    /// Gets the hyperbolic cosine of a Fraction
    /// uses cosh(x) = (e^x + e^-x) / 2
    pub fn cosh(&self, precision: u32) -> Result<Fraction, String> {
        Ok(
            (self.exp(precision)? + (-self).exp(precision)?) / FRAC_TWO.clone()
        )
    }

    /// Gets the hyperbolic tangent of a Fraction
    /// uses tanh(x) = sinh(x) / cosh(x)
    pub fn tanh(&self, precision: u32) -> Result<Fraction, String> {
        let cosh = self.cosh(precision)?;
        if cosh == Fraction::zero() {
            return Err("Division by zero in tanh calculation".to_string())
        }
        
        Ok(
            self.sinh(precision)? / cosh
        )
    }

    /// Gets the inverse hyperbolic sine of a Fraction
    /// uses asinh(x) = ln(x + sqrt(x^2 + 1))
    pub fn asinh(&self, precision: u32) -> Result<Fraction, String> {
        Ok(
            (self.added_to(&(self.pow(&INT_TWO, precision)?.added_to(&FRAC_ONE)).nth_root(&FRAC_TWO, precision)?)).ln(precision)?
        )
    }

    /// Gets the inverse hyperbolic cosine of a Fraction
    /// uses acosh(x) = ln(x + sqrt(x^2 - 1))
    pub fn acosh(&self, precision: u32) -> Result<Fraction, String> {
        if *self < FRAC_ONE {
            return Err("Input to acosh must be greater than or equal to 1".to_string())
        }

        Ok(
            (self.clone() + (self.pow(&INT_TWO, precision)? - FRAC_ONE.clone()).nth_root(&FRAC_TWO, precision)?).ln(precision)?
        )
    }

    /// Gets the inverse hyperbolic tangent of a Fraction
    /// uses atanh(x) = (ln(1 + x) - ln(1 - x)) / 2
    pub fn atanh(&self, precision: u32) -> Result<Fraction, String> {
        if self.abs() >= FRAC_ONE {
            return Err("Absolute value of input to atanh must be less than 1".to_string())
        }

        Ok(
            ((FRAC_ONE.clone() + self.clone()) / (FRAC_ONE.clone() - self.clone())).ln(precision)? / FRAC_TWO.clone()
        )
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
        let mut result = FRAC_ONE.clone();
        let mut i = FRAC_ONE.clone();
        while i <= *self {
            result.mul_assign(&i);
            i.add_assign(&FRAC_ONE);
        }
        Ok(result)
    }

    /// Gets the gamma function of a Fraction. <br>
    /// Uses the taylor series from: https://github.com/microsoft/calculator/blob/main/src/CalcManager/Ratpack/fact.cpp
    //      n
    //     ___    2j
    //   n \  ]  A       1          A
    //  A   \   -----[ ---- - ---------------]
    //      /   (2j)!  n+2j   (n+2j+1)(2j+1)
    //     /__]
    //     j=0
    //
    //  It can be shown that the above series is within precision if A is chosen
    //  big enough.
    //                          A    n  precision
    //  Based on the relation ne  = A 10            A was chosen as
    //
    //             precision
    //  A = ln(Base         /n)+1
    //  A += n*ln(A)  This is close enough for precision > base and n < 1.5
    //
    //  self is n
    fn gamma(&self, mut precision: u32) -> Result<Fraction, String> {
        const BASE: u32 = 10u32;
        const LN_PRECISION: u32 = 100u32; // ln is expensive so we use a fixed lower precision; doesn't affect the result
        let original_precision = precision;

        // get A
        let mut a = Fraction::from(precision)
            .divide(self)
            .ln(LN_PRECISION)?
            .multiply(&Fraction::from(BASE))
            .added_to(&FRAC_ONE);
        a.add_assign(&self.multiply(&a.ln(LN_PRECISION)?));
        a.trim(precision);

        // bump precision by ln(exp(a)*pow(a,n+1.5)-ln(BASE));
        // using f64 because it's faster and we're truncating the result anyway
        let a_f64 = f64::from_str(&a.to_string_decimal(20)).unwrap();
        let bump = &a_f64.exp()
            * a_f64.powf(
                f64::from_str(&self.added_to(&Fraction::new(3, 2)).to_string_decimal(20)).unwrap(),
            )
            - f64::from(BASE).ln();
        precision += bump.trunc().abs() as u32;

        // set the stop conditions
        const MAX_LOOP_TIMES: u64 = 500;
        let STOP_AFTER = Fraction::from(BASE)
            .pow_frac(&Fraction::from(precision).negate(), precision)?
            .divide(&Fraction::from(BASE));

        // first term (when j is 0)
        let mut sum = self.recip() - &a / &(self + &FRAC_ONE);

        let a_pow_2 = &a.multiply(&a);
        let mut a_pow_j2 = a_pow_2.clone();
        let mut j2_fact = Natural::from(2u8);

        // loop until the sum converges
        for j in 1..MAX_LOOP_TIMES {
            let j2 = j * 2;
            let n_plus_2j = self.added_to(&Fraction::from(j2));

            // part1 = (a ^ (2 * j)) / ((2 * j)!)
            let part1 = (&a_pow_j2 / &Fraction::from(&j2_fact)).trimed(precision);
            // part2 = 1 / (n + 2 * j)
            let part2 = n_plus_2j.recip();
            // part3 = a / (n + 2 * j + 1) / (2 * j + 1)
            let part3 = a
                .divide(
                    &n_plus_2j
                        .added_to(&FRAC_ONE)
                        .multiply(&Fraction::from(j2 + 1)),
                )
                .trimed(precision);
            // term = part1 * (part2 - part3)
            let term = &part1.multiply(&part2.subtract(&part3));

            // add the term to the sum
            sum.add_assign(term);
            sum.trim(precision);

            // if the precision is reached, break
            if term.abs() < STOP_AFTER {
                break;
            }

            // set up for the next loop
            a_pow_j2.mul_assign(&a_pow_2);
            a_pow_j2.trim(precision);
            j2_fact *= Natural::from((j2 + 1) * (j2 + 2));
        }

        Ok(
            // pow_frac uses ln; the '* 2' is pretty arbitrary but required
            a.pow_frac(self, LN_PRECISION * 2)?
                .multiply(&sum)
                .trimed(original_precision),
        )
    }

    /// Gets the factorial of a Fraction. <br>
    /// Uses the gamma function.
    /// Takes on average 100ms for precision 500.
    pub fn fact_fraction(&self, precision: u32) -> Result<Fraction, String> {
        // if the fraction is negative
        if self.value < 0.0 {
            //return -gamma(-x)
            return Ok(-(-self.clone()).fact_fraction(precision)?);
        }
        // if it's an integer
        if self.denom() == &Natural::from(1u8) {
            //return x!
            return Ok(self.factorial()?);
        }

        // scale down
        // to the corresponding number between -1 and 0 that gives the same result
        // no idea how they figured out these specific loops
        let mut fact = FRAC_ONE.clone();
        let mut x = self.clone();
        while x.value > 0.0 {
            fact.mul_assign(&x);
            x.sub_assign(&FRAC_ONE);
        }
        while x.value < -1.0 {
            x.add_assign(&FRAC_ONE);
            fact.div_assign(&x);
        }

        //dbg!(&fact.to_string_decimal(precision));
        //dbg!(&x.to_string_decimal(precision));

        Ok(
            x
            .added_to(&FRAC_ONE)
            .gamma(precision)?
            .multiply(&fact)
            .trimed(precision)
        )
    }

    /// Takes a Fraction to an integer power.
    fn pow(&self, exponent: &Integer, precision: u32) -> Result<Fraction, String> {
        // if the exponent is 0 or 1
        if exponent == &0 {
            return Ok(FRAC_ONE.clone());
        } else if exponent == &INT_ONE {
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
        let mut result = FRAC_ONE.clone();

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
        }
        // if it's too large
        else {
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

    /// Takes one Fraction to the power of another Fraction.
    pub fn pow_frac(&self, exponent: &Fraction, precision: u32) -> Result<Fraction, String> {
        let p_less = precision / 5;

        if exponent.value == 0.0 {
            //return 1
            return Ok(FRAC_ONE.clone());
        }
        if self.value == 0.0 {
            //return 0
            return Ok(Fraction::zero());
        }
        if exponent.value < 0.0 {
            //return 1 / x ^ -n
            return Ok(self.pow_frac(&-exponent.clone(), precision)?.recip());
        }
        if self == Fraction::e() {
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
        // if self.trunc().value == 0.0 {
        //     return;
        // }
        let distance = Fraction::parse_decimal("0.0000000000000000000000001").unwrap();
        let frac_part = self.fract().abs();
        // if the fraction is less than the distance from the nearest integer
        if frac_part < distance || frac_part > (&FRAC_ONE - &distance) {
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
        // TODO: fix for very small numbers with low precision (where it uses scientific notation)
        let mut options = ToSciOptions::default();
        let mut res = String::new();
        
        if self.value < 0.0 {
            res.push('-');
        }
        res += &self.trunc().numer().to_string(); // the integer part
        options.set_precision(precision as u64);
        options.set_neg_exp_threshold(-(precision as i64));
        if !self.value.fmt_sci_valid(options) {
            options.set_precision(35); // fallback to 35
        }
        if self.value.fmt_sci_valid(options) {
            res.push_str( // the fractional part
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
        // add commas
        let parts: Vec<&str> = res.split('.').collect();
        let integer_part = parts[0];
        let decimal_part = parts.get(1).unwrap_or(&"");
        let is_negative = integer_part.starts_with("-");
        let integer_part = if is_negative { &integer_part[1..] } else { integer_part };
        let integer_with_commas = integer_part.chars().rev().enumerate().map(|(i, c)| {
            if i % 3 == 0 && i != 0 {
                format!(",{}", c)
            } else {
                c.to_string()
            }
        }).collect::<String>().chars().rev().collect::<String>();
        let integer_with_commas = if is_negative { format!("-{}", integer_with_commas) } else { integer_with_commas };
        res = if decimal_part.len() > 0 {format!("{}.{}", integer_with_commas, decimal_part)} else {integer_with_commas};
        res
    }

    /// Returns a string representation of the fraction in mixed number form.
    pub fn to_string_mixed(&self, precision: u32) -> String {
        let mut res = String::new();
        if self < &Fraction::zero() {
            res += "-";
        }
        res += &self.trunc().numer().to_string();
        res.push_str(" ");
        res += &self.fract().abs().trimed(precision).to_string();
        res
    }

    /// Returns a string representation of the fraction in scientific notation.
    pub fn to_string_scientific(&self, precision: u32) -> String {
        // the difference from to_string_decimal is that it will always use scientific notation
        let mut options = ToSciOptions::default();
        options.set_precision(precision as u64);
        options.set_neg_exp_threshold(-(precision as i64));
        options.set_e_uppercase();
        if self.value.fmt_sci_valid(options) {
            self.value.to_sci_with_options(options).to_string()
        } else {
            // if it's not valid, use mixed number notation
            self.to_string_mixed(precision)
        }
    }

    /// Returns a string representation of the fraction in fraction form.
    pub fn to_string_p(&self, precision: u32) -> String {
        format!("{}", self.trimed(precision).value)
    }
}

/// Gets the number of decimal digits in a number. <br>
/// Uses: number of decimal digits ~= floor( self.num_bytes * log(256) ) + 1
#[inline]
fn num_decimal_digits(num: &Natural) -> u32 {
    ((num.significant_bits() as f64 / 8.0) * 2.408_239_965_311_849_6 + 1.0) as u32
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
        Fraction::new_from_big_ints(n, &INT_ONE)
    }
}
impl From<Integer> for Fraction {
    fn from(n: Integer) -> Fraction {
        Fraction::new_from_big_ints(&n, &INT_ONE)
    }
}
//from Natural
impl From<&Natural> for Fraction {
    fn from(n: &Natural) -> Fraction {
        Fraction::new_from_big_ints(&Integer::from(n), &INT_ONE)
    }
}
impl From<Natural> for Fraction {
    fn from(n: Natural) -> Fraction {
        Fraction::new_from_big_ints(&Integer::from(&n), &INT_ONE)
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
//Sum
impl std::iter::Sum for Fraction {
    fn sum<I: Iterator<Item=Fraction>>(iter: I) -> Self {
        iter.fold(Fraction::zero(), std::ops::Add::add)
    }
}




// ==============================================================
// Matrices
// ==============================================================

#[derive(Clone, Debug, PartialEq)]
pub struct Matrix {
    rows: usize,
    cols: usize,
    data: Vec<Fraction>, 
}

impl Matrix {

    pub fn new(rows: usize, cols: usize) -> Matrix {
        Matrix {
            rows,
            cols,
            data: Vec::with_capacity(rows * cols),
        }
    }

    pub fn new_from_data(rows: usize, cols: usize, data: Vec<Fraction>) -> Result<Matrix, String> {
        if data.len() != rows * cols {
            return Err("Data size does not match matrix dimensions".to_string());
        }

        Ok(Matrix {
            rows,
            cols,
            data,
        })
    }
    
    // Create a new Matrix from a string
    pub fn new_from_str(s: &str) -> Result<Matrix, String> {
        let mut rows = Vec::new();
        let mut current_row = Vec::new();
        
        for c in s.chars() {
            if c == ';' {
                rows.push(current_row);
                current_row = Vec::new();
            } else if c == ',' {
                current_row.push(Fraction::zero()); 
            } else {
                let v = c.to_string().parse::<Fraction>().map_err(|_| "Invalid number")?;
                current_row.push(v);
            }
        }
        
        rows.push(current_row); // add final row
        
        Self::new_from_rows(rows)
    }

    pub fn new_from_rows(rows: Vec<Vec<Fraction>>) -> Result<Matrix, String> {
        let num_cols = rows[0].len();
        let num_rows = rows.len();
        for row in &rows {
            if row.len() != num_cols {
                return Err("Rows must have equal length".to_string());
            }
        }
        
        let mut data = Vec::new();
        for row in rows {
            data.extend(row.into_iter());
        }
        
        Ok(Matrix{ 
            rows: num_rows,
            cols: num_cols,
            data 
        })
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn cols(&self) -> usize {
        self.cols
    }

    pub fn size(&self) -> usize {
        self.rows * self.cols
    }

    // Add two matrices 
    pub fn add(&self, other: &Matrix) -> Result<Matrix, String> {
        if self.rows != other.rows || self.cols != other.cols {
            return Err("Matrices must have equal dimensions".to_string());
        }
        
        let mut data = Vec::with_capacity(self.data.len());
        for i in 0..self.data.len() {
            data.push(self.data[i].added_to(&other.data[i])); 
        }
        
        Ok(Matrix {
            rows: self.rows,
            cols: self.cols,
            data 
        })
    }

    // Subtract two matrices
    pub fn subtract(&self, other: &Matrix) -> Result<Matrix, String> {
        if self.rows != other.rows || self.cols != other.cols {
            return Err("Matrices must have equal dimensions".to_string());
        }
        
        let mut data = Vec::with_capacity(self.data.len());
        for i in 0..self.data.len() {
            data.push(self.data[i].subtract(&other.data[i])); 
        }
        
        Ok(Matrix {
            rows: self.rows,
            cols: self.cols,
            data 
        })
    }
    
    // Multiply two matrices 
    pub fn multiply(&self, other: &Matrix) -> Result<Matrix, String> {
        if self.cols != other.rows {
            return Err("Can not multiply matrices with incompatible dimensions".to_string());
        }
        
        let mut result = Matrix::zeros(self.rows, other.cols);
        
        for i in 0..self.rows {
            for j in 0..other.cols {
                result.data[i*other.cols + j] = self.multiply_row_column(i, j, other);
            }
        }
        
        Ok(result)
    }
    fn multiply_row_column(&self, row: usize, col: usize, other: &Matrix) -> Fraction {
        (0..self.cols).map(|k| self.data[row*self.cols + k].multiply(&other.data[k*other.cols + col]))
        .sum()
    }

    // Multiply matrix by a scalar
    pub fn scale(&self, k: &Fraction) -> Matrix {
        let mut data = self.data.clone();
        for v in &mut data {
            v.mul_assign(k);
        }
        
        Matrix {
            rows: self.rows,
            cols: self.cols,
            data
        }
    }

    // Apply a function to each element
    pub fn apply(&self, f: &dyn Fn(Fraction) -> Fraction) -> Matrix {
        let mut data = self.data.clone();
        for v in &mut data {
            *v = f(v.clone());
        }
        
        Matrix {
            rows: self.rows,
            cols: self.cols,
            data
        }
    }
    pub fn try_apply(&self, f: &dyn Fn(Fraction) -> Result<Fraction, String>) -> Result<Matrix, String> {
        let mut data = self.data.clone();
        for v in &mut data {
            *v = f(v.clone())?;
        }
        
        Ok(Matrix {
            rows: self.rows,
            cols: self.cols,
            data
        })
    }

    // Compute the mean of all elements in the matrix
    pub fn mean(&self) -> Result<Fraction, String> {
        let sum: Fraction = self.data.iter().cloned().sum();
        let count = Fraction::from((self.rows * self.cols) as i32);
        Ok(sum.divide(&count))
    }

    // Compute the median of all elements in the matrix
    pub fn median(&self) -> Result<Fraction, String> {
        let mut sorted_data = self.data.clone();
        sorted_data.sort();
        let mid = sorted_data.len() / 2;
        if sorted_data.len() % 2 == 0 {
            let median = (&sorted_data[mid - 1] + &sorted_data[mid]).divide(&Fraction::from(2));
            Ok(median)
        } else {
            Ok(sorted_data[mid].clone())
        }
    }

    // Compute the mode of all elements in the matrix
    pub fn mode(&self) -> Result<Fraction, String> {
        let mut occurrences = std::collections::HashMap::new();
        for value in &self.data {
            *occurrences.entry(value).or_insert(0) += 1;
        }
        let max_occurrences = occurrences.values().max().ok_or("No mode found")?.clone();
        let mode = occurrences
            .into_iter()
            .filter(|&(_, v)| v == max_occurrences)
            .map(|(k, _)| k)
            .next()
            .ok_or("No mode found")?
            .clone();
        Ok(mode)
    }

    // Compute the sum of all elements in the matrix
    pub fn sum(&self) -> Fraction {
        self.data.iter().cloned().sum()
    }

    // Compute the product of all elements in the matrix
    pub fn prod(&self) -> Fraction {
        self.data.iter().cloned().fold(Fraction::from(1), |acc, x| acc * x)
    }

    // Compute inverse using adjugate matrix divided by determinant
    pub fn inverse(&self) -> Result<Matrix, String> {
        let det = self.determinant()?;
        if det == Fraction::zero() {
            return Err("Matrix is not invertible".to_string());
        }
        
        let mut adjugate = Matrix::zeros(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                adjugate.data[j*self.cols + i] = self.cofactor(i, j)?; 
            }
        }
        
        Ok(adjugate.scale(&(&FRAC_ONE.divide(&det))))
    }

    // Compute cofactor recursively 
    pub fn cofactor(&self, row: usize, col: usize) -> Result<Fraction, String> {

        if self.rows != self.cols {
            return Err("Matrix must be square".to_string());
        }

        let sign: Fraction = if (row + col) % 2 == 0 { 
            1.into() 
        } else { 
            (-1).into() 
        };

        let minor = self.minor(row, col)?;
        Ok(sign * minor)
    }

    fn minor(&self, row: usize, col: usize) -> Result<Fraction, String> {

        if self.rows == 1 {
            return Ok(FRAC_ONE.clone());
        }

        let mut submatrix = Vec::new();

        for i in 0..self.rows {
            if i != row {
                let mut subrow = Vec::new();
                for j in 0..self.cols {
                    if j != col {
                        subrow.push(self.data[i * self.cols + j].clone()); 
                    }
                }
                submatrix.push(subrow);
            }
        }

        let submatrix = Matrix::new_from_rows(submatrix)?; 
        submatrix.determinant()
    }

    // Compute determinant recursively
    pub fn determinant(&self) -> Result<Fraction, String> {
        
        if self.rows == 1 {
            return Ok(self.data[0].clone());
        }

        let mut det = Fraction::zero();
        for i in 0..self.cols {
            let cofactor = self.cofactor(0, i)?;
            det.add_assign(&(&cofactor.multiply(&self.data[i])));
        }

        Ok(det)
    }

    // REF
    // TODO: doesn't work
    pub fn to_row_echelon_form(&mut self) {
        let mut pivot_row = 0;
    
        for pivot_col in 0..self.cols {
            if pivot_row >= self.rows {
                break;
            }
    
            let mut max_row = pivot_row;
            for r in (pivot_row + 1)..self.rows {
                if self.data[r * self.cols + pivot_col].abs() > self.data[max_row * self.cols + pivot_col].abs() {
                    max_row = r;
                }
            }
    
            if self.data[max_row * self.cols + pivot_col] == Fraction::zero() {
                continue;
            }
    
            self.swap_rows(pivot_row, max_row);
    
            let pivot = self.data[pivot_row * self.cols + pivot_col].clone();
    
            for r in (pivot_row + 1)..self.rows {
                let scale = self.data[r * self.cols + pivot_col].clone() / pivot.clone();
                for c in pivot_col..self.cols {
                    let temp = self.data[pivot_row * self.cols + c].clone() * scale.clone();
                    self.data[r * self.cols + c] -= temp;
                }
            }
    
            pivot_row += 1;
        }
    }
    fn swap_rows(&mut self, i: usize, j: usize) {
        for k in 0..self.cols {
            self.data.swap(i * self.cols + k, j * self.cols + k);
        }
    }

    pub fn row_echelon_form(&self) -> Matrix {
        let mut m = self.clone();
        m.to_row_echelon_form();
        m
    }

    

    fn zeros(rows: usize, cols: usize) -> Matrix {
        Matrix {
            rows,
            cols,
            data: vec![Fraction::zero(); rows*cols],
        }
    }


    pub fn to_string_fmt(&self, frac_format_func: fn(&Fraction, u32) -> String, precision: u32) -> String {
        let mut result = String::new();

        if self.rows() > 1 && self.cols() > 0 {
            result.push_str("\n");
        }

        let max_width = self.data.iter()
            .map(|fraction| frac_format_func(fraction, precision).len())
            .max()
            .unwrap_or(0);

        for i in 0..self.rows {
            for j in 0..self.cols {
                let fraction = &self.data[i * self.cols + j];
                result.push_str(&format!("{:>width$}", frac_format_func(fraction, precision), width = max_width));
                if j != self.cols - 1 {
                    result.push_str(" ");
                }
            }
            if i != self.rows - 1 {
                result.push_str("\n");
            }
        }

        result
    }

}

impl IntoIterator for Matrix {
    type Item = Fraction;
    type IntoIter = std::vec::IntoIter<Fraction>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}
impl std::ops::Index<[usize; 2]> for Matrix {
    type Output = Fraction;
    
    fn index(&self, index: [usize; 2]) -> &Self::Output {
        let row = index[0];
        let col = index[1];
        &self.data[row * self.cols + col]
    }
}
use std::fmt;

impl fmt::Display for Matrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_fmt(Fraction::to_string_decimal, 3))
    }
}



























// tests
#[cfg(test)]
mod tests {
    use super::Fraction;
    use malachite::Integer;
    use malachite::Natural;
    use malachite::Rational;

    // test utilites
    const TEST_PRECISION: u32 = 1000;
    const TEST_ACCURACY_MIN: u32 = 30;

    // if they are the same, return u32::MAX
    fn first_difference_between_strings(a: String, b: String) -> u32 {
        let mut i = 0;
        for (x, y) in a.chars().zip(b.chars()) {
            if x != y {
                return i;
            }
            i += 1;
        }
        u32::MAX
    }

    // tests

    #[test]
    fn test_new() {
        // 1/2
        let a = Fraction::new(1, 2);
        assert_eq!(a.value, Rational::from_signeds(1, 2));

        // -1/2
        let b = Fraction::new(1, -2);
        assert_eq!(b.value, Rational::from_signeds(-1, 2));

        // -1/2
        let c = Fraction::new(-1, 2);
        assert_eq!(c.value, Rational::from_signeds(-1, 2));

        // 1/2
        let d = Fraction::new(-1, -2);
        assert_eq!(d.value, Rational::from_signeds(1, 2));
    }

    #[test]
    fn test_new_from_big_ints() {
        // 1/2
        let a = Fraction::new_from_big_ints(&Integer::from(1), &Integer::from(2));
        assert_eq!(a.value, Rational::from_signeds(1, 2));

        // -1/2
        let b = Fraction::new_from_big_ints(&Integer::from(1), &Integer::from(-2));
        assert_eq!(b.value, Rational::from_signeds(-1, 2));

        // -1/2
        let c = Fraction::new_from_big_ints(&Integer::from(-1), &Integer::from(2));
        assert_eq!(c.value, Rational::from_signeds(-1, 2));

        // 1/2
        let d = Fraction::new_from_big_ints(&Integer::from(-1), &Integer::from(-2));
        assert_eq!(d.value, Rational::from_signeds(1, 2));
    }

    #[test]
    fn test_new_from_naturals() {
        // 1/2
        let a = Fraction::new_from_big_naturals(&Natural::from(1u32), &Natural::from(2u32));
        assert_eq!(a.value, Rational::from_signeds(1, 2));

        // 5/2
        let b = Fraction::new_from_big_naturals(&Natural::from(5u32), &Natural::from(2u32));
        assert_eq!(b.value, Rational::from_signeds(5, 2));
    }

    #[test]
    fn test_new_from_rational() {
        // 1
        let a = Fraction::from(&Rational::from(1));
        assert_eq!(a.value, Rational::from(1));

        // -1
        let b = Fraction::from(&Rational::from(-1));
        assert_eq!(b.value, Rational::from(-1));

        // 1/2
        let c = Fraction::from(&Rational::from_signeds(1, 2));
        assert_eq!(c.value, Rational::from_signeds(1, 2));

        // -1/2
        let d = Fraction::from(&Rational::from_signeds(-1, 2));
        assert_eq!(d.value, Rational::from_signeds(-1, 2));
    }

    #[test]
    fn test_parse() {
        // 1/2
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.value, Rational::from_signeds(1, 2));

        // -1/2
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(b.value, Rational::from_signeds(-1, 2));
    }

    #[test]
    fn test_parse_decimal() {
        // 0.5
        let a = Fraction::parse_decimal("0.5").unwrap();
        assert_eq!(a.value, Rational::from_signeds(1, 2));

        // -0.5
        let b = Fraction::parse_decimal("-0.5").unwrap();
        assert_eq!(b.value, Rational::from_signeds(-1, 2));

        // 2
        let c = Fraction::parse_decimal("2").unwrap();
        assert_eq!(c.value, Rational::from(2));

        // -2
        let d = Fraction::parse_decimal("-2").unwrap();
        assert_eq!(d.value, Rational::from(-2));
    }

    #[test]
    fn test_trunc() {
        // trunc(1/2) = 0
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.trunc().numer(), &Natural::from(0u32));

        // trunc(-1/2) = 0
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(b.trunc().numer(), &Natural::from(0u32));

        // trunc(3/2) = 1
        let c = Fraction::parse("3/2").unwrap();
        assert_eq!(c.trunc().numer(), &Natural::from(1u32));

        // trunc(-3/2) = -1
        let d = Fraction::parse("-3/2").unwrap();
        assert_eq!(
            Integer::from(d.trunc().numer()) * Integer::from(-1),
            Integer::from(-1)
        );
    }

    #[test]
    fn test_fract() {
        // fract(5/2) = 1/2
        let a = Fraction::parse("5/2").unwrap();
        assert_eq!(a.fract(), Fraction::parse("1/2").unwrap());

        // fract(-5/2) = -1/2
        let b = Fraction::parse("-5/2").unwrap();
        assert_eq!(b.fract(), Fraction::parse("-1/2").unwrap());

        // fract(1/2) = 1/2
        let c = Fraction::parse("1/2").unwrap();
        assert_eq!(c.fract(), Fraction::parse("1/2").unwrap());

        // fract(-1/2) = -1/2
        let d = Fraction::parse("-1/2").unwrap();
        assert_eq!(d.fract(), Fraction::parse("-1/2").unwrap());
    }

    #[test]
    fn test_floor() {
        // floor(1/2) = 0
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.floor().numer(), &Natural::from(0u32));

        // floor(-1/2) = -1
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(
            Integer::from(b.floor().numer()) * Integer::from(-1),
            Integer::from(-1)
        );

        // floor(3/2) = 1
        let c = Fraction::parse("3/2").unwrap();
        assert_eq!(c.floor().numer(), &Natural::from(1u32));

        // floor(-3/2) = -2
        let d = Fraction::parse("-3/2").unwrap();
        assert_eq!(
            Integer::from(d.floor().numer()) * Integer::from(-1),
            Integer::from(-2)
        );
    }

    #[test]
    fn test_ceil() {
        // ceil(1/2) = 1
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.ceil().numer(), &Natural::from(1u32));

        // ceil(-1/2) = 0
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(b.ceil().numer(), &Natural::from(0u32));

        // ceil(3/2) = 2
        let c = Fraction::parse("3/2").unwrap();
        assert_eq!(c.ceil().numer(), &Natural::from(2u32));

        // ceil(-3/2) = -1
        let d = Fraction::parse("-3/2").unwrap();
        assert_eq!(
            Integer::from(d.ceil().numer()) * Integer::from(-1),
            Integer::from(-1)
        );
    }

    #[test]
    fn test_round() {
        // round(1/2) = 1
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.round().numer(), &Natural::from(1u32));

        // round(-1/2) = -1
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(
            Integer::from(b.round().numer()) * Integer::from(-1),
            Integer::from(-1)
        );

        // round(3/2) = 2
        let c = Fraction::parse("3/2").unwrap();
        assert_eq!(c.round().numer(), &Natural::from(2u32));

        // round(-3/2) = -2
        let d = Fraction::parse("-3/2").unwrap();
        assert_eq!(
            Integer::from(d.round().numer()) * Integer::from(-1),
            Integer::from(-2)
        );
    }

    #[test]
    fn test_abs() {
        // abs(1/2) = 1/2
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.abs(), Fraction::parse("1/2").unwrap());

        // abs(-1/2) = 1/2
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(b.abs(), Fraction::parse("1/2").unwrap());
    }

    #[test]
    fn test_recip() {
        // recip(1/2) = 2/1
        let a = Fraction::parse("1/2").unwrap();
        assert_eq!(a.recip(), Fraction::parse("2/1").unwrap());

        // recip(-1/2) = -2/1
        let b = Fraction::parse("-1/2").unwrap();
        assert_eq!(b.recip(), Fraction::parse("-2/1").unwrap());
    }

    #[test]
    fn test_dif_strings() {
        assert_eq!(
            first_difference_between_strings("1234567890".to_string(), "1234567890".to_string()),
            u32::MAX
        );
        assert_eq!(
            first_difference_between_strings("1234567890".to_string(), "1234567891".to_string()),
            9
        );
    }

    #[test]
    fn test_exp() {
        // -exp(1/2) = 0.6065306597126334...
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(first_difference_between_strings(a.exp(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "0.6065306597126334236037995349911804534419181354871869556828921587350565194137484239986476115079894560264237897940395251765378080".to_string()) >= TEST_ACCURACY_MIN, true);

        // exp(3/2) = 1.6487212707001281...
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(first_difference_between_strings(b.exp(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "4.4816890703380648226020554601192758190057498683696670567726500827859366744667137729810538313824533913886163506518301957689627464".to_string()) >= TEST_ACCURACY_MIN, true);

        // exp(5) = 148.4131591025766...
        let c = Fraction::parse("5").unwrap();
        assert_eq!(first_difference_between_strings(c.exp(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "148.41315910257660342111558004055227962348766759387898904675284511091206482095857607968840945989902114129280827066632605290992623".to_string()) >= TEST_ACCURACY_MIN, true);
    }

    #[test]
    fn test_ln() {
        // -ln(1/2) = 0.6931471805599453...
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(first_difference_between_strings(a.ln(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186875420014810205706857336855202".to_string()) >= TEST_ACCURACY_MIN, true);

        // ln(3/2) = 0.4054651081081644...
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(first_difference_between_strings(b.ln(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "0.4054651081081643819780131154643491365719904234624941976140143241441006712489142512677524278173134012459685480453871800086824839".to_string()) >= TEST_ACCURACY_MIN, true);

        // ln(5) = 1.6094379124341003...
        let c = Fraction::parse("5").unwrap();
        assert_eq!(first_difference_between_strings(c.ln(TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "1.6094379124341003746007593332261876395256013542685177219126478914741789877076577646301338780931796107999663030217155628997240052".to_string()) >= TEST_ACCURACY_MIN, true);
    }

    #[test]
    fn test_log() {
        // -log10(1/2) = 0.3010299956639812...
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(first_difference_between_strings(a.log(&Fraction::from(10),TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "0.3010299956639811952137388947244930267681898814621085413104274611271081892744245094869272521181861720406844771914309953790947678".to_string()) >= TEST_ACCURACY_MIN, true);

        // log2(3/2) = 0.5849625007211561...
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(first_difference_between_strings(b.log(&Fraction::from(2),TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "0.5849625007211561814537389439478165087598144076924810604557526545410982277943585625222804749180882420909806624750591673437175524".to_string()) >= TEST_ACCURACY_MIN, true);

        // log0.5(5) = -2.3219280948873623...
        let c = Fraction::parse("5").unwrap();
        assert_eq!(first_difference_between_strings(c.log(&Fraction::new(1,2),TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), 
        "-2.3219280948873623478703194294893901758648313930245806120547563958159347766086252158501397433593701550996573717102502518268240".to_string()) >= TEST_ACCURACY_MIN, true);
    }

    #[test]
    fn test_pow_frac() {
        // (-1/2)^10 = 0.0009765625
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(
            (first_difference_between_strings(
                a.pow_frac(&Fraction::from(10), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "0.0009765625".to_string()
            ) >= TEST_ACCURACY_MIN),
            true
        );

        // (3/2)^2 = 2.25
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(
            first_difference_between_strings(
                b.pow_frac(&Fraction::from(2), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "2.25".to_string()
            ) >= TEST_ACCURACY_MIN,
            true
        );

        // (5)^(1/2) = 2.2360679774997897...
        let c = Fraction::parse("5").unwrap();
        assert_eq!(first_difference_between_strings(c.pow_frac(&Fraction::new(1,2),TEST_PRECISION).unwrap().to_string_decimal(TEST_PRECISION), "2.2360679774997896964091736687312762354406183596115257242708972454105209256378048994144144083787822749695081761507737835042532677".to_string()) >= TEST_ACCURACY_MIN, true);
    }

    #[test]
    fn test_pow() {
        // (-1/2)^10 = 0.0009765625
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(
            (first_difference_between_strings(
                a.pow(&Integer::from(10), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "0.0009765625".to_string()
            ) >= TEST_ACCURACY_MIN),
            true
        );

        // (3/2)^2 = 2.25
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(
            first_difference_between_strings(
                b.pow(&Integer::from(2), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "2.25".to_string()
            ) >= TEST_ACCURACY_MIN,
            true
        );

        // (5)^(-2) = 0.04
        let c = Fraction::parse("5").unwrap();
        assert_eq!(
            first_difference_between_strings(
                c.pow(&Integer::from(-2), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "0.04".to_string()
            ) >= TEST_ACCURACY_MIN,
            true
        );
    }

    #[test]
    fn test_nth_root() {
        // (-1/2)^(1/2) = -0.7071067811865475...
        let a = Fraction::parse("-1/2").unwrap();
        assert_eq!(
            (first_difference_between_strings(
                a.nth_root(&Fraction::from(2), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "-0.7071067811865475244008443621048490392848359376884740365883398689953662392310535194251937671638207863675069231154561485124624".to_string()
                    .to_string()
            ) <= TEST_ACCURACY_MIN),
            true
        );

        // (3/2)^(1/2) = 1.224744871391589...
        let b = Fraction::parse("3/2").unwrap();
        assert_eq!(
            first_difference_between_strings(
                b.nth_root(&Fraction::from(2), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "1.2247448713915890490986420373529456959829737403283350642163462836254801887286575132699297165523201174092973006133070945624294327".to_string()
            ) >= TEST_ACCURACY_MIN,
            true
        );

        // (5)^(3/5) = 2.626527804403767...
        let c = Fraction::parse("5").unwrap();
        assert_eq!(
            first_difference_between_strings(
                c.nth_root(&Fraction::new(5,3), TEST_PRECISION)
                    .unwrap()
                    .to_string_decimal(TEST_PRECISION),
                "2.6265278044037672364551312664964795821156628028108985300344363303869270378546021066316150651750738427353574321046405931908800517".to_string()
            ) >= TEST_ACCURACY_MIN,
            true
        );
    }
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
//         return Ok(Fraction::zero());
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
//         Fraction::zero()
//     };
//     // scale frac between 1 and e^(1/2)
//     let mut scale_small = 0;
//     while frac > Fraction::e_sqrt() {
//         frac.div_assign(&Fraction::e_sqrt());
//         scale_small += 1;
//     }

//     const MAX_LOOP_TIMES: i64 = 500;
//     let STOP_AFTER: Fraction = Fraction::new_from_big_ints(
//         &INT_ONE,
//         &Integer::from(PRECISION).pow(PRECISION as u64 / 10),
//     );

//     let mut sum = frac.clone();
//     let mut last_term = frac.clone();
//     for i in 0..MAX_LOOP_TIMES {
//         let this_term = last_term.multiply(
//             &Fraction::from(i)
//                 .multiply(&FRAC_ONE.subtract(&frac))
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
//         .added_to(&Fraction::from(scale_small).divide(&FRAC_TWO))
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
//     //return self.divide(&FRAC_TWO).exp().pow(&INT_TWO);
// }
