# Rust CLI calculator

An arbitrary-precision scientific calculator written in Rust, can parse complex math expressions and handle operations such as rational exponents, logarithms, and trigonometric functions. Users can declare custom functions and variables and work with a basic matrix implementation.
Examples of supported expressions:
- "f(x) = 2x^3 - 4x^(2/3) + 2.6x - 8" (declares a function f that can be called later)
- "det( [1,2,3; 4,5,6; 7,8,9] )" (gets the determinant of the given matrix)
- "e^5000000" (prints: 2.5675343297838180005005330297099321__E2171472__)

Meant to somewhat compete with the speed and accuracy of the Windows calculator, while taking a lot of the technical stuff from it.

Also helped solidify my parsing knowledge and my first time doing unit testing.
