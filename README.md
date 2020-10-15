# calc
This is an infix calculator programmed in D. It uses [pegged](https://github.com/PhilippeSigaud/Pegged/) for expression parsing and the [arsd](https://github.com/adamdruppe/arsd) terminal module for input.
Currently support for:
* double-precision values
* complex numbers
* addition, subtraction, multiplication, division, exponentiation
* unary negation
* implied multiplication and parentheses
* builtin functions: sin, cos, tan, asin, acos, atan, abs, sqrt, log, log2, log10
* builtin constant pi
* variables can be defined and used
* terminal input can be navigated with arrow keys
