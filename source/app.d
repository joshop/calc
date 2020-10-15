import std.stdio: writeln, readln, write, writefln;
import std.algorithm.iteration: sum, fold, map;
import std.conv: to;
import std.complex: Complex, sin, cos, abs, sqrt;
import std.math: tan, asin, acos, atan, log, log2, log10, PI, approxEqual, quantize;
import pegged.grammar;
import arsd.terminal;
mixin(grammar(`
Expression:
Start < (Variable '=')? Add
Add < Mul MulRep*
MulRep < ('+' / '-') Mul
Mul < Exp ExpRep*
ExpRep < ('*' / '/') Exp
Exp < Neg NegRep*
NegRep < '^' Neg
Neg < '-'? Atom
Atom < Function Atom* / Variable / Atom Atom+ / Literal / '(' Add ')'
Function < ~(identifier) '(' Add ')'
Literal <- ~([0-9]+ ('.' [0-9]+)*)
Variable <- ~(identifier)
`));
struct United {
	Complex!double dless;
	alias dless this;
}
United[string] variables;
United[string] constants;
United function(United)[string] functs;
bool dbEnabled = false;
United evaluate(ParseTree expr) {
	if (!expr.successful) {
		throw new Exception("Syntax error.");
	}
	switch(expr.name) {
		case "Expression":
			return evaluate(expr.children[0]);
		case "Expression.Start":
			if (expr.children.length == 2) {
				if (expr.children[0].matches[0] in constants) {
					throw new Exception(expr.children[0].matches[0] ~ " is a constant.");
				}
				United result = evaluate(expr.children[1]);
				variables[expr.children[0].matches[0]] = result;
				return result;
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Add":
			return United(fold!((a, b) => a + b)(map!evaluate(expr.children)));
		case "Expression.MulRep":
			if (expr.matches[0] == "+") {
				return evaluate(expr.children[0]);
			} else {
				return United(-evaluate(expr.children[0]));
			}
		case "Expression.Mul":
			return United(fold!((a, b) => a * b)(map!evaluate(expr.children)));
		case "Expression.ExpRep":
			if (expr.matches[0] == "*") {
				return evaluate(expr.children[0]);
			} else {
				return United(1/evaluate(expr.children[0]));
			}
		case "Expression.Exp":
			return United(fold!((a, b) => a ^^ b)(map!evaluate(expr.children)));
		case "Expression.NegRep":
			return evaluate(expr.children[0]);
		case "Expression.Neg":
			if (expr.matches[0] == "-") {
				return United(-evaluate(expr.children[0]));
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Atom":
			if (expr.children.length > 1) {
				return United(fold!((a, b) => a * b)(map!evaluate(expr.children)));
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Variable":
			if (expr.matches[0] in variables) {
				return variables[expr.matches[0]];
			} else if (expr.matches[0] in constants) {
				return constants[expr.matches[0]];
			} else {
				throw new Exception("Variable " ~ expr.matches[0] ~ " not declared.");
			}
		case "Expression.Literal":
			return United(Complex!double(to!(double)(expr.matches[0])));
		case "Expression.Function":
			if (expr.matches[0] in functs) {
				return functs[expr.matches[0]](evaluate(expr.children[0]));
			} else if (expr.matches[0] in variables) {
				return United(variables[expr.matches[0]]*evaluate(expr.children[0]));
			} else if (expr.matches[0] in constants) {
				return United(constants[expr.matches[0]]*evaluate(expr.children[0]));
			} else {
				throw new Exception("Function " ~ expr.matches[0] ~ " not found.");
			}
		default:
			assert(0, "problems have arisen");
	}
}
void main() {
	functs["sin"] = function United(United x) { return United(sin(x));};
	functs["cos"] = function United(United x) { return United(cos(x));};
	functs["tan"] = function United(United x) { return United(Complex!double(tan(x.re), x.im));};
	functs["asin"] = function United(United x) { return United(Complex!double(asin(x.re), x.im));};
	functs["acos"] = function United(United x) { return United(Complex!double(acos(x.re), x.im));};
	functs["atan"] = function United(United x) { return United(Complex!double(atan(x.re), x.im));};
	functs["abs"] = function United(United x) { return United(Complex!double(abs(x)));};
	functs["sqrt"] = function United(United x) { return United(sqrt(x));};
	functs["log"] = function United(United x) { return United(Complex!double(log(x.re), x.im));};
	functs["log2"] = function United(United x) { return United(Complex!double(log2(x.re), x.im));};
	functs["log10"] = function United(United x) { return United(Complex!double(log10(x.re), x.im));};
	functs["_debug"] = function United(United x) { dbEnabled = x != 0; return x; };
	constants["pi"] = United(Complex!double(PI));
	constants["i"] = United(sqrt(Complex!double(-1)));
	writeln("Executing program now");
	auto terminal = Terminal(ConsoleOutputType.linear);
	while (true) {
		try {
			terminal.write("> ");
			auto tree = Expression(terminal.getline());
			if (dbEnabled) terminal.writeln(tree);
			auto result = evaluate(tree);
			if (dbEnabled) {
				terminal.writefln("=> Exact result: %g", result);
			}
			if (approxEqual(result.re, 0) && !approxEqual(result.im, 0)) {
				terminal.writefln("=> %.14gi", quantize!(10, -14)(result.im));
			} else if (approxEqual(result.im, 0)) {
				terminal.writefln("=> %.14g", quantize!(10, -14)(result.re));
			} else {
				terminal.writefln("=> %.14g", result);
			}
		} catch (UserInterruptionException) {
			break;
		} catch (Exception err) {
			terminal.writeln("Error: " ~ err.msg);
		}
	}
}

