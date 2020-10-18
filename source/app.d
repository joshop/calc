import std.stdio: writeln, readln, write, writefln;
import std.array: assocArray;
import std.algorithm.iteration: sum, fold, map;
import std.conv: to;
import std.complex: Complex, sin, cos, tan, abs, sqrt, exp, log, log10;
import std.math: asin, acos, atan, log2,  PI, E, approxEqual, quantize;
import std.format: format;
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
struct United { // i.e. with units... units being added now!!
	Complex!double dless; // the dimensionless part
	alias dless this; // hopefully won't get used much?
	double[string] dimension; // the dimension: key is the si unit symbol, value is the exponent of it (undefined is zero)
	this(Complex!double initDless, double[string] initDimension) {
		dless = initDless;
		dimension = initDimension;
	}
	this(Complex!double initDless) {
		dless = initDless;
		dimension = null;
	}
	string hrDimension(bool nameEmpty = false) { // human readable dimension information, nameEmpty = true means say "unit" for the empty unit
		string num, denom;
		foreach (string unit, double exponent; dimension) {
			if (exponent > 0) {
				num ~= unit;
				if (exponent != 1) {
					num ~= "^" ~ to!string(exponent);
				}
				num ~= " ";
			} else if (exponent < 0) {
				denom ~= unit;
				if (exponent != -1) {
					denom ~= "^" ~ to!string(-exponent);
				}
				denom ~= " ";
			}
		}
		if (denom == "" && num == "") { // i.e. null dimension
			return nameEmpty ? "unit" : "";
		} else if (denom == "") {
			return num[0..$-1];
		} else if (num == "") {
			return "1 / " ~ denom[0..$-1];
		} else {
			return num[0..$-1] ~ " / " ~ denom[0..$-1];
		}
	}
	United opBinary(string op)(United other) if (op == "+" || op == "-") { // case 1: unlike units error here
		if (dimension != other.dimension) {
			dbInfo = format!("Tried to %s units %s and %s")(op, dimension, other.dimension);
			throw new Exception("Operation " ~ op ~ " can't operate on units " ~ hrDimension(true) ~ " and " ~ other.hrDimension(true) ~ ".");
		}
		return United(mixin("dless" ~ op ~ "other.dless"), dimension);
	}
	United opBinary(string op)(United other) if (op == "*" || op == "/") { // case 2: units multiply or divide here
		double[string] finalDim = dimension.dup;
		foreach(string unit, double exponent; other.dimension) {
			if (unit in finalDim) {
				finalDim[unit] += op == "*" ? exponent : -exponent; // negate exponent in other for division
				if (finalDim[unit] == 0) {
					finalDim.remove(unit); // hrDimension can't handle ^0 so that needs to be removed
				}
			} else {
				finalDim[unit] = op == "*" ? exponent : -exponent;
			}
		}
		return United(mixin("dless" ~ op ~ "other.dless"), finalDim);
	}
	United opBinary(string op)(United other) if (op == "^^") { // case 3: error if exponent is not dimensionless
		if (other.dimension.length) { // is not dimensionless
			throw new Exception("Unable to raise to the power of non-dimensionless unit " ~ other.hrDimension() ~ ".");
		}
		auto finalDim = dimension.dup; 
		foreach(string unit, double exponent; finalDim) {
			if (other.dless.im) { // this should error for now?
				throw new Exception("Unable to raise non-dimensionless quantity with units " ~ hrDimension() ~ " to a complex power.");
			}
			finalDim[unit] *= other.dless.re;
		}
		return United(dless ^^ other.dless, finalDim);
	}
	United opUnary(string op)() if (op == "-") {
		return United(-dless, dimension);
	}
}
United[string] variables; // user-defined
United[string] constants; // not user-defined
United function(United)[string] functs; // non-unary functions to come later also
bool dbEnabled = false; // whether debug mode enabled
string dbInfo = ""; // debug error info string
United evaluate(ParseTree expr) { // recursively parse the tree
	switch(expr.name) {
		case "Expression":
			return evaluate(expr.children[0]);
		case "Expression.Start":
			if (expr.children.length == 2) {
				if (expr.children[0].matches[0] in constants) {
					dbInfo = format!("%s constant value: %g")(expr.children[0].matches[0], constants[expr.children[0].matches[0]]);
					throw new Exception(expr.children[0].matches[0] ~ " is a constant or unit.");
				}
				United result = evaluate(expr.children[1]);
				variables[expr.children[0].matches[0]] = result;
				return result;
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Add":
			return fold!((a, b) => a + b)(map!evaluate(expr.children));
		case "Expression.MulRep":
			if (expr.matches[0] == "+") {
				return evaluate(expr.children[0]);
			} else {
				return -evaluate(expr.children[0]);
			}
		case "Expression.Mul":
			return fold!((a, b) => a * b)(map!evaluate(expr.children));
		case "Expression.ExpRep":
			if (expr.matches[0] == "*") {
				return evaluate(expr.children[0]);
			} else {
				return United(Complex!double(1))/evaluate(expr.children[0]); 
			}
		case "Expression.Exp":
			return fold!((a, b) => a ^^ b)(map!evaluate(expr.children)); 
		case "Expression.NegRep":
			return evaluate(expr.children[0]);
		case "Expression.Neg":
			if (expr.matches[0] == "-") {
				return -evaluate(expr.children[0]);
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Atom":
			if (expr.children.length > 1) {
				return fold!((a, b) => a * b)(map!evaluate(expr.children));
			} else {
				return evaluate(expr.children[0]);
			}
		case "Expression.Variable":
			if (expr.matches[0] in variables) {
				return variables[expr.matches[0]];
			} else if (expr.matches[0] in constants) {
				return constants[expr.matches[0]];
			} else {
				dbInfo = format!("Variables declared: %s")(variables);
				throw new Exception("Variable " ~ expr.matches[0] ~ " not declared.");
			}
		case "Expression.Literal":
			return United(Complex!double(to!(double)(expr.matches[0])));
		case "Expression.Function":
			if (expr.matches[0] in functs) {
				return functs[expr.matches[0]](evaluate(expr.children[0]));
			} else if (expr.matches[0] in variables) {
				return variables[expr.matches[0]]*evaluate(expr.children[0]);
			} else if (expr.matches[0] in constants) {
				return constants[expr.matches[0]]*evaluate(expr.children[0]);
			} else {
				dbInfo = format!("Functions defined: %s")(functs);
				throw new Exception("Function " ~ expr.matches[0] ~ " not found.");
			}
		default:
			assert(0, "problems have arisen");
	}
}
void main() {
	functs["sin"] = function United(United x) { return United(sin(x));};
	functs["cos"] = function United(United x) { return United(cos(x));};
	functs["tan"] = function United(United x) { return United(tan(x));};
	functs["asin"] = function United(United x) { return United(Complex!double(asin(x.re), x.im));};
	functs["acos"] = function United(United x) { return United(Complex!double(acos(x.re), x.im));};
	functs["atan"] = function United(United x) { return United(Complex!double(atan(x.re), x.im));};
	functs["abs"] = function United(United x) { return United(Complex!double(abs(x)));};
	functs["sqrt"] = function United(United x) { return United(sqrt(x));};
	functs["log"] = function United(United x) { return United(log(x));};
	functs["log2"] = function United(United x) { return United(Complex!double(log2(x.re), x.im));};
	functs["log10"] = function United(United x) { return United(log10(x));};
	functs["_debug"] = function United(United x) { dbEnabled = x != 0; return x; }; // enable/disable debug function
	functs["exp"] = function United(United x) { return United(exp(x));};
	constants["pi"] = United(Complex!double(PI));
	constants["i"] = United(sqrt(Complex!double(-1))); // maybe add support for j?
	constants["e"] = United(Complex!double(E));
	constants["m"] = United(Complex!double(1), ["m": 1]);
	constants["s"] = United(Complex!double(1), ["s": 1]);
	constants["g"] = United(Complex!double(1), ["g": 1]);
	auto terminal = Terminal(ConsoleOutputType.linear);
	while (true) {
		try {
			terminal.write("> ");
			auto inp = terminal.getline();
			if (inp == "ENABLE DEBUG") {
				dbEnabled = true;
				continue;
			}
			auto tree = Expression(inp);
			if (dbEnabled) terminal.writeln(tree);
			if (!tree.successful || tree.end != tree.input.length) { // i.e. parsing error from pegged or not fully parsed
				dbInfo = format!("Expression: %s; parse ended at %d < %d")(tree.input, tree.end, tree.input.length);
				throw new Exception("Syntax error.");
			}
			auto result = evaluate(tree);
			if (dbEnabled) {
				terminal.writefln("=> Exact result: %g of units %s", result, result.dimension);
				terminal.writefln("=> Human-readable units: %s", result.hrDimension());
			}
			if (approxEqual(result.re, 0) && !approxEqual(result.im, 0)) {
				terminal.writefln("=> %.14gi %s", quantize!(10, -14)(result.im), result.hrDimension());
			} else if (approxEqual(result.im, 0)) {
				terminal.writefln("=> %.14g %s", quantize!(10, -14)(result.re), result.hrDimension());
			} else {
				terminal.writefln("=> %.14g %s", result, result.hrDimension());
			}
		} catch (UserInterruptionException) { // ctrl-c from Terminal
			break;
		} catch (Exception err) { // TODO: make my own type of exception
			if (dbEnabled) {
				terminal.writeln("DEBUG INFO for error: " ~ dbInfo);
			}
			terminal.writeln("Error: " ~ err.msg);
		}
	}
}

