import std.stdio: writeln, readln, write, writefln;
import std.array: assocArray;
import std.algorithm.iteration: sum, fold, map;
import std.algorithm.searching: startsWith, endsWith, minElement;
import std.algorithm.sorting: sort;
import std.algorithm.comparison: min;
import std.conv: to;
import std.complex;
import std.math;
import std.format: format, formattedRead;
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
struct United { // i.e. with units...
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
		foreach (string unit, double exponent; repUnits(dimension)) {
			if (exponent > 0) {
				num ~= unit;
				if (exponent != 1) {
					num ~= "^" ~ to!string(exponent);
				}
				num ~= "*";
			} else if (exponent < 0) {
				denom ~= unit;
				if (exponent != -1) {
					denom ~= "^" ~ to!string(-exponent);
				}
				denom ~= "*";
			}
		}
		if (denom == "" && num == "") { // i.e. null dimension
			return nameEmpty ? "unit" : "";
		} else if (denom == "") {
			return num[0..$-1];
		} else if (num == "") {
			return "(" ~ denom[0..$-1] ~ ")^-1";
		} else {
			return num[0..$-1] ~ " / " ~ denom[0..$-1];
		}
	}
	Complex!double dispDless() {
		auto value = dless;
		foreach(string unit, double exponent; repUnits(dimension)) {
			if (unit in altCoeffs) {
				value /= altCoeffs[unit];
			}
		}
		return value;
	}
	string siPrefix() { // get the SI prefix, *or empty if it's dimensionless*
		if (dimension.length == 0) return ""; // otherwise 100*10 = 1k not 1000
		auto bestPrefix = "";
		auto bestValue = dispDless();
		auto bestExp = abs(log10(dispDless()));
		auto trueDless = dispDless();
		foreach(string pref, int exponent; siPrefixes) {
			auto val = dispDless()*United(Complex!double(10.0^^-exponent));
			if (log10(val).re < bestExp && log10(val).re >= 0) {
				bestPrefix = pref;
				bestValue = val;
				bestExp = abs(log10(val));
			}
		}
		return bestPrefix;
	}
	Complex!double siValue() { // the value for the prefix to be applied to
		auto usingPrefix = siPrefix();
		if (usingPrefix == "") return dispDless();
		foreach(string pref, int exponent; siPrefixes) {
			if (usingPrefix == pref) return dispDless()*United(Complex!double(10.0^^-exponent));
		}
		assert(0, "something went really wrong with siPrefix()");
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
			dbInfo = format!("Dimension: %s")(other.dimension);
			throw new Exception("Unable to raise to the power of non-dimensionless unit " ~ other.hrDimension() ~ ".");
		}
		auto finalDim = dimension.dup; 
		foreach(string unit, double exponent; finalDim) {
			if (other.dless.im) { // this should error for now?
				dbInfo = format!("Power: %g")(other.dless);
				throw new Exception("Unable to raise non-dimensionless quantity with units " ~ hrDimension() ~ " to a complex power.");
			}
			finalDim[unit] *= other.dless.re;
		}
		return United(dless ^^ other.dless, finalDim);
	}
	United opUnary(string op)() if (op == "-") {
		return United(-dless, dimension);
	}
	United usqrt() {
		return this ^^ United(Complex!double(0.5));
	}
}
United[string] variables; // user-defined
United[string] constants; // not user-defined
United function(United)[string] functs; // non-unary functions to come later also
bool dbEnabled = false; // whether debug mode enabled
string dbInfo = ""; // debug error info string
int[string] siPrefixes;
int numDecimals = 5;
bool noDimlessPrefs = true; // no dimensionless prefixes: 1000 -> 1000 not 1k, not implemented yet
double[string][string] altUnits; // derived or nonSI units
double[string] altCoeffs; // coefficients between the SI units and these
// the units here aren't true SI units because the base unit of mass is the gram, not the kilogram
double[string] repUnits(double[string] baseUnits) { // recursively replace base units with derived units
	double[string][] possible;
	possible ~= baseUnits;
	foreach (string altUnit, double[string] definition; altUnits) {
		int maxRepable = int.max;
		foreach(string baseUnit, double exponent; definition) {
			if (!(baseUnit in baseUnits)) {
				maxRepable = 0;
			} else {
				maxRepable = to!int(min(maxRepable, floor(baseUnits[baseUnit]/exponent)));
			}
		}
		if (maxRepable == int.max || maxRepable == 0) continue;
		double[string] newBaseUnits = baseUnits.dup;
		foreach(string baseUnit, double exponent; definition) {
			newBaseUnits[baseUnit] -= maxRepable*exponent;
			if (newBaseUnits[baseUnit] == 0) {
				newBaseUnits.remove(baseUnit);
			}
		}
		newBaseUnits[altUnit] = maxRepable;
		possible ~= repUnits(newBaseUnits);
	}
	possible.sort!((x, y) => sum(map!(abs)(x.byValue())) < sum(map!(abs)(y.byValue())));
	return possible.minElement!(a => a.length);
}
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
				foreach (string pref, int exponent; siPrefixes) { // scan si prefixes for matches
					foreach (string name, United value; constants) {
						if (pref ~ name == expr.matches[0]) {
							return value * United(Complex!double(10.0^^exponent));
						}
					}
				}
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
	siPrefixes["k"] = 3; // afaik d doesn't have aa initializers?
	siPrefixes["M"] = 6;
	siPrefixes["G"] = 9;
	siPrefixes["T"] = 12;
	siPrefixes["P"] = 15;
	siPrefixes["E"] = 18;
	siPrefixes["Z"] = 21;
	siPrefixes["Y"] = 24;
	siPrefixes["m"] = -3;
	siPrefixes["u"] = -6;
	siPrefixes["n"] = -9;
	siPrefixes["p"] = -12;
	siPrefixes["f"] = -15;
	siPrefixes["a"] = -18;
	siPrefixes["z"] = -21;
	siPrefixes["y"] = -24;
	altUnits["N"] = null;
	altUnits["N"]["g"] = 1;
	altUnits["N"]["m"] = 1;
	altUnits["N"]["s"] = -2;
	altCoeffs["N"] = 1000; // after all, a newton is a *kilo*gram meter per second squared
	altUnits["J"]["g"] = 1;
	altUnits["J"]["m"] = 2;
	altUnits["J"]["s"] = -2;
	altCoeffs["J"] = 1000;
	functs["sin"] = function United(United x) { return United(sin(x));};
	functs["cos"] = function United(United x) { return United(cos(x));};
	functs["tan"] = function United(United x) { return United(tan(x));};
	functs["asin"] = function United(United x) { return United(Complex!double(asin(x.re), x.im));};
	functs["acos"] = function United(United x) { return United(Complex!double(acos(x.re), x.im));};
	functs["atan"] = function United(United x) { return United(Complex!double(atan(x.re), x.im));};
	functs["abs"] = function United(United x) { return United(Complex!double(abs(x)), x.dimension);};
	functs["sqrt"] = function United(United x) { return x.usqrt();};
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
	constants["ohm"] = United(Complex!double(1), ["ohm": 1]);
	constants["henry"] = United(Complex!double(1), ["henry": 1]);
	constants["grav"] = United(Complex!double(-9.80655), ["m": 1, "s": -2]);
	auto terminal = Terminal(ConsoleOutputType.linear);
	while (true) {
		try {
			terminal.write("> ");
			auto inp = terminal.getline();
			if (inp == "ENABLE DEBUG") {
				dbEnabled = true;
				continue;
			}
			if (inp.startsWith("config: ") && inp.endsWith("decimals")) {
				inp.formattedRead!"config: %d decimals"(numDecimals);
				numDecimals++;
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
				terminal.writefln("=> %.*gi %s%s", numDecimals, result.siValue().im.quantize!(10)(-numDecimals), result.siPrefix(), result.hrDimension());
			} else if (approxEqual(result.im, 0)) {
				terminal.writefln("=> %.*g %s%s", numDecimals, result.siValue().re.quantize!(10)(-numDecimals), result.siPrefix(), result.hrDimension());
			} else {
				terminal.writefln("=> %.*g %s%s", numDecimals, result.siValue(), result.siPrefix(), result.hrDimension());
			}
			constants["ans"] = result;
			constants["_"] = result;
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

