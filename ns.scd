(
// an ad-hoc, informally-specified, bug-ridden, slow implementation of half of Common Lisp.

/*
TODO: assoc / assv / assq TODO
TODO: (sc only) suspicion that slow ss_* functions has performance penalty - check by testing parsed statements in define_non_prim_standard_procedures
TODO: (sc only) for clarity, use .value() over .()
*/

/*

inspiration:
https://norvig.com/lispy.html
scheme r4rs @ https://people.csail.mit.edu/jaffer/r4rs_toc.html
TODO r4rs defines 146 essential procedures excluding additional car/cdr permutations

a few differences to r4rs:
no support for macros (macros are not required in r4rs)
no TCO yet
symbol case is significant
strings are immutable
quasiquote does not support nesting

*/

// TODO: turn on function inline hints!
/*
LanguageConfig.postInlineWarnings_(true);
*/

var
run_tests = {
	currentEnvironment['_NS_ENV'] = ();
	init_ns_environment.(currentEnvironment['_NS_ENV']);
	// run_rep_tests1();
	// run_rep_tests2();
	// run_rep_tests3();
	ss_test.();
	ss_as_string_test.();
	// read_test();
};

var
ss_test = {
	var s;
	s = ss_new.("This is an example string");
	assert_equal.( "This", ss_scan.(s, "\\w+") );
	assert_equal.( nil, ss_scan.(s, "\\w+") );
	assert_equal.( " ", ss_scan.(s, "\\s+") );
	assert_equal.( nil, ss_scan.(s, "\\s+") );
	assert_equal.( "is", ss_scan.(s, "\\w+") );
	assert_false.( ss_eos.(s) );

	assert_equal.( " ", ss_scan.(s, "\\s+") );
	assert_equal.( "an", ss_scan.(s, "\\w+") );
	assert_equal.( " ", ss_scan.(s, "\\s+") );
	assert_equal.( "example", ss_scan.(s, "\\w+") );
	assert_equal.( " ", ss_scan.(s, "\\s+") );
	assert_equal.( "string", ss_scan.(s, "\\w+") );
	assert_true.( ss_eos.(s) );

	assert_equal.( nil, ss_scan.(s, "\\w+") );
	assert_equal.( nil, ss_scan.(s, "\\s+") );
};

var
ss_as_string_test = {
	var abc = ss_new.("test string 42134");
	assert_equal.("StringScanner 0/17 @ \"test string 42134\"", ss_as_string.(abc));
	assert_equal.(4, ss_matches.(abc, "\\S+"));

	assert_equal.("StringScanner 0/17 @ \"test string 42134\"", ss_as_string.(abc));
	ss_skip.(abc, "\\S+");
	assert_equal.("StringScanner 4/17 \"test\" @ \" string 42134\"", ss_as_string.(abc));
};

/*
repl
*/

var
repl =
{
	var cmd_period_preprocessor_key = '*cmdperiod-is-preprocessor-toggle*';

	var enable_pre_processor = {
		// TODO var funcName = 'enable_pre_processor';
		this.preProcessor = { |code, interpreter| "e.val(\""++code.escapeChar($")++"\");" };
		"lisp preprocessor enabled!".inform;
	};

	var disable_pre_processor = {
		// TODO var funcName = 'disable_pre_processor';
		this.preProcessor = nil;
		"lisp preprocessor disabled".inform;
	};

	currentEnvironment['_NS_ENV'] = nil;
	init_ns_environment.value(currentEnvironment);

	e = e ? ();
	e['val'] = { |self, str, env| rep.value(str, env) };

	if (CmdPeriod.objects.includes(e.cmdPeriodHook)) {
		CmdPeriod.remove(e.cmdPeriodHook)
	};

	e['cmdPeriod'] = e['cmdPeriod'] ? {
		if (currentEnvironment[cmd_period_preprocessor_key].asBoolean) {
			if (this.preProcessor.notNil) {
				disable_pre_processor.value
			} {
				enable_pre_processor.value;
			};
		};
	};
	CmdPeriod.add(e['cmdPeriod']);

	currentEnvironment[cmd_period_preprocessor_key] = true;
	currentEnvironment['enable-ns-preprocessor'] = enable_pre_processor;
	currentEnvironment['disable-ns-preprocessor'] = disable_pre_processor;

	"interpreter variable e is used".warn;
	"e.val(\"(+ 1 2)\"); // to interpret a lisp expression in the sclang interpreter".inform;
	"currentEnvironment['*cmdperiod-is-preprocessor-toggle*'] = true; // if set to true cmdPeriod will toggle lisp preprocessor enabled/disabled (default is true)".inform;
	enable_pre_processor.value;
};

var
rep =
{ |str, env|
	// TODO var funcName = 'rep';
	var val = read_eval.value(str, env ? currentEnvironment['_NS_ENV'] ? currentEnvironment);
	if (val.notNil) {
		scheme_str.value(val);
	};
};

/*
read / eval
*/

var
read_eval =
{ |str, env|
	eval.value(read.value(str), env);
};

var
init_ns_environment =
{ |dest_env|
	var environment = ();
	environment putAll: standard_procedures.value;
	environment putAll: additional_procedures.value;
	dest_env putAll: environment;
};

var
standard_procedures =
{
	var procedures = (
		/*
		r4rs essential procedure: (= z1 z2 z3 ...) TODO: varargs
		*/
		'=': { |a, b|
			a.asFloat == b.asFloat // TODO
		},
		/*
		r4rs essential procedure: (< z1 z2 z3 ...) TODO: varargs
		*/
		'<': { |a, b|
			a < b
		},
		/*
		r4rs essential procedure: (> z1 z2 z3 ...) TODO: varargs
		*(
		'>': { |a, b|
			a > b
		},
		// r4rs essential procedure: (<= z1 z2 z3 ...) TODO: varargs
		'<=': { |a, b|
			a <= b
		},
		// r4rs essential procedure: (>= z1 z2 z3 ...) TODO: varargs
		'>=': { |a, b|
			a >= b
		},
		// r4rs essential procedure: (+ z1 ...) TODO: varargs
		'+': { |a, b|
			a + b
		},
		// r4rs essential procedure: (* z1 ...) TODO: varargs
		'*': { |a, b|
			a * b
		},
		// r4rs essential procedure: (- z1 z2)
		// r4rs essential procedure: (- z) TODO
		// r4rs procedure: (- z1 z2 ...) TODO
		'-': { |a, b|
			a - b
		},
		// r4rs essential procedure: (/ z1 z2)
		// r4rs essential procedure: (/ z) TODO
		// r4rs procedure: (/ z1 z2 ...) TODO
		'/': { |a, b|
			a / b
		},
		// r4rs essential procedure: (abs x)
		'abs': { |x|
			x.abs
		},
		// r4rs essential procedure: (append list ...)
		'append': { |... lists|
			var result = [];

			lists.do { |list|
				if (is_list.value(list).not) {
					Error("not a list: %".format(scheme_str.value(list))).throw;
				};
				result = result.addAll(list)
			};

			result
		},
		// r4rs essential procedure: (apply proc args)
		// r4rs procedure: (apply proc arg1 ... args)
		'apply': { |proc, args|
			Error("TODO: apply").throw;
		},
		// r4rs essential procedure: (boolean? obj)
		'boolean?': { |obj|
			is_boolean(obj)
		},
		// r4rs essential procedure: (call-with-current-continuation proc)
		'call-with-current-continuation': { |proc|
			Error("TODO: call-with-current-continuation").throw;
		},
		// r4rs essential procedure: (call-with-input-file string proc)
		'call-with-input-file': { |string, proc|
			Error("TODO: call-with-input-file").throw;
		},
		// r4rs essential procedure: (call-with-output-file string proc)
		'call-with-output-file': { |string, proc|
			Error("TODO: call-with-output-file").throw;
		},

		// r4rs essential procedure: (close-input-port port)
		'close-input-port': { |port|
			Error("TODO: close-input-port").throw;
		},
		// r4rs essential procedure: (close-output-port port)
		'close-output-port': { |port|
			Error("TODO: close-output-port").throw;
		},
		// r4rs essential procedure: (current-input-port)
		'current-input-port': {
			Error("TODO: current-input-port").throw;
		},
		// r4rs essential procedure: (current-output-port)
		'current-output-port': {
			Error("TODO: current-output-port").throw;
		},
		// r4rs essential procedure: (char? obj)
		'char?': { |obj|
			is_chr.value(obj)
		},
		// r4rs essential procedure: (char=? char1 char2)
		'char=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1 == char2)
		},
		// r4rs essential procedure: (char<? char1 char2)
		'char<?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1 < char2)
		},
		// r4rs essential procedure: (char>? char1 char2)
		'char>?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1 > char2)
		},
		// r4rs essential procedure: (char<=? char1 char2)
		'char<=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1 <= char2)
		},
		// r4rs essential procedure: (char>=? char1 char2)
		'char>=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1 >= char2)
		},
		// r4rs essential procedure: (char-ci=? char1 char2)
		'char-ci=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1.toUpper == char2.toUpper)
		},
		// r4rs essential procedure: (char-ci<? char1 char2)
		'char-ci<?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1.toUpper < char2.toUpper)
		},
		// r4rs essential procedure: (char-ci>? char1 char2)
		'char-ci>?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1.toUpper > char2.toUpper)
		},
		// r4rs essential procedure: (char-ci<=? char1 char2)
		'char-ci<=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1.toUpper <= char2.toUpper)
		},
		// r4rs essential procedure: (char-ci>=? char1 char2)
		'char-ci>=?': { |char1, char2|
			is_chr.value(char1) and: is_chr.value(char2) and: (char1.toUpper >= char2.toUpper)
		},
		// r4rs essential procedure: (char-alphabetic? char)
		'char-alphabetic?': { |char|
			is_chr.value(char) and: char.isAlpha
		},
		// r4rs essential procedure: (char-lower-case? letter)
		'char-lower-case?': { |letter|
			is_chr.value(letter) and: letter.isLower
		},
		// r4rs essential procedure: (char-numeric? char)
		'char-numeric?': { |char|
			is_chr.value(char) and: char.isDecDigit
		},
		// r4rs essential procedure: (char-upper-case? letter)
		'char-upper-case?': { |letter|
			is_chr.value(letter) and: letter.isUpper
		},
		// r4rs essential procedure: (char-whitespace? char)
		'char-whitespace?': { |char|
			is_chr.value(char) and: char.isSpace
		},
		// r4rs essential procedure: (char->integer char)
		'char->integer': { |char|
			char.ascii
		},
		// r4rs essential procedure: (char-upcase char)
		'char-upcase': { |char|
			char.toUpper
		},
		// r4rs essential procedure: (char-downcase char)
		'char-downcase': { |char|
			char.toLower
		},
		// r4rs essential procedure: (complex? obj)
		'complex?': { |obj|
			false
		},
		// r4rs essential procedure: (car pair)
		'car': { |pair|
			pair[0];
		},
		// r4rs essential procedure: (cdr pair)
		'cdr': { |pair|
			pair[1..]
		},
		// r4rs essential procedure: (ceiling x)
		'ceiling': { |x|
			x.ceil.asInteger
		},
		// r4rs essential procedure: (cons obj1 obj2)
		'cons': { |obj1, obj2|
			[obj1] ++ obj2
		},
		// r4rs essential procedure: (display obj)
		// r4rs essential procedure: (display obj port) TODO
		'display': { |obj|
			if (is_str.value(obj)) {
				obj.post;
			} {
				scheme_str.value(obj).post;
			};
			nil;
		},
		'do': { |init_exprs, test_exprs, commands|
			// r4rs syntax:
			//   (do ((<variable1> <init1> <step1>)
			//     ...) (<test> <expression> ...) <command> ...)
			Error("TODO: do").throw;

		},
		// r4rs essential procedure: (eof-object? obj)
		'eof-object?': { |obj|
			Error("TODO: eof-object?").throw;
		},
		// r4rs essential procedure: (eq? obj1 obj2)
		'eq?': { |obj1, obj2|
			obj1 === obj2
		},
		// r4rs essential procedure: (eqv? obj1 obj2)
		'eqv?': { |obj1, obj2|

			// TODO: unreasonable performance

			// The eqv? procedure returns #t if:

			// obj1 and obj2 are both #t or both #f
			((obj1 == true) and: (obj2 == true))
			or:
			((obj1 == false) and: (obj2 == false))
			or:

			// obj1 and obj2 are both symbols and
			// (string=? (symbol->string obj1) (symbol->string obj2)) ==>  #t
			(is_sym.value(obj1) and: is_sym.value(obj2) and: (obj1.asString == obj2.asString)) // TODO: DRY with string=?
			or:

			// obj1 and obj2 are both numbers, are numerically equal (see =, section see section 6.5 Numbers), and are either both exact or both inexact.
			(is_number.value(obj1) and: is_number.value(obj2) and: (obj1 == obj2)) // TODO: DRY with =
			or:

			// obj1 and obj2 are both characters and are the same character according to the char=? procedure
			(is_chr.value(obj1) and: is_chr.value(obj2) and: (obj1 == obj2))  // TODO: DRY with char=?
			or:

			// both obj1 and obj2 are the empty list
			(is_empty_list.value(obj1) and: is_empty_list.value(obj2))
			or:

			// obj1 and obj2 are procedures whose location tags are equal
			(is_procedure.value(obj1) and: is_procedure.value(obj2) and: (obj1 === obj2))
			or:

			// obj1 and obj2 are pairs, vectors, or strings that denote the same locations in the store
			(is_pair.value(obj1) and: is_pair.value(obj2) and: (obj1 === obj2))
			or:

			(is_str.value(obj1) and: is_str.value(obj2) and: (obj1 === obj2))
			or:

			(is_vector.value(obj1) and: is_vector.value(obj2) and: (obj1 === obj2))
		},
		// r4rs essential procedure: (equal? obj1 obj2)
		'equal?': { |obj1, obj2|
			obj1 == obj2
		},
		'expt': { |z1, z2|
			// r4rs procedure: expt z1 z2
			z1.pow(z2);
		},
		// r4rs essential procedure: (exact? z)
		'exact?': { |z|
			z.isKindOf(Integer)
		},
		// r4rs essential procedure: (even? z)
		'even?': { |z|
			(z mod: 2) == 0
		},
		// r4rs essential procedure: (floor x)
		'floor': { |x|
			x.floor.asInteger
		},
		// r4rs essential procedure: (for-each proc list1 list2 ...) TODO: test
		'for-each': { |proc ... lists|
			var result;
			lists.first.do { |element, i|
				var args = lists[1..].collect { |list|
					list[i]
				};
				result = proc.valueArray(args);
			};
			result;
		},
		// r4rs essential procedure: (gcd n1 ...)
		'gcd': { |... args|
			Error("TODO: gcd").throw;
		},
		// r4rs essential procedure: (inexact? z)
		'inexact?': { |z|
			z.isKindOf(Float)
		},
		// r4rs essential procedure: (input-port? obj)
		'input-port?': { |obj|
			Error("TODO: input-port?").throw;
		},
		// r4rs essential procedure: (integer? obj)
		'integer?': { |obj|
			obj.isKindOf(Integer)
		},
		// r4rs essential procedure: (integer->char n)
		'integer->char': { |n|
			n.asAscii
		},
		// r4rs essential procedure: (lcm n1 ...)
		'lcm': { |... args|
			Error("TODO: lcm").throw;
		},
		// r4rs essential procedure: (length list)
		'length': { |list|
			list.size;
		},
		// r4rs essential procedure: (list obj ...)
		'list': { |...objs|
			objs
		},
		// r4rs essential procedure: (list? obj)
		'list?': { |obj|
			is_list.value(obj)
		},
		// r4rs essential procedure: (list-ref list k)
		'list-ref': { |list, k|

			/*
			TODO
			This is the same as the car of (list-tail list k)
			*/
			list[k];
		},
		// r4rs essential procedure: (list->string chars)
		'list->string': { |chars|
			chars.join
		},
		// r4rs essential procedure: (list->vector list)
		'list->vector': { |list|
			(__type__: 'vector', content: list.copy );
		},
		'list-tail': { |list, k|
			// r4rs procedure: list-tail list k

			/*
			TODO:
(define list-tail
  (lambda (x k)
    (if (zero? k)
        x
        (list-tail (cdr x) (- k 1)))))
			*/

			list.drop(k);
		},
		// r4rs essential procedure: (load filename)
		'load': { |filename|
			Error("TODO: load").throw;
		},
		// r4rs essential procedure: (make-string k)
		// r4rs essential procedure: (make-string k char)
		'make-string': { |k, char|
			((char ? $ ) ! k).join
		},
		// r4rs essential procedure: (make-vector k)
		'make-vector': { |k, fill|
			// procedure: make-vector k fill

			(__type__: 'vector', content: Array.fill(k, fill) );
		},
		// r4rs essential procedure: (map proc list1 list2 ...)
		'map': { |proc ... lists|

			lists.first.collect { |element, i|
				var args = lists.collect { |list|
					list[i]
				};
				proc.valueArray(args);
			};
		},
		// r4rs essential procedure: (max x1 x2 ...) TODO varargs
		'max': { |x1, x2|
			x1.max(x2)
		},
		// r4rs essential procedure: (min x1 x2 ...) TODO varargs
		'min': { |x1, x2|
			x1.min(x2)
		},
		// r4rs essential procedure: (modulo n1 n2) TODO: "number theoretic"
		'modulo': { |n1, n2|
			n1 % n2
		},
		// r4rs essential procedure: (negative? z)
		'negative?': { |z|
			z < 0
		},
		// r4rs essential procedure: (newline)
		// r4rs essential procedure: (newline port) TODO
		'newline': {
			"".postln;
			nil;
		},
		// r4rs essential procedure: (not obj)
		'not': { |obj|
			if (obj == false) {
				true
			} {
				false
			};
		},
		// r4rs essential procedure: (null? obj)
		'null?': { |obj|
			obj == []
		},
		// r4rs essential procedure: (number? obj)
		'number?': { |obj|
			is_number.value(obj);
		},
		// r4rs essential procedure: (number->string number)
		// r4rs essential procedure: (number->string number radix) TODO
		'number->string': { |number|
      		// TODO: check type
			number.asString
		},
		// r4rs essential procedure: (odd? z)
		'odd?': { |z|
			((z mod: 2) == 0).not
		},
		// r4rs essential procedure: (open-input-file filename)
		'open-input-file': { |filename|
			Error("TODO: open-input-file").throw;
		},
		// r4rs essential procedure: (open-output-file filename)
		'open-output-file': { |filename|
			Error("TODO: open-output-file").throw;
		},
		// r4rs essential procedure: (output-port? obj)
		'output-port?': { |obj|
			Error("TODO: output-port?").throw;
		},
		// r4rs essential procedure: (pair? obj)
		'pair?': { |obj|
			is_pair.value(obj);
		},
		// r4rs essential procedure: (peek-char) TODO
		// r4rs essential procedure: (peek-char port) TODO
		'peek-char': { |port|
			Error("TODO: peek-char").throw;
		},
		'pi': pi, // TODO not in r4rs?
		// r4rs essential procedure: (positive? z)
		'positive?': { |z|
			z > 0
		},
		// r4rs essential procedure: (procedure? obj)
		'procedure?': { |obj|
			is_procedure.value(obj)
		},
		// r4rs essential procedure: (quotient n1 n2) TODO
		'quotient': { |n1, n2|
			Error("TODO: quotient").throw;
		},
		// r4rs essential procedure: (rational? obj)
		'rational?': { |obj|
			false
		},
		// r4rs essential procedure: (read) TODO
		// r4rs essential procedure: (read port) TODO
		'read': { |port|
			Error("TODO: read").throw;
		},
		// r4rs essential procedure: (read-char) TODO
		// r4rs essential procedure: (read-char port) TODO
		'read-char': { |port|
			Error("TODO: read-char").throw;
		},
		// r4rs essential procedure: (real? obj)
		'real?': { |obj|
			obj.isKindOf(Float)
		},
		// r4rs essential procedure: (remainder n1 n2) TODO
		'remainder': { |n1, n2|
			Error("TODO: remainder").throw;
		},
		// r4rs essential procedure: (reverse list)
		'reverse': { |list|
			list.reverse
		},
		// r4rs essential procedure: (round x)
		'round': { |x|
			x.round.asInteger
		},
		// r4rs essential procedure: (set-car! pair obj)
		'set-car!': { |pair, obj|
			Error("TODO: set-car!").throw;
		},
		// r4rs essential procedure: (set-cdr! pair obj)
		'set-cdr!': { |pair, obj|
			Error("TODO: set-cdr!").throw;
		},
		'sqrt': { |z|
			// r4rs procedure: sqrt z
			z.sqrt
		},
		// r4rs essential procedure: (string? obj)
		'string?': { |obj|
			is_list.value(obj)
		},
		// r4rs essential procedure: (string char ...)
		'string': { |... char|
			// TODO: validate it's all chars
			char.join;
		},
		// r4rs essential procedure: (string-length string)
		'string-length': { |string|
			// TODO: validate it's String?
			string.size
		},
		// r4rs essential procedure: (string-ref string k)
		'string-ref': { |string, k|
			// TODO: validate it's String?
			string[k];
		},
		// r4rs essential procedure: (string-set! string k char)
		'string-set!': { |string, k, char|
			// TODO: sclang strings are immutable
			Error("TODO: string-set!").throw;
		},
		// r4rs essential procedure: (string=? string1 string2)
		'string=?': { |string1, string2|
			is_str.value(string1) and: is_str.value(string2) and: (string1 == string2)
		},
		// r4rs essential procedure: (string-append string ...)
		'string-append': { |...strings|
			var value = "";
			strings.do { |str|
				value = value ++ str;
			};
			value;
		},
		// r4rs essential procedure: (string->list string)
		'string->list': { |string|
			var list = Array.new;
			string.size.do { |i|
				list = list.add(string[i]);
			};
			list;
		},
		// r4rs essential procedure: (string->number string)
		// r4rs essential procedure: (string->number string radix) TODO
		'string->number': { |string|
      		// TODO: check type
			string.asFloat
		},
		// r4rs essential procedure: (string->symbol string)
		'string->symbol': { |string|
			if (is_str.value(string)) {
				string.asSymbol;
			} {
				Error("TODO").throw;
			};
		},
		// r4rs essential procedure: (string-ci=? string1 string2)
		'string-ci=?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1.toUpper == string2.toUpper)
		},
		// r4rs essential procedure: (string<? string1 string2)
		'string<?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1 < string2)
		},
		// r4rs essential procedure: (string>? string1 string2)
		'string>?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1 > string2)
		},
		// r4rs essential procedure: (string<=? string1 string2)
		'string<=?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1 <= string2)
		},
		// r4rs essential procedure: (string>=? string1 string2)
		'string>=?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1 >= string2)
		},
		// r4rs essential procedure: (string-ci<? string1 string2)
		'string-ci<?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1.toUpper < string2.toUpper)
		},
		// r4rs essential procedure: (string-ci>? string1 string2)
		'string-ci>?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1.toUpper > string2.toUpper)
		},
		// r4rs essential procedure: (string-ci<=? string1 string2)
		'string-ci<=?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1.toUpper <= string2.toUpper)
		},
		// r4rs essential procedure: (string-ci>=? string1 string2)
		'string-ci>=?': { |string1, string2|
			is_list.value(string1) and: is_list.value(string2) and: (string1.toUpper >= string2.toUpper)
		},
		'string->symbol': { |string|
			// r4rs essential procedure: string->symbol string
			if (is_list.value(string)) {
				string.asSymbol;
			} {
				Error("TODO").throw;
			};
		},
		// r4rs essential procedure: (substring string start end)
		'substring': { |string, start, end|

			// TODO: String must be a string, and start and end must be exact integers satisfying 0 <= start <= end <= (string-length string).

			string[start, end-1]
		},
		// r4rs essential procedure: (symbol? obj)
		'symbol?': { |obj|
			is_sym.value(obj)
		},
		// r4rs essential procedure: (symbol->string symbol)
		'symbol->string': { |symbol|
			if (is_sym.value(symbol)) {
				symbol.asString;
			} {
				Error("TODO").throw;
			};
		},
		// r4rs essential procedure: (truncate x)
		'truncate': { |x|
			x.trunc.asInteger
		},
		// r4rs essential procedure: (write obj)
		// r4rs essential procedure: (write obj port)
		'write': { |obj, port|
			Error("TODO: write").throw;
		},
		// r4rs essential procedure: (write-char char)
		// r4rs essential procedure: (write-char char port)
		'write-char': { |char, port|
			Error("TODO: write-char").throw;
		},
		// r4rs essential procedure: (vector obj ...)
		'vector': { |...args|
			(__type__: 'vector', content: args ) // TODO: or use proto or parent event?
		},
		// r4rs essential procedure: (vector? obj)
		'vector?': { |obj|
			is_vector.value(obj)
		},
		'vector-fill!': { |vector, fill|
			// r4rs procedure: vector-fill! vector fill
			vector.fill(fill);
		},
		// r4rs essential procedure: (vector-length vector)
		'vector-length': { |vector|
			vector['content'].size
		},
		// r4rs essential procedure: (vector-ref vector k)
		'vector-ref': { |vector, k|
			vector['content'][k]
		},
		// r4rs essential procedure: (vector-set! vector k obj)
		'vector-set!': { |vector, k, obj|
			vector['content'][k] = obj
		},
		// r4rs essential procedure: (vector->list vector)
		'vector->list': { |vector|
			Array.newFrom(vector['content']);
		},
		// r4rs essential procedure: (zero? z)
		'zero?': { |z|
			z == 0
		}
	);

	define_non_prim_standard_procedures_2.value(procedures);

	procedures;
};

var
define_non_prim_standard_procedures =
{ |env|
	// TODO: assq, assv, assoc possible to DRY
	// TODO: memq, memv, member possible to DRY
	var standard_procedure_defs =
"
; r4rs essential procedure: (assq obj alist)
;

(define assq
  (lambda (obj alist)
	(cond
	  [(null? alist) #f]
	  [(eq? obj (caar alist)) (car alist)]
	  [else (assoc obj (cdr alist))]))) ; TODO: assoc here? not assq?

; r4rs essential procedure: (assv obj alist)
;

(define assv
  (lambda (obj alist)
	(cond
	  [(null? alist) #f]
	  [(eqv? obj (caar alist)) (car alist)]
	  [else (assoc obj (cdr alist))]))) ; TODO: assoc here? not assv?

; r4rs essential procedure: (assoc obj alist)
;

(define assoc
  (lambda (obj alist)
	(cond
	  [(null? alist) #f]
	  [(equal? obj (caar alist)) (car alist)]
	  [else (assoc obj (cdr alist))])))

; r4rs essential procedure: (memq obj list)
;

(define memq
  (lambda (obj list)
	(cond
	  [(null? list) #f]
	  [(eq? obj (car list)) list]
	  [else (member obj (cdr list))])))

; r4rs essential procedure: (memv obj list)
;

(define memv
  (lambda (obj list)
	(cond
	  [(null? list) #f]
	  [(eqv? obj (car list)) list]
	  [else (member obj (cdr list))])))

; r4rs essential procedure: (member obj list)
;

(define member
  (lambda (obj list)
	(cond
	  [(null? list) #f]
	  [(equal? obj (car list)) list]
	  [else (member obj (cdr list))])))

; r4rs essential procedures: caar ... cdddr
;

(define caar
  (lambda (list)
	(car (car list))))

;

(define caar
  (lambda (list)
	(car (car list))))

;

(define cadr
  (lambda (list)
	(car (cdr list))))

;

(define cdar
  (lambda (list)
	(cdr (car list))))

;

(define cddr
  (lambda (list)
	(cdr (cdr list))))

;

(define caaar
  (lambda (list)
	(car (car (car list)))))

;

(define caadr
  (lambda (list)
	(car (car (cdr list)))))

;

(define cadar
  (lambda (list)
	(car (cdr (car list)))))

;

(define caddr
  (lambda (list)
	(car (cdr (cdr list)))))

;

(define cdaar
  (lambda (list)
	(cdr (car (car list)))))

;

(define cdadr
  (lambda (list)
	(cdr (car (cdr list)))))

;

(define cddar
  (lambda (list)
	(cdr (cdr (car list)))))

;

(define cdddr
  (lambda (list)
	(cdr (cdr (cdr list)))))
;
";

	standard_procedure_defs.split($;).select { |str|
		str.contains("(define ")
	}.do { |standard_procedure_def|
		read.value(standard_procedure_def).postcs;
		eval.value(read.value(standard_procedure_def), env);
	};
};

var
define_non_prim_standard_procedures_2 =
{ |env|
	// TODO: assq, assv, assoc possible to DRY
/*
		[ 'define', 'assq',
			[ 'lambda', [ 'obj', 'alist' ],
				[ 'cond',
					[ [ 'null?', 'alist' ], false ],
					[ [ 'eq?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ],
					[ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ]
*/
	// TODO: memq, memv, member possible to DRY
/*
	var standard_procedure_defs =
	[
		// r4rs essential procedure: (assq obj alist)
		['define', 'assq',
			['lambda', ['obj', 'alist'],
				['cond',
					[['null?', 'alist'], '#f'],
					[['eq?', 'obj', ['caar', 'alist']], ['car', 'alist']],
					['else', ['assoc', 'obj', ['cdr', 'alist']]]]]],

		// r4rs essential procedure: (assv obj alist)
		['define', 'assv',
			['lambda', ['obj', 'alist'],
				['cond',
					[['null?', 'alist'], '#f'],
					[['eqv?', 'obj', ['caar', 'alist']], ['car', 'alist']],
					['else', ['assoc', 'obj', ['cdr', 'alist']]]]]],
		// r4rs essential procedure: (assoc obj alist)
		['define', 'assoc',
			['lambda', ['obj', 'alist'],
				['cond',
					[['null?', 'alist'], '#f'],
					[['equal?', 'obj', ['caar', 'alist']], ['car', 'alist']],
					['else', ['assoc', 'obj', ['cdr', 'alist']]]]]],
	]
;
*/

	var standard_procedure_defs =
	[
		[ 'define', 'assq', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'eq?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'assv', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'eqv?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'assoc', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'equal?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'memq', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'eq?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'memv', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'eqv?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'member', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'equal?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'caar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', 'list' ] ] ] ],
		[ 'define', 'caar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', 'list' ] ] ] ],
		[ 'define', 'cadr', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', 'list' ] ] ] ],
		[ 'define', 'cdar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', 'list' ] ] ] ],
		[ 'define', 'cddr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', 'list' ] ] ] ],
		[ 'define', 'caaar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'caadr', [ 'lambda', [ 'list' ], [ 'car', [ 'car', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cadar', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'caddr', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cdaar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'cdadr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cddar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'cdddr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'assq', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'eq?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'assv', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'eqv?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'assoc', [ 'lambda', [ 'obj', 'alist' ], [ 'cond', [ [ 'null?', 'alist' ], false ], [ [ 'equal?', 'obj', [ 'caar', 'alist' ] ], [ 'car', 'alist' ] ], [ 'else', [ 'assoc', 'obj', [ 'cdr', 'alist' ] ] ] ] ] ],
		[ 'define', 'memq', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'eq?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'memv', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'eqv?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'member', [ 'lambda', [ 'obj', 'list' ], [ 'cond', [ [ 'null?', 'list' ], false ], [ [ 'equal?', 'obj', [ 'car', 'list' ] ], 'list' ], [ 'else', [ 'member', 'obj', [ 'cdr', 'list' ] ] ] ] ] ],
		[ 'define', 'caar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', 'list' ] ] ] ],
		[ 'define', 'caar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', 'list' ] ] ] ],
		[ 'define', 'cadr', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', 'list' ] ] ] ],
		[ 'define', 'cdar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', 'list' ] ] ] ],
		[ 'define', 'cddr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', 'list' ] ] ] ],
		[ 'define', 'caaar', [ 'lambda', [ 'list' ], [ 'car', [ 'car', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'caadr', [ 'lambda', [ 'list' ], [ 'car', [ 'car', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cadar', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'caddr', [ 'lambda', [ 'list' ], [ 'car', [ 'cdr', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cdaar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'cdadr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'car', [ 'cdr', 'list' ] ] ] ] ],
		[ 'define', 'cddar', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', [ 'car', 'list' ] ] ] ] ],
		[ 'define', 'cdddr', [ 'lambda', [ 'list' ], [ 'cdr', [ 'cdr', [ 'cdr', 'list' ] ] ] ] ]
	]
;

	standard_procedure_defs.do { |standard_procedure_def|
		eval.value(standard_procedure_def, env);
	};
};

var
additional_procedures =
{
	// TODO var funcName = 'additional_procedures';

	(
		'hash': { |...args| // TODO: immutable hash table
			// racket (hash key val ... ...)
			var content = IdentityDictionary.new;
			args.pairsDo { |a, b| content[a] = eval.value(b) };
			(__type__: 'hash', content: content) // TODO: __immutable_hash__ ??
		},
		'make-hash': { |assocs| // TODO: mutable hash table
			// racket (make-hash [assocs])
			var content = IdentityDictionary.new;
			assocs.do { |assoc|
				var key, value;
				# key ... value = assoc;
				content[key] = value // TODO: eval values(?) eval key?
			};
			(__type__: 'hash', content: content) // TODO: __mutable_hash__ ??
		},
		'hash-ref': { |hash, key|
			// racket (hash-ref hash key [failure-result]) TODO: failure-result
			hash['content'][key];
		},
		'hash-set!': { |hash, key, v|
			// racket (hash-set! hash key v)
			hash['content'][key] = v;
		},
		'hash-count': { |hash|
			// racket (hash-count hash)
			hash['content'].size
		},
		'hash?': { |obj|
			// racket (hash? v)
			is_hash.value(obj)
		},
		'vector-filter': { |proc, vec|
			// racket (vector-filter pred vec)
			(__type__: 'vector', content: vec['content'].select(proc) );
		},
		'vector-filter-not': { |proc, vec|
			// racket (vector-filter-not pred vec)
			(__type__: 'vector', content: vec['content'].reject(proc) );
		},
		'vector-map': { |proc, vec|
			// racket (vector-map proc vec ...+) TODO: ...+
			(__type__: 'vector', content: vec['content'].collect(proc) );
		},
	);
};

var
read =
{ |str|
	var ss = ss_new.(str);
	var result = parse.(ss);
	result
};

var
parse =
{ |ss|
  	var rg_ignore = "^\\s+";

	var value;
	var result;

	var open_paren;

	ss_skip.(ss, rg_ignore);

	open_paren = ss_scan.(ss, "\\(") ? ss_scan.(ss, "\\[");

	case
	{ open_paren.notNil } {
    	var close_paren;
		var list;

		if (open_paren == "(") {
		  close_paren = "^\\)";
		} {
		  close_paren = "^\\]";
		};

		ss_skip.(ss, rg_ignore);

		list = Array.new;
		while { ss_matches.(ss, close_paren).isNil } {
			list = list.add(parse.(ss));
			ss_skip.(ss, rg_ignore);
		};

		ss_skip.(ss, close_paren);

		result = list;
	}
/*
	TODO: # only external representation?
	{ is_vector_char.value(token) } {
		// TODO: validate a list follows
		var list = Array.new;
		list = ['vector'] ++ read_from_tokens.value(tokens);
		list;
	}
*/
	{ ss_scan.(ss, "^'").notNil } {
		// r4rs essential syntax: '<datum>
		var list = Array.new;
		list = list.add('quote');
		list = list.add(parse.value(ss));
		result = list
	}
	{ ss_scan.(ss, "^`").notNil } {
    	// r4rs essential syntax: `<template>
		var list = Array.new;
		list = list.add('quasiquote');
		list = list.add(parse.value(ss));
		result = list
	}
	{ ss_scan.(ss, "^,@").notNil } {
		var list = Array.new;
		list = list.add('unquote-splicing');
		list = list.add(parse.value(ss));
		result = list
	}
	{ ss_scan.(ss, "^,").notNil } {
		var list = Array.new;
		list = list.add('unquote');
		list = list.add(parse.value(ss));
		result = list
	}
	{ true } {
		result = atom.(ss);
	}
	;

	if (result.isNil) {
		if (ss_eos.(ss)) {
			Error("parse error: unexpected EOF").throw;
		} {
			// Error("parse error: unexpected token at %".format(ss_peek.(ss).quote)).throw;
			Error("parse error: unexpected token at %".format(ss_as_string.(ss).quote)).throw;
		};
	};

	expand.(result);
};

var
expand =
{ |x|
	// TODO var funcName = 'expand';

	if (x.class != Array) {
		x
	} {
		var head, tail;
		# head ... tail = x;

		case
		{ head == 'quote' } {
			if (tail.size != 1) {
				Error("in %: quote syntax error: 1 expression expected, got %".format(scheme_str.value(x), tail.size)).throw;
			} {
				x
			};
		}
		{ head == 'begin' } {
			// TODO: (begin) => None
			x
		}
		{ head == 'define' } {
			if (x.size != 3) {
				Error("in %: expected == 3 expressions in define: got %".format(scheme_str.value(x), x.size)).throw;
			} {
				// (define (f args) body) => (define f (lambda (args) body))
				var variable_part, body;
				# variable_part ... body = tail;
				if (is_list.value(variable_part)) {
					var variables, formals;
					# variables ... formals = variable_part;
					[
						'define',
						variables,
						// (lambda (x) e1 e2) => (lambda (x) (begin e1 e2))
						expand_lambda.value([formals] ++ body)
					]
				} {
					x
				}
			}
		}
		{ head == 'lambda' } {
			if (x.size < 3) {
				Error("in %: expected >= 3 expressions in lambda: got %".format(scheme_str.value(x), x.size)).throw;
			} {
				// (lambda (x) e1 e2) => (lambda (x) (begin e1 e2))
				expand_lambda.value(tail);
			};
		}
		{ head == 'quasiquote' } {
			// r4rs essential syntax: (quasiquote <template>)
			if (tail.size != 1) {
				Error("in %: quasiquote syntax error: 1 expression expected, got %".format(scheme_str.value(x), tail.size)).throw;
			} {
				expand_quasiquote.value(tail.first);
			};
		}
		{ true } {
			x.collect { |part| expand.value(part) };
		};
	};
};

// (lambda (x) e1 e2) => (lambda (x) (begin e1 e2))
var
expand_lambda =
{ |tail|
	var formals, body, exp;
	# formals ... body = tail;

	/*
	TODO where vars == formals
	require(x, (isa(vars, list) and all(isa(v, Symbol) for v in vars))
	or isa(vars, Symbol), "illegal lambda argument list")
	*/

	if (body.size == 1) {
		exp = body[0];
	} {
		exp = [ 'begin' ] ++ body;
	};
	[
		'lambda',
		formals,
		expand.value(exp)
	];
};

/*
Expand `x => 'x; `,x => x; `(,@x y) => (append x y)
*/
var
expand_quasiquote = { |x|
	// TODO var funcName = 'expand_quasiquote';

	if (is_pair.value(x).not) {
		['quote', x]
	} {
		var head, tail;
		var continueFunc = {
			['cons', expand_quasiquote.value(head), expand_quasiquote.value(tail)]
		};
		# head ... tail = x;

		case
		{ head == 'unquote' } {
			if (tail.size != 1) {
				Error("in %: quasiquote syntax error: 1 expression expected, got %".format(scheme_str.value(x), tail.size)).throw;
			} {
				tail.first;
			};
		}
		{ is_pair.value(head) } {
			if (head[0] == 'unquote-splicing') { // TODO: awkward due to non-shortcircuiting and in sclang
				[ 'append', head[1], expand_quasiquote.value(tail) ]
			} {
				continueFunc.value;
			}
		}
		{ true } {
			continueFunc.value;
		};
	};
};

var
atom =
{ |ss|
	// TODO var funcName = 'atom';

	var value;

	var rg_float = "(-?(?:0|[1-9]\\d*)(?:\\.\\d+(?i:e[+-]?\\d+)|\\.\\d+|(?i:e[+-]?\\d+)))";
	var rg_integer = "-?0|-?[1-9]\\d*";
	// var rg_symbol = "[0-9a-zA-Z_!|@=*/+-<>:;,.?&\\\\'']+";
	var rg_symbol = "[a-zA-Z+-.*/<=>!?:\$%_&~\^][0-9a-zA-Z+-.*/<=>!?:\$%_&~\^]*";
	var rg_char = "#\\\\[0-9a-zA-Z]";
	var rg_char_space = "#\\\\space";
	var rg_char_newline = "#\\\\newline";
	var rg_boolean = "#[ft]";
	var rg_string = "\"[0-9a-zA-Z_!|@=*/+-<>:;,.()?&#\\\\'']*\"";

	case
	{ (value = ss_scan.(ss, rg_float)).notNil } {
		value.asFloat
	}
	{ (value = ss_scan.(ss, rg_integer)).notNil } {
		value.asInteger
	}
	{ (value = ss_scan.(ss, rg_symbol)).notNil } {
		value.asSymbol
	}
	{ (value = ss_scan.(ss, rg_char_newline)).notNil } {
		Char.nl
	}
	{ (value = ss_scan.(ss, rg_char_space)).notNil } {
		Char.space
	}
	{ (value = ss_scan.(ss, rg_char)).notNil } {
		value[2]
	}
	{ (value = ss_scan.(ss, rg_boolean)).notNil } {
		value == "#t"
	}
	{ (value = ss_scan.(ss, rg_string)).notNil } {
		value[1..value.size-2].asString.replace("\\n", "\n")
	}
/*
	TODO: ?
	{ true } {
		Error("parse error, token: %".format(token)).throw;
	}
*/
};

var
eval =
{ |x, env|
	// TODO var funcName = 'eval';

	case
	{ is_sym.value(x) } {
		// r4rs essential syntax: <variable>
		var found_env = find_env.value(env, x);
		if (found_env.notNil) {
			found_env[x];
		} {
			// "%: undefined".format(x).error;
			Error("%: undefined".format(x)).throw;
		};
	}
	{ is_list.value(x) } {
		var op, args;
		# op ... args = x;
		case
		{ op == 'and' } {
			// r4rs essential syntax: (and <test1> ...)
			var value = true;
			var index = 0;

			while { (value != false) and: (index < args.size) } {
				value = eval.value(args[index], env);
				index = index + 1;
			};

			value;
		}
		{ op == 'begin' } {
			// r4rs essential syntax: (begin <expression1> <expression2> ...)
			args.inject([nil, env]) { |val_env, exp|
				[eval.value(exp, val_env[1]), val_env[1]]
			}[0];
		}
		{ op == 'case' } {
			// r4rs essential syntax: (case <key> <clause1> <clause2> ...)
			var num_clauses = args.size-1;
			var key = eval.value(args[0], env);
			var i = 0;

			var result;

			while { result.isNil and: (i < num_clauses)} {
				var clause = args[1+i];
				var object_expr = clause[0];
				var then_body = clause[1];

				result = case
				{ object_expr == 'else' } {
					eval.value(then_body, env); // TODO can be made more DRY
				}
				{ object_expr.includes(key) } {
					eval.value(then_body, env);
				};

				i = i + 1;
			};
			result;
		}
		{ op == 'cond' } {
			// r4rs essential syntax: (cond <clause1> <clause2> ...)
			var num_clauses = args.size;

			var i = 0;

			var result;

			while { result.isNil and: (i < num_clauses)} {
				var clause = args[i];
				var test_expr = clause[0];
				var then_body = clause[1];

				result = case
				{ test_expr == 'else' } {
					eval.value(then_body, env); // TODO can be made more DRY
				}
				{ eval.value(test_expr, env) } {
					eval.value(then_body, env);
				};

				i = i + 1;
			};
			result;
		}
		{ op == 'define' } {
			var symbol, exp;
			# symbol, exp = args;
			env[symbol] = eval.value(exp, env);
			nil;
		}
		{ op == 'if' } {
			// r4rs essential syntax: (if <test> <consequent> <alternate>)
			// r4rs syntax: (if <test> <consequent>)
			var test, conseq, alt;
			var expr;
			# test, conseq, alt = args;
			expr = if (eval.value(test, env), conseq, alt); // TODO: #t and #f only works??
			if (expr.notNil) {
				eval.value(expr, env);
			};
		}
		{ op == 'lambda' } {
			// r4rs essential syntax: (lambda <formals> <body>)
			var formals, body;
			# formals, body = args;

			// TODO: might be optimized by not using a separate make_lambda function?
			make_lambda.value(formals, body, env);
		}
		{ op == 'let' } {
			// r4rs essential syntax: (let <bindings> <body>)
			// Syntax: <bindings> should have the form ((<variable1> <init1>) ...), where each <init> is an expression, and <body> should be a sequence of one or more expressions
			var bindings, exprs, body;
			# bindings ... exprs = args;

			if (exprs.size == 1) {
				body = exprs[0];
			} {
				body = ['begin'] ++ exprs;
			};

			// TODO: might be optimized by not using a separate make_let/make_lambda functions?
			make_let.value(bindings, body, env);
		}
		{ op == 'let*' } {
			// r4rs syntax: let* <bindings> <body>
			// Syntax: <bindings> should have the form ((<variable1> <init1>) ...), and <body> should be a sequence of one or more expressions.
			var bindings, exprs, body;
			# bindings ... exprs = args;

			if (exprs.size == 1) {
				body = exprs[0];
			} {
				Error(
					"in %: let* body error: 1 expression expected, % found".format(
						scheme_str.value([op]++args),
						exprs.size
					)
				).throw;
			};

			if (bindings.size == 0) {
				make_lambda.value([], body, env).value;
			} {
				var binding, rest;
				# binding ... rest = bindings;

				make_let.value(
					[binding],
					['let*', rest, body],
					env
				).value;
			};
		}
		{ op == 'letrec' } {
			// r4rs essential syntax: (letrec <bindings> <body>)
			// Syntax: <Bindings> should have the form ((<variable1> <init1>) ...), and <body> should be a sequence of one or more expressions

			Error("TODO: letrec").throw;
		}
		{ op == 'or' } {
			// r4rs essential syntax: (or <test1> ...)

			var value = false;
			var index = 0;

			while { (value == false) and: (index < args.size) } {
				value = eval.value(args[index], env);
				index = index + 1;
			};

			value;
		}
		{ op == 'quote' } {
			// r4rs essential syntax: (quote <datum>)
			args.first;
		}
		{ op == 'set!' } {
			// r4rs essential syntax: (set! <variable> <expression>)
			var variable, exprs, expression;
			# variable ... exprs = args;
			if (exprs.size != 1) {
				Error(
					"in %: set! expr error: 1 expression expected, not %".format(

						scheme_str.value([op]++exprs), exprs.size
					)
				).throw;
			};
			expression = exprs[0];
			find_env.value(env, variable)[variable] = eval.value(expression, env);
			nil;
		}
		{ true } {
			// r4rs essential syntax: (<operator> <operand1> ...)
			var operator = op;
			var operands = args;
			var func = eval.value(operator, env);
			var vals;

			if (func.isNil) {
				Error("%: undefined".format(x)).throw;
			};

			if (is_procedure.value(func).not) {
				Error("not a procedure: %".format(scheme_str.value(operator))).throw;
			};

			vals = operands.collect { |a| eval.value(a, env) };

			func.value(*vals);
		};
	}
	{ true } {
		// r4rs essential syntax: <constant>

		// TODO: this lets everything through, narrow scope?
		x;
	}
};

var
make_let =
{ |bindings, body, env|
	// derived expression type:
	// (let ((<variable1> <init1>) ...)
	//  <body>)
	// ==   ((lambda (<variable1> ...) <body>) <init1> ...)

	// TODO var funcName = 'make_let';

	var parse_letbinding = { |binding, env|
		// TODO var funcName = 'parse_letbinding';
		[ binding[0], eval.value(binding[1], env) ]
	};

	var vars, inits;

	// (bindings: bindings, body: body, env: env.keys).debug(funcName);

	vars = [];
	inits = [];

	bindings.do { |binding|
		var varr, init;

		# varr, init = parse_letbinding.value(binding, env);

		vars = vars.add(varr);
		inits = inits.add(init);
	};

	make_lambda.value(vars, body, env).valueArray(inits);
};

var
make_lambda =
{ |formals, body, env|
	// TODO var funcName = 'make_lambda';

	// (body: body, formals: formals, env: env.keys).debug(funcName);

	{ |...args| eval.value(body, make_env.value(formals, args, env)) }
};

var
make_env =
{ |params([]), args([]), outer|
	// TODO var funcName = 'make_env';
	var env = ();
	params.do { |param, i|
		env[param] = args[i];
	};
	env['__outer__'] = outer; // TODO: __outer__ is magic key. it should not be possible to define
	env;
};

var
find_env =
{ |env, symbol|
	// TODO var funcName = 'find_env';
	if (env[symbol].notNil) { env } {
		var outer = env['__outer__'];
		if (outer.notNil) {
			find_env.value(outer, symbol);
		}
	};
};

var
scheme_str =
{ |obj|
	// TODO var funcName = 'scheme_str';
	case
	{ is_boolean.value(obj) } {
		if (obj) {
			"#t";
		} {
			"#f";
		}
	}
	{ is_number.value(obj) } {
		obj
	}
	{ is_sym.value(obj) } {
		obj.asString
	}
	{ is_chr.value(obj) } {
		case
		{ obj == Char.nl } {
			"#\\newline";
		}
		{ obj == Char.space } {
			"#\\space";
		}
		{ true } {
			"#\\"++obj;
		}
	}
	{ is_str.value(obj) } {
		obj.quote
	}
	{ is_procedure.value(obj) } {
		"a procedure"
	}
	{ is_list.value(obj) } { // TODO is_list
		"(" ++ obj.collect { |element| scheme_str.value(element) }.join($ ) ++ ")";
	}
	{ is_vector.value(obj) } {
		"#(" ++ obj['content'].collect { |element| scheme_str.value(element) }.join($ ) ++ ")";
	}
	{ is_hash.value(obj) } {
		var content = obj['content'];
		"#hash(" ++ content.keys.collect { |key| "(" ++ scheme_str.value(key) ++ " . " ++ scheme_str.value(content[key]) ++ ")" }.asArray.join($ ) ++ ")";
	}
	?? {
		Error("invalid obj: " ++ obj).throw;
	};
};

/*
utility functions
*/

var
is_boolean =
{ |obj|
	obj.isKindOf(Boolean)
};

var
is_number =
{ |obj|
	obj.isKindOf(Number)
};

var
is_sym =
{ |obj|
	obj.class == Symbol
};

var
is_chr =
{ |obj|
	obj.class == Char
};

var
is_str =
{ |obj|
	obj.class == String
};

var
is_procedure =
{ |obj|
	obj.class == Function;
};

var
is_list =
{ |obj|
	obj.class == Array
};

var
is_vector =
{ |obj|
	if (obj.class == Event) {
		obj['__type__'] == 'vector' // TODO: use parent or proto-table?
	} {
		false
	};
};

var
is_hash =
{ |obj|
	if (obj.class == Event) {
		obj['__type__'] == 'hash' // TODO: use parent or proto-table?
	} {
		false
	};
};

var
is_pair =
{ |obj|
	(obj.class == Array) and: (obj.size > 0) // TODO: not accurate
};

var
is_empty_list =
{ |obj|
	if (is_list.value(obj)) {
		obj.size == 0 // TODO: was set to 1, uhm?
	} {
		false
	};
};

/*
string scanner
...code is based upon StringScanner in the ruby standard library
*/

var
ss_new =
{ |str|
	IdentityDictionary[
		'pos' -> 0,
		'peekLength' -> 100,
		'str' -> str,
		'debug' -> false
	];
};

var
ss_matches =
{ |ss, regexp|
	// TODO var funcName = 'ss_matches';
	var match;
	match = ss_pr_find_regexp_directly_after_pos.(ss, regexp);
	match.notNil.if {
		if (ss['debug']) { "matched: '%'".format(match).debug };
		match.size
	} { nil }
};

var
ss_scan =
{ |ss, regexp|
	// TODO var funcName = 'ss_scan';
	var match;
	match = ss_pr_find_regexp_directly_after_pos.(ss, regexp);
	match.notNil.if {
		if (ss['debug']) { "scanned: '%'".format(match).debug };
		ss['pos'] = ss['pos'] + match.size;
		match
	} { nil }
};

var
ss_scan_until =
{ |ss, regexp|
	// TODO var funcName = 'ss_scan_until';
	var match_data;
	match_data = ss_pr_find_first_regexp_after_pos.(ss, regexp);
	match_data.notNil.if {
		ss['pos'] = ss['pos'] + match_data[0] + match_data[1].size;
		match_data[1]
	} { nil }
};

var
ss_skip =
{ |ss, regexp|
	// TODO var funcName = 'ss_skip';
	var match;
	match = ss_pr_find_regexp_directly_after_pos.(ss, regexp);
	match.notNil.if {
		if (ss['debug']) { "skipped: '%'".format(match).debug };
		ss['pos'] = ss['pos'] + match.size;
		match.size
	} { nil }
};

var
ss_skip_until =
{ |ss, regexp|
	// TODO var funcName = 'ss_skip_until';
	var match_data;
	match_data = ss_pr_find_first_regexp_after_pos(ss, regexp);
	match_data.notNil.if {
		ss['pos'] = ss['pos'] + match_data[0] + match_data[1].size;
		match_data[1].size
	} { nil }
};

var
ss_get_char =
{ |ss|
	// TODO var funcName = 'ss_get_char';
	var char;
	char = ss['str'][ss['pos']];
	ss['pos'] = ss['pos'] + 1;
	char
};

var
ss_reset =
{ |ss|
	// TODO var funcName = 'ss_reset';
	ss['pos'] = 0;
};

var
ss_eos =
{ |ss|
	// TODO var funcName = 'ss_eos';
	ss_at_end_of_string.(ss);
};

var
ss_bos =
{ |ss|
	// TODO var funcName = 'ss_bos';
	ss_at_beginning_of_string.(ss);
};

var
ss_at_end_of_string =
{ |ss|
	// TODO var funcName = 'ss_at_end_of_string';
	ss['pos'] == ss_pr_eos_pos.(ss);
};

var
ss_at_beginning_of_string =
{ |ss|
	// TODO var funcName = 'ss_at_beginning_of_string';
	ss['pos'] == 0;
};

var
ss_peek =
{ |ss|
	// TODO var funcName = 'ss_peek';
	ss['str'][ss['pos']..(ss['pos']+ss['peekLength']-1)]
};

var
ss_as_string =
{ |ss|
	// TODO var funcName = 'ss_as_string';
	"StringScanner" +
	ss_at_end_of_string.(ss).if {
		"fin"
	} {
		"%/%".format(ss['pos'], ss_pr_eos_pos.(ss)) +
		ss_at_beginning_of_string.(ss).if {
			"@" + ss_pr_after_pos.(ss).quote
		} {
			ss_pr_before_pos.(ss).quote + "@" + ss_pr_after_pos.(ss).quote
		}
	}
};

/*
stringscanner implementation (considered private)
*/

var
ss_pr_find_regexp_directly_after_pos =
{ |ss, regexp|
	// TODO var funcName = 'ss_pr_find_regexp_directly_after_pos';
	var match_data;
	match_data = ss_pr_find_first_regexp.(ss, ss['str'], regexp, ss['pos']);
	match_data.notNil.if {
		if (match_data[0] == ss['pos']) {
			match_data[1]
		} { nil }
	} { nil }
};

var
ss_pr_find_first_regexp_after_pos =
{ |ss, regexp|
	// TODO var funcName = 'ss_pr_find_first_regexp_after_pos';
	var match_data;
	match_data = ss_pr_find_first_regexp.(ss, ss['str'], regexp, ss['pos']);
	match_data.notNil.if { [match_data[0]-ss['pos'], match_data[1]] } { nil }
};

var
ss_pr_find_first_regexp =
{ |ss, str, regexp, offset|
	// TODO var funcName = 'ss_pr_find_first_regexp';
	str.findRegexp(regexp, ss['pos']).first
};

var
ss_pr_before_pos =
{ |ss|
	// TODO var funcName = 'ss_pr_before_pos';
	var start = max(0, ss['pos']-ss['peekLength']),
	end = ss['pos']-1;
	if (start <= 0) {""} {"..."} ++ ss['str'][start..end].asString
};

var
ss_pr_after_pos =
{ |ss|
	// TODO var funcName = 'ss_pr_after_pos';
	var start = ss['pos'],
	end = min(ss['str'].size-1, ss['pos']+ss['peekLength']-1);
	ss['str'][start..end].asString ++ if (end == (ss['str'].size-1)) {""} {"..."}
};

var
ss_pr_eos_pos =
{ |ss|
	// TODO var funcName = 'ss_pr_eos_pos';
	ss['str'].size;
};

/*
assertions
*/

var
assert_equal =
{ |a, b|
	if (a != b) {
		Error("assertion failed, expected a == b, actual % != %".format(a, b)).throw;
	};
};

var
assert_true =
{ |a|
	if (a != true) {
		Error("assertion failed, expected a == true, actual % != true".format(a)).throw;
	};
};

var
assert_false =
{ |a|
	if (a != false) {
		Error("assertion failed, expected a == false, actual % != false".format(a)).throw;
	};
};

run_tests.value;

repl.value;

'ok'
)
