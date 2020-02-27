--[[
an ad-hoc, informally-specified, bug-ridden, slow implementation of half of Common Lisp.

inspiration:
https://norvig.com/lispy.html
scheme r4rs @ https://people.csail.mit.edu/jaffer/r4rs_toc.html
dybvig's the scheme programming language: https://www.scheme.com/tspl2

TODO r4rs defines 146 essential procedures excluding additional car/cdr permutations

differences to r4rs:
no TCO. yet.
no support for macros (macros are not required in r4rs)
no call-cc
symbol case is significant
strings are immutable
quasiquote does not support nesting

]]

-- tests

local run_tests
local ss_test
local ss_as_string_test
local read_test
local run_applicable_r4rs_examples_as_tests

-- repl

local run_repl
local rep

-- standard environment

local init_ns_environment
local standard_procedures
local define_non_prim_standard_procedures 
local additional_procedures

-- read

local read
local parse
local expand
local expand_quasiquote 
local atom

-- eval

local eval
local make_env
local find_env

local char_prefix = "chr/"
local string_prefix = "str/"
local symbol_prefix = "sym/"

local is_boolean
local is_number
local is_sym
local is_chr
local is_str
local is_procedure
local is_list
local is_vector
local is_hash

local is_pair
local is_empty_list

local sym
local get_sym
local str
local get_str
local chr
local get_chr

local pair_mt = {}
local vector_mt = {}
local hash_mt = {}

-- print

local scheme_str

-- assertions

local assert_equal
local assert_true
local assert_false
local assert_error_thrown

-- utils

local pop_first
local put_all
local split

local map
local filter
local inject
local slice
local round
local table_includes
local begins_with
local print_table
local table_as_string
local table_as_string2
local quote
local tablesize
local deepcompare
local as_string
local find_regexp
local even
local odd

local invoke_function
local invoke_function_by_eval 

-- tests

run_tests = function()
  ss_test()
  ss_as_string_test()
  read_test()

  _NS_ENV = {}
  init_ns_environment(_NS_ENV)

  run_applicable_r4rs_examples_as_tests()
end

ss_test = function()
  local s
  s = ss_new("This is an example string");
  assert_equal( "This", ss_scan(s, "%w+") );
  assert_equal( nil, ss_scan(s, "%w+") );
  assert_equal( " ", ss_scan(s, "%s+") );
  assert_equal( nil, ss_scan(s, "%s+") );
  assert_equal( "is", ss_scan(s, "%w+") );
  assert_false( ss_eos(s) );

  assert_equal( " ", ss_scan(s, "%s+") );
  assert_equal( "an", ss_scan(s, "%w+") );
  assert_equal( " ", ss_scan(s, "%s+") );
  assert_equal( "example", ss_scan(s, "%w+") );
  assert_equal( " ", ss_scan(s, "%s+") );
  assert_equal( "string", ss_scan(s, "%w+") );
  assert_true( ss_eos(s) );

  assert_equal( nil, ss_scan(s, "%w+") );
  assert_equal( nil, ss_scan(s, "%s+") );
end

ss_as_string_test = function()
  local abc = ss_new("test string 42134")
  assert_equal("1/18 @ \"test string 42134\"", ss_as_string(abc))
  assert_equal(4, ss_matches(abc, "%S+"))
  assert_equal("1/18 @ \"test string 42134\"", ss_as_string(abc))
  ss_skip(abc, "%S+")
  assert_equal("5/18 \"test\" @ \" string 42134\"", ss_as_string(abc))
end

read_test = function()
  assert_equal(0, read("0"))
  assert_equal(732, read("732"))
  assert_equal(-1, read("-001"))
  assert_equal(732, read("732.0"))
  assert_equal(732.01, read("732.01"))

  assert_equal(str("abc"), read("\"abc\""))
  assert_equal(sym("abc"), read("abc"))
  assert_equal(true, read("#t"))
  assert_equal(false, read("#f"))
  assert_equal(chr("c"), read("#\\c"))

  assert_equal({5, 2}, read("(5 2)"))
  assert_equal({sym("+"), 2, 9}, read("(+ 2 9)"))
  assert_equal({sym("+"), 5, {sym("*"), 9, 9}}, read("(+ 5 (* 9 9))"))
  assert_equal({sym("define"), sym("my-var"), {sym("lambda"), {sym("x")}, {sym("*"), sym("x"), sym("x")}}}, read("(define my-var (lambda (x) (* x x)))"))
  --[[
  --TODO
  assert_equal(1, read("(+ 4))(+ 1)"))
  assert_equal(1, read(")(+ 1)"))
  -- TODO assert_error_thrown("parse error: unexpected token at 5/18 \"test\" @ \" string 42134\"", read("(+ 4))(+ 1)"))
  ]]

end

run_applicable_r4rs_examples_as_tests = function()
  local r4rs_examples = 0

  local test = function(str)
    r4rs_examples = r4rs_examples + 1
    return read_eval(str, _NS_ENV)
  end

--[[
  1. Overview of Scheme
  1.3.4. Evaluation examples
]]
  assert_equal(40, test("(* 5 8)"))

--[[
  2.2 Whitespace and comments
]]

  assert_no_error_thrown(function()
    test([[
;;; The FACT procedure computes the factorial
;;; of a non-negative integer.
(define fact
  (lambda (n)
    (if (= n 0)
        1 ; Base case: return 1
        (* n (fact (- n 1))))))
    ]])
  end)

--[[
  3.4 Disjointness of types

  No object satisfies more than one of the following predicates:

    boolean?
    symbol?
    char?
    vector?
    pair?
    number?
    string?
    procedure?

  These predicates define the types boolean, pair, symbol,
  number, char (or character), string, vector, and procedure.
]]
  assert_equal(true, test("(boolean? #t)"))
  assert_equal(false, test("(symbol? #t)"))
  assert_equal(false, test("(char? #t)"))
  assert_equal(false, test("(vector? #t)"))
  assert_equal(false, test("(pair? #t)"))
  assert_equal(false, test("(number? #t)"))
  assert_equal(false, test("(string? #t)"))
  assert_equal(false, test("(procedure? #t)"))

  assert_equal(false, test("(boolean? 'a-symbol)"))
  assert_equal(true, test("(symbol? 'a-symbol)"))
  assert_equal(false, test("(char? 'a-symbol)"))
  assert_equal(false, test("(vector? 'a-symbol)"))
  assert_equal(false, test("(pair? 'a-symbol)"))
  assert_equal(false, test("(number? 'a-symbol)"))
  assert_equal(false, test("(string? 'a-symbol)"))
  assert_equal(false, test("(procedure? 'a-symbol)"))

  assert_equal(false, test("(boolean? #\\a)"))
  assert_equal(false, test("(symbol? #\\a)"))
  assert_equal(true, test("(char? #\\a)"))
  assert_equal(false, test("(vector? #\\a)"))
  assert_equal(false, test("(pair? #\\a)"))
  assert_equal(false, test("(number? #\\a)"))
  assert_equal(false, test("(string? #\\a)"))
  assert_equal(false, test("(procedure? #\\a)"))

  assert_equal(false, test("(boolean? (vector 1 3 6))"))
  assert_equal(false, test("(symbol? (vector 1 3 6))"))
  assert_equal(false, test("(char? (vector 1 3 6))"))
  assert_equal(true, test("(vector? (vector 1 3 6))"))
  assert_equal(false, test("(pair? (vector 1 3 6))"))
  assert_equal(false, test("(number? (vector 1 3 6))"))
  assert_equal(false, test("(string? (vector 1 3 6))"))
  assert_equal(false, test("(procedure? (vector 1 3 6))"))

  assert_equal(false, test("(boolean? (cons 1 2))"))
  assert_equal(false, test("(symbol? (cons 1 2))"))
  assert_equal(false, test("(char? (cons 1 2))"))
  assert_equal(false, test("(vector? (cons 1 2))"))
  assert_equal(true, test("(pair? (cons 1 2))"))
  assert_equal(false, test("(number? (cons 1 2))"))
  assert_equal(false, test("(string? (cons 1 2))"))
  assert_equal(false, test("(procedure? (cons 1 2))"))

  assert_equal(false, test("(boolean? 79)"))
  assert_equal(false, test("(symbol? 79)"))
  assert_equal(false, test("(char? 79)"))
  assert_equal(false, test("(vector? 79)"))
  assert_equal(false, test("(pair? 79)"))
  assert_equal(true, test("(number? 79)"))
  assert_equal(false, test("(string? 79)"))
  assert_equal(false, test("(procedure? 79)"))

  assert_equal(false, test("(boolean? \"a string\")"))
  assert_equal(false, test("(symbol? \"a string\")"))
  assert_equal(false, test("(char? \"a string\")"))
  assert_equal(false, test("(vector? \"a string\")"))
  assert_equal(false, test("(pair? \"a string\")"))
  assert_equal(false, test("(number? \"a string\")"))
  assert_equal(true, test("(string? \"a string\")"))
  assert_equal(false, test("(procedure? \"a string\")"))

  assert_equal(false, test("(boolean? (lambda (x) (* x x)))"))
  assert_equal(false, test("(symbol? (lambda (x) (* x x)))"))
  assert_equal(false, test("(char? (lambda (x) (* x x)))"))
  assert_equal(false, test("(vector? (lambda (x) (* x x)))"))
  assert_equal(false, test("(pair? (lambda (x) (* x x)))"))
  assert_equal(false, test("(number? (lambda (x) (* x x)))"))
  assert_equal(false, test("(string? (lambda (x) (* x x)))"))
  assert_equal(true, test("(procedure? (lambda (x) (* x x)))"))

  --[[
  4.1.1 Variable references

  An expression consisting of a variable (section 3.1) is a
  variable reference. The value of the variable reference is
  the value stored in the location to which the variable is
  bound. It is an error to reference an unbound variable.
  ]]

  assert_equal(nil, test("(define x 28)"))
  assert_equal(28, test("x"))

  --[[
  4.1.2 Literal expressions

  (quote <datum>) evaluates to <datum>. <Datum> may be
  any external representation of a Scheme object (see sec-
  tion 3.3). This notation is used to include literal constants
  in Scheme code.
  ]]

  assert_equal(sym("a"), test("(quote a)"))
  assert_equal({sym("vector"), sym("a"), sym("b"), sym("c")}, test("(quote (vector a b c))")) --TODO: (quote #(a b c)) // ==>  #(a b c)
  assert_equal({sym("+"), 1, 2}, test("(quote (+ 1 2))"))

  --[[
  (quote <datum>) may be abbreviated as ’<datum>. The
  two notations are equivalent in all respects.
  ]]

  assert_equal(sym("a"), test("'a"))
  assert_equal({sym("vector"), sym("a"), sym("b"), sym("c")}, test("'(vector a b c)")) --TODO: '#(a b c) // ==>  #(a b c)
  assert_equal({}, test("'()"))
  assert_equal({sym("+"), 1, 2}, test("'(+ 1 2)"))
  assert_equal({sym("quote"), sym("a")}, test("'(quote a)"))
  assert_equal({sym("quote"), sym("a")}, test("''a"))

  --[[
  Numerical constants, string constants, character constants,
  and boolean constants evaluate “to themselves”; they need
  not be quoted.
  ]]

  assert_equal(str("abc"), test("'\"abc\""))
  assert_equal(str("abc"), test("\"abc\""))
  assert_equal(145932, test("'145932"))
  assert_equal(145932, test("145932"))
  assert_equal(true, test("'#t"))
  assert_equal(true, test("#t"))

  --[[
  4.1.3 Procedure calls

  A procedure call is written by simply enclosing in parentheses expressions for the procedure to be called and the arguments to be passed to it. The operator and operand expressions are evaluated (in an unspecified order) and the resulting procedure is passed the resulting arguments.
  ]]

  assert_equal(7, test("(+ 3 4)"))
  assert_equal(12, test("((if #f + *) 3 4)"))

  --[[
  4.1.4 Lambda expressions
  ]]

  assert_equal("function", type(test("(lambda (x) (+ x x))"))) -- (lambda (x) (+ x x)) //  ==>  a procedure
  assert_equal(8, test("((lambda (x) (+ x x)) 4)"))
  test([[
    (define reverse-subtract
      (lambda (x y) (- y x)))
  ]])
  assert_equal(3, test("(reverse-subtract 7 10)"))

  test([[
  (define add4
    (let ((x 4))
      (lambda (y) (+ x y))))
  ]])
  assert_equal(10, test("(add4 6)"))

  assert_equal({3, 4, 5, 6}, test("((lambda x x) 3 4 5 6)"))

  --TODO
  --assert_equal({5, 6}, test([[
  --((lambda (x y . z) x)
  --  3 4 5 6)
  --]]))

  --[[
  4.1.5 Conditionals
  ]]

  assert_equal(sym("yes"), test("(if (> 3 2) 'yes 'no)"))
  assert_equal(sym("no"), test("(if (> 2 3) 'yes 'no)"))
  assert_equal(1, test([[
  (if (> 3 2)
      (- 3 2)
      (+ 3 2))
  ]]))

  --[[
  4.1.6 Assignments
  ]]

  test("(define x 2)")
  assert_equal(3, test("(+ x 1)"))
  assert_equal(nil, test("(set! x 4)")) -- (set! x 4) // ==>  unspecified
  assert_equal(5, test("(+ x 1)"))


  --[[
  4.2.1 Conditionals

  essential syntax: cond <clause1> <clause2> ...
  ]]

  assert_equal(sym("greater"), test([[
    (cond ((> 3 2) 'greater)
          ((< 3 2) 'less))
  ]]))

  assert_equal(sym("equal"), test([[
    (cond ((> 3 3) 'greater)
          ((< 3 3) 'less)
          (else 'equal))
  ]]))

  -- TODO: => undefined
  --assert_equal(2, test([[
  --  (cond ((assv 'b '((a 1) (b 2))) => cadr)
  --        (else #f))
  --]]))

  --[[
  essential syntax: case <key> <clause1> <clause2> ...
  ]]

  assert_equal(sym("composite"), test([[
    (case (* 2 3)
      ((2 3 5 7) 'prime)
      ((1 4 6 8 9) 'composite))
  ]]))

  assert_equal(nil, test([[
    (case (car '(c d))
      ((a) 'a)
      ((b) 'b))
  ]]))

  assert_equal(sym("consonant"), test([[
    (case (car '(c d))
      ((a e i o u) 'vowel)
      ((w y) 'semivowel)
      (else 'consonant))
  ]]))

  --[[
  essential syntax: and <test1> ...
  ]]

  assert_equal(true, test("(and (= 2 2) (> 2 1))"))
  assert_equal(false, test("(and (= 2 2) (< 2 1))"))
  assert_equal({sym("f"), sym("g")}, test("(and 1 2 'c '(f g))"))
  assert_equal(true, test("(and)"))

  --[[
  essential syntax: or <test1> ...
  ]]

  assert_equal(true, test("(or (= 2 2) (> 2 1))"))
  assert_equal(true, test("(or (= 2 2) (< 2 1))"))
  assert_equal(false, test("(or #f #f #f)"))
  assert_equal({sym("b"), sym("c")}, test([[
    (or (memq 'b '(a b c))
        (/ 3 0))
  ]]))

  --[[
  4.2.2 Binding constructs
  ]]

  assert_equal(6, test([[
    (let ((x 2) (y 3))
      (* x y))
  ]]))

  assert_equal(35, test([[
    (let ((x 2) (y 3))
      (let ((x 7)
            (z (+ x y)))
        (* z x)))
  ]]))

  assert_equal(70, test([[
    (let ((x 2) (y 3))
      (let* ((x 7)
             (z (+ x y)))
        (* z x)))
  ]]))

  --TODO: letrec
  --assert_equal(true, test([[
  --  (letrec ((even?
  --            (lambda (n)
  --              (if (zero? n)
  --                  #t
  --                  (odd? (- n 1)))))
  --           (odd?
  --            (lambda (n)
  --              (if (zero? n)
  --                  #f
  --                  (even? (- n 1))))))
  --    (even? 88))
  --]]))

  --[[
  4.2.3 Sequencing
  ]]
  test("(define x 0)")

  assert_equal(6, test([[
    (begin (set! x 5)
           (+ x 1))
  ]]))

  -- TODO: strings with whitespace, asserting text output
  --assert_equal(6, test([[
  --  (begin (display "4 plus 1 equals ")
  --         (display (+ 4 1))) // ==>  unspecified and prints  4 plus 1 equals 5
  --]]))

  --[[
  4.2.4 Iteration
  ]]

  -- TODO: do
  --local vector = test([[
  --  (do ((vec (make-vector 5))
  --       (i 0 (+ i 1)))
  --      ((= i 5) vec)
  --    (vector-set! vec i i))
  --]])
  --assert_equal({0, 1, 2, 3, 4}, vector)
  --assert_equal(vector_mt, getmetatable(vector))

  -- TODO: do
  --assert_equal(25, test([[
  --  (let ((x '(1 3 5 7 9)))
  --    (do ((x x (cdr x))
  --         (sum 0 (+ sum (car x))))
  --        ((null? x) sum)))
  --]]))

  -- TODO: named let
  --assert_equal({{6, 1, 3}, {-5, -2}}, test([[
  --  (let loop ((numbers '(3 -2 1 6 -5))
  --             (nonneg '())
  --             (neg '()))
  --    (cond ((null? numbers) (list nonneg neg))
  --          ((>= (car numbers) 0)
  --           (loop (cdr numbers)
  --                 (cons (car numbers) nonneg)
  --                 neg))
  --          ((< (car numbers) 0)
  --           (loop (cdr numbers)
  --                 nonneg
  --                 (cons (car numbers) neg)))))
  --]]))

  --[[
  4.2.6 Quasiquotation
  ]]

  assert_equal({sym("list"), 3, 4}, test("`(list ,(+ 1 2) 4)"))
  assert_equal(
    {sym("list"), sym("a"), {sym("quote"), sym("a")}},
    test("(let ((name 'a)) `(list ,name ',name))")
  )

  -- TODO
  --assert_equal(
  --  {sym("a"), 3, 4, 5, 6, sym("b")},
  --  test("`(a ,(+ 1 2) ,@(map abs '(4 -5 6)) b)")
  --)

  -- TODO: dotted pairs
  -- `((foo ,(- 10 3)) ,@(cdr '(c)) . ,(car '(cons)))
  -- ==>  ((foo 7) . cons)
  --local pair = test([[
  --  `((foo ,(- 10 3)) ,@(cdr '(c)) . ,(car '(cons)))
  --]])
  --assert_equal(
  --  true,
  --  is_pair(pair)
  --)
  --assert_equal(
  --  {{sym("foo"), 7}, sym("cons")},
  --  pair
  --)

  -- TODO: # vs vector
  -- TODO: quotes as (vector
  -- `#(10 5 ,(sqrt 4) ,@(map sqrt '(16 9)) 8)
  -- ==>  #(10 5 2 4 3 8)
  -- TODO
  --assert_equal(
  --  {sym("vector"), 10, 5, 2, 4, 3, 8},
  --  test("`(vector 10 5 ,(sqrt 4) ,@(map sqrt '(16 9)) 8)")
  --)

  -- TODO
  -- `(a `(b ,(+ 1 2) ,(foo ,(+ 1 3) d) e) f)
  -- ==>  (a `(b ,(+ 1 2) ,(foo 4 d) e) f)

  -- TODO
  -- (let ((name1 'x)
  --       (name2 'y))
  --   `(a `(b ,,name1 ,',name2 d) e))
  -- ==>  (a `(b ,x ,'y d) e)

  -- TODO
  -- (quasiquote (list (unquote (+ 1 2)) 4))
  -- ==>  (list 3 4)

  -- TODO
  -- '(quasiquote (list (unquote (+ 1 2)) 4))
  -- ==>  `(list ,(+ 1 2) 4) // TODO
  --     i.e., (quasiquote (list (unquote (+ 1 2)) 4))

  --[[
  5.2.1 Top level definitions
  ]]

  test([[
    (define add3
      (lambda (x) (+ x 3)))
  ]])
  assert_equal(6, test("(add3 3)"))

  test("(define first car)")
  assert_equal(1, test("(first '(1 2))"))

  --[[
  5.2.2 Internal definitions
  ]]

  -- TODO: letrec
  --test([[
  --  (let ((x 5))
  --    (letrec ((foo (lambda (y) (bar x y)))
  --             (bar (lambda (a b) (+ (* a b) a))))
  --      (foo (+ x 3))))
  --]])

  --[[
  6.1 Booleans
  ]]

  assert_equal(true, test("#t"))
  assert_equal(false, test("#f"))
  assert_equal(false, test("'#f"))

  assert_equal(false, test("(not #t)"))
  assert_equal(false, test("(not 3)"))
  assert_equal(false, test("(not (list 3))"))
  assert_equal(true, test("(not #f)"))
  assert_equal(false, test("(not '())"))
  assert_equal(false, test("(not (list))"))
  assert_equal(false, test("(not (quote nil))"))

  assert_equal(true, test("(boolean? #f)"))
  assert_equal(false, test("(boolean? 0)"))
  assert_equal(false, test("(boolean? '())"))

  --[[
  6.2 Equivalence predicates

  essential procedure: eqv? obj1 obj2
  ]]


  assert_equal(true, test("(eqv? 'a 'a)"))
  assert_equal(false, test("(eqv? 'a 'b)"))
  assert_equal(true, test("(eqv? 2 2)"))
  assert_equal(true, test("(eqv? '() '())"))
  assert_equal(true, test("(eqv? 100000000 100000000)"))
  assert_equal(false, test("(eqv? (cons 1 2) (cons 1 2))"))
  assert_equal(false, test([[
    (eqv? (lambda () 1)
          (lambda () 2))
  ]]))
  assert_equal(false, test("(eqv? #f 'nil)"))
  assert_equal(true, test([[
    (let ((p (lambda (x) x)))
      (eqv? p p))
  ]]))
  assert_no_error_thrown(function()
    test("(eqv? \"\" \"\")")
  end) -- ==>  unspecified
  -- TODO vector # assert_no_error_thrown(function() test("(eqv? '#() '#())") end) -- ==>  unspecified
  assert_no_error_thrown(function()
    test([[
      (eqv? (lambda (x) x)
            (lambda (x) x)) 
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (eqv? (lambda (x) x)
            (lambda (y) y))
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (define gen-counter
        (lambda ()
          (let ((n 0))
            (lambda () (set! n (+ n 1)) n))))
    ]])
  end)

  assert_equal(true, test([[
    (let ((g (gen-counter)))
      (eqv? g g))
  ]]))

  assert_equal(false, test([[
    (eqv? (gen-counter) (gen-counter))
  ]]))

  assert_no_error_thrown(function()
    test([[
      (define gen-loser
        (lambda ()
          (let ((n 0))
            (lambda () (set! n (+ n 1)) 27))))
    ]])
  end)

  assert_equal(true, test([[
    (let ((g (gen-loser)))
      (eqv? g g))
  ]]))

  assert_no_error_thrown(function()
    test([[
      (eqv? (gen-loser) (gen-loser))
    ]])
  end) -- ==>  unspecified

  --[[
    (letrec ((f (lambda () (if (eqv? f g) 'both 'f))) // TODO
             (g (lambda () (if (eqv? f g) 'both 'g)))
      (eqv? f g))

    )
    // ==>  unspecified

    (letrec ((f (lambda () (if (eqv? f g) 'f 'both))) // TODO
             (g (lambda () (if (eqv? f g) 'g 'both)))
      (eqv? f g))

    )
    // ==>  #f
  ]]

  assert_no_error_thrown(function()
    test([[
      (eqv? '(a) '(a))
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (eqv? "a" "a")
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (eqv? '(b) (cdr '(a b)))
    ]])
  end) -- ==>  unspecified

  assert_equal(true, test([[
    (let ((x '(a)))
      (eqv? x x))
  ]]))

  --[[
  r4rs essential procedure: eq? obj1 obj2
  ]]

  assert_equal(true, test([[
    (eq? 'a 'a)
  ]]))

  assert_no_error_thrown(function()
    test([[
      (eq? '(a) '(a))
    ]])
  end) -- ==>  unspecified

  assert_equal(false, test([[
    (eq? (list 'a) (list 'a))
  ]]))

  assert_no_error_thrown(function()
    test([[
      (eq? "a" "a")
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (eq? "" "")
    ]])
  end) -- ==>  unspecified

  assert_equal(true, test([[
    (eq? '() '())
  ]]))

  assert_no_error_thrown(function()
    test([[
      (eq? 2 2)
    ]])
  end) -- ==>  unspecified

  assert_no_error_thrown(function()
    test([[
      (eq? #\A #\A)
    ]])
  end) -- ==>  unspecified

  assert_equal(true, test([[
    (eq? car car)
  ]]))

  assert_no_error_thrown(function()
    test([[
      (let ((n (+ 2 3)))
        (eq? n n))
    ]])
  end) -- ==>  unspecified

  assert_equal(true, test([[
    (let ((x '(a)))
      (eq? x x))
  ]]))

  -- TODO: vector #
  --assert_equal(true, test([[
  --  (let ((x '#()))
  --    (eq? x x))
  --]]))

  assert_equal(true, test([[
    (let ((p (lambda (x) x)))
      (eq? p p))
  ]]))

  --[[
  essential procedure: equal? obj1 obj2
  ]]

  assert_equal(true, test([[
    (equal? 'a 'a)
  ]]))

  assert_equal(true, test([[
    (equal? '(a) '(a))
  ]]))

  assert_equal(true, test([[
    (equal? '(a (b) c)
            '(a (b) c))
  ]]))

  assert_equal(true, test([[
    (equal? "abc" "abc")
  ]]))

  assert_equal(true, test([[
    (equal? 2 2)
  ]]))

  assert_equal(true, test([[
    (equal? (make-vector 5 'a)
            (make-vector 5 'a))
  ]]))

  assert_no_error_thrown(function()
    test([[
      (equal? (lambda (x) x)
              (lambda (y) y))
    ]])
  end) -- ==>  unspecified

  --[[
  6.3 Pairs and lists
  ]]

  assert_no_error_thrown(function()
    test([[
      (define x (list 'a 'b 'c))
    ]])
  end)

  assert_no_error_thrown(function()
    test([[
      (define y x)
    ]])
  end)

  assert_equal({sym("a"), sym("b"), sym("c")}, test("y"))
  assert_equal(true, test("(list? y)"))

  -- TODO: set-cdr!
  --assert_no_error_thrown(function()
  --  test([[
  --    (set-cdr! x 4)
  --  ]])
  --end) -- ==>  unspecified

  -- TODO dotted pair x // ==>  (a . 4)
  
  --assert_equal(true, test("(eqv? x y)"))

  -- TODO dotted pair y // ==>  (a . 4)

  --assert_equal(false, test("(list? y)"))

  -- TODO: set-cdr!
  --assert_no_error_thrown(function()
  --  test([[
  --    (set-cdr! x x)
  --  ]])
  --end) -- ==>  unspecified

  --assert_equal(false, test("(list? x)"))

  --[[
  essential procedure: pair? obj
  ]]

  -- TODO dotted pair assert_equal(true, test("(pair? '(a . b))"))
  assert_equal(true, test("(pair? '(a b c))"))
  assert_equal(false, test("(pair? '())"))
  -- TODO: vector # assert_equal(false, test("(pair? '#(a b))"))

  --[[
  essential procedure: cons obj1 obj2
  ]]

  assert_equal({sym("a")}, test("(cons 'a '())"))
  assert_equal({{sym("a")}, sym("b"), sym("c"), sym("d")}, test("(cons '(a) '(b c d))"))
  assert_equal({str("a"), sym("b"), sym("c")}, test("(cons \"a\" '(b c))"))
  --(cons 'a 3) // ==>  (a . 3) TODO: dotted pair
  --(cons '(a b) 'c) // ==>  ((a b) . c) TODO: dotted pair

  --[[
  essential procedure: car pair
  ]]

  assert_equal(sym("a"), test("(car '(a b c))"))
  assert_equal({sym("a")}, test("(car '((a) b c d))"))
  --(car '(1 . 2))                         ==>  1 TODO: dotted pair
  --TODO: error
  --assert_error_thrown(function()
  --  test("(car '())")
  --end)

  --[[
  essential procedure: cdr pair
  ]]
  assert_equal({sym("b"), sym("c"), sym("d")}, test("(cdr '((a) b c d))"))
  -- TODO: dotted pair (cdr '(1 . 2))                         ==>  2
  -- TODO: error (cdr '())                              ==>  error TODO

  --[[
  essential procedure: set-car! pair obj
  ]]

  assert_no_error_thrown(function()
    test([[
      (define (f) (list 'not-a-constant-list))
    ]])
  end)

  assert_no_error_thrown(function()
    test([[
      (define (g) '(constant-list))
    ]])
  end)

  -- TODO: set-car!
  -- assert_no_error_thrown(function()
  --  test([[
  --    (set-car! (f) 3)
  --  ]])
  --end) -- ==>  unspecified

  -- TODO: set-car!
  -- assert_error_thrown(function()
  --  test([[
  --    (set-car! (g) 3)
  --  ]])
  --end)

  --[[
  essential procedure: caar pair
  essential procedure: cadr pair
  ...
  essential procedure: cdddar pair
  essential procedure: cddddr pair
  ]]

  assert_no_error_thrown(function()
    test([[
      (define caddr (lambda (x) (car (cdr (cdr x)))))
    ]])
  end)

  --[[
  essential procedure: list? obj
  ]]

  assert_equal(true, test("(list? '(a b c))"))
  assert_equal(true, test("(list? '())"))
  -- TODO: dotted pair assert_equal(false, test("(list? '(a . b))"))
  
  -- TODO: set-cdr!
  --assert_equal(false, test([[
  --  (let ((x (list 'a)))
  --    (set-cdr! x x)
  --    (list? x)) // ==>  #f
  --]])

  --[[
  essential procedure: list obj ...
  ]]

  assert_equal({sym("a"), 7, sym("c")}, test("(list 'a (+ 3 4) 'c)"))
  assert_equal({}, test("(list)"))

  --[[
  essential procedure: length list
  ]]

  assert_equal(3, test("(length '(a b c))"))
  assert_equal(3, test("(length '(a (b) (c d e)))"))
  assert_equal(0, test("(length '())"))

  --[[
  essential procedure: append list ...
  ]]

  assert_equal({sym("x"), sym("y")}, test("(append '(x) '(y))"))
  assert_equal({sym("a"), sym("b"), sym("c"), sym("d")}, test("(append '(a) '(b c d))"))
  assert_equal({sym("a"), {sym("b")}, {sym("c")}}, test("(append '(a (b)) '((c)))"))
  -- TODO: dotted pair (append '(a b) '(c . d)) // ==>  (a b c . d)
  --assert_equal(sym("a"), test("(append '() 'a)")) --TODO: (append '() 'a) // ==>  a

  --[[
  essential procedure: reverse list
  ]]

  assert_equal({sym("c"), sym("b"), sym("a")}, test("(reverse '(a b c))"))
  assert_equal({{sym("e"), {sym("f")}}, sym("d"), {sym("b"), sym("c")}, sym("a")}, test("(reverse '(a (b c) d (e (f))))"))

  --[[
  procedure: list-tail list k
  ]]

  assert_no_error_thrown(function()
    test([[
      (define list-tail
        (lambda (x k)
          (if (zero? k)
              x
              (list-tail (cdr x) (- k 1)))))
    ]])
  end)

  --[[
  essential procedure: list-ref list k
  ]]

  assert_equal(sym("c"), test("(list-ref '(a b c d) 2)"))

  -- TODO: inexact->exact
  --assert_equal(sym("c"), test([[
  --  (list-ref '(a b c d)
  --            (inexact->exact (round 1.8)))
  --]]))

  --[[
  essential procedure: memq obj list
  essential procedure: memv obj list
  essential procedure: member obj list
  ]]

  assert_equal({sym("a"), sym("b"), sym("c")}, test("(memq 'a '(a b c))"))
  assert_equal({sym("b"), sym("c")}, test("(memq 'b '(a b c))"))
  assert_equal(false, test("(memq 'a '(b c d))"))
  assert_equal(false, test("(memq (list 'a) '(b (a) c))"))
  assert_equal({{sym("a")}, sym("c")}, test([[
    (member (list 'a)
            '(b (a) c))
  ]]))
  assert_no_error_thrown(function()
    test([[
      (memq 101 '(100 101 102))
      (define list-tail
        (lambda (x k)
          (if (zero? k)
              x
              (list-tail (cdr x) (- k 1)))))
    ]])
  end) -- ==>  unspecified
  assert_equal({101, 102}, test("(memv 101 '(100 101 102))"))

  --[[
  essential procedure: assq obj alist
  essential procedure: assv obj alist
  essential procedure: assoc obj alist
  ]]

  assert_no_error_thrown(function()
    test([[
      (define e '((a 1) (b 2) (c 3)))
    ]])
  end)

  assert_equal({sym("a"), 1}, test("(assq 'a e)"))
  assert_equal({sym("b"), 2}, test("(assq 'b e)"))
  assert_equal(false, test("(assq 'd e)"))
  assert_equal(false, test("(assq (list 'a) '(((a)) ((b)) ((c))))"))
  assert_equal({{sym("a")}}, test("(assoc (list 'a) '(((a)) ((b)) ((c))))"))

  assert_no_error_thrown(function()
    test([[
      (assq 5 '((2 3) (5 7) (11 13)))
    ]])
  end) -- ==>  unspecified

  assert_equal({5, 7}, test("(assv 5 '((2 3) (5 7) (11 13)))"))

  --[[
  6.4 Symbols

  essential procedure: symbol? obj
  ]]

  assert_equal(true, test("(symbol? 'foo)"))
  assert_equal(true, test("(symbol? (car '(a b)))"))
  assert_equal(false, test("(symbol? \"bar\")"))
  assert_equal(true, test("(symbol? 'nil)"))
  assert_equal(false, test("(symbol? '())"))
  assert_equal(false, test("(symbol? #f)"))

  --[[
  essential procedure: symbol->string symbol
  ]]

  assert_equal(str("flying-fish"), test("(symbol->string 'flying-fish)"))
  -- TODO: case insensitivity? assert_equal(str("martin"), test("(symbol->string 'Martin)"))
  assert_equal(str("Malvina"), test([[
    (symbol->string
       (string->symbol "Malvina"))
  ]]))

  --[[
  essential procedure: string->symbol string
  ]]

  -- diverges from r4rs: case is significant
  assert_equal(false, test([[
    (eq? 'mISSISSIppi 'mississippi)
  ]]))

  assert_equal(sym("mISSISSIppi"), test([[
    (string->symbol "mISSISSIppi")
  ]]))

  -- diverges from r4rs: case is significant
  assert_equal(true, test([[
    (eq? 'bitBlt (string->symbol "bitBlt"))
  ]]))

  assert_equal(true, test([[
    (eq? 'JollyWog
         (string->symbol
           (symbol->string 'JollyWog)))
  ]]))

  assert_equal(true, test([[
    (string=? "K. Harper, M.D."
              (symbol->string
                (string->symbol "K. Harper, M.D.")))
  ]]))

  --[[
  6.5 Numbers
  ]]

  --TODO


  --[[
  6.6 Characters
  ]]

  -- #\a ; lower case letter
  assert_equal(
    chr("a"),
    test([[
      #\a
    ]])
  )

  -- #\A ; upper case letter
  assert_equal(
    chr("A"),
    test([[
      #\A
    ]])
  )

  -- #\( ; left parenthesis
  assert_equal(
    chr("("),
    test([[
      #\(
    ]])
  )

  -- #\ ; the space character
  assert_equal(
    chr(" "),
    test([[
      #\ 
    ]])
  )

  -- #\space ; the preferred way to write a space
  assert_equal(
    chr(" "),
    test([[
      #\space
    ]])
  )

  -- #\newline ; the newline character
  assert_equal(
    chr("\n"),
    test([[
      #\newline
    ]])
  )

  --[[
  essential procedure: char->integer char
  essential procedure: integer->char n
  ]]

  assert_equal(true, test("(char<? #\\A #\\B)"))
  assert_equal(true, test("(char<? #\\a #\\b)"))
  assert_equal(true, test("(char<? #\\0 #\\9)"))

  assert_equal(true, test("(char-ci=? #\\A #\\a)"))

  --[[
  (char->integer char) essential procedure
  (integer->char n) essential procedure
  ]]

  test("(define a #\\a)")
  test("(define b #\\b)")
  test("(define x 97)")
  test("(define y 98)")

  assert_equal(true, test("(char<=? a b)"))
  assert_equal(true, test("(<= x y)"))

  assert_equal(true, test([[
    (<= (char->integer a)
        (char->integer b))
  ]]))

  assert_equal(true, test([[
    (char<=? (integer->char x)
             (integer->char y))
  ]]))

  --[[
  6.7 Strings
  ]]

  --TODO: quoted characters are not supported yet
  --assert_equal(
  --  str("The word \"recursion\" has many meanings."),
  --  test([[
  --    "The word \"recursion\" has many meanings."
  --  ]])
  --)

  --[[
  essential procedure: string-set! string k char
  ]]

  --[[
  TODO: strings are immutable

    (define (f) (make-string 3 #\*))
    (define (g) "***")
    (string-set! (f) 0 #\?)                ==>  unspecified
    (string-set! (g) 0 #\?)                ==>  error
    (string-set! (symbol->string 'immutable)
                 0
                 #\?)                      ==>  error
  ]]

  --[[
  6.8 Vectors
  ]]

  --TODO: vector #
  --local vector = test([[
  --  '#(0 (2 2 2 2) "Anna")
  --]])
  ---- ==> #(0 (2 2 2 2) "Anna")

  local vector = test([[
    '(vector 0 (2 2 2 2) "Anna")
  ]])

  assert_equal(
    {sym("vector"), 0, {2, 2, 2, 2}, str("Anna")},
    vector
  )

  -- TODO: metatable check?
  --assert_equal(
  --  vector_mt,
  --  getmetatable(vector)
  --)

  --[[
  essential procedure: vector-ref vector k
  ]]

  --[[ TODO: vector #
    (vector-ref '#(1 1 2 3 5 8 13 21)
                5)
    ==>  8
    (vector-ref '#(1 1 2 3 5 8 13 21)
                (inexact->exact
                  (round (* 2 (acos -1)))))
    ==> 13
  ]]

  -- TODO: vector-ref, inexact->exact, acos
  --assert_equal(
  --  8,
  --  test([[
  --    (vector-ref (vector 1 1 2 3 5 8 13 21)
  --                5)
  --  ]])
  --)

  -- TODO: vector-ref, inexact->exact, acos
  --assert_equal(
  --  13,
  --  test([[
  --    (vector-ref (vector 1 1 2 3 5 8 13 21)
  --                (inexact->exact
  --                  (round (* 2 (acos -1)))))
  --  ]])
  --)

  --[[
  essential procedure: vector-set! vector k obj
  ]]

  -- TODO: vector-set!
  --assert_equal(
  --  {sym("vector"), 0, {str("Sue"), str("Sue")}, str("Anna")},
  --  test([[
  --    (let ((vec (vector 0 '(2 2 2 2) "Anna")))
  --      (vector-set! vec 1 '("Sue" "Sue"))
  --      vec)
  --  ]])
  --)
  -- ==>  #(0 ("Sue" "Sue") "Anna") TODO: vector #

  -- TODO vector #, constant vector
  --assert_error_thrown(function()
  --  test([[
  --    (vector-set! '#(0 1 2) 1 "doe")
  --  ]])
  --end) -- ==>  error  ; constant vector

  --[[
  essential procedure: vector->list vector
  essential procedure: list->vector list
  ]]

  --assert_equal(
  --  {sym("dah"), sym("dah"), sym("didah")},
  --  test([[
  --    (vector->list '#(dah dah didah))
  --  ]])
  --)

  -- TODO: vector #
  --assert_equal(
  --  {sym("vector"), sym("dididit"), sym("dah")},
  --  test([[
  --    (list->vector '(dididit dah))
  --  ]])
  --) -- ==>  #(dididit dah)

  --[[
  6.9 Control features

  essential procedure: procedure? obj
  ]]

  assert_equal(true, test("(procedure? car)"))
  assert_equal(false, test("(procedure? 'car)"))
  assert_equal(true, test("(procedure? (lambda (x) (* x x)))"))
  assert_equal(false, test("(procedure? '(lambda (x) (* x x)))"))
  assert_equal(false, test("(procedure? '(lambda (x) (* x x)))"))
  -- TODO: call-cc assert_equal(true, test("(call-with-current-continuation procedure?)"))

  --[[
  essential procedure: apply proc args
  procedure: apply proc arg1 ... args
  ]]

  assert_equal(7, test("(apply + (list 3 4))"))

  assert_no_error_thrown(function()
    test([[
      (define compose
        (lambda (f g)
          (lambda args
            (f (apply g args)))))
    ]])
  end)
  assert_equal(30, test("((compose sqrt *) 12 75)"))

  --[[
  essential procedure: map proc list1 list2 ...
  ]]

  assert_equal({sym("b"), sym("e"), sym("h")}, test("(map cadr '((a b) (d e) (g h)))"))

  assert_equal(
    {1, 4, 27, 256, 3125},
    test([[
      (map (lambda (n) (expt n n))
           '(1 2 3 4 5))
    ]])
  )

  assert_equal({5, 7, 9}, test("(map + '(1 2 3) '(4 5 6))"))

  assert_no_error_thrown(function()
    test([[
    (let ((count 0))
      (map (lambda (ignored)
             (set! count (+ count 1))
             count)
           '(a b c)))
    ]])
  end) -- ==>  unspecified


  --[[
  essential procedure: for-each proc list1 list2 ...
  ]]

  --[[ TODO: for-each, vector-set!
    (let ((v (make-vector 5)))
      (for-each (lambda (i)
                  (vector-set! v i (* i i)))
                '(0 1 2 3 4))
      v) -- ==>  #(0 1 4 9 16)
  ]]

  --[[
  procedure: (force promise) TODO
  ]]

  --[[
    (force (delay (+ 1 2))) ==> 3
    (let ((p (delay (+ 1 2))))
      (list (force p) (force p))) ==> (3 3)

    (define a-stream
      (letrec ((next
        (lambda (n)
          (cons n (delay (next (+ n 1)))))))
        (next 0)))
    (define head car)
    (define tail
      (lambda (stream) (force (cdr stream))))

    (head (tail (tail a-stream))) ==> 2
  ]]

  --[[
    (define count 0)
    (define p
      (delay (begin (set! count (+ count 1))
        (if (> count x)
          count
          (force p)))))
    (define x 5)
    p ==> a promise
    (force p) ==> 6
    p ==> a promise, still
    (begin (set! x 10)
      (force p)) ==> 6
  ]]

  --[[
    TODO

    Here is a possible implementation of delay and force.
    Promises are implemented here as procedures of no arguments, and force simply calls its argument:

    (define force
      (lambda (object)
        (object)))

    We define the expression
      (delay <expression>)

    to have the same meaning as the procedure call
      (make-promise (lambda () <expression>)),

    where make-promise is defined as follows:

      (define make-promise
        (lambda (proc)
          (let ((result-ready? #f)
            (result #f))
              (lambda ()
                (if result-ready?
                  result
                  (let ((x (proc)))
                    (if result-ready?
                      result
                        (begin (set! result-ready? #t)
                          (set! result x)
                          result))))))))
  ]]

  --[[
    TODO

    (eqv? (delay 1) 1) ==> unspecified
    (pair? (delay (cons 1 2))) ==> unspecified
  ]]

  --[[
    TODO
  Some implementations may implement “implicit forcing,” where the value of a promise is forced by primitive procedures like cdr and +:

    (+ (delay (* 3 7)) 13) ==> 34
  ]]

  --[[
  essential procedure: call-with-current-continuation proc

    (call-with-current-continuation
      (lambda (exit)
        (for-each (lambda (x)
          (if (negative? x)
            (exit x)))
          ’(54 0 37 -3 245 19))
        #t)) ==> -3

    (define list-length
      (lambda (obj)
        (call-with-current-continuation
          (lambda (return)
            (letrec ((r
              (lambda (obj)
              (cond ((null? obj) 0)
              ((pair? obj)
              (+ (r (cdr obj)) 1))
              (else (return #f))))))
            (r obj))))))

    (list-length ’(1 2 3 4)) ==> 4

    (list-length ’(a b . c)) ==> #f
  ]]

  -- print("r4rs examples: "..r4rs_examples)
end

--[[
repl
]]

run_repl =
function()
  local get_num_occurences_of = function(str, char)
    local count = 0
    for _ in string.gmatch(str, char) do
      count = count + 1
    end
    return count
  end

  io.write("ns repl\n")
  repeat
    io.write("> ")
    io.stdout:flush()
    local str = io.read()

    if str == "exit" then
      break
    end

    local unbalanced_parens = get_num_occurences_of(str, "%(") - get_num_occurences_of(str, "%)") -- TODO: ugly balanced paren hack

    if unbalanced_parens ~= 0 then
      repeat
        str = str .. "\n" .. io.read()

        unbalanced_parens = get_num_occurences_of(str, "%(") - get_num_occurences_of(str, "%)") -- TODO: ugly balanced paren hack
      until unbalanced_parens == 0
    end

    -- TODO: alt 1, pcall
    local ok, err = pcall(rep, str)
    if not ok then
      print("error: "..err.."")
      print(debug.traceback())
    end
    -- TODO: alt 2, die on error, more extensive error reporting
    --[[
    rep(str)
    ]]
  until false
end

rep =
function(str, env)
  local val = read_eval(str, env or _NS_ENV or _G)
  if val ~= nil then
    print(scheme_str(val))
    return scheme_str(val)
  end
end

--[[
read / eval
]]

read_eval =
function(str, env)
  return eval(read(str), env)
end

init_ns_environment =
function(dest_env)
  local environment = {}
  put_all(environment, standard_procedures())
  put_all(environment, additional_procedures())
  put_all(dest_env, environment)
end

standard_procedures =
function()
  local procedures = {
    --[[
    r4rs essential procedure: (= z1 z2 z3 ...) TODO: varargs
    ]]
    ['='] = function(a, b)
      return tonumber(a) == tonumber(b) -- TODO
    end,
    --[[
    r4rs essential procedure: (< z1 z2 z3 ...) TODO: varargs
    ]]
    ['<'] = function(a, b)
      return a < b
    end,
    --[[
    r4rs essential procedure: (> z1 z2 z3 ...) TODO: varargs
    ]]
    ['>'] = function(a, b)
      return a > b
    end,
    -- r4rs essential procedure: (<= z1 z2 z3 ...) TODO: varargs
    ['<='] = function(a, b)
      return a <= b
    end,
    -- r4rs essential procedure: (>= z1 z2 z3 ...) TODO: varargs
    ['>='] = function(a, b)
      return a >= b
    end,
    -- r4rs essential procedure: (+ z1 ...) TODO: varargs
    ['+'] = function(a, b)
      return a + b
    end,
    -- r4rs essential procedure: (* z1 ...) TODO: varargs
    ['*'] = function(a, b)
      return a * b
    end,
    -- r4rs essential procedure: (- z1 z2)
    -- r4rs essential procedure: (- z) TODO
    -- r4rs procedure: (- z1 z2 ...) TODO
    ['-'] = function(a, b)
      return a - b
    end,
    -- r4rs essential procedure: (/ z1 z2)
    -- r4rs essential procedure: (/ z) TODO
    -- r4rs procedure: (/ z1 z2 ...) TODO
    ['/'] = function(a, b)
      return a / b
    end,
    -- r4rs essential procedure: (abs x)
    ['abs'] = function(x)
      return math.abs(x)
    end,
    -- r4rs essential procedure: (append list ...)
    ['append'] = function(...)
      local lists = {...}
      local result = {}
      for _,list in ipairs(lists) do
        if not is_list(list) then
          error("not a list: "..scheme_str(list))
        end
        for _,v in ipairs(list) do
          table.insert(result, v)
        end
      end
      return result
    end,
    -- r4rs essential procedure: (apply proc args)
    -- r4rs procedure: (apply proc arg1 ... args)
    ['apply'] = function(proc, ...)
      local args = {...}
      if #args == 1 then
        return invoke_function(proc, args[1])
      else
        return invoke_function(proc, args)
      end
    end,
    -- r4rs essential procedure: (boolean? obj)
    ['boolean?'] = function(obj)
      return is_boolean(obj)
    end,
    -- r4rs essential procedure: (call-with-current-continuation proc)
    ['call-with-current-continuation'] = function(proc)
      error("TODO: call-with-current-continuation")
    end,
    -- r4rs essential procedure: (call-with-input-file string proc)
    ['call-with-input-file'] = function(string, proc)
      error("TODO: call-with-input-file")
    end,
    -- r4rs essential procedure: (call-with-output-file string proc)
    ['call-with-output-file'] = function(string, proc)
      error("TODO: call-with-output-file")
    end,
    -- r4rs essential procedure: (close-input-port port)
    ['close-input-port'] = function(port)
      error("TODO: close-input-port")
    end,
    -- r4rs essential procedure: (close-output-port port)
    ['close-output-port'] = function(port)
      error("TODO: close-output-port")
    end,
    -- r4rs essential procedure: (current-input-port)
    ['current-input-port'] = function()
      error("TODO: current-input-port")
    end,
    -- r4rs essential procedure: (current-output-port)
    ['current-output-port'] = function()
      error("TODO: current-output-port")
    end,
    -- r4rs essential procedure: (char? obj)
    ['char?'] = function(obj)
      return is_chr(obj)
    end,
    -- r4rs essential procedure: (char=? char1 char2)
    ['char=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and get_chr(char1) == get_chr(char2)
    end,
    -- r4rs essential procedure: (char<? char1 char2)
    ['char<?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and get_chr(char1) < get_chr(char2)
    end,
    -- r4rs essential procedure: (char>? char1 char2)
    ['char>?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and get_chr(char1) > get_chr(char2)
    end,
    -- r4rs essential procedure: (char<=? char1 char2)
    ['char<=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and get_chr(char1) <= get_chr(char2)
    end,
    -- r4rs essential procedure: (char>=? char1 char2)
    ['char>=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and get_chr(char1) >= get_chr(char2)
    end,
    -- r4rs essential procedure: (char-ci=? char1 char2)
    ['char-ci=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and string.upper(get_chr(char1)) == string.upper(get_chr(char2))
    end,
    -- r4rs essential procedure: (char-ci<? char1 char2)
    ['char-ci<?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and string.upper(get_chr(char1)) < string.upper(get_chr(char2))
    end,
    -- r4rs essential procedure: (char-ci>? char1 char2)
    ['char-ci>?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and string.upper(get_chr(char1)) > string.upper(get_chr(char2))
    end,
    -- r4rs essential procedure: (char-ci<=? char1 char2)
    ['char-ci<=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and string.upper(get_chr(char1)) <= string.upper(get_chr(char2))
    end,
    -- r4rs essential procedure: (char-ci>=? char1 char2)
    ['char-ci>=?'] = function(char1, char2)
      return is_chr(char1) and is_chr(char2) and string.upper(get_chr(char1)) >= string.upper(get_chr(char2))
    end,
    -- r4rs essential procedure: (char-alphabetic? char)
    ['char-alphabetic?'] = function(char)
      return is_chr(char) and string.match(get_chr(char), "%a")
    end,
    -- r4rs essential procedure: (char-lower-case? char)
    ['char-lower-case?'] = function(char)
      return is_chr(char) and string.match(get_chr(char), "%l")
    end,
    -- r4rs essential procedure: (char-numeric? char)
    ['char-numeric?'] = function(char)
      return is_chr(char) and string.match(get_chr(char), "%d")
    end,
    -- r4rs essential procedure: (char-upper-case? char)
    ['char-upper-case?'] = function(char)
      return is_chr(char) and string.match(get_chr(char), "%u")
    end,
    -- r4rs essential procedure: (char-whitespace? char)
    ['char-whitespace?'] = function(char)
      return is_chr(char) and string.match(get_chr(char), "%s")
    end,
    -- r4rs essential procedure: (char->integer char)
    ['char->integer'] = function(char)
      return string.byte(get_chr(char), 1)
    end,
    -- r4rs essential procedure: (char-upcase char)
    ['char-upcase'] = function(char)
      return chr(string.upper(get_chr(char)))
    end,
    -- r4rs essential procedure: (char-downcase char)
    ['char-downcase'] = function(char)
      return chr(string.lower(get_chr(char)))
    end,
    -- r4rs essential procedure: (complex? obj)
    ['complex?'] = function(obj)
      return false
    end,
    -- r4rs essential procedure: (car pair)
    ['car'] = function(pair)
      return pair[1]
    end,
    -- r4rs essential procedure: (cdr pair)
    ['cdr'] = function(pair)
      return slice(pair, 2, #pair)
    end,
    -- r4rs essential procedure: (ceiling x)
    ['ceiling'] = function(x)
      return math.ceil(x)
    end,
    -- r4rs essential procedure: (cons obj1 obj2)
    ['cons'] = function(obj1, obj2)
      if is_list(obj2) then
        local new_list = duplicate_list(obj2)
        table.insert(new_list, 1, obj1)
        return new_list
      else
        return new_pair(obj1, obj2)
      end
    end,
    -- essential procedure: (display obj)
    -- essential procedure: (display obj port) TODO
    ['display'] = function(obj)
      if is_str(obj) then
        io.write(get_str(obj))
      else
        io.write(scheme_str(obj))
      end
    end,
    ['do'] = function(init_exprs, test_exprs, commands)
      -- r4rs syntax:
      --   (do ((<variable1> <init1> <step1>)
      --     ...) (<test> <expression> ...) <command> ...)
      error("TODO: do")
    end,
    -- r4rs essential procedure: (eof-object? obj)
    ['eof-object?'] = function(obj)
      error("TODO: eof-object?")
    end,
    -- r4rs essential procedure: (eq? obj1 obj2)
    ['eq?'] = function(obj1, obj2)
      return obj1 == obj2 or (is_empty_list(obj1) and is_empty_list(obj2))
    end,
    -- r4rs essential procedure: (eqv? obj1 obj2)
    ['eqv?'] = function(obj1, obj2)

      -- The eqv? procedure returns #t if:

      local result =

      -- obj1 and obj2 are both #t or both #f
      (obj1 == true and obj2 == true)
      or
      (obj1 == false and obj2 == false)
      or

      -- obj1 and obj2 are both symbols and
      -- (string=? (symbol->string obj1) (symbol->string obj2)) ==>  #t
      (is_sym(obj1) and is_sym(obj2) and get_sym(obj1) == get_sym(obj2)) -- TODO: DRY with string=?
      or

      -- obj1 and obj2 are both numbers, are numerically equal (see =, section see section 6.5 Numbers), and are either both exact or both inexact.
      (is_number(obj1) and is_number(obj2) and obj1 == obj2) -- TODO: DRY with =
      or

      -- obj1 and obj2 are both characters and are the same character according to the char=? procedure
      (is_chr(obj1) and is_chr(obj2) and obj1 == obj2)  -- TODO: DRY with char=?
      or

      -- both obj1 and obj2 are the empty list
      (is_empty_list(obj1) and is_empty_list(obj2))
      or

      -- obj1 and obj2 are procedures whose location tags are equal
      (is_procedure(obj1) and is_procedure(obj2) and obj1 == obj2)
      or

      -- obj1 and obj2 are pairs, vectors, or strings that denote the same locations in the store
      (is_pair(obj1) and is_pair(obj2) and obj1 == obj2)
      or

      (is_str(obj1) and is_str(obj2) and obj1 == obj2)

      --[[
      or
      (is_vector(obj1) and is_vector(obj2) and obj1 == obj2)
      ]]
      return result
    end,
    -- r4rs essential procedure: (equal? obj1 obj2)
    ['equal?'] = function(obj1, obj2)
      -- return obj1 == obj2 -- TODO
      return deepcompare(obj1, obj2) -- TODO
    end,
    ['expt'] = function(z1, z2)
      -- r4rs procedure: expt z1 z2
      return z1^z2
    end,
    -- r4rs essential procedure: (exact? z)
    ['exact?'] = function(z)
      return false
    end,
    -- r4rs essential procedure: (even? z)
    ['even?'] = function(z)
      return z % 2 == 0
    end,
    -- r4rs essential procedure: (floor x)
    ['floor'] = function(x)
      return math.floor(x)
    end,
    -- r4rs essential procedure: (for-each proc list1 list2 ...) TODO: test
    ['for-each'] = function(proc, ...)
      local lists = {...}
      local result
      for i,v in ipairs(lists[1]) do
        local args = {}
        for _,v in ipairs(slice(lists, 2, #lists)) do
          args[i] = v[i]
        end
        result = invoke_function(proc, args)
      end
      return result
    end,
    -- r4rs essential procedure: (gcd n1 ...) TODO
    ['gcd'] = function(...)
      error("TODO: gcd")
    end,
    -- r4rs essential procedure: (inexact? z)
    ['inexact?'] = function(z)
      return true
    end,
    -- r4rs essential procedure: (input-port? obj)
    ['input-port?'] = function(obj)
      error("TODO: input-port?")
    end,
    -- r4rs essential procedure: (integer? obj)
    ['integer?'] = function(obj)
      return false
    end,
    -- r4rs essential procedure: (integer->char n)
    ['integer->char'] = function(n)
      return chr(string.char(n))
    end,
    -- r4rs essential procedure: (lcm n1 ...) TODO
    ['lcm'] = function(...)
      error("TODO: lcm")
    end,
    -- r4rs essential procedure: (length list)
    ['length'] = function(list)
      return #list
    end,
    -- r4rs essential procedure: (list obj ...)
    ['list'] = function(...)
      local objs = {...}
      return objs
    end,
    -- r4rs essential procedure: (list? obj)
    ['list?'] = function(obj)
      return is_list(obj)
    end,
    -- r4rs essential procedure: (list-ref list k)
    ['list-ref'] = function(list, k)
      return list[k+1]
    end,
    -- r4rs essential procedure: (list->string chars)
    ['list->string'] = function(chars)
      return table.concat(chars)
    end,
    -- r4rs essential procedure: (list->vector list)
    ['list->vector'] = function(list)
      error("TODO: list->vector")
    end,
    ['list-tail'] = function(list, k)
      -- r4rs procedure: list-tail list k
      return slice(list, k+1, #list)
    end,
    -- r4rs essential procedure: (load filename)
    ['load'] = function(filename)
      error("TODO: load")
    end,
    -- r4rs essential procedure: (make-string k) TODO
    -- r4rs essential procedure: (make-string k char) TODO
    ['make-string'] = function(k, char)
      error("TODO: make-string")
    end,
    -- r4rs essential procedure: (make-vector k)
    ['make-vector'] = function(k, fill)
      -- procedure: make-vector k fill
      local vector = {}
      for index=1,k do
        vector[index]=fill
      end
      setmetatable(vector, vector_mt)
      return vector
    end,
    -- r4rs essential procedure: (map proc list1 list2 ...)
    ['map'] = function(proc, ...)
      local lists = {...}

      local result = {}

      local first_list = lists[1]

      for index=1,#first_list do
        local args = {}
        for _,list in ipairs(lists) do
          table.insert(args, list[index])
        end
        result[index] = invoke_function(proc, args)
      end

      return result
    end,
    -- r4rs essential procedure: (max x1 x2 ...) TODO: varargs
    ['max'] = function(x1, x2)
      return math.max(x1, x2)
    end,
    -- r4rs essential procedure: (min x1 x2 ...) TODO: varargs
    ['min'] = function(x1, x2)
      return math.min(x1, x2)
    end,
    -- r4rs essential procedure: (modulo n1 n2) TODO: "number theoretic"
    ['modulo'] = function(n1, n2)
      return n1 % n2
    end,
    -- r4rs essential procedure: (negative? z)
    ['negative?'] = function(z)
      return z < 0
    end,
    -- r4rs essential procedure: (newline)
    -- r4rs essential procedure: (newline port) TODO
    ['newline'] = function()
      io.write("\n")
    end,
    -- r4rs essential procedure: (not obj)
    ['not'] = function(obj)
      return not obj
    end,
    -- r4rs essential procedure: (null? obj)
    ['null?'] = function(obj)
      return is_empty_list(obj)
    end,
    -- r4rs essential procedure: (number? obj)
    ['number?'] = function(obj)
      return is_number(obj)
    end,
    -- r4rs essential procedure: (number->string number)
    -- r4rs essential procedure: (number->string number radix) TODO
    ['number->string'] = function(number)
      -- TODO: check type
      return tostring(number)
    end,
    -- r4rs essential procedure: (odd? z)
    ['odd?'] = function(z)
      return not (z % 2 == 0)
    end,
    -- r4rs essential procedure: (open-input-file filename)
    ['open-input-file'] = function(filename)
      error("TODO: open-input-file")
    end,
    -- r4rs essential procedure: (open-output-file filename)
    ['open-output-file'] = function(filename)
      error("TODO: open-output-file")
    end,
    -- r4rs essential procedure: (output-port? obj)
    ['output-port?'] = function(obj)
      error("TODO: output-port?")
    end,
    -- r4rs essential procedure: (pair? obj)
    ['pair?'] = function(obj)
      return is_pair(obj)
    end,
    -- r4rs essential procedure: (peek-char)
    -- r4rs essential procedure: (peek-char port)
    ['peek-char'] = function(port)
      error("TODO: peek-char")
    end,
    ['pi'] = function() -- TODO not in r4rs?
      return math.pi
    end,
    -- r4rs essential procedure: (positive? z)
    ['positive?'] = function(z)
      return z > 0
    end,
    -- r4rs essential procedure: (procedure? obj)
    ['procedure?'] = function(obj)
      return is_procedure(obj)
    end,
    -- r4rs essential procedure: (quotient n1 n2) TODO
    ['quotient'] = function(n1, n2)
      error("TODO: quotient")
    end,
    -- r4rs essential procedure: (rational? obj)
    ['rational?'] = function(obj)
      return false
    end,
    -- r4rs essential procedure: (read)
    -- r4rs essential procedure: (read port)
    ['read'] = function(port)
      error("TODO: read")
    end,
    -- r4rs essential procedure: (read-char)
    -- r4rs essential procedure: (read-char port)
    ['read-char'] = function(port)
      error("TODO: read-char")
    end,
    -- r4rs essential procedure: (real? obj)
    ['real?'] = function(obj)
      return true
    end,
    -- r4rs essential procedure: (remainder n1 n2) TODO
    ['remainder'] = function(n1, n2)
      error("TODO: remainder")
    end,
    -- r4rs essential procedure: (reverse list)
    ['reverse'] = function(list)
      result = {}
      for i=#list,1,-1 do
        table.insert(result, list[i])
      end
      return result
    end,
    -- r4rs essential procedure: (round x)
    ['round'] = function(x)
      return round(x)
    end,
    -- r4rs essential procedure: (set-car! pair obj) TODO
    ['set-car!'] = function(pair, obj)
      error("TODO: set-car!")
    end,
    -- r4rs essential procedure: (set-cdr! pair obj) TODO
    ['set-cdr!'] = function(pair, obj)
      error("TODO: set-cdr!")
    end,
    ['sqrt'] = function(z)
      -- r4rs procedure: sqrt z
      return math.sqrt(z)
    end,
    -- r4rs essential procedure: (string char ...)
    --[[
    --TODO: conflicts with lua string global. causes string.gmatch to fail.
    ['string'] = function(obj)
    error("TODO: string")
    end,
    ]]
    -- r4rs essential procedure: (string? obj)
    ['string?'] = function(obj)
      return is_str(obj)
    end,
    -- TODO: make ns symbol case insignificant and stuff everything into UPCASE environment, unless all UPCASE (and possibly option is set) in which the symbol is stuffed into both UPCASE and lowercase in the global environment
    ['string+'] = function(...) -- TODO: string causes issues when in _G, should _G original string be renamed and that renamed module be used throughout here?
      local chars = {...}
      return table.concat(chars)
    end,
    -- r4rs essential procedure: (string-length string)
    ['string-length'] = function(string)
      -- TODO: validate it's String?
      return #get_str(string)
    end,
    -- r4rs essential procedure: (string-ref string k)
    ['string-ref'] = function(string, k)
      return string[k+1] -- TODO: does this work? lua has 1 based indexing
    end,
    -- r4rs essential procedure: (string-set! string k char)
    ['string-set!'] = function(string, k, char)
      -- TODO: strings are immutable
      error("TODO: string-set!")
    end,
    -- r4rs essential procedure: (string=? string1 string2)
    ['string=?'] = function(string1, string2)
      return is_str(string1) and is_str(string2) and string1 == string2
    end,
    -- r4rs essential procedure: (string-append string ...)
    ['string-append'] = function(...)
      local strings = {...}
      local result = ""
      for _,string in ipairs(strings) do
        result = result .. get_str(string)
      end
      return result
    end,
    -- r4rs essential procedure: (string->list string)
    ['string->list'] = function(string)
      result = {}
      for i,v in ipairs(string) do
        result[i] = v
      end
      return result
    end,
    -- r4rs essential procedure: (string->number string)
    -- r4rs essential procedure: (string->number string radix) TODO
    ['string->number'] = function(string)
      -- TODO: check type
      return tonumber(string)
    end,
    -- r4rs essential procedure: (string->symbol string)
    ['string->symbol'] = function(string)
      if is_str(string) then
        return sym(get_str(string))
      else
        error("TODO: symbol->string")
      end
    end,
    -- r4rs essential procedure: (string-ci=? string1 string2)
    ['string-ci=?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string.upper(string1) == string.upper(string2)
    end,
    -- r4rs essential procedure: (string<? string1 string2)
    ['string<?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string1 < string2
    end,
    -- r4rs essential procedure: (string>? string1 string2)
    ['string>?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string1 > string2
    end,
    -- r4rs essential procedure: (string<=? string1 string2)
    ['string<=?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string1 <= string2
    end,
    -- r4rs essential procedure: (string>=? string1 string2)
    ['string>=?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string1 >= string2
    end,
    -- r4rs essential procedure: (string-ci<? string1 string2)
    ['string-ci<?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string.upper(string1) < string.upper(string2)
    end,
    -- r4rs essential procedure: (string-ci>? string1 string2)
    ['string-ci>?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string.upper(string1) > string.upper(string2)
    end,
    -- r4rs essential procedure: (string-ci<=? string1 string2)
    ['string-ci<=?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string.upper(string1) <= string.upper(string2)
    end,
    -- r4rs essential procedure: (string-ci>=? string1 string2)
    ['string-ci>=?'] = function(string1, string2)
      return is_list(string1) and is_list(string2) and string.upper(string1) >= string.upper(string2)
    end,
    -- r4rs essential procedure: (substring string start end)
    ['substring'] = function(str, start, fin)
      -- TODO: String must be a string, and start and end must be exact integers satisfying 0 <= start <= end <= (string-length string).
      return string.sub(str, start+1, fin+1)
    end,
    -- r4rs essential procedure: (symbol? obj)
    ['symbol?'] = function(obj)
      return is_sym(obj)
    end,
    -- r4rs essential procedure: (symbol->string symbol)
    ['symbol->string'] = function(symbol)
      if is_sym(symbol) then
        return str(get_sym(symbol))
      else
        error("TODO: symbol->string")
      end
    end,
    -- r4rs essential procedure: (truncate x)
    ['truncate'] = function(x)
      return math.floor(x)
    end,
    -- r4rs essential procedure: (write obj)
    -- r4rs essential procedure: (write obj port)
    ['write'] = function(obj, port)
      error("TODO: write")
    end,
    -- r4rs essential procedure: (write-char char)
    -- r4rs essential procedure: (write-char char port)
    ['write-char'] = function(char, port)
      error("TODO: write")
    end,
    -- r4rs essential procedure: (vector obj ...)
    ['vector'] = function(...)
      local args = {...}
      -- TODO
      setmetatable(args, vector_mt)
      return args
    end,
    -- r4rs essential procedure: (vector? obj)
    ['vector?'] = function(obj)
      return is_vector(obj)
    end,
    ['vector-fill!'] = function(vector, fill)
      -- r4rs procedure: vector-fill! vector fill
      -- TODO
      error("TODO: vector-fill!")
    end,
    ['vector-fill!'] = function(vector, fill)
      -- r4rs procedure: vector-fill! vector fill
      -- TODO
      error("TODO: vector-fill!")
    end,
    -- r4rs essential procedure: (vector-length vector)
    ['vector-length'] = function(vector)
      error("TODO: vector-length")
    end,
    -- r4rs essential procedure: (vector-ref vector k)
    ['vector-ref'] = function(vector, k)
      error("TODO: vector-ref")
    end,
    -- r4rs essential procedure: (vector-set! vector k obj)
    ['vector-set!'] = function(vector, k, obj)
      error("TODO: vector-set!")
    end,
    -- r4rs essential procedure: (vector->list vector)
    ['vector->list'] = function(vector)
      error("TODO: vector->list")
    end,
    -- r4rs essential procedure: (zero? z)
    ['zero?'] = function(z)
      return z == 0
    end
  }

  define_non_prim_standard_procedures(procedures)

  return procedures
end

-- re, assoc: http://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v13/schintro_106.html
define_non_prim_standard_procedures =
function(env)
  -- TODO: assq, assv, assoc possible to DRY
  -- TODO: memq, memv, member possible to DRY
  local standard_procedure_defs =
[[
; r4rs essential procedure: (assq obj alist)
;

(define assq
  (lambda (obj alist)
    (cond
      [(null? alist) #f]
      [(eq? obj (caar alist)) (car alist)]
      [else (assq obj (cdr alist))])))

; r4rs essential procedure: (assv obj alist)
;

(define assv
  (lambda (obj alist)
    (cond
      [(null? alist) #f]
      [(eqv? obj (caar alist)) (car alist)]
      [else (assv obj (cdr alist))])))

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
      [else (memq obj (cdr list))])))

; r4rs essential procedure: (memv obj list)
;

(define memv
  (lambda (obj list)
    (cond
      [(null? list) #f]
      [(eqv? obj (car list)) list]
      [else (memv obj (cdr list))])))

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
]]

  local procs = split(standard_procedure_defs, ";")
  procs = filter(function(str)
    return string.sub(trim(str), 1, 1) == "("
  end, procs)
  for _,standard_procedure_def in ipairs(procs) do
    eval(read(standard_procedure_def), env)
  end
end

additional_procedures =
function()
  return {
    ['hash'] = function(assocs) -- TODO: immutable hash table
			-- racket (hash key val ... ...)
      --[[
			var content = IdentityDictionary.new;
			args.pairsDo { |a, b| content[a] = eval.value(b) };
			(type: '__hash__', content: content)
      ]]
    end,
    ['make-hash'] = function(...) -- TODO: mutable hash table
      -- racket (make-hash [assocs])
      local assocs = {...}
      local hash = {}
      for _,v in ipairs(assocs) do
        hash[v[1]] = slice(v, 2, #v)
      end
      setmetatable(hash, hash_mt) -- TODO: mutable_hash_mt ??
      return hash
    end,
    ['hash-ref'] = function(hash, key)
      -- racket (hash-ref hash key [failure-result]) TODO: failure-result
      if is_hash(vec) then
        return hash[key]
      else
        error("in hash-ref: not a hash")
      end
    end,
    ['hash-set!'] = function(hash, key, v)
      -- racket (hash-set! hash key v)
      if is_hash(vec) then
        hash[key] = v
      else
        error("in hash-set!: not a hash")
      end
    end,
    ['hash-count'] = function(hash)
      -- racket (hash-count hash)
      if is_hash(vec) then
        return #hash
      else
        error("in hash-count: not a hash")
      end
    end,
    ['hash?'] = function(obj)
      -- racket (hash? v)
      return is_hash(obj)
    end,
    ['vector-filter'] = function(proc, vec)
      -- racket (vector-filter pred vec)
      if is_vector(vec) then
        local result = filter(proc, vec)
        setmetatable(result, vector_mt)
        return result
      else
        error("in vector-filter: not a vector")
      end
    end,
    ['vector-filter-not'] = function(proc, vec)
      -- racket (vector-filter-not pred vec)
      if is_vector(vec) then
        local result = filter_not(proc, vec)
        setmetatable(result, vector_mt)
        return result
      else
        error("in vector-filter-not: not a vector")
      end
    end,
    ['vector-map'] = function(proc, vec)
      -- racket (vector-map proc vec ...+) TODO: ...+
      if is_vector(vec) then
        local result = map(proc, vec)
        setmetatable(result, vector_mt)
        return result
      else
        error("in vector-map: not a vector")
      end
    end,
  }
end

read =
function(str)
  local ss = ss_new(str)
  result = parse(ss)
  return result
end

parse =
function (ss)
  local rg_ignore = "^%s+"
  local rg_comment_prefix = ";"

  local value
  local result

  -- TODO print(ss_as_string(ss))

  ss_skip(ss, rg_ignore)
  while ss_scan(ss, rg_comment_prefix) do
    ss_skip_until(ss, ".-\n")
  end
  ss_skip(ss, rg_ignore)

  local open_paren = ss_scan(ss, "^%(") or ss_scan(ss, "^%[")

  if open_paren then
    local close_paren
    if open_paren == "(" then
      close_paren = "^%)"
    else
      close_paren = "^%]"
    end
    ss_skip(ss, rg_ignore)

    local list = {}
    while not ss_matches(ss, close_paren) do
      table.insert(list, parse(ss))
      ss_skip(ss, rg_ignore)
    end

    ss_skip(ss, close_paren)

    result = list
  elseif ss_scan(ss, "^'") then
    -- r4rs essential syntax: '<datum>
    local list = {}
    table.insert(list, sym("quote"))
    table.insert(list, parse(ss))
    result = list
  elseif ss_scan(ss, "^`") then
    -- r4rs essential syntax: `<template>
    local list = {}
    table.insert(list, sym("quasiquote"))
    table.insert(list, parse(ss))
    result = list
  elseif ss_scan(ss, "^,@") then
    local list = {}
    table.insert(list, sym("unquote-splicing"))
    table.insert(list, parse(ss))
    result = list
  elseif ss_scan(ss, "^,") then
    local list = {}
    table.insert(list, sym("unquote"))
    table.insert(list, parse(ss))
    result = list
  else
    result = atom(ss)
  end

  if result == nil then
    if ss_eos(ss) then
      error("parse error: unexpected EOF")
    else
      error("parse error: unexpected token at "..ss_as_string(ss))
    end
  end

  return expand(result)
end

local expand_lambda

expand =
function(x)
  if not is_list(x) then
    return x
  else
    local head = x[1]
    local tail = slice(x, 2, #x)
    if head == sym("quote") then
      if #tail ~= 1 then
        error("in "..scheme_str(x)..": quote syntax error: 1 expression expected, got %"..#tail)
      else
        return x
      end
    elseif head == sym("begin") then
      -- TODO: (begin) => None
      return x
    elseif head == sym("define") then
      if #x ~= 3 then
        error("in "..scheme_str(x)..": expected == 3 expressions in define: got "..#x)
      else
        local variable_part = tail[1]
        local body = slice(tail, 2, #tail)
        if is_list(variable_part) then
          local variables, formals
          variables = variable_part[1]
          formals = slice(variable_part, 2, #variable_part)

          table.insert(body, 1, formals)

          return {
            sym("define"),
            variables,
            -- (lambda (x) e1 e2) => (lambda (x) (begin e1 e2))
            expand_lambda(body)
          }
        else
          return x
        end
      end
    elseif head == sym("lambda") then
      if #x < 3 then
        error("in "..scheme_str(x)..": expected >= 3 expressions in lambda: got "..#x)
      else
        return expand_lambda(tail)
      end
    elseif head == sym("quasiquote") then
      -- r4rs essential syntax: (quasiquote <template>)
      if #tail ~= 1 then
        error("in "..scheme_str(x)..": quote syntax error: 1 expression expected, got %"..#tail)
      else
        return expand_quasiquote(tail[1])
      end
    else
      return map(function(part) return expand(part) end, x)
    end
  end
end

-- (lambda (x) e1 e2) => (lambda (x) (begin e1 e2))
expand_lambda =
function(tail)
  local formals, body, exp

  formals = tail[1]
  body = slice(tail, 2, #tail)

  -- TODO where vars == formals
  -- require(x, (isa(vars, list) and all(isa(v, Symbol) for v in vars))
  --         or isa(vars, Symbol), "illegal lambda argument list")

  if #body == 1 then
    exp = body[1]
  else
    exp = { sym("begin") }
    for _,v in ipairs(body) do -- TODO: effectively an "append" - refactor for clarity?
      table.insert(exp, v)
    end
  end
  return { sym("lambda"), formals, expand(exp) }
end

--[[
Expand `x => 'x; `,x => x; `(,@x y) => (append x y)
]]
expand_quasiquote =
function(x)
  if not is_pair(x) then
    return {sym('quote'), x}
  else
    local head = x[1]
    local tail = slice(x, 2, #x)
    local continue_func = function()
      return {sym('cons'), expand_quasiquote(head), expand_quasiquote(tail)}
    end

    if head == sym("unquote") then
      if #tail ~= 1 then
        error("in "..scheme_str(x)..": quasiquote syntax error: 1 expression expected, got %"..#tail)
      else
        return tail[1]
      end
    elseif is_pair(head) then
      if head == sym("unquote-splicing") then
        return {sym('append'), head[2], expand_quasiquote(tail)}
      else
        return continue_func()
      end
    else
      return continue_func()
    end
  end
end

atom =
function(ss)
  -- TODO: remove rg_float = "(-?(?:0|[1-9]\\d*)(?:\\.\\d+(?i:e[+-]?\\d+)|\\.\\d+|(?i:e[+-]?\\d+)))"
  -- TODO: remove rg_integer = "[+-]?%d+"
  --
  --[[

from https://www.scheme.com/tspl2/intro.html#g1478

Keywords, variables, and symbols are collectively called identifiers. Identifiers may be formed from the following set of characters:

the lowercase letters a through z,
the uppercase letters A through Z,
the digits 0 through 9, and
the characters ? ! . + - * / < = > : $ % ^ & _ ~.

  ]]
  local rg_symbol = "[a-zA-Z+-./<=>*!?:%$%_&~%^][0-9a-zA-Z+-./<=>*!?:%$%_&~%^]*"
  --local rg_symbol = "[a-zA-Z?!.+-*/<=>:%$%%%^&%_~][a-zA-Z0-9?!.+-*/<=>:%$%%%^&%_~]*"
  local rg_char = "#\\." -- TODO: not enough, will include #\mutliple_chars
  local rg_char_space = "#\\space"
  local rg_char_newline = "#\\newline"
  local rg_boolean = "#[ft]"
  local rg_string = "\"[0-9a-zA-Z_!| *@=/+-<>:;,.()?&#\\\\'']*\""

  local scan_number = function(ss)
    local rg_token = "[-%d.e]+"
    local value = ss_matches(ss, rg_token)
    local possibly_a_number
    if value then
      local token = string.sub(ss['str'], ss['pos'], ss['pos']+value-1)
      possibly_a_number = tonumber(token)
    end
    if possibly_a_number then
      ss_skip(ss, rg_token)
      return possibly_a_number
    end
  end

  local value = scan_number(ss)
  if value then
    return value
  end

  value = ss_scan(ss, rg_symbol)
  if value then
    return sym(value)
  end

  value = ss_scan(ss, rg_char_newline)
  if value then
    return chr("\n")
  end

  value = ss_scan(ss, rg_char_space)
  if value then
    return chr(" ")
  end

  value = ss_scan(ss, rg_char)
  if value then
    return chr(string.sub(value, 3, 3))
  end

  value = ss_scan(ss, rg_boolean)
  if value then
    return value == "#t"
  end

  value = ss_scan(ss, rg_string)
  if value then
    return str(string.sub(value, 2, -2))
  end
end

local make_let
local make_lambda

eval =
function(expr, env)
  if is_sym(expr) then
    -- r4rs essential syntax: <variable>
    local symbol = get_sym(expr)
    local found_env = find_env(env, symbol)
    if found_env then
      return found_env[symbol]
    else
      error(symbol..": undefined")
    end
  elseif is_list(expr) then
    local op = expr[1]
    local args = slice(expr, 2, #expr)
    --TODO: refactor out num_clauses and use args instead of expr below (see scd version) 

    -- TODO https://www.gnu.org/software/mit-scheme/documentation/mit-scheme-ref/Conditionals.html
    if op == sym("and") then
      -- r4rs essential syntax: (and <test1> ...)
      local value = true
      local index = 1

      while value ~= false and index <= #args do
        value = eval(args[index], env)
        index = index + 1
      end

      return value
    elseif op == sym("begin") then
      -- r4rs essential syntax: (begin <expression1> <expression2> ...)
      local tab = inject(args, {nil, env}, function(val_env, exp)
        return {eval(exp, val_env[2]), val_env[2]}
      end)
      return tab[1]
    elseif op == sym("case") then
      -- r4rs essential syntax: (case <key> <clause1> <clause2> ...)
      local num_clauses = #expr-2

      local key = eval(expr[2], env)
      local i = 1

      repeat
        local clause = expr[2+i]
        local object_expr = clause[1]
        local then_body = clause[2]

        if object_expr == sym("else") then
          return eval(then_body, env)
        elseif table_includes(object_expr, key) then
          return eval(then_body, env)
        end
        i = i + 1
      until i > num_clauses

      return nil
    elseif op == sym("cond") then
      -- r4rs essential syntax: (cond <clause1> <clause2> ...)
      local num_clauses = #expr-1

      local i = 1

      repeat
        local clause = expr[1+i]
        local test_expr = clause[1]
        local then_body = clause[2]

        i = i + 1

        if test_expr == sym("else") then
          return eval(then_body, env) -- TODO can be made more DRY
        elseif eval(test_expr, env) then
          return eval(then_body, env)
        end
      until i > num_clauses

      return nil
    elseif op == sym("define") then
      local symbol = get_sym(args[1])
      local define_expr = args[2]
      env[symbol] = eval(define_expr, env)
    elseif op == sym("if") then
      -- r4rs essential syntax: (if <test> <consequent> <alternate>)
      -- r4rs syntax: (if <test> <consequent>)
      local test_expr, consequent_expr, alternate_expr

      test_expr = expr[2]
      consequent_expr = expr[3]
      alternate_expr = expr[4] -- TODO: this is optional

      if eval(test_expr, env) then
        return eval(consequent_expr, env)
      elseif alternate_expr then
        return eval(alternate_expr, env)
      end
    elseif op == sym("lambda") then
      -- r4rs essential syntax: (lambda <formals> <body>)
      if #expr > 3 then
        -- error("in "..scheme_str(expr) ..": lambda body error: 1 expression expected, found "..#expr)
        error("lambda body error: 1 expression expected, found "..#expr)
      end

      local formals = args[1]
      local body = args[2]

      -- TODO return make_lambda(formals, body, env)
      local vars_by_name = {}

      if is_list(formals) then
        for i,v in ipairs(formals) do
          vars_by_name[i] = get_sym(v)
        end
        return function(...)
          local args = {...}
          -- TODO print_table(args)
          return eval(body, make_env(vars_by_name, args, env))
        end
      else
        vars_by_name[1] = get_sym(formals)
        return function(...)
          local list = {...} -- TODO: add and use make-list instead, for clarity
          local args = {list}
          return eval(body, make_env(vars_by_name, args, env))
        end
      end
    elseif op == sym("let") then
      -- r4rs essential syntax: (let <bindings> <body>)
      -- Syntax: <bindings> should have the form ((<variable1> <init1>) ...), where each <init> is an expression, and <body> should be a sequence of one or more expressions
      local bindings, exprs, body

      bindings = args[1]
      exprs = slice(args, 2, #args)

      if #exprs == 1 then
        body = exprs[1]
      else
        table.insert(exprs, 1, sym("begin"))
        body = exprs
      end

      -- TODO: might be optimized by not using a separate make_let/make_lambda functions?
      return make_let(bindings, body, env)
    elseif op == sym("let*") then
      -- r4rs syntax: (let* <bindings> <body>)
      -- Syntax: <bindings> should have the form ((<variable1> <init1>) ...), and <body> should be a sequence of one or more expressions.
      local bindings, exprs, body

      bindings = args[1]
      exprs = slice(args, 2, #args)

      if #exprs == 1 then
        body = exprs[1]
      else
        table.insert(args, 1, op) -- TODO: ugly hack, improve
        error("in "..scheme_str(args)..": let* body error: 1 expression expected, "..#exprs.." found")
      end
      if #bindings == 0 then
        local func = make_lambda({}, body, env)
        if type(func) == "function" then -- TODO: understand this!
          return func()
        else
          return func
        end
      else
        local binding, rest
        binding = bindings[1]
        rest = slice(bindings, 2, #bindings)

        local new_body = {}
        table.insert(new_body, sym("let*"))
        table.insert(new_body, rest)
        table.insert(new_body, body)

        -- TODO print_table({binding}, "{binding}")
        -- TODO print_table(new_body, "new_body")
        local func = make_let({binding}, new_body, env)
        if type(func) == "function" then -- TODO: understand this!
          return func()
        else
          return func
        end
      end
    elseif op == sym("letrec") then
      -- r4rs essential syntax: (letrec <bindings> <body>)
      -- Syntax: <Bindings> should have the form ((<variable1> <init1>) ...), and <body> should be a sequence of one or more expressions

      error("TODO: letrec")
      -- TODO https://www.gnu.org/software/mit-scheme/documentation/mit-scheme-ref/Conditionals.html
    elseif op == sym("or") then
      -- r4rs essential syntax: (or <test1> ...)
      --[[
      local num_clauses = #expr-1

      if num_clauses == 0 then
        return true
      else
        local i = 1
        local val
        repeat
          local test_expr = expr[1+i]
          val = eval(test_expr, env)

          if val == true then
            return val
          end
          i = i + 1
        until i > num_clauses

        return val
      end
      ]]
      local value = false
      local index = 1

      while value == false and index <= #args do
        value = eval(args[index], env)
        index = index + 1
      end

      return value
    elseif op == sym("quote") then
      -- r4rs essential syntax: (quote <datum>)
      return args[1]
    elseif op == sym("set!") then
      -- r4rs essential syntax: (set! <variable> <expression>)
      local symbol = args[1]
      local symbol_name = get_sym(symbol)
      local e = args[2]
      local found_env = find_env(env, symbol_name)
      found_env[symbol_name] = eval(e, env)
    else
      -- r4rs essential syntax: (<operator> <operand1> ...)
      local func = eval(op, env)

      if func == nil then
        error(expr..": undefined")
      end

      if not is_procedure(func) then
        error("not a procedure: "..scheme_str(op))
      end

      local vals = {}

      for i,a in ipairs(args) do
        vals[i] = eval(a, env)
      end

      return invoke_function(func, vals)
    end
  else
    -- r4rs essential syntax: <constant>
    return expr
  end
end

make_let =
function(bindings, body, env)
	-- derived expression type:
	-- (let ((<variable1> <init1>) ...)
	--  <body>)
	-- ==   ((lambda (<variable1> ...) <body>) <init1> ...)

  local parse_letbinding = function(binding, env)
    return binding[1], eval(binding[2], env)
  end

  local vars = {}
  local inits = {}

  for i,binding in ipairs(bindings) do
    local varr, init

    varr, init = parse_letbinding(binding, env)

    table.insert(vars, get_sym(varr))
    table.insert(inits, init)
  end

  local lambda = make_lambda(vars, body, env)
  return invoke_function(lambda, inits)
end

make_lambda =
function(formals, body, env)
  return function(...)
    local args = {...}
    return eval(body, make_env(formals, args, env))
  end
end

make_env =
function(params, args, outer)
  local env = {}
  for i,param in ipairs(params) do
    env[param] = args[i]
  end
  env["__outer__"] = outer -- TODO: __outer__ is magic key. it should not be possible to define
  return env
end

find_env =
function(env, symbol)
  if env[symbol] then
    return env
  else
    local outer = env["__outer__"]
    if outer then
      return find_env(outer, symbol)
    else
      return nil
    end
  end
end

scheme_str =
function(obj)
  local generic_list_representation = function(obj)
    return "("..table.concat(
      map(function (v)
        return scheme_str(v)
      end, obj),
      " "
    )..")"
  end

  if is_boolean(obj) then
    if obj then
      return "#t"
    else
      return "#f"
    end
  elseif is_number(obj) then
    return obj
  elseif is_sym(obj) then
    return get_sym(obj)
  elseif is_chr(obj) then
    local char = get_chr(obj)
    if char == " " then
      return "#\\space"
    elseif char == "\n" then
      return "#\\newline"
    else
      return "#\\"..char
    end
  elseif is_str(obj) then
    return "\""..get_str(obj).."\""
  elseif is_procedure(obj) then
    return "a procedure"
  elseif is_list(obj) then
    return generic_list_representation(obj)
  elseif is_pair(obj) then
    return "(".. obj[1] .. " . " .. obj[2] .. ")"
  elseif is_vector(obj) then
    return "#"..generic_list_representation(obj)
  elseif is_hash(obj) then
    local str = "#hash("

    for k,v in pairs(obj) do
      str = str.."("..scheme_str(k).." . "..scheme_str(v)..") " -- TODO: make this more beautiful with join and concat instead
    end
    str = str..")"
    return str
  else
    error("invalid obj: "..obj)
  end
end

--[[
utility functions
]]

is_boolean =
function(obj)
  return type(obj) == "boolean"
end

is_number =
function(obj)
  return type(obj) == "number"
end

is_sym =
function(obj)
  return type(obj) == "string" and begins_with(obj, symbol_prefix)
end

is_chr =
function(obj)
  return type(obj) == "string" and begins_with(obj, char_prefix)
end

is_str =
function(obj)
  return type(obj) == "string" and begins_with(obj, string_prefix)
end

is_procedure =
function(obj)
  return type(obj) == "function"
end

is_list =
function(obj)
  return type(obj) == "table" and getmetatable(obj) == nil
end

is_vector =
function(obj)
  return type(obj) == "table" and getmetatable(obj) == vector_mt
end

is_hash =
function(obj)
  return type(obj) == "table" and getmetatable(obj) == hash_mt
end

is_pair =
function(obj)
  local is_ns_pair = (type(obj) == "table" and getmetatable(obj) == pair_mt)
  local is_ns_list = is_list(obj)
  local is_ns_empty_list = is_empty_list(obj)
  
  if is_ns_empty_list then
    return false
  elseif is_ns_pair or is_ns_list then
    return true
  else
    return false
  end
end

is_empty_list =
function(obj)
  return is_list(obj) and #obj == 0
end

--[[
lua specific utility functions
]]

sym = function(str)
  return symbol_prefix..str
end

get_sym = function(str)
  return string.sub(str, #symbol_prefix+1, #str)
end

str = function(str)
  return string_prefix..str
end

get_str = function(str)
  return string.sub(str, #string_prefix+1, #str)
end

chr = function(str)
  return char_prefix..str
end

get_chr = function(str)
  return string.sub(str, #char_prefix+1, #str)
end

new_pair = function(obj1, obj2)
  local pair = {obj1, obj2}
  setmetatable(pair, pair_mt)
  return pair
end

--[[
string scanner
...code is based upon StringScanner in the ruby standard library
]]

ss_new =
function(str)
  return {
    pos = 1,
    peekLength = 100,
    str = str,
    debug = false
  }
end

ss_matches =
function(ss, regexp)
  local match
  match = ss_pr_find_regexp_directly_after_pos(ss, regexp)
  if match then
    if ss['debug'] then
      print("matched: '"..match.."'")
    end
    return #match
  else
    return nil
  end
end

ss_scan =
function(ss, regexp)
  local match
  match = ss_pr_find_regexp_directly_after_pos(ss, regexp)
  if match then
    if ss['debug'] then
      print("scanned: '"..match.."'")
    end
    ss['pos'] = ss['pos'] + #match
    return match
  else
    return nil
  end
end

ss_scan_until =
function(ss, regexp)
  local match_data
  match_data = ss_pr_find_first_regexp_after_pos(ss, regexp)
  if match_data then
    ss['pos'] = ss['pos'] + match_data[1] + #match_data[2]
    return match_data[2]
  else
    return nil
  end
end

ss_skip =
function(ss, regexp)
  local match
  match = ss_pr_find_regexp_directly_after_pos(ss, regexp)
  if match then
    if ss['debug'] then
      print("skipped: '"..match.."'")
    end
    ss['pos'] = ss['pos'] + #match
    return #match
  else
    return nil
  end
end

ss_skip_until =
function(ss, regexp)
  local match_data
  match_data = ss_pr_find_first_regexp_after_pos(ss, regexp)
  if match_data then
    ss['pos'] = ss['pos'] + match_data[1] + #match_data[2]
    return #match_data[2]
  else
    return nil
  end
end

ss_get_char =
function(ss)
  local char
  char = ss['str'][ss['pos']]
  ss['pos'] = ss['pos'] + 1
  return char
end

ss_reset =
function(ss)
  ss['pos'] = 1
end

ss_reset =
function(ss)
  ss['pos'] = 1
end

ss_eos =
function(ss)
  return ss_at_end_of_string(ss)
end

ss_bos =
function(ss)
  return ss_at_beginning_of_string(ss)
end

ss_at_end_of_string =
function(ss)
  return ss['pos'] == ss_pr_eos_pos(ss)
end

ss_at_beginning_of_string =
function(ss)
  return ss['pos'] == 1
end

ss_peek =
function(ss, argLength)
  return string.sub(ss['str'], ss['pos'], ss['pos']+ss['peekLength']-1)
end

ss_as_string =
function(ss)
  local str
  if ss_at_end_of_string(ss) then
    str = "fin"
  else
    local position = ss['pos'] .. "/" .. ss_pr_eos_pos(ss)
    if ss_at_beginning_of_string(ss) then
      str = position .. " @ " .. quote(ss_pr_after_pos(ss))
    else
      str = position .. " " .. quote(ss_pr_before_pos(ss)) .. " @ " .. quote(ss_pr_after_pos(ss))
    end
  end
  return str
end

--[[
stringscanner implementation (considered private)
]]

ss_pr_find_regexp_directly_after_pos =
function(ss, regexp)
  local match_data
  match_data = ss_pr_find_first_regexp(ss, ss['str'], regexp, ss['pos'])
  if match_data then
    if match_data[1] == ss['pos'] then
      return match_data[2]
    else
      return nil
    end
  else
    return nil
  end
end

ss_pr_find_first_regexp_after_pos =
function(ss, regexp)
  local match_data
  match_data = ss_pr_find_first_regexp(ss, ss['str'], regexp, ss['pos'])
  if match_data then
    return { match_data[1]-ss['pos'], match_data[2] }
  else
    return nil
  end
end

ss_pr_find_first_regexp =
function(ss, str, regexp, offset)
  return find_regexp(str, regexp, ss['pos'])[1]
end

ss_pr_before_pos =
function(ss)
  local start = math.max(0, ss['pos']-ss['peekLength'])
  local fin = ss['pos']-1
  local suffix = string.sub(ss['str'], start, fin)

  if start <= 0 then
    return "" .. suffix
  else
    return "..." .. suffix
  end
end

ss_pr_after_pos =
function(ss)
  local start = ss['pos']
  local fin = math.min(#ss['str'], ss['pos']+ss['peekLength']-1)
  local prefix = string.sub(ss['str'], start, fin)

  if fin == #ss['str'] then
    return prefix .. ""
  else
    return prefix .. "..."
  end
end

ss_pr_eos_pos =
function(ss)
  return #ss['str']+1
end

--[[
assertions
]]

assert_equal =
function(a, b)
  if not deepcompare(a, b) then
    error("assertion failed, expected a == b, actual "..as_string(a).." != "..as_string(b))
  end
end

assert_true =
function(a)
  if not a then
    error("assertion failed, expected a == true, actual false == true")
  end
end

assert_false =
function(a)
  if a then
    error("assertion failed, expected a == false, actual true == false")
  end
end

assert_error_thrown = function(func, err_msg)
  local prefix = "assertion failed, expected error " .. quote(err_msg) .. " thrown"
  local ok, err = pcall(func)
  if ok then
    error(prefix .. ", but no error thrown")
  else
    if err ~= err_msg then
      error(prefix .. ", but error " .. quote(err) .. " was thrown.")
    end
  end
end

assert_no_error_thrown = function(func)
  local ok, err = pcall(func)
  if not ok then
    error("assertion failed, expected no thrown error, but error " .. quote(err) .. " was thrown")
  end
end

--[[
lua specific utils
]]

duplicate_list = function(list)
  local new_list = {}
  for i, element in ipairs(list) do
    table.insert(new_list, element) -- TODO: recursively duplicate object *with* metatable setting
  end
  return new_list
end

pop_first = function(tab)
  return table.remove(tab, 1)
end

put_all = function(tab1, tab2)
  for k,v in pairs(tab2) do
    tab1[k] = v
  end
end

split = function(str, delim)
  local result = {}
  for s in string.gmatch(str, "([^"..delim.."]+) ?") do
    table.insert(result, s)
  end
  return result
end

function trim(str)
  return (string.gsub(str, "^%s*(.-)%s*$", "%1"))
end

map = function(func, tab)
  local result = {}
  for i,v in ipairs(tab) do
    table.insert(result, func(v))
  end
  return result
end

filter = function(pred, tab)
  local result = {}
  for i,v in ipairs(tab) do
    if pred(v) then
      table.insert(result, v)
    end
  end
  return result
end

filter_not = function(pred, tab)
  local result = {}
  for i,v in ipairs(tab) do
    if not pred(v) then
      table.insert(result, v)
    end
  end
  return result
end

inject = function(tab, initval, func)
  local val = initval
  for i,v in ipairs(tab) do
    val = func(val, v)
  end
  return val
end

slice = function(tab, start, fin)
  local pos = 1
  local new_tab = {}
  for i = start, fin do
    new_tab[pos] = tab[i]
    pos = pos + 1
  end
  return new_tab
end

round = function(number, quant)
  if quant == 0 then
    return number
  else
    return math.floor(number/(quant or 1) + 0.5) * (quant or 1)
  end
end

table_includes = function(tab, element)
  for _,v in ipairs(tab) do
    if v == element then
      return true
    end
  end
  return false
end

begins_with = function(str, prefix)
  return string.sub(str, 1, #prefix) == prefix
end

print_table = function(t, label)
  if label then
    print(label)
  end

  print(table_as_string(t))
end

table_as_string = function(t, level)
  local lev
  if level ~= nil then
    lev = level
  else
    lev = 1
  end

  local str = ""
  for k,v in pairs(t) do
    if type(v) == "table" then
      for i=1,lev-1 do
        str = str .. "\t"
      end
      str = str .. tostring(k) .. ":\n" .. table_as_string(v, lev+1)
    else
      for i=1,lev-1 do
        str = str .. "\t"
      end
      str = str .. tostring(k) .. ": " .. tostring(v)
    end
    str = str .. "\n"
  end
  return str
end

table_as_string2 = function(t)
  local str = "{"
  local size = #t
  local count = 0
  for k,v in pairs(t) do
    if type(v) == "table" then
      str = str .. tostring(k) .. ": " .. table_as_string2(v)
    else
      str = str .. tostring(k) .. ": " .. tostring(v)
    end
    if count < size-1 then
      str = str .. ", "
    end
    count = count + 1
  end
  return str .. "}"
end

quote = function(str)
  return "\""..str.."\""
end

tablesize = function(tab)
  local count = 0
  for _ in pairs(tab) do
    count = count + 1
  end
  return count
end

-- https://web.archive.org/web/20131225070434/http://snippets.luacode.org/snippets/Deep_Comparison_of_Two_Values_3
deepcompare = function(t1, t2, ignore_mt)
  local ty1 = type(t1)
  local ty2 = type(t2)
  if ty1 ~= ty2 then return false end

  -- non-table types can be directly compared
  if ty1 ~= 'table' and ty2 ~= 'table' then return t1 == t2 end

  -- as well as tables which have the metamethod __eq
  local mt = getmetatable(t1)
  if not ignore_mt and mt and mt.__eq then return t1 == t2 end
  for k1,v1 in pairs(t1) do
    local v2 = t2[k1]
    if v2 == nil or not deepcompare(v1,v2) then return false end
  end
  for k2,v2 in pairs(t2) do
    local v1 = t1[k2]
    if v1 == nil or not deepcompare(v1,v2) then return false end
  end

  return true
end

as_string = function(a)
  if a == nil then
    return "nil"
  elseif type(a) == "table" then
    return table_as_string2(a)
  else
    return tostring(a)
  end
end

find_regexp = function(str, regexp, offset) -- TODO: patterns are used in lua, not regexps
  local result = {}

  local start, fin
  start, fin = string.find(str, regexp, offset)

  while start do
    table.insert(result, {start, string.sub(str, start, fin)})
    start, fin = string.find(str, regexp, start+1)
  end

  return result
end

even = function(number)
  return number % 2 == 0
end

odd = function(number)
  return number % 2 == 1
end

invoke_function = function(func, args)
  if #args == 0 then
    return func()
  elseif #args == 1 then
    return func(args[1])
  elseif #args == 2 then
    return func(args[1], args[2])
  elseif #args == 3 then
    return func(args[1], args[2], args[3])
  elseif #args == 4 then
    return func(args[1], args[2], args[3], args[4])
  elseif #args == 5 then
    return func(args[1], args[2], args[3], args[4], args[5])
  elseif #args == 6 then
    return func(args[1], args[2], args[3], args[4], args[5], args[6])
  elseif #args == 7 then
    return func(args[1], args[2], args[3], args[4], args[5], args[6], args[7])
  elseif #args == 8 then
    return func(args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8])
  else
    return invoke_function_by_eval(func, args)
  end
end

invoke_function_by_eval = function(func, args)
  local eval_env = {}
  eval_env["func"] = func
  eval_env["args"] = vals

  local arglist = ""
  for i=1,#vals do
    arglist = arglist.."args["..i.."]"
    if i ~= #vals then
      arglist = arglist..", "
    end
  end

  local func_call_string = "func("..arglist..")"

  local lua_function = assert(load("return "..func_call_string, nil, "t", eval_env))
  return lua_function()
end


-- main

run_tests() -- TODO: should not clobber _G

print("tests: ok")

init_ns_environment(_G)

run_repl()
