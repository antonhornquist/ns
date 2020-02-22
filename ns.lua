-- an ad-hoc, informally-specified, bug-ridden, slow implementation of half of Common Lisp.

--[[
]]

--[[

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

]]

-- tests

local run_tests
local run_rep_tests1
local run_rep_tests2
local run_rep_tests3
local ss_test
local ss_as_string_test
local read_test

-- repl

local repl
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
  _NS_ENV = {}
  init_ns_environment(_NS_ENV)
  -- run_rep_tests1()
  -- run_rep_tests2()
  -- run_rep_tests3()
  ss_test()
  ss_as_string_test()
  read_test()
end

-- TODO: assertions
run_rep_tests1 = function()
  rep("(append (quote (1 2 3)) (quote (4 5 99)))")

  rep("(+ 2 5)")

  rep("(quote (+ 2 5))")

  rep("(define tst 4321)")

  rep("(set! tst 1234)")

  rep("tst")

  rep("(define tst (+ 2 5))")

  rep("tst")

  rep(
  [[
  (define func
  (lambda (op) (op 4 2)))
  ]]
  )

  rep("(func +)")
  rep("(func -)")
  rep("(func *)")
  rep("(func /)")

  print("test-1")
  print(_NS_ENV["func"](function(a, b) return a + b + b end))
  print()
  print()
  print()

  rep([[
  (lambda (x) (1))
  ]])

  rep([[
  (if #t 1 2)
  ]])

  rep([[
  (define factorial
  (lambda [n]
  (if
  (<= n 1) 1 (* n (factorial (- n 1))))))
  ]])

  rep([[
  (factorial 12)
  ]])

  --[[ TODO: strings do not work
  (cond
  [(<= 5 2) (display "yeah")]
  [(not (= 1 1)) (display "two)]
  [else (display "else")])
  ]]

  rep([[
  (cond
  [(<= 7 5) 1]
  [(not (= 1 1)) 2]
  [else 3])
  ]])

  rep([[
  (case (+ 3 3)
  [(1 6 7) (quote one)]
  [(a 7 c) (quote two)]
  [else (quote else)])
  ]])

  rep([[
  (and (= 2 2) (> 2 1))
  ]])

  rep([[
  (and 1 2 (quote c) (quote (f g)))]])

  rep([[
  (display "test")
  ]])

  rep([[
  (define my-test
  (lambda (a)
  (begin
  (display (string-append "a+5=" (+ a 5)))
  (newline)
  (display (/ a 2))
  (newline)
  (display (* a 2))
  (newline)))
  )
  ]])

  rep("(my-test 2)")

  print("test-1")
  print(_G["my-test"](2))
  print()
  print()
  print()

  rep("#a")

  -- TODO rep("#(1 2 3)")

  rep("(boolean? #a)")

  rep("(boolean? #t)")

  rep("(eqv? \"abc\" \"cdef\")")

  rep("(eqv? \"abc\" \"abc\")")

  rep("(reverse (quote (1 2 3)))")

  rep("(reverse '(1 2 3))")

  rep("(assoc 'a '((a b) (c d) (e f)))")
  rep("(assoc 'b '((a b) (c d) (e f)))")
  rep("(assoc 'c '((a b) (c d) (e f)))")

  rep("`(assoc c ((a b) (c d) (e f)))")
  rep("(quasiquote (assoc c ((a b) (c d) (e f))))")

  rep("(define d 4424)")
  rep("(define l '(1 2 3))")
  rep("`(assoc c ((a b) (c ,d) (e @l)))")
end

-- TODO: assertions
run_rep_tests2 = function()
  rep([[
  (define println (lambda (x) (begin (display x) (newline))))
  ]])
  rep([[
  (define identity (lambda (x) x))
  ]])
  rep([[
  (define sc/read-sound identity)
  ]])
  rep([[
  (define sc/free-sound identity)
  ]])
  rep([[
  (define sc/play-seq
  (lambda (seq_def)
  (let ((dispatch
  (lambda (cmd)
  (let ( (op (car cmd)) (args (cdr cmd)) )
  (cond ((equal? cmd 'stop) (println "stop!"))
  (else (println (string-append "idunno about this op: " (symbol->string op)))))))))
  dispatch)))
  ]])
  rep([[
  (define bassdrum (sc/read-sound "BD_09.wav"))
  ]])
  rep([[
  (define snare (sc/read-sound "SN_43.wav"))
  ]])
  rep([[
  (define hihat (sc/read-sound "Hihat.wav"))
  ]])
  rep([[
  (define seq1-def 
  `(
  (tempo 130 bpm)
  (kit b ,bassdrum s ,snare h ,hihat)
  (sequence
  b___b___b___b_b_
  ____s_______s_ss
  __h___h___h__hh_)))
  ]])
  rep([[
  (define seq1-def-noquasi
  (list
  '(tempo 130 bpm)
  (list 'kit 'b bassdrum 's snare 'h hihat)
  '(sequence
  b___b___b___b_b_
  ____s_______s_ss
  __h___h___h__hh_)))
  ]])
  rep([[
  (define seq1-kit
  (list 'b bassdrum 's snare 'h hihat))
  ]])
  rep([[
  (define seq1-def-noquasi-vari
  (list '(tempo 130 bpm)
  (append '(kit) seq1-kit)
  '(sequence
  b___b___b___b_b_
  ____s_______s_ss
  __h___h___h__hh_)))
  ]])
  rep("seq1-def")
  --  rep([[
  --(for-each println
  --		  (list
  --			(assoc 'kit seq1-def)
  --			(assoc 'tempo seq1-def)
  --			(assoc 'sequence seq1-def)))
  --]])
end

-- TODO: assertions
run_rep_tests3 = function()
  imaginary = [[
  (define hihat2 "Hihat.wav")
  (define hihat2 "Hats R Us.wav")
  (define hihat2 "Snare
  Me
  Then.wav")

  (define hihat2 "Snare
  Me
  Then.wav")

  `(set-kit b ,bassdrum s ,snare h ,hihat2)

  '(set-sequence
  b___b___b_bb__b_
  ____s__s_s__s_ss
  __h___h___h__hh_)
  ]]
  rep(imaginary)
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

--[[
repl
]]

repl =
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
  env = env or _NS_ENV or _G
  local val = eval(read(str), env)
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
    ['apply'] = function(proc, args)
      error("TODO: apply")
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
      return tonumber(get_chr(char))
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
      table.insert(obj2, 1, obj1)
      return obj2
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
      return obj1 == obj2
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
      return obj1 == obj2 -- TODO
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
      return string.char(n)
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
      return is_list(objs)
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
      error("TODO: make-vector")
    end,
    -- r4rs essential procedure: (map proc list1 list2 ...)
    ['map'] = function(proc, ...)
      local lists = {...}

      local result = {}

      for i,v in ipairs(lists) do
        local args = {}
        for _,v in ipairs(lists) do
          args[i] = v
        end
        result[i] = invoke_function(proc, args)
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
      error("TODO: set-car!")
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
        sym(get_str(string))
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
        str(get_sym(symbol))
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
      -- TODO
      error("TODO: vector?")
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

  local value
  local result

  -- TODO print(ss_as_string(ss))

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
  local rg_symbol = "[a-zA-Z+-./<=>*!?:%$%_&~%^][0-9a-zA-Z+-./<=>*!?:%$%_&~%^]*"
  local rg_char = "#\\[0-9a-zA-Z ]" -- TODO: not enough, will include #\mutliple_chars
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

    -- TODO https://www.gnu.org/software/mit-scheme/documentation/mit-scheme-ref/Conditionals.html
    if op == sym("and") then
      -- r4rs essential syntax: (and <test1> ...)
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
      local vars = expr[2]
      local body = expr[3]
      if #expr > 3 then
        -- error("in "..scheme_str(expr) ..": lambda body error: 1 expression expected, found "..#expr)
        error("lambda body error: 1 expression expected, found "..#expr)
      end

      local vars_by_name = {}
      for i,v in ipairs(vars) do
        vars_by_name[i] = get_sym(v)
      end
      return function(...)
        local args = {...}
        -- TODO print_table(args)
        return eval(body, make_env(vars_by_name, args, env))
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

        print_table({binding}, "{binding}")
        print_table(new_body, "new_body")
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
  return type(obj) == "table" and not getmetatable(obj)
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
  return type(obj) == "table" and #obj > 0 -- TODO: not accurate
end

is_empty_list =
function(obj)
  return is_list(obj) and #obj == 0
end

--[[
lua specific sym/str/chr utility functions
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
  match = ss_pr_find_regext_directly_after_pos(ss, regexp)
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
  match = ss_pr_find_regext_directly_after_pos(ss, regexp)
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
  match = ss_pr_find_regext_directly_after_pos(ss, regexp)
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

ss_pr_find_regext_directly_after_pos =
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

--[[
lua specific utils
]]

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
    return ""..a
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

run_tests()

print("tests: ok")

init_ns_environment(_G)

repl()
