(* Author: Tobias Nipkow *)

subsection "Abstract Interpretation Test Programs"

theory Abs_Int_Tests
imports Com
begin

text\<open>For constant propagation:\<close>

text\<open>Straight line code:\<close>
definition "test1_const =
 ''y'' ::= N 7;;
 ''z'' ::= Plus (V ''y'') (N 2);;
 ''y'' ::= Plus (V ''x'') (N 0)"

text\<open>Conditional:\<close>
definition "test2_const =
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 5"

text\<open>Conditional, test is relevant:\<close>
definition "test3_const =
 ''x'' ::= N 42;;
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 6"

text\<open>While:\<close>
definition "test4_const =
 ''x'' ::= N 0;; WHILE Bc True DO ''x'' ::= N 0"

text\<open>While, test is relevant:\<close>
definition "test5_const =
 ''x'' ::= N 0;; WHILE Less (V ''x'') (N 1) DO ''x'' ::= N 1"

text\<open>Iteration is needed:\<close>
definition "test6_const =
  ''x'' ::= N 0;; ''y'' ::= N 0;; ''z'' ::= N 2;;
  WHILE Less (V ''x'') (N 1) DO (''x'' ::= V ''y'';; ''y'' ::= V ''z'')"

text\<open>For intervals:\<close>

definition "test1_ivl =
 ''y'' ::= N 7;;
 IF Less (V ''x'') (V ''y'')
 THEN ''y'' ::= Plus (V ''y'') (V ''x'')
 ELSE ''x'' ::= Plus (V ''x'') (V ''y'')"

definition "test2_ivl =
 WHILE Less (V ''x'') (N 100)
 DO ''x'' ::= Plus (V ''x'') (N 1)"

definition "test3_ivl =
 ''x'' ::= N 0;;
 WHILE Less (V ''x'') (N 100)
 DO ''x'' ::= Plus (V ''x'') (N 1)"

definition "test4_ivl =
 ''x'' ::= N 0;; ''y'' ::= N 0;;
 WHILE Less (V ''x'') (N 11)
 DO (''x'' ::= Plus (V ''x'') (N 1);; ''y'' ::= Plus (V ''y'') (N 1))"

definition "test5_ivl =
 ''x'' ::= N 0;; ''y'' ::= N 0;;
 WHILE Less (V ''x'') (N 100)
 DO (''y'' ::= V ''x'';; ''x'' ::= Plus (V ''x'') (N 1))"

definition "test6_ivl =
 ''x'' ::= N 0;;
 WHILE Less (N (- 1)) (V ''x'') DO ''x'' ::= Plus (V ''x'') (N 1)"

end
