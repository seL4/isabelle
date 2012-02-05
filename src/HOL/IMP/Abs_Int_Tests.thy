theory Abs_Int_Tests
imports ACom
begin

subsection "Test Programs"

text{* For constant propagation: *}

text{* Straight line code: *}
definition "test1_const =
 ''y'' ::= N 7;
 ''z'' ::= Plus (V ''y'') (N 2);
 ''y'' ::= Plus (V ''x'') (N 0)"

text{* Conditional: *}
definition "test2_const =
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 5"

text{* Conditional, test is relevant: *}
definition "test3_const =
 ''x'' ::= N 42;
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 6"

text{* While: *}
definition "test4_const =
 ''x'' ::= N 0; WHILE Bc True DO ''x'' ::= N 0"

text{* While, test is relevant: *}
definition "test5_const =
 ''x'' ::= N 0; WHILE Less (V ''x'') (N 1) DO ''x'' ::= N 1"

text{* Iteration is needed: *}
definition "test6_const =
  ''x'' ::= N 0; ''y'' ::= N 0; ''z'' ::= N 2;
  WHILE Less (V ''x'') (N 1) DO (''x'' ::= V ''y''; ''y'' ::= V ''z'')"

text{* For intervals: *}

definition "test1_ivl =
 ''y'' ::= N 7;
 IF Less (V ''x'') (V ''y'')
 THEN ''y'' ::= Plus (V ''y'') (V ''x'')
 ELSE ''x'' ::= Plus (V ''x'') (V ''y'')"

definition "test2_ivl =
 WHILE Less (V ''x'') (N 100)
 DO ''x'' ::= Plus (V ''x'') (N 1)"

definition "test3_ivl =
 ''x'' ::= N 7;
 WHILE Less (V ''x'') (N 100)
 DO ''x'' ::= Plus (V ''x'') (N 1)"

definition "test4_ivl =
 ''x'' ::= N 0; ''y'' ::= N 0;
 WHILE Less (V ''x'') (N 11)
 DO (''x'' ::= Plus (V ''x'') (N 1); ''y'' ::= Plus (V ''y'') (N 1))"

definition "test5_ivl =
 ''x'' ::= N 0; ''y'' ::= N 0;
 WHILE Less (V ''x'') (N 1000)
 DO (''y'' ::= V ''x''; ''x'' ::= Plus (V ''x'') (N 1))"

definition "test6_ivl =
 ''x'' ::= N 0;
 WHILE Less (V ''x'') (N 1) DO ''x'' ::= Plus (V ''x'') (N -1)"

end
