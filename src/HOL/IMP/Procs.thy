header "Extensions and Variations of IMP"

theory Procs imports BExp begin

subsection "Procedures and Local Variables"

datatype
  com = SKIP 
      | Assign name aexp         ("_ ::= _" [1000, 61] 61)
      | Semi   com  com          ("_;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Var    name com         ("(1{VAR _;;/ _})")
      | Proc   name com com     ("(1{PROC _ = _;;/ _})")
      | CALL   name

definition "test_com =
{VAR ''x'';;
 ''x'' ::= N 0;
 {PROC ''p'' = ''x'' ::= Plus (V ''x'') (V ''x'');;
  {PROC ''q'' = CALL ''p'';;
   {VAR ''x'';;
    ''x'' ::= N 5;
    {PROC ''p'' = ''x'' ::= Plus (V ''x'') (N 1);;
     CALL ''q''; ''y'' ::= V ''x''}}}}}"

end
