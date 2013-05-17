header "Extensions and Variations of IMP"

theory Procs imports BExp begin

subsection "Procedures and Local Variables"

type_synonym pname = string

datatype
  com = SKIP 
      | Assign vname aexp        ("_ ::= _" [1000, 61] 61)
      | Seq    com  com          ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Var    vname com        ("(1{VAR _;/ _})")
      | Proc   pname com com    ("(1{PROC _ = _;/ _})")
      | CALL   pname

definition "test_com =
{VAR ''x'';
 {PROC ''p'' = ''x'' ::= N 1;
  {PROC ''q'' = CALL ''p'';
   {VAR ''x'';
    ''x'' ::= N 2;;
    {PROC ''p'' = ''x'' ::= N 3;
     CALL ''q'';; ''y'' ::= V ''x''}}}}}"

end
