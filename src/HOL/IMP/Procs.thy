section "Extensions and Variations of IMP"

theory Procs imports BExp begin

subsection "Procedures and Local Variables"

type_synonym pname = string

datatype
  com = SKIP 
      | Assign vname aexp        (\<open>_ ::= _\<close> [1000, 61] 61)
      | Seq    com  com          (\<open>_;;/ _\<close>  [60, 61] 60)
      | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
      | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)
      | Var    vname com        (\<open>(1{VAR _;/ _})\<close>)
      | Proc   pname com com    (\<open>(1{PROC _ = _;/ _})\<close>)
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
