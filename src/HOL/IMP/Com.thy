section "IMP --- A Simple Imperative Language"

theory Com imports BExp begin

datatype
  com = SKIP 
      | Assign vname aexp       (\<open>_ ::= _\<close> [1000, 61] 61)
      | Seq    com  com         (\<open>_;;/ _\<close>  [60, 61] 60)
      | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
      | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)

end
