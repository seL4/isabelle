theory Collecting_list
imports ACom
begin

subsection "Executable Collecting Semantics on lists"

fun step_cs :: "state list \<Rightarrow> state list acom \<Rightarrow> state list acom" where
"step_cs S (SKIP {P}) = (SKIP {S})" |
"step_cs S (x ::= e {P}) =
  (x ::= e {[s(x := aval e s). s \<leftarrow> S]})" |
"step_cs S (c1; c2) = step_cs S c1; step_cs (post c1) c2" |
"step_cs S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step_cs [s \<leftarrow> S. bval b s] c1 ELSE step_cs [s\<leftarrow>S. \<not> bval b s] c2
   {post c1 @ post c2}" |
"step_cs S ({Inv} WHILE b DO c {P}) =
  {S @ post c} WHILE b DO (step_cs [s\<leftarrow>Inv. bval b s] c) {[s\<leftarrow>Inv. \<not> bval b s]}"

definition "c = WHILE Less (V ''x'') (N 2) DO ''x'' ::= Plus (V ''x'') (N 1)"
definition "c0 = anno [] c"

definition "show_acom xs = map_acom (map (show_state xs))"

value "show_acom [''x''] (((step_cs [<>]) ^^ 6) c0)"

end
