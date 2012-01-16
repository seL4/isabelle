theory Collecting_list
imports ACom
begin

subsection "Executable Collecting Semantics on lists"

fun step :: "state list \<Rightarrow> state list acom \<Rightarrow> state list acom" where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  (x ::= e {[s(x := aval e s). s \<leftarrow> S]})" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step [s \<leftarrow> S. bval b s] c1 ELSE step [s\<leftarrow>S. \<not> bval b s] c2
   {post c1 @ post c2}" |
"step S ({Inv} WHILE b DO c {P}) =
  {S @ post c} WHILE b DO (step [s\<leftarrow>Inv. bval b s] c) {[s\<leftarrow>Inv. \<not> bval b s]}"


text{* Examples: *}

definition "c = WHILE Less (V ''x'') (N 3)
                DO ''x'' ::= Plus (V ''x'') (N 2)"
definition "c0 = anno [] c"

definition "show_acom xs = map_acom (map (show_state xs))"


text{* Collecting semantics: *}

value "show_acom [''x''] (((step [<>]) ^^ 6) c0)"


text{* Small step semantics: *}

value "show_acom [''x''] (((step []) ^^ 5) (step [<>] c0))"

end
