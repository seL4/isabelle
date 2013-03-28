theory Collecting_Examples
imports Collecting Vars
begin

subsection "Pretty printing state sets"

text{* Tweak code generation to work with sets of non-equality types: *}
declare insert_code[code del] union_coset_filter[code del]
lemma insert_code [code]:  "insert x (set xs) = set (x#xs)"
by simp

text{* Collect variables in acom: *}
fun cvars :: "'a acom \<Rightarrow> vname set" where
"cvars (SKIP {P})= {}" |
"cvars (x::=e {P}) = {x} \<union> vars e" |
"cvars (c1;c2) = cvars c1 \<union> cvars c2" |
"cvars (IF b THEN {P1} c1 ELSE {P2} c2 {Q}) = vars b \<union> cvars c1 \<union> cvars c2" |
"cvars ({I} WHILE b DO {P} c {Q}) = vars b \<union> cvars c"

text{* Compensate for the fact that sets may now have duplicates: *}
definition compact :: "'a set \<Rightarrow> 'a set" where
"compact X = X"

lemma [code]: "compact(set xs) = set(remdups xs)"
by(simp add: compact_def)

definition "vars_acom = compact o cvars"

text{* In order to display commands annotated with state sets, states must be
translated into a printable format as sets of variable-state pairs, for the
variables in the command: *}

definition show_acom ::
  "state set acom \<Rightarrow> (vname*val)set set acom" where
"show_acom C = map_acom (\<lambda>S. (\<lambda>s. (\<lambda>x. (x, s x)) ` (vars_acom C)) ` S) C"


subsection "Examples"

definition "c0 = WHILE Less (V ''x'') (N 3)
                DO ''x'' ::= Plus (V ''x'') (N 2)"
definition C0 :: "state set acom" where "C0 = anno {} c0"

text{* Collecting semantics: *}

value "show_acom (((step {<>}) ^^ 1) C0)"
value "show_acom (((step {<>}) ^^ 2) C0)"
value "show_acom (((step {<>}) ^^ 3) C0)"
value "show_acom (((step {<>}) ^^ 4) C0)"
value "show_acom (((step {<>}) ^^ 5) C0)"
value "show_acom (((step {<>}) ^^ 6) C0)"
value "show_acom (((step {<>}) ^^ 7) C0)"
value "show_acom (((step {<>}) ^^ 8) C0)"

text{* Small-step semantics: *}
value "show_acom (((step {}) ^^ 0) (step {<>} C0))"
value "show_acom (((step {}) ^^ 1) (step {<>} C0))"
value "show_acom (((step {}) ^^ 2) (step {<>} C0))"
value "show_acom (((step {}) ^^ 3) (step {<>} C0))"
value "show_acom (((step {}) ^^ 4) (step {<>} C0))"
value "show_acom (((step {}) ^^ 5) (step {<>} C0))"
value "show_acom (((step {}) ^^ 6) (step {<>} C0))"
value "show_acom (((step {}) ^^ 7) (step {<>} C0))"
value "show_acom (((step {}) ^^ 8) (step {<>} C0))"

end
