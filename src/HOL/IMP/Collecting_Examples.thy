theory Collecting_Examples
imports Collecting
begin

text{* Tweak code generation to work with sets of non-equality types: *}
declare insert_code[code del] union_coset_filter[code del]
lemma insert_code [code]:  "insert x (set xs) = set (x#xs)"
by simp

text{* Make assignment rule executable: *}
declare step.simps(2)[code del]
lemma [code]: "step S (x ::= e {P}) = (x ::= e {(%s. s(x := aval e s)) ` S})"
by auto
declare step.simps(1,3-)[code]

text{* The example: *}
definition "c = WHILE Less (V ''x'') (N 3)
                DO ''x'' ::= Plus (V ''x'') (N 2)"
definition c0 :: "state set acom" where "c0 = anno {} c"

definition "show_acom xs = map_acom (\<lambda>S. show_state xs ` S)"

text{* Collecting semantics: *}
value "show_acom [''x''] (((step {%x. 0}) ^^ 1) c0)"
value "show_acom [''x''] (((step {%x. 0}) ^^ 2) c0)"
value "show_acom [''x''] (((step {%x. 0}) ^^ 3) c0)"
value "show_acom [''x''] (((step {%x. 0}) ^^ 4) c0)"
value "show_acom [''x''] (((step {%x. 0}) ^^ 5) c0)"
value "show_acom [''x''] (((step {%x. 0}) ^^ 6) c0)"

text{* Small-step semantics: *}
value "show_acom [''x''] (((step {}) ^^ 0) (step {%x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 1) (step {%x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 2) (step {%x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 3) (step {%x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 4) (step {%x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 5) (step {%x. 0} c0))"


end
