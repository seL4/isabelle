theory Collecting_Examples
imports Collecting
begin

text{* Tweak code generation to work with sets of non-equality types: *}
declare insert_code[code del] union_coset_filter[code del]
lemma insert_code [code]:  "insert x (set xs) = set (x#xs)"
by simp

text{* The example: *}
definition "c = WHILE Less (V ''x'') (N 3)
                DO ''x'' ::= Plus (V ''x'') (N 2)"
definition c0 :: "state set acom" where "c0 = anno {} c"

definition "show_acom xs = map_acom (\<lambda>S. show_state xs ` S)"

text{* Collecting semantics: *}
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 1) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 2) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 3) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 4) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 5) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 6) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 7) c0)"
value "show_acom [''x''] (((step {\<lambda>x. 0}) ^^ 8) c0)"

text{* Small-step semantics: *}
value "show_acom [''x''] (((step {}) ^^ 0) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 1) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 2) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 3) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 4) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 5) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 6) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 7) (step {\<lambda>x. 0} c0))"
value "show_acom [''x''] (((step {}) ^^ 8) (step {\<lambda>x. 0} c0))"


end
