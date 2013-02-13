theory Collecting_Examples
imports Collecting
begin

text{* Tweak code generation to work with sets of non-equality types: *}
declare insert_code[code del] union_coset_filter[code del]
lemma insert_code [code]:  "insert x (set xs) = set (x#xs)"
by simp

text{* In order to display commands annotated with state sets,
states must be translated into a printable format as lists of pairs,
for a given set of variable names. This is what @{text show_acom} does: *}

definition show_acom ::
  "vname list \<Rightarrow> state set acom \<Rightarrow> (vname*val)list set acom" where
"show_acom xs = map_acom (\<lambda>S. (\<lambda>s. map (\<lambda>x. (x, s x)) xs) ` S)"


text{* The example: *}
definition "c = WHILE Less (V ''x'') (N 3)
                DO ''x'' ::= Plus (V ''x'') (N 2)"
definition C0 :: "state set acom" where "C0 = anno {} c"

text{* Collecting semantics: *}

value "show_acom [''x''] (((step {<>}) ^^ 1) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 2) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 3) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 4) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 5) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 6) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 7) C0)"
value "show_acom [''x''] (((step {<>}) ^^ 8) C0)"

text{* Small-step semantics: *}
value "show_acom [''x''] (((step {}) ^^ 0) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 1) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 2) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 3) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 4) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 5) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 6) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 7) (step {<>} C0))"
value "show_acom [''x''] (((step {}) ^^ 8) (step {<>} C0))"

end
