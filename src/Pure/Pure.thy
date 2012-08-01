theory Pure
begin

section {* Further content for the Pure theory *}

subsection {* Meta-level connectives in assumptions *}

lemma meta_mp:
  assumes "PROP P ==> PROP Q" and "PROP P"
  shows "PROP Q"
    by (rule `PROP P ==> PROP Q` [OF `PROP P`])

lemmas meta_impE = meta_mp [elim_format]

lemma meta_spec:
  assumes "!!x. PROP P x"
  shows "PROP P x"
    by (rule `!!x. PROP P x`)

lemmas meta_allE = meta_spec [elim_format]

lemma swap_params:
  "(!!x y. PROP P x y) == (!!y x. PROP P x y)" ..


subsection {* Meta-level conjunction *}

lemma all_conjunction:
  "(!!x. PROP A x &&& PROP B x) == ((!!x. PROP A x) &&& (!!x. PROP B x))"
proof
  assume conj: "!!x. PROP A x &&& PROP B x"
  show "(!!x. PROP A x) &&& (!!x. PROP B x)"
  proof -
    fix x
    from conj show "PROP A x" by (rule conjunctionD1)
    from conj show "PROP B x" by (rule conjunctionD2)
  qed
next
  assume conj: "(!!x. PROP A x) &&& (!!x. PROP B x)"
  fix x
  show "PROP A x &&& PROP B x"
  proof -
    show "PROP A x" by (rule conj [THEN conjunctionD1, rule_format])
    show "PROP B x" by (rule conj [THEN conjunctionD2, rule_format])
  qed
qed

lemma imp_conjunction:
  "(PROP A ==> PROP B &&& PROP C) == (PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
proof
  assume conj: "PROP A ==> PROP B &&& PROP C"
  show "(PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
  proof -
    assume "PROP A"
    from conj [OF `PROP A`] show "PROP B" by (rule conjunctionD1)
    from conj [OF `PROP A`] show "PROP C" by (rule conjunctionD2)
  qed
next
  assume conj: "(PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
  assume "PROP A"
  show "PROP B &&& PROP C"
  proof -
    from `PROP A` show "PROP B" by (rule conj [THEN conjunctionD1])
    from `PROP A` show "PROP C" by (rule conj [THEN conjunctionD2])
  qed
qed

lemma conjunction_imp:
  "(PROP A &&& PROP B ==> PROP C) == (PROP A ==> PROP B ==> PROP C)"
proof
  assume r: "PROP A &&& PROP B ==> PROP C"
  assume ab: "PROP A" "PROP B"
  show "PROP C"
  proof (rule r)
    from ab show "PROP A &&& PROP B" .
  qed
next
  assume r: "PROP A ==> PROP B ==> PROP C"
  assume conj: "PROP A &&& PROP B"
  show "PROP C"
  proof (rule r)
    from conj show "PROP A" by (rule conjunctionD1)
    from conj show "PROP B" by (rule conjunctionD2)
  qed
qed

end

