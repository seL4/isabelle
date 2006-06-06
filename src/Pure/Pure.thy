(*  Title:      Pure/Pure.thy
    ID:         $Id$

The Pure theory.
*)

header {* The Pure theory *}

theory Pure
imports ProtoPure
begin
ML{*set Toplevel.debug*}
setup  -- {* Common setup of internal components *}


subsection {* Meta-level connectives in assumptions *}

lemma meta_mp:
  assumes "PROP P ==> PROP Q" and "PROP P"
  shows "PROP Q"
    by (rule `PROP P ==> PROP Q` [OF `PROP P`])

lemma meta_spec:
  assumes "!!x. PROP P(x)"
  shows "PROP P(x)"
    by (rule `!!x. PROP P(x)`)

lemmas meta_allE = meta_spec [elim_format]


subsection {* Meta-level conjunction *}

locale (open) meta_conjunction_syntax =
  fixes meta_conjunction :: "prop => prop => prop"  (infixr "&&" 2)

parse_translation {*
  [("\<^fixed>meta_conjunction", fn [t, u] => Logic.mk_conjunction (t, u))]
*}

lemma all_conjunction:
  includes meta_conjunction_syntax
  shows "(!!x. PROP A(x) && PROP B(x)) == ((!!x. PROP A(x)) && (!!x. PROP B(x)))"
proof
  assume conj: "!!x. PROP A(x) && PROP B(x)"
  show "(\<And>x. PROP A(x)) && (\<And>x. PROP B(x))"
  proof -
    fix x
    from conj show "PROP A(x)" by (rule conjunctionD1)
    from conj show "PROP B(x)" by (rule conjunctionD2)
  qed
next
  assume conj: "(!!x. PROP A(x)) && (!!x. PROP B(x))"
  fix x
  show "PROP A(x) && PROP B(x)"
  proof -
    show "PROP A(x)" by (rule conj [THEN conjunctionD1, rule_format])
    show "PROP B(x)" by (rule conj [THEN conjunctionD2, rule_format])
  qed
qed

lemma imp_conjunction:
  includes meta_conjunction_syntax
  shows "(PROP A ==> PROP B && PROP C) == (PROP A ==> PROP B) && (PROP A ==> PROP C)"
proof
  assume conj: "PROP A ==> PROP B && PROP C"
  show "(PROP A ==> PROP B) && (PROP A ==> PROP C)"
  proof -
    assume "PROP A"
    from conj [OF `PROP A`] show "PROP B" by (rule conjunctionD1)
    from conj [OF `PROP A`] show "PROP C" by (rule conjunctionD2)
  qed
next
  assume conj: "(PROP A ==> PROP B) && (PROP A ==> PROP C)"
  assume "PROP A"
  show "PROP B && PROP C"
  proof -
    from `PROP A` show "PROP B" by (rule conj [THEN conjunctionD1])
    from `PROP A` show "PROP C" by (rule conj [THEN conjunctionD2])
  qed
qed

lemma conjunction_imp:
  includes meta_conjunction_syntax
  shows "(PROP A && PROP B ==> PROP C) == (PROP A ==> PROP B ==> PROP C)"
proof
  assume r: "PROP A && PROP B ==> PROP C"
  assume "PROP A" and "PROP B"
  show "PROP C" by (rule r) -
next
  assume r: "PROP A ==> PROP B ==> PROP C"
  assume conj: "PROP A && PROP B"
  show "PROP C"
  proof (rule r)
    from conj show "PROP A" by (rule conjunctionD1)
    from conj show "PROP B" by (rule conjunctionD2)
  qed
qed

end
