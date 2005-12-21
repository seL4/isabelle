(*  Title:      Pure/Pure.thy
    ID:         $Id$
*)

header {* The Pure theory *}

theory Pure
imports ProtoPure
begin

setup "Context.setup ()"


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
  fix X assume r: "(!!x. PROP A(x)) ==> (!!x. PROP B(x)) ==> PROP X"
  show "PROP X"
  proof (rule r)
    fix x
    from conj show "PROP A(x)" .
    from conj show "PROP B(x)" .
  qed
next
  assume conj: "(!!x. PROP A(x)) && (!!x. PROP B(x))"
  fix x
  fix X assume r: "PROP A(x) ==> PROP B(x) ==> PROP X"
  show "PROP X"
  proof (rule r)
    show "PROP A(x)"
    proof (rule conj)
      assume "!!x. PROP A(x)"
      then show "PROP A(x)" .
    qed
    show "PROP B(x)"
    proof (rule conj)
      assume "!!x. PROP B(x)"
      then show "PROP B(x)" .
    qed
  qed
qed

lemma imp_conjunction [unfolded prop_def]:
  includes meta_conjunction_syntax
  shows "(PROP A ==> PROP prop (PROP B && PROP C)) == (PROP A ==> PROP B) && (PROP A ==> PROP C)"
proof (unfold prop_def, rule)
  assume conj: "PROP A ==> PROP B && PROP C"
  fix X assume r: "(PROP A ==> PROP B) ==> (PROP A ==> PROP C) ==> PROP X"
  show "PROP X"
  proof (rule r)
    assume "PROP A"
    from conj [OF `PROP A`] show "PROP B" .
    from conj [OF `PROP A`] show "PROP C" .
  qed
next
  assume conj: "(PROP A ==> PROP B) && (PROP A ==> PROP C)"
  assume "PROP A"
  fix X assume r: "PROP B ==> PROP C ==> PROP X"
  show "PROP X"
  proof (rule r)
    show "PROP B"
    proof (rule conj)
      assume "PROP A ==> PROP B"
      from this [OF `PROP A`] show "PROP B" .
    qed
    show "PROP C"
    proof (rule conj)
      assume "PROP A ==> PROP C"
      from this [OF `PROP A`] show "PROP C" .
    qed
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
    from conj show "PROP A" .
    from conj show "PROP B" .
  qed
qed

lemma conjunction_assoc:
  includes meta_conjunction_syntax
  shows "((PROP A && PROP B) && PROP C) == (PROP A && (PROP B && PROP C))"
  by (rule equal_intr_rule) (unfold imp_conjunction conjunction_imp)

end
