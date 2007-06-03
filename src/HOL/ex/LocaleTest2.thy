(*  Title:      HOL/ex/LocaleTest2.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2007 by Clemens Ballarin

More regression tests for locales.
Definitions are less natural in FOL, since there is no selection operator.
Hence we do them in HOL, not in the main test suite for locales:
FOL/ex/LocaleTest.thy
*)

header {* Test of Locale Interpretation *}

theory LocaleTest2
imports Main
begin

ML {* set quick_and_dirty *}    (* allow for thm command in batch mode *)
ML {* set show_hyps *}
ML {* set show_sorts *}


subsection {* Interpretation of Defined Concepts *}

text {* Naming convention for global objects: prefixes D and d *}

(* Group example with defined operation inv *)

locale Dsemi =
  fixes prod (infixl "**" 65)
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"

locale Dmonoid = Dsemi +
  fixes one
  assumes lone: "one ** x = x"
    and rone: "x ** one = x"

definition (in Dmonoid)
  inv where "inv(x) == THE y. x ** y = one & y ** x = one"

lemma (in Dmonoid) inv_unique:
  assumes eq: "y ** x = one" "x ** y' = one"
  shows "y = y'"
proof -
  from eq have "y = y ** (x ** y')" by (simp add: rone)
  also have "... = (y ** x) ** y'" by (simp add: assoc)
  also from eq have "... = y'" by (simp add: lone)
  finally show ?thesis .
qed

locale Dgrp = Dmonoid +
  assumes linv_ex: "EX y. y ** x = one"
    and rinv_ex: "EX y. x ** y = one"

lemma (in Dgrp) linv:
  "inv x ** x = one"
apply (unfold inv_def)
apply (insert rinv_ex [where x = x])
apply (insert linv_ex [where x = x])
apply (erule exE) apply (erule exE)
apply (rule theI2)
apply rule apply assumption
apply (frule inv_unique, assumption)
apply simp
apply (rule inv_unique)
apply fast+
done

lemma (in Dgrp) rinv:
  "x ** inv x = one"
apply (unfold inv_def)
apply (insert rinv_ex [where x = x])
apply (insert linv_ex [where x = x])
apply (erule exE) apply (erule exE)
apply (rule theI2)
apply rule apply assumption
apply (frule inv_unique, assumption)
apply simp
apply (rule inv_unique)
apply fast+
done

lemma (in Dgrp) lcancel:
  "x ** y = x ** z <-> y = z"
proof
  assume "x ** y = x ** z"
  then have "inv(x) ** x ** y = inv(x) ** x ** z" by (simp add: assoc)
  then show "y = z" by (simp add: lone linv)
qed simp

interpretation Dint: Dmonoid ["op +" "0::int"]
  where "Dmonoid.inv (op +) (0::int)" = "uminus"
proof -
  show "Dmonoid (op +) (0::int)" by unfold_locales auto
  note Dint = this (* should have this as an assumption in further goals *)
  {
    fix x
    have "Dmonoid.inv (op +) (0::int) x = - x"
      by (auto simp: Dmonoid.inv_def [OF Dint])
  }
  then show "Dmonoid.inv (op +) (0::int) == uminus"
    by (rule_tac eq_reflection) (fast intro: ext)
qed

thm Dmonoid.inv_def Dint.inv_def

lemma "- x \<equiv> THE y. x + y = 0 \<and> y + x = (0::int)"
  apply (rule Dint.inv_def) done

interpretation Dclass: Dmonoid ["op +" "0::'a::ab_group_add"]
  where "Dmonoid.inv (op +) (0::'a::ab_group_add)" = "uminus"
proof -
  show "Dmonoid (op +) (0::'a::ab_group_add)" by unfold_locales auto
  note Dclass = this (* should have this as an assumption in further goals *)
  {
    fix x
    have "Dmonoid.inv (op +) (0::'a::ab_group_add) x = - x"
      by (auto simp: Dmonoid.inv_def [OF Dclass] equals_zero_I [symmetric])
  }
  then show "Dmonoid.inv (op +) (0::'a::ab_group_add) == uminus"
    by (rule_tac eq_reflection) (fast intro: ext)
qed

interpretation Dclass: Dgrp ["op +" "0::'a::ring"]
apply unfold_locales
apply (rule_tac x="-x" in exI) apply simp
apply (rule_tac x="-x" in exI) apply simp
done

(* Equation for inverse from Dclass: Dmonoid effective. *)

thm Dclass.linv
lemma "-x + x = (0::'a::ring)" apply (rule Dclass.linv) done

(* Equations have effect in "subscriptions" *)

(* In the same module *)

lemma (in Dmonoid) trivial:
  "inv one = inv one"
  by rule

thm Dclass.trivial

(* Inherited: interpretation *)

lemma (in Dgrp) inv_inv:
  "inv (inv x) = x"
proof -
  have "inv x ** inv (inv x) = inv x ** x"
    by (simp add: linv rinv)
  then show ?thesis by (simp add: lcancel)
qed

thm Dclass.inv_inv
lemma "- (- x) = (x::'a::ring)"
  apply (rule Dclass.inv_inv) done

end
