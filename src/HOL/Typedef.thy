(*  Title:      HOL/Typedef.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Munich

Misc set-theory lemmas and HOL type definitions.
*)

theory Typedef = Set
files "subset.ML" "equalities.ML" "mono.ML"
  "Tools/induct_attrib.ML" ("Tools/typedef_package.ML"):

(* Courtesy of Stephan Merz *)
lemma Least_mono: 
  "mono (f::'a::order => 'b::order) ==> EX x:S. ALL y:S. x <= y
    ==> (LEAST y. y : f ` S) = f (LEAST x. x : S)"
  apply clarify
  apply (erule_tac P = "%x. x : S" in LeastI2)
   apply fast
  apply (rule LeastI2)
  apply (auto elim: monoD intro!: order_antisym)
  done


(*belongs to theory Set*)
setup Rulify.setup


section {* HOL type definitions *}

constdefs
  type_definition :: "('a => 'b) => ('b => 'a) => 'b set => bool"
  "type_definition Rep Abs A ==
    (\<forall>x. Rep x \<in> A) \<and>
    (\<forall>x. Abs (Rep x) = x) \<and>
    (\<forall>y \<in> A. Rep (Abs y) = y)"
  -- {* This will be stated as an axiom for each typedef! *}

lemma type_definitionI [intro]:
  "(!!x. Rep x \<in> A) ==>
    (!!x. Abs (Rep x) = x) ==>
    (!!y. y \<in> A ==> Rep (Abs y) = y) ==>
    type_definition Rep Abs A"
  by (unfold type_definition_def) blast

theorem Rep: "type_definition Rep Abs A ==> Rep x \<in> A"
  by (unfold type_definition_def) blast

theorem Rep_inverse: "type_definition Rep Abs A ==> Abs (Rep x) = x"
  by (unfold type_definition_def) blast

theorem Abs_inverse: "type_definition Rep Abs A ==> y \<in> A ==> Rep (Abs y) = y"
  by (unfold type_definition_def) blast

theorem Rep_inject: "type_definition Rep Abs A ==> (Rep x = Rep y) = (x = y)"
proof -
  assume tydef: "type_definition Rep Abs A"
  show ?thesis
  proof
    assume "Rep x = Rep y"
    hence "Abs (Rep x) = Abs (Rep y)" by (simp only:)
    thus "x = y" by (simp only: Rep_inverse [OF tydef])
  next
    assume "x = y"
    thus "Rep x = Rep y" by simp
  qed
qed

theorem Abs_inject:
  "type_definition Rep Abs A ==> x \<in> A ==> y \<in> A ==> (Abs x = Abs y) = (x = y)"
proof -
  assume tydef: "type_definition Rep Abs A"
  assume x: "x \<in> A" and y: "y \<in> A"
  show ?thesis
  proof
    assume "Abs x = Abs y"
    hence "Rep (Abs x) = Rep (Abs y)" by simp
    moreover from x have "Rep (Abs x) = x" by (rule Abs_inverse [OF tydef])
    moreover from y have "Rep (Abs y) = y" by (rule Abs_inverse [OF tydef])
    ultimately show "x = y" by (simp only:)
  next
    assume "x = y"
    thus "Abs x = Abs y" by simp
  qed
qed

theorem Rep_cases:
  "type_definition Rep Abs A ==> y \<in> A ==> (!!x. y = Rep x ==> P) ==> P"
proof -
  assume tydef: "type_definition Rep Abs A"
  assume y: "y \<in> A" and r: "(!!x. y = Rep x ==> P)"
  show P
  proof (rule r)
    from y have "Rep (Abs y) = y" by (rule Abs_inverse [OF tydef])
    thus "y = Rep (Abs y)" ..
  qed
qed

theorem Abs_cases:
  "type_definition Rep Abs A ==> (!!y. x = Abs y ==> y \<in> A ==> P) ==> P"
proof -
  assume tydef: "type_definition Rep Abs A"
  assume r: "!!y. x = Abs y ==> y \<in> A ==> P"
  show P
  proof (rule r)
    have "Abs (Rep x) = x" by (rule Rep_inverse [OF tydef])
    thus "x = Abs (Rep x)" ..
    show "Rep x \<in> A" by (rule Rep [OF tydef])
  qed
qed

theorem Rep_induct:
  "type_definition Rep Abs A ==> y \<in> A ==> (!!x. P (Rep x)) ==> P y"
proof -
  assume tydef: "type_definition Rep Abs A"
  assume "!!x. P (Rep x)" hence "P (Rep (Abs y))" .
  moreover assume "y \<in> A" hence "Rep (Abs y) = y" by (rule Abs_inverse [OF tydef])
  ultimately show "P y" by (simp only:)
qed

theorem Abs_induct:
  "type_definition Rep Abs A ==> (!!y. y \<in> A ==> P (Abs y)) ==> P x"
proof -
  assume tydef: "type_definition Rep Abs A"
  assume r: "!!y. y \<in> A ==> P (Abs y)"
  have "Rep x \<in> A" by (rule Rep [OF tydef])
  hence "P (Abs (Rep x))" by (rule r)
  moreover have "Abs (Rep x) = x" by (rule Rep_inverse [OF tydef])
  ultimately show "P x" by (simp only:)
qed

setup InductAttrib.setup
use "Tools/typedef_package.ML"

end
