(*  Title:      HOL/Typedef.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Munich
*)

header {* HOL type definitions *}

theory Typedef
imports Set
uses
  ("Tools/typedef_package.ML")
  ("Tools/typecopy_package.ML")
  ("Tools/typedef_codegen.ML")
begin

ML {*
structure HOL = struct val thy = theory "HOL" end;
*}  -- "belongs to theory HOL"

locale type_definition =
  fixes Rep and Abs and A
  assumes Rep: "Rep x \<in> A"
    and Rep_inverse: "Abs (Rep x) = x"
    and Abs_inverse: "y \<in> A ==> Rep (Abs y) = y"
  -- {* This will be axiomatized for each typedef! *}
begin

lemma Rep_inject:
  "(Rep x = Rep y) = (x = y)"
proof
  assume "Rep x = Rep y"
  then have "Abs (Rep x) = Abs (Rep y)" by (simp only:)
  moreover have "Abs (Rep x) = x" by (rule Rep_inverse)
  moreover have "Abs (Rep y) = y" by (rule Rep_inverse)
  ultimately show "x = y" by simp
next
  assume "x = y"
  thus "Rep x = Rep y" by (simp only:)
qed

lemma Abs_inject:
  assumes x: "x \<in> A" and y: "y \<in> A"
  shows "(Abs x = Abs y) = (x = y)"
proof
  assume "Abs x = Abs y"
  then have "Rep (Abs x) = Rep (Abs y)" by (simp only:)
  moreover from x have "Rep (Abs x) = x" by (rule Abs_inverse)
  moreover from y have "Rep (Abs y) = y" by (rule Abs_inverse)
  ultimately show "x = y" by simp
next
  assume "x = y"
  thus "Abs x = Abs y" by (simp only:)
qed

lemma Rep_cases [cases set]:
  assumes y: "y \<in> A"
    and hyp: "!!x. y = Rep x ==> P"
  shows P
proof (rule hyp)
  from y have "Rep (Abs y) = y" by (rule Abs_inverse)
  thus "y = Rep (Abs y)" ..
qed

lemma Abs_cases [cases type]:
  assumes r: "!!y. x = Abs y ==> y \<in> A ==> P"
  shows P
proof (rule r)
  have "Abs (Rep x) = x" by (rule Rep_inverse)
  thus "x = Abs (Rep x)" ..
  show "Rep x \<in> A" by (rule Rep)
qed

lemma Rep_induct [induct set]:
  assumes y: "y \<in> A"
    and hyp: "!!x. P (Rep x)"
  shows "P y"
proof -
  have "P (Rep (Abs y))" by (rule hyp)
  moreover from y have "Rep (Abs y) = y" by (rule Abs_inverse)
  ultimately show "P y" by simp
qed

lemma Abs_induct [induct type]:
  assumes r: "!!y. y \<in> A ==> P (Abs y)"
  shows "P x"
proof -
  have "Rep x \<in> A" by (rule Rep)
  then have "P (Abs (Rep x))" by (rule r)
  moreover have "Abs (Rep x) = x" by (rule Rep_inverse)
  ultimately show "P x" by simp
qed

lemma Rep_range:
assumes "type_definition Rep Abs A"
shows "range Rep = A"
proof -
  from assms have A1: "!!x. Rep x : A"
              and A2: "!!y. y : A ==> y = Rep(Abs y)"
     by (auto simp add: type_definition_def)
  have "range Rep <= A" using A1 by (auto simp add: image_def)
  moreover have "A <= range Rep"
  proof
    fix x assume "x : A"
    hence "x = Rep (Abs x)" by (rule A2)
    thus "x : range Rep" by (auto simp add: image_def)
  qed
  ultimately show ?thesis ..
qed

end

use "Tools/typedef_package.ML"
use "Tools/typecopy_package.ML"
use "Tools/typedef_codegen.ML"

setup {*
  TypecopyPackage.setup
  #> TypedefCodegen.setup
*}

end
