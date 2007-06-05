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
  hence "Abs (Rep x) = Abs (Rep y)" by (simp only:)
  also have "Abs (Rep x) = x" by (rule Rep_inverse)
  also have "Abs (Rep y) = y" by (rule Rep_inverse)
  finally show "x = y" .
next
  assume "x = y"
  thus "Rep x = Rep y" by (simp only:)
qed

lemma Abs_inject:
  assumes x: "x \<in> A" and y: "y \<in> A"
  shows "(Abs x = Abs y) = (x = y)"
proof
  assume "Abs x = Abs y"
  hence "Rep (Abs x) = Rep (Abs y)" by (simp only:)
  also from x have "Rep (Abs x) = x" by (rule Abs_inverse)
  also from y have "Rep (Abs y) = y" by (rule Abs_inverse)
  finally show "x = y" .
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
  also from y have "Rep (Abs y) = y" by (rule Abs_inverse)
  finally show "P y" .
qed

lemma Abs_induct [induct type]:
  assumes r: "!!y. y \<in> A ==> P (Abs y)"
  shows "P x"
proof -
  have "Rep x \<in> A" by (rule Rep)
  hence "P (Abs (Rep x))" by (rule r)
  also have "Abs (Rep x) = x" by (rule Rep_inverse)
  finally show "P x" .
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
