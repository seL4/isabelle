(*  Title:      HOL/Typedef.thy
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

lemma Rep_range: "range Rep = A"
proof
  show "range Rep <= A" using Rep by (auto simp add: image_def)
  show "A <= range Rep"
  proof
    fix x assume "x : A"
    hence "x = Rep (Abs x)" by (rule Abs_inverse [symmetric])
    thus "x : range Rep" by (rule range_eqI)
  qed
qed

lemma Abs_image: "Abs ` A = UNIV"
proof
  show "Abs ` A <= UNIV" by (rule subset_UNIV)
next
  show "UNIV <= Abs ` A"
  proof
    fix x
    have "x = Abs (Rep x)" by (rule Rep_inverse [symmetric])
    moreover have "Rep x : A" by (rule Rep)
    ultimately show "x : Abs ` A" by (rule image_eqI)
  qed
qed

end

use "Tools/typedef_package.ML" setup TypedefPackage.setup
use "Tools/typecopy_package.ML" setup TypecopyPackage.setup
use "Tools/typedef_codegen.ML" setup TypedefCodegen.setup


text {* This class is just a workaround for classes without parameters;
  it shall disappear as soon as possible. *}

class itself = type + 
  fixes itself :: "'a itself"

setup {*
let fun add_itself tyco thy =
  let
    val vs = Name.names Name.context "'a"
      (replicate (Sign.arity_number thy tyco) @{sort type});
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name itself}, Term.itselfT ty);
    val rhs = Logic.mk_type ty;
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort itself})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
    |> LocalTheory.exit_global
  end
in TypedefPackage.interpretation add_itself end
*}

instantiation bool :: itself
begin

definition "itself = TYPE(bool)"

instance ..

end

instantiation "fun" :: ("type", "type") itself
begin

definition "itself = TYPE('a \<Rightarrow> 'b)"

instance ..

end

hide (open) const itself

end
