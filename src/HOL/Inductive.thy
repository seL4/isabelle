(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Inductive = Gfp + Sum_Type + NatDef
files
  ("Tools/induct_method.ML")
  ("Tools/inductive_package.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_package.ML")
  ("Tools/primrec_package.ML"):

constdefs
  forall :: "('a => bool) => bool"
  "forall P == \<forall>x. P x"
  implies :: "bool => bool => bool"
  "implies A B == A --> B"
  equal :: "'a => 'a => bool"
  "equal x y == x = y"

lemma forall_eq: "(!!x. P x) == Trueprop (forall (\<lambda>x. P x))"
  by (simp only: atomize_all forall_def)

lemma implies_eq: "(A ==> B) == Trueprop (implies A B)"
  by (simp only: atomize_imp implies_def)

lemma equal_eq: "(x == y) == Trueprop (equal x y)"
  by (simp only: atomize_eq equal_def)

hide const forall implies equal

lemmas inductive_atomize = forall_eq implies_eq equal_eq
lemmas inductive_rulify1 = inductive_atomize [symmetric, standard]
lemmas inductive_rulify2 = forall_def implies_def equal_def

use "Tools/induct_method.ML"
setup InductMethod.setup

use "Tools/inductive_package.ML"
setup InductivePackage.setup

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_package.ML"
setup DatatypePackage.setup

use "Tools/primrec_package.ML"
setup PrimrecPackage.setup

theorems basic_monos [mono] =
   subset_refl imp_refl disj_mono conj_mono ex_mono all_mono
   Collect_mono in_mono vimage_mono
   imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
   not_all not_ex
   Ball_def Bex_def

(*belongs to theory Transitive_Closure*)
declare rtrancl_induct [induct set: rtrancl]
declare rtranclE [cases set: rtrancl]
declare trancl_induct [induct set: trancl]
declare tranclE [cases set: trancl]

end
