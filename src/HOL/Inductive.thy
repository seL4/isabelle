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

lemma forall_eq: "(!!x. P x) == Trueprop (forall (\<lambda>x. P x))"
proof
  assume "!!x. P x"
  thus "forall (\<lambda>x. P x)" by (unfold forall_def) blast
next
  fix x
  assume "forall (\<lambda>x. P x)"
  thus "P x" by (unfold forall_def) blast
qed

lemma implies_eq: "(A ==> B) == Trueprop (implies A B)"
proof
  assume "A ==> B"
  thus "implies A B" by (unfold implies_def) blast
next
  assume "implies A B" and A
  thus B by (unfold implies_def) blast
qed

lemmas inductive_atomize = forall_eq implies_eq
lemmas inductive_rulify = inductive_atomize [symmetric, standard]
hide const forall implies

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
