(*  Title:      HOL/Inductive.thy
    ID:         $Id$
*)

theory Inductive = Gfp + Prod + Sum + NatDef
files
  "Tools/induct_method.ML"
  "Tools/inductive_package.ML"
  "Tools/datatype_aux.ML"
  "Tools/datatype_prop.ML"
  "Tools/datatype_rep_proofs.ML"
  "Tools/datatype_abs_proofs.ML"
  "Tools/datatype_package.ML"
  "Tools/primrec_package.ML":

setup InductMethod.setup
setup InductivePackage.setup
setup DatatypePackage.setup

theorems [mono] =
   subset_refl imp_refl disj_mono conj_mono ex_mono all_mono
   Collect_mono in_mono vimage_mono
   imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
   not_all not_ex
   Ball_def Bex_def

end
