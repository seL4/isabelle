(*  Title:      HOL/Inductive.thy
    ID:         $Id$
*)

theory Inductive = Gfp + Prod + Sum
files
  "Tools/inductive_package.ML"
  "Tools/datatype_aux.ML"
  "Tools/datatype_prop.ML"
  "Tools/datatype_rep_proofs.ML"
  "Tools/datatype_abs_proofs.ML"
  "Tools/datatype_package.ML"
  "Tools/primrec_package.ML":

setup InductivePackage.setup
setup DatatypePackage.setup


end
