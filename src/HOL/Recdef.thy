(*  Title:      HOL/Recdef.thy
    ID:         $Id$
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen

TFL: recursive function definitions.
*)

theory Recdef = Wellfounded_Relations + Datatype
files
  ("../TFL/utils.ML")
  ("../TFL/usyntax.ML")
  ("../TFL/dcterm.ML")
  ("../TFL/thms.ML")
  ("../TFL/rules.ML")
  ("../TFL/thry.ML")
  ("../TFL/tfl.ML")
  ("../TFL/post.ML")
  ("Tools/recdef_package.ML")
  ("Tools/basic_codegen.ML")
  ("Tools/inductive_codegen.ML"):

lemma tfl_eq_True: "(x = True) --> x"
  by blast

lemma tfl_rev_eq_mp: "(x = y) --> y --> x";
  by blast

lemma tfl_simp_thm: "(x --> y) --> (x = x') --> (x' --> y)"
  by blast

lemma tfl_P_imp_P_iff_True: "P ==> P = True"
  by blast

lemma tfl_imp_trans: "(A --> B) ==> (B --> C) ==> (A --> C)"
  by blast

lemma tfl_disj_assoc: "(a \\<or> b) \\<or> c == a \\<or> (b \\<or> c)"
  by simp

lemma tfl_disjE: "P \\<or> Q ==> P --> R ==> Q --> R ==> R"
  by blast

lemma tfl_exE: "\\<exists>x. P x ==> \\<forall>x. P x --> Q ==> Q"
  by blast

use "../TFL/utils.ML"
use "../TFL/usyntax.ML"
use "../TFL/dcterm.ML"
use "../TFL/thms.ML"
use "../TFL/rules.ML"
use "../TFL/thry.ML"
use "../TFL/tfl.ML"
use "../TFL/post.ML"
use "Tools/recdef_package.ML"
use "Tools/basic_codegen.ML"
use "Tools/inductive_codegen.ML"
setup RecdefPackage.setup
setup BasicCodegen.setup
setup InductiveCodegen.setup

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] = if_cong image_cong

lemma let_cong [recdef_cong]:
    "M = N ==> (!!x. x = N ==> f x = g x) ==> Let M f = Let N g"
  by (unfold Let_def) blast

lemmas [recdef_wf] =
  wf_trancl
  wf_less_than
  wf_lex_prod
  wf_inv_image
  wf_measure
  wf_pred_nat
  wf_same_fst
  wf_empty

end
