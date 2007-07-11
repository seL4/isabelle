(*  Title:      HOL/Recdef.thy
    ID:         $Id$
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen
*)

header {* TFL: recursive function definitions *}

theory Recdef
imports Wellfounded_Relations FunDef
uses
  ("Tools/TFL/casesplit.ML")
  ("Tools/TFL/utils.ML")
  ("Tools/TFL/usyntax.ML")
  ("Tools/TFL/dcterm.ML")
  ("Tools/TFL/thms.ML")
  ("Tools/TFL/rules.ML")
  ("Tools/TFL/thry.ML")
  ("Tools/TFL/tfl.ML")
  ("Tools/TFL/post.ML")
  ("Tools/recdef_package.ML")
begin

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

lemma tfl_disj_assoc: "(a \<or> b) \<or> c == a \<or> (b \<or> c)"
  by simp

lemma tfl_disjE: "P \<or> Q ==> P --> R ==> Q --> R ==> R"
  by blast

lemma tfl_exE: "\<exists>x. P x ==> \<forall>x. P x --> Q ==> Q"
  by blast

use "Tools/TFL/casesplit.ML"
use "Tools/TFL/utils.ML"
use "Tools/TFL/usyntax.ML"
use "Tools/TFL/dcterm.ML"
use "Tools/TFL/thms.ML"
use "Tools/TFL/rules.ML"
use "Tools/TFL/thry.ML"
use "Tools/TFL/tfl.ML"
use "Tools/TFL/post.ML"
use "Tools/recdef_package.ML"
setup RecdefPackage.setup

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] =
  if_cong let_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong

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
