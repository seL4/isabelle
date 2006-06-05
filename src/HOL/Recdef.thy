(*  Title:      HOL/Recdef.thy
    ID:         $Id$
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen
*)

header {* TFL: recursive function definitions *}

theory Recdef
imports Wellfounded_Relations
uses
  ("../TFL/casesplit.ML")
  ("../TFL/utils.ML")
  ("../TFL/usyntax.ML")
  ("../TFL/dcterm.ML")
  ("../TFL/thms.ML")
  ("../TFL/rules.ML")
  ("../TFL/thry.ML")
  ("../TFL/tfl.ML")
  ("../TFL/post.ML")
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

use "../TFL/casesplit.ML"
use "../TFL/utils.ML"
use "../TFL/usyntax.ML"
use "../TFL/dcterm.ML"
use "../TFL/thms.ML"
use "../TFL/rules.ML"
use "../TFL/thry.ML"
use "../TFL/tfl.ML"
use "../TFL/post.ML"
use "Tools/recdef_package.ML"
setup RecdefPackage.setup

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] = 
  if_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong

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

(* The following should really go into Datatype or Finite_Set, but
each one lacks the other theory as a parent . . . *)

lemma insert_None_conv_UNIV: "insert None (range Some) = UNIV"
by (rule set_ext, case_tac x, auto)

instance option :: (finite) finite
proof
  have "finite (UNIV :: 'a set)" by (rule finite)
  hence "finite (insert None (Some ` (UNIV :: 'a set)))" by simp
  also have "insert None (Some ` (UNIV :: 'a set)) = UNIV"
    by (rule insert_None_conv_UNIV)
  finally show "finite (UNIV :: 'a option set)" .
qed


end
