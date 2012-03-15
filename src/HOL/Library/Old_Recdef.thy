(*  Title:      HOL/Library/Old_Recdef.thy
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen
*)

header {* TFL: recursive function definitions *}

theory Old_Recdef
imports Wfrec
keywords "recdef" :: thy_decl and "permissive" "congs" "hints"
uses
  ("~~/src/HOL/Tools/TFL/casesplit.ML")
  ("~~/src/HOL/Tools/TFL/utils.ML")
  ("~~/src/HOL/Tools/TFL/usyntax.ML")
  ("~~/src/HOL/Tools/TFL/dcterm.ML")
  ("~~/src/HOL/Tools/TFL/thms.ML")
  ("~~/src/HOL/Tools/TFL/rules.ML")
  ("~~/src/HOL/Tools/TFL/thry.ML")
  ("~~/src/HOL/Tools/TFL/tfl.ML")
  ("~~/src/HOL/Tools/TFL/post.ML")
  ("~~/src/HOL/Tools/recdef.ML")
begin

subsection {* Lemmas for TFL *}

lemma tfl_wf_induct: "ALL R. wf R -->  
       (ALL P. (ALL x. (ALL y. (y,x):R --> P y) --> P x) --> (ALL x. P x))"
apply clarify
apply (rule_tac r = R and P = P and a = x in wf_induct, assumption, blast)
done

lemma tfl_cut_apply: "ALL f R. (x,a):R --> (cut f R a)(x) = f(x)"
apply clarify
apply (rule cut_apply, assumption)
done

lemma tfl_wfrec:
     "ALL M R f. (f=wfrec R M) --> wf R --> (ALL x. f x = M (cut f R x) x)"
apply clarify
apply (erule wfrec)
done

lemma tfl_eq_True: "(x = True) --> x"
  by blast

lemma tfl_rev_eq_mp: "(x = y) --> y --> x"
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

use "~~/src/HOL/Tools/TFL/casesplit.ML"
use "~~/src/HOL/Tools/TFL/utils.ML"
use "~~/src/HOL/Tools/TFL/usyntax.ML"
use "~~/src/HOL/Tools/TFL/dcterm.ML"
use "~~/src/HOL/Tools/TFL/thms.ML"
use "~~/src/HOL/Tools/TFL/rules.ML"
use "~~/src/HOL/Tools/TFL/thry.ML"
use "~~/src/HOL/Tools/TFL/tfl.ML"
use "~~/src/HOL/Tools/TFL/post.ML"
use "~~/src/HOL/Tools/recdef.ML"
setup Recdef.setup

subsection {* Rule setup *}

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] =
  if_cong let_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong
  map_cong filter_cong takeWhile_cong dropWhile_cong foldl_cong foldr_cong 

lemmas [recdef_wf] =
  wf_trancl
  wf_less_than
  wf_lex_prod
  wf_inv_image
  wf_measure
  wf_measures
  wf_pred_nat
  wf_same_fst
  wf_empty

end
