(*  Title:      HOL/Recdef.thy
    ID:         $Id$
    Author:     Konrad Slind

TFL: recursive function definitions.
*)

theory Recdef = Wellfounded_Relations + Datatype
files
  "../TFL/utils.sml"
  "../TFL/usyntax.sml"
  "../TFL/thms.sml"
  "../TFL/dcterm.sml"
  "../TFL/rules.sml"
  "../TFL/thry.sml"
  "../TFL/tfl.sml"
  "../TFL/post.sml"
  "Tools/recdef_package.ML":

setup RecdefPackage.setup

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] =
  if_cong

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
  wf_empty

end
