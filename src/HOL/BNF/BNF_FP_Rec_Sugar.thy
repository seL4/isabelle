(*  Title:      HOL/BNF/BNF_FP_Rec_Sugar.thy
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Recursor and corecursor sugar.
*)

header {* Recursor and Corecursor Sugar *}

theory BNF_FP_Rec_Sugar
imports BNF_FP_N2M
keywords
  "primrec_new" :: thy_decl and
  "primcorec" :: thy_goal and
  "sequential"
begin

lemma if_if_True:
"(if (if b then True else b') then (if b then x else x') else f (if b then y else y')) =
 (if b then x else if b' then x' else f y')"
by simp

lemma if_if_False:
"(if (if b then False else b') then (if b then x else x') else f (if b then y else y')) =
 (if b then f y else if b' then x' else f y')"
by simp

ML_file "Tools/bnf_fp_rec_sugar_util.ML"
ML_file "Tools/bnf_fp_rec_sugar_tactics.ML"
ML_file "Tools/bnf_fp_rec_sugar.ML"

end
