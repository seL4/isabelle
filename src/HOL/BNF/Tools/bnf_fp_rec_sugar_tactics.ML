(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Tactics for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_TACTICS =
sig
  val mk_primcorec_assumption_tac: Proof.context -> tactic
  val mk_primcorec_code_tac: Proof.context -> thm -> thm list -> tactic
  val mk_primcorec_code_of_ctr_tac: Proof.context -> int list -> thm list -> tactic
  val mk_primcorec_ctr_of_dtr_tac: Proof.context -> int -> thm -> thm option -> thm list -> tactic
  val mk_primcorec_ctr_or_sel_tac: Proof.context -> thm list -> thm -> int -> int ->
    thm list list list -> thm list -> thm list -> thm list -> tactic
  val mk_primcorec_disc_of_ctr_tac: thm -> thm -> tactic;
  val mk_primcorec_disc_tac: Proof.context -> thm list -> thm -> int -> int -> thm list list list ->
    tactic
  val mk_primcorec_sel_of_ctr_tac: thm -> thm -> tactic;
  val mk_primrec_tac: Proof.context -> int -> thm list -> thm list -> thm list -> thm -> tactic
end;

structure BNF_FP_Rec_Sugar_Tactics : BNF_FP_REC_SUGAR_TACTICS =
struct

open BNF_Util
open BNF_Tactics

fun mk_primrec_tac ctxt num_extra_args map_idents map_comps fun_defs recx =
  unfold_thms_tac ctxt fun_defs THEN
  HEADGOAL (rtac (funpow num_extra_args (fn thm => thm RS fun_cong) recx RS trans)) THEN
  unfold_thms_tac ctxt (@{thms id_def split o_def fst_conv snd_conv} @ map_comps @ map_idents) THEN
  HEADGOAL (rtac refl);

fun mk_primcorec_assumption_tac ctxt =
  HEADGOAL (blast_tac (put_claset (claset_of @{theory_context HOL}) ctxt));

fun mk_primcorec_same_case_tac m =
  HEADGOAL (if m = 0 then rtac TrueI
    else REPEAT_DETERM_N (m - 1) o (rtac conjI THEN' atac) THEN' atac);

fun mk_primcorec_different_case_tac ctxt excl =
  unfold_thms_tac ctxt @{thms not_not not_False_eq_True} THEN
  HEADGOAL (rtac excl THEN_ALL_NEW SELECT_GOAL (mk_primcorec_assumption_tac ctxt));

fun mk_primcorec_cases_tac ctxt k m exclsss =
  let val n = length exclsss in
    EVERY (map (fn [] => if k = n then all_tac else mk_primcorec_same_case_tac m
        | [excl] => mk_primcorec_different_case_tac ctxt excl)
      (take k (nth exclsss (k - 1))))
  end;

fun mk_primcorec_prelude ctxt defs thm =
  unfold_thms_tac ctxt defs THEN HEADGOAL (rtac thm) THEN unfold_thms_tac ctxt @{thms split};

fun mk_primcorec_disc_tac ctxt defs disc_corec k m exclsss =
  mk_primcorec_prelude ctxt defs disc_corec THEN mk_primcorec_cases_tac ctxt k m exclsss;

fun mk_primcorec_ctr_or_sel_tac ctxt defs f_eq k m exclsss maps map_idents map_comps =
  mk_primcorec_prelude ctxt defs (f_eq RS trans) THEN
  mk_primcorec_cases_tac ctxt k m exclsss THEN
  unfold_thms_tac ctxt (@{thms if_if_True if_if_False if_True if_False if_cancel[of _ True]
    if_cancel[of _ False] o_def split_def sum.cases} @ maps @ map_comps @ map_idents) THEN
  HEADGOAL (rtac refl);

fun mk_primcorec_ctr_of_dtr_tac ctxt m collapse maybe_disc_f sel_fs =
  HEADGOAL (rtac ((if null sel_fs then collapse else collapse RS sym) RS trans) THEN'
    (the_default (K all_tac) (Option.map rtac maybe_disc_f)) THEN' REPEAT_DETERM_N m o atac) THEN
  unfold_thms_tac ctxt sel_fs THEN HEADGOAL (rtac refl);

fun mk_primcorec_disc_of_ctr_tac discI f_ctr =
  HEADGOAL (rtac discI THEN' rtac f_ctr) THEN ALLGOALS atac;

fun mk_primcorec_sel_of_ctr_tac sel f_ctr =
  HEADGOAL (etac (f_ctr RS arg_cong RS trans) THEN' rtac sel);

fun mk_primcorec_code_of_ctr_case_tac ctxt m f_ctr =
  HEADGOAL (REPEAT o rtac @{thm eq_ifI}) THEN
  mk_primcorec_prelude ctxt [] (f_ctr RS trans) THEN
  REPEAT_DETERM_N m (mk_primcorec_assumption_tac ctxt) THEN
  (* FIXME: Something like (ss_only @{thms if_True if_False not_False_eq_True simp_thms} ctxt) *)
  HEADGOAL (asm_simp_tac ctxt);

fun mk_primcorec_code_of_ctr_tac ctxt ms ctr_thms =
  EVERY (map2 (mk_primcorec_code_of_ctr_case_tac ctxt) ms ctr_thms);

fun mk_primcorec_code_tac ctxt raw collapses =
  HEADGOAL (rtac (raw RS trans)) THEN unfold_thms_tac ctxt @{thms split_ifs} THEN
  Method.intros_tac @{thms conjI impI} [] THEN
  REPEAT (HEADGOAL (rtac refl ORELSE' (etac notE THEN' atac) ORELSE'
    eresolve_tac (maps (fn thm => [thm, thm RS sym]) collapses)));

end;
