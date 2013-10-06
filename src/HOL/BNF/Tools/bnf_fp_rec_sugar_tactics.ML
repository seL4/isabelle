(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Tactics for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_TACTICS =
sig
  val mk_primcorec_assumption_tac: Proof.context -> thm list -> int -> tactic
  val mk_primcorec_code_of_raw_code_tac: thm list -> thm -> tactic
  val mk_primcorec_ctr_of_dtr_tac: Proof.context -> int -> thm -> thm option -> thm list -> tactic
  val mk_primcorec_disc_tac: Proof.context -> thm list -> thm -> int -> int -> thm list list list ->
    tactic
  val mk_primcorec_raw_code_of_ctr_tac: Proof.context -> thm list -> thm list -> thm list ->
    thm list -> int list -> thm list -> tactic
  val mk_primcorec_sel_tac: Proof.context -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm -> int -> int -> thm list list list -> tactic
  val mk_primrec_tac: Proof.context -> int -> thm list -> thm list -> thm list -> thm -> tactic
end;

structure BNF_FP_Rec_Sugar_Tactics : BNF_FP_REC_SUGAR_TACTICS =
struct

open BNF_Util
open BNF_Tactics

val falseEs = @{thms not_TrueE FalseE};
val neq_eq_eq_contradict = @{thm neq_eq_eq_contradict};
val split_if = @{thm split_if};
val split_if_asm = @{thm split_if_asm};
val split_connectI = @{thms allI impI conjI};

fun mk_primrec_tac ctxt num_extra_args map_idents map_comps fun_defs recx =
  unfold_thms_tac ctxt fun_defs THEN
  HEADGOAL (rtac (funpow num_extra_args (fn thm => thm RS fun_cong) recx RS trans)) THEN
  unfold_thms_tac ctxt (@{thms id_def split o_def fst_conv snd_conv} @ map_comps @ map_idents) THEN
  HEADGOAL (rtac refl);

fun mk_primcorec_assumption_tac ctxt discIs =
  SELECT_GOAL (unfold_thms_tac ctxt
      @{thms not_not not_False_eq_True not_True_eq_False de_Morgan_conj de_Morgan_disj} THEN
    SOLVE (HEADGOAL (REPEAT o (rtac refl ORELSE' atac ORELSE' etac conjE ORELSE'
    resolve_tac @{thms TrueI conjI disjI1 disjI2} ORELSE'
    dresolve_tac discIs THEN' atac ORELSE'
    etac notE THEN' atac ORELSE'
    etac disjE))));

fun mk_primcorec_same_case_tac m =
  HEADGOAL (if m = 0 then rtac TrueI
    else REPEAT_DETERM_N (m - 1) o (rtac conjI THEN' atac) THEN' atac);

fun mk_primcorec_different_case_tac ctxt m excl =
  HEADGOAL (if m = 0 then mk_primcorec_assumption_tac ctxt []
    else dtac excl THEN' (REPEAT_DETERM_N (m - 1) o atac) THEN' mk_primcorec_assumption_tac ctxt []);

fun mk_primcorec_cases_tac ctxt k m exclsss =
  let val n = length exclsss in
    EVERY (map (fn [] => if k = n then all_tac else mk_primcorec_same_case_tac m
        | [excl] => mk_primcorec_different_case_tac ctxt m excl)
      (take k (nth exclsss (k - 1))))
  end;

fun mk_primcorec_prelude ctxt defs thm =
  unfold_thms_tac ctxt defs THEN HEADGOAL (rtac thm) THEN
  unfold_thms_tac ctxt @{thms Let_def split};

fun mk_primcorec_disc_tac ctxt defs disc_corec k m exclsss =
  mk_primcorec_prelude ctxt defs disc_corec THEN mk_primcorec_cases_tac ctxt k m exclsss;

fun mk_primcorec_sel_tac ctxt defs distincts splits split_asms maps map_idents map_comps f_sel k m
    exclsss =
  mk_primcorec_prelude ctxt defs (f_sel RS trans) THEN
  mk_primcorec_cases_tac ctxt k m exclsss THEN
  HEADGOAL (REPEAT_DETERM o (rtac refl ORELSE' rtac ext ORELSE'
    eresolve_tac falseEs ORELSE'
    resolve_tac split_connectI ORELSE'
    Splitter.split_asm_tac (split_if_asm :: split_asms) ORELSE'
    Splitter.split_tac (split_if :: splits) ORELSE'
    eresolve_tac (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN' atac ORELSE'
    etac notE THEN' atac ORELSE'
    (CHANGED o SELECT_GOAL (unfold_thms_tac ctxt
      (@{thms id_apply o_def split_def sum.cases} @ maps @ map_comps @ map_idents)))));

fun mk_primcorec_ctr_of_dtr_tac ctxt m collapse maybe_disc_f sel_fs =
  HEADGOAL (rtac ((if null sel_fs then collapse else collapse RS sym) RS trans) THEN'
    (the_default (K all_tac) (Option.map rtac maybe_disc_f)) THEN' REPEAT_DETERM_N m o atac) THEN
  unfold_thms_tac ctxt sel_fs THEN HEADGOAL (rtac refl);

(* TODO: reduce code duplication with selector tactic above *)
fun mk_primcorec_raw_code_of_ctr_single_tac ctxt distincts discIs splits split_asms m f_ctr =
  HEADGOAL (REPEAT o (resolve_tac split_connectI ORELSE' split_tac (split_if :: splits))) THEN
  mk_primcorec_prelude ctxt [] (f_ctr RS trans) THEN
  HEADGOAL ((REPEAT_DETERM_N m o mk_primcorec_assumption_tac ctxt discIs) THEN'
    SELECT_GOAL (SOLVE (HEADGOAL (REPEAT_DETERM o
    (rtac refl ORELSE' atac ORELSE'
     resolve_tac split_connectI ORELSE'
     Splitter.split_asm_tac (split_if_asm :: split_asms) ORELSE'
     Splitter.split_tac (split_if :: splits) ORELSE'
     mk_primcorec_assumption_tac ctxt discIs ORELSE'
     eresolve_tac (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN' atac ORELSE'
     (TRY o dresolve_tac discIs) THEN' etac notE THEN' atac)))));

fun mk_primcorec_raw_code_of_ctr_tac ctxt distincts discIs splits split_asms ms ctr_thms =
  EVERY (map2 (mk_primcorec_raw_code_of_ctr_single_tac ctxt distincts discIs splits split_asms)
    ms ctr_thms);

fun mk_primcorec_code_of_raw_code_tac splits raw =
  HEADGOAL (rtac raw ORELSE' rtac (raw RS trans) THEN' REPEAT_DETERM o
    (rtac refl ORELSE'
     (TRY o rtac sym) THEN' atac ORELSE'
     resolve_tac split_connectI ORELSE'
     Splitter.split_tac (split_if :: splits) ORELSE'
     etac notE THEN' atac));

end;
