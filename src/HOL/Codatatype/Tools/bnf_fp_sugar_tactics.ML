(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for the LFP/GFP sugar.
*)

signature BNF_FP_SUGAR_TACTICS =
sig
  val mk_exhaust_tac: Proof.context -> int -> int list -> thm list -> thm -> thm -> tactic
  val mk_fld_iff_unf_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm
    -> tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> tactic
end;

structure BNF_FP_Sugar_Tactics : BNF_FP_SUGAR_TACTICS =
struct

open BNF_Tactics
open BNF_Util

fun mk_exhaust_tac ctxt n ms ctr_defs fld_iff_unf sumEN' =
  Local_Defs.unfold_tac ctxt (fld_iff_unf :: ctr_defs) THEN
  rtac sumEN' 1 THEN
  Local_Defs.unfold_tac ctxt @{thms all_prod_eq} THEN
  EVERY' (map2 (fn k => fn m =>
     select_prem_tac n (REPEAT_DETERM_N m o dtac @{thm meta_spec} THEN' etac @{thm meta_mp}) k THEN'
     atac) (1 upto n) ms) 1;

fun mk_fld_iff_unf_tac ctxt cTs cfld cunf fld_unf unf_fld =
  (rtac iffI THEN'
   EVERY' (map3 (fn cTs => fn cx => fn th =>
     dtac (Drule.instantiate' cTs [NONE, NONE, SOME cx] arg_cong) THEN'
     SELECT_GOAL (Local_Defs.unfold_tac ctxt [th]) THEN'
     atac) [rev cTs, cTs] [cunf, cfld] [unf_fld, fld_unf])) 1;

fun mk_inject_tac ctxt ctr_def fld_inject =
  Local_Defs.unfold_tac ctxt [ctr_def] THEN
  rtac (fld_inject RS ssubst) 1 THEN
  Local_Defs.unfold_tac ctxt @{thms sum.inject Pair_eq conj_assoc} THEN
  rtac refl 1;

end;
