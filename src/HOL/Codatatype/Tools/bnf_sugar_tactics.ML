(*  Title:      HOL/Codatatype/Tools/bnf_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for sugar on top of a BNF.
*)

signature BNF_SUGAR_TACTICS =
sig
  val mk_case_cong_tac: thm -> thm list -> tactic
  val mk_case_disc_tac: Proof.context -> thm -> thm list -> thm list list -> thm list list -> tactic
  val mk_ctr_sel_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_disc_exhaust_tac: int -> thm -> thm list -> tactic
  val mk_half_disc_exclus_tac: int -> thm -> thm -> tactic
  val mk_nchotomy_tac: int -> thm -> tactic
  val mk_other_half_disc_exclus_tac: thm -> tactic
  val mk_split_tac: thm -> thm list -> thm list list -> thm list list list -> tactic
  val mk_split_asm_tac: Proof.context -> thm -> tactic
end;

structure BNF_Sugar_Tactics : BNF_SUGAR_TACTICS =
struct

open BNF_Util
open BNF_Tactics
open BNF_FP_Util

fun triangle _ [] = []
  | triangle k (xs :: xss) = take k xs :: triangle (k + 1) xss

fun mk_if_P_or_not_P thm =
  thm RS @{thm if_not_P} handle THM _ => thm RS @{thm if_P}

fun ss_only thms = Simplifier.clear_ss HOL_basic_ss addsimps thms

fun mk_nchotomy_tac n exhaust =
  (rtac allI THEN' rtac exhaust THEN'
   EVERY' (maps (fn k => [rtac (mk_disjIN n k), REPEAT_DETERM o rtac exI, atac]) (1 upto n))) 1;

fun mk_half_disc_exclus_tac m discD disc'_thm =
  (dtac discD THEN'
   REPEAT_DETERM_N m o etac exE THEN'
   hyp_subst_tac THEN'
   rtac disc'_thm) 1;

fun mk_other_half_disc_exclus_tac half_thm =
  (etac @{thm contrapos_pn} THEN' etac half_thm) 1;

fun mk_disc_exhaust_tac n exhaust discIs =
  (rtac exhaust THEN'
   EVERY' (map2 (fn k => fn discI =>
     dtac discI THEN' select_prem_tac n (etac @{thm meta_mp}) k THEN' atac) (1 upto n) discIs)) 1;

fun mk_ctr_sel_tac ctxt m discD sel_thms =
  (dtac discD THEN'
   (if m = 0 then
      atac
    else
      REPEAT_DETERM_N m o etac exE THEN'
      hyp_subst_tac THEN'
      SELECT_GOAL (Local_Defs.unfold_tac ctxt sel_thms) THEN'
      rtac refl)) 1;

fun mk_case_disc_tac ctxt exhaust' case_thms disc_thmss' sel_thmss =
  (rtac exhaust' THEN'
   EVERY' (map3 (fn case_thm => fn if_disc_thms => fn sel_thms => EVERY' [
     hyp_subst_tac THEN'
     SELECT_GOAL (Local_Defs.unfold_tac ctxt (if_disc_thms @ sel_thms)) THEN'
     rtac case_thm]) case_thms
  (map (map mk_if_P_or_not_P) (triangle 1 (map (fst o split_last) disc_thmss'))) sel_thmss)) 1;

fun mk_case_cong_tac exhaust' case_thms =
  (rtac exhaust' THEN'
   EVERY' (maps (fn case_thm => [dtac sym, asm_simp_tac (ss_only [case_thm])]) case_thms)) 1;

val naked_ctxt = Proof_Context.init_global @{theory HOL};

fun mk_split_tac exhaust' case_thms injectss distinctsss =
  rtac exhaust' 1 THEN
  ALLGOALS (fn k =>
    (hyp_subst_tac THEN'
     simp_tac (ss_only (@{thms simp_thms} @ case_thms @ nth injectss (k - 1) @
       flat (nth distinctsss (k - 1))))) k) THEN
  ALLGOALS (blast_tac naked_ctxt);

val split_asm_thms = @{thms imp_conv_disj de_Morgan_conj de_Morgan_disj not_not not_ex};

fun mk_split_asm_tac ctxt split =
  rtac (split RS trans) 1 THEN
  Local_Defs.unfold_tac ctxt split_asm_thms THEN
  rtac refl 1;

end;
