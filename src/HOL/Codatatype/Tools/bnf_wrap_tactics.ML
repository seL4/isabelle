(*  Title:      HOL/Codatatype/Tools/bnf_wrap_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for wrapping datatypes.
*)

signature BNF_WRAP_TACTICS =
sig
  val mk_alternate_disc_def_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_case_cong_tac: thm -> thm list -> tactic
  val mk_case_eq_tac: Proof.context -> int -> thm -> thm list -> thm list list -> thm list list ->
    tactic
  val mk_collapse_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_disc_exhaust_tac: int -> thm -> thm list -> tactic
  val mk_half_disc_exclude_tac: int -> thm -> thm -> tactic
  val mk_nchotomy_tac: int -> thm -> tactic
  val mk_other_half_disc_exclude_tac: thm -> tactic
  val mk_split_tac: thm -> thm list -> thm list list -> thm list list list -> tactic
  val mk_split_asm_tac: Proof.context -> thm -> tactic
  val mk_unique_disc_def_tac: int -> thm -> tactic
end;

structure BNF_Wrap_Tactics : BNF_WRAP_TACTICS =
struct

open BNF_Util
open BNF_Tactics

fun if_P_or_not_P_OF pos thm = thm RS (if pos then @{thm if_P} else @{thm if_not_P});

fun mk_nchotomy_tac n exhaust =
  (rtac allI THEN' rtac exhaust THEN'
   EVERY' (maps (fn k => [rtac (mk_disjIN n k), REPEAT_DETERM o rtac exI, atac]) (1 upto n))) 1;

fun mk_unique_disc_def_tac m exhaust' =
  EVERY' [rtac iffI, rtac exhaust', REPEAT_DETERM_N m o rtac exI, atac, rtac refl] 1;

fun mk_alternate_disc_def_tac ctxt k other_disc_def distinct exhaust' =
  EVERY' ([subst_tac ctxt [other_disc_def], rtac @{thm iffI_np}, REPEAT_DETERM o etac exE,
    hyp_subst_tac, SELECT_GOAL (unfold_defs_tac ctxt [not_ex]), REPEAT_DETERM o rtac allI,
    rtac distinct, rtac exhaust'] @
    (([etac notE, REPEAT_DETERM o rtac exI, atac], [REPEAT_DETERM o rtac exI, atac])
     |> k = 1 ? swap |> op @)) 1;

fun mk_half_disc_exclude_tac m discD disc' =
  (dtac discD THEN' REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac THEN' rtac disc') 1;

fun mk_other_half_disc_exclude_tac half = (etac @{thm contrapos_pn} THEN' etac half) 1;

fun mk_disc_exhaust_tac n exhaust discIs =
  (rtac exhaust THEN'
   EVERY' (map2 (fn k => fn discI =>
     dtac discI THEN' select_prem_tac n (etac @{thm meta_mp}) k THEN' atac) (1 upto n) discIs)) 1;

fun mk_collapse_tac ctxt m discD sels =
  (dtac discD THEN'
   (if m = 0 then
      atac
    else
      REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac THEN'
      SELECT_GOAL (unfold_defs_tac ctxt sels) THEN' rtac refl)) 1;

fun mk_case_eq_tac ctxt n exhaust' cases discss' selss =
  (rtac exhaust' THEN'
   EVERY' (map3 (fn casex => fn if_discs => fn sels =>
       EVERY' [hyp_subst_tac, SELECT_GOAL (unfold_defs_tac ctxt (if_discs @ sels)), rtac casex])
     cases (map2 (seq_conds if_P_or_not_P_OF n) (1 upto n) discss') selss)) 1;

fun mk_case_cong_tac exhaust' cases =
  (rtac exhaust' THEN'
   EVERY' (maps (fn casex => [dtac sym, asm_simp_tac (ss_only [casex])]) cases)) 1;

val naked_ctxt = Proof_Context.init_global @{theory HOL};

fun mk_split_tac exhaust' cases injectss distinctsss =
  rtac exhaust' 1 THEN
  ALLGOALS (fn k => (hyp_subst_tac THEN'
     simp_tac (ss_only (@{thms simp_thms} @ cases @ nth injectss (k - 1) @
       flat (nth distinctsss (k - 1))))) k) THEN
  ALLGOALS (blast_tac naked_ctxt);

val split_asm_thms = @{thms imp_conv_disj de_Morgan_conj de_Morgan_disj not_not not_ex};

fun mk_split_asm_tac ctxt split =
  rtac (split RS trans) 1 THEN unfold_defs_tac ctxt split_asm_thms THEN rtac refl 1;

end;
