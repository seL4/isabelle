(*  Title:      HOL/BNF/Tools/bnf_wrap_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for wrapping datatypes.
*)

signature BNF_WRAP_TACTICS =
sig
  val mk_alternate_disc_def_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_case_cong_tac: thm -> thm list -> tactic
  val mk_case_conv_tac: Proof.context -> int -> thm -> thm list -> thm list list -> thm list list ->
    tactic
  val mk_collapse_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_disc_exhaust_tac: int -> thm -> thm list -> tactic
  val mk_expand_tac: Proof.context -> int -> int list -> thm -> thm -> thm list ->
    thm list list list -> thm list list list -> tactic
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

val meta_mp = @{thm meta_mp};

fun if_P_or_not_P_OF pos thm = thm RS (if pos then @{thm if_P} else @{thm if_not_P});

fun mk_nchotomy_tac n exhaust =
  (rtac allI THEN' rtac exhaust THEN'
   EVERY' (maps (fn k => [rtac (mk_disjIN n k), REPEAT_DETERM o rtac exI, atac]) (1 upto n))) 1;

fun mk_unique_disc_def_tac m uexhaust =
  EVERY' [rtac iffI, rtac uexhaust, REPEAT_DETERM_N m o rtac exI, atac, rtac refl] 1;

fun mk_alternate_disc_def_tac ctxt k other_disc_def distinct uexhaust =
  EVERY' ([rtac (other_disc_def RS @{thm arg_cong[of _ _ Not]} RS trans),
    rtac @{thm iffI_np}, REPEAT_DETERM o etac exE,
    hyp_subst_tac, SELECT_GOAL (unfold_thms_tac ctxt [not_ex]), REPEAT_DETERM o rtac allI,
    rtac distinct, rtac uexhaust] @
    (([etac notE, REPEAT_DETERM o rtac exI, atac], [REPEAT_DETERM o rtac exI, atac])
     |> k = 1 ? swap |> op @)) 1;

fun mk_half_disc_exclude_tac m discD disc' =
  (dtac discD THEN' REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac THEN' rtac disc') 1;

fun mk_other_half_disc_exclude_tac half = (etac @{thm contrapos_pn} THEN' etac half) 1;

fun mk_disc_exhaust_tac n exhaust discIs =
  (rtac exhaust THEN'
   EVERY' (map2 (fn k => fn discI =>
     dtac discI THEN' select_prem_tac n (etac meta_mp) k THEN' atac) (1 upto n) discIs)) 1;

fun mk_collapse_tac ctxt m discD sels =
  (dtac discD THEN'
   (if m = 0 then
      atac
    else
      REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac THEN'
      SELECT_GOAL (unfold_thms_tac ctxt sels) THEN' rtac refl)) 1;

fun mk_expand_tac ctxt n ms udisc_exhaust vdisc_exhaust uncollapses disc_excludesss
    disc_excludesss' =
  if ms = [0] then
    rtac (@{thm trans_sym} OF (replicate 2 (the_single uncollapses RS sym))) 1
  else
    let
      val ks = 1 upto n;
      val maybe_atac = if n = 1 then K all_tac else atac;
    in
      (rtac udisc_exhaust THEN'
       EVERY' (map5 (fn k => fn m => fn disc_excludess => fn disc_excludess' => fn uuncollapse =>
         EVERY' [if m = 0 then K all_tac else rtac (uuncollapse RS trans) THEN' maybe_atac,
           rtac sym, rtac vdisc_exhaust,
           EVERY' (map4 (fn k' => fn disc_excludes => fn disc_excludes' => fn vuncollapse =>
             EVERY'
               (if k' = k then
                  if m = 0 then
                    [hyp_subst_tac, rtac refl]
                  else
                    [rtac (vuncollapse RS trans), maybe_atac,
                     if n = 1 then K all_tac else EVERY' [dtac meta_mp, atac, dtac meta_mp, atac],
                     REPEAT_DETERM_N (Int.max (0, m - 1)) o etac conjE, asm_simp_tac (ss_only [])]
                else
                  [dtac (the_single (if k = n then disc_excludes else disc_excludes')),
                   etac (if k = n then @{thm iff_contradict(1)} else @{thm iff_contradict(2)}),
                   atac, atac]))
             ks disc_excludess disc_excludess' uncollapses)])
         ks ms disc_excludesss disc_excludesss' uncollapses)) 1
    end;

fun mk_case_conv_tac ctxt n uexhaust cases discss' selss =
  (rtac uexhaust THEN'
   EVERY' (map3 (fn casex => fn if_discs => fn sels =>
       EVERY' [hyp_subst_tac, SELECT_GOAL (unfold_thms_tac ctxt (if_discs @ sels)), rtac casex])
     cases (map2 (seq_conds if_P_or_not_P_OF n) (1 upto n) discss') selss)) 1;

fun mk_case_cong_tac uexhaust cases =
  (rtac uexhaust THEN'
   EVERY' (maps (fn casex => [dtac sym, asm_simp_tac (ss_only [casex])]) cases)) 1;

val naked_ctxt = Proof_Context.init_global @{theory HOL};

(* TODO: More precise "simp_thms"; get rid of "blast_tac" *)
fun mk_split_tac uexhaust cases injectss distinctsss =
  rtac uexhaust 1 THEN
  ALLGOALS (fn k => (hyp_subst_tac THEN'
     simp_tac (ss_only (@{thms simp_thms} @ cases @ nth injectss (k - 1) @
       flat (nth distinctsss (k - 1))))) k) THEN
  ALLGOALS (blast_tac naked_ctxt);

val split_asm_thms = @{thms imp_conv_disj de_Morgan_conj de_Morgan_disj not_not not_ex};

fun mk_split_asm_tac ctxt split =
  rtac (split RS trans) 1 THEN unfold_thms_tac ctxt split_asm_thms THEN rtac refl 1;

end;
