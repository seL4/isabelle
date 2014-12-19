(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Tactics for wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR_GENERAL_TACTICS =
sig
  val clean_blast_tac: Proof.context -> int -> tactic
  val select_prem_tac: int -> (int -> tactic) -> int -> int -> tactic
  val unfold_thms_tac: Proof.context -> thm list -> tactic
end;

signature CTR_SUGAR_TACTICS =
sig
  include CTR_SUGAR_GENERAL_TACTICS

  val mk_alternate_disc_def_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_case_tac: Proof.context -> int -> int -> thm -> thm list -> thm list list -> tactic
  val mk_case_cong_tac: Proof.context -> thm -> thm list -> tactic
  val mk_case_distrib_tac: Proof.context -> cterm -> thm -> thm list -> tactic
  val mk_case_eq_if_tac: Proof.context -> int -> thm -> thm list -> thm list list ->
    thm list list -> tactic
  val mk_collapse_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_exhaust_disc_tac: int -> thm -> thm list -> tactic
  val mk_exhaust_sel_tac: int -> thm -> thm list -> tactic
  val mk_expand_tac: Proof.context -> int -> int list -> thm -> thm -> thm list ->
    thm list list list -> thm list list list -> tactic
  val mk_half_distinct_disc_tac: Proof.context -> int -> thm -> thm -> tactic
  val mk_nchotomy_tac: int -> thm -> tactic
  val mk_other_half_distinct_disc_tac: thm -> tactic
  val mk_split_tac: Proof.context -> thm -> thm list -> thm list list -> thm list list ->
    thm list list list -> tactic
  val mk_split_asm_tac: Proof.context -> thm -> tactic
  val mk_unique_disc_def_tac: int -> thm -> tactic
end;

structure Ctr_Sugar_Tactics : CTR_SUGAR_TACTICS =
struct

open Ctr_Sugar_Util

val meta_mp = @{thm meta_mp};

fun clean_blast_tac ctxt = blast_tac (put_claset (claset_of @{theory_context HOL}) ctxt);

fun select_prem_tac n tac k = DETERM o (EVERY' [REPEAT_DETERM_N (k - 1) o etac thin_rl,
  tac, REPEAT_DETERM_N (n - k) o etac thin_rl]);

fun unfold_thms_tac _ [] = all_tac
  | unfold_thms_tac ctxt thms = Local_Defs.unfold_tac ctxt (distinct Thm.eq_thm_prop thms);

fun if_P_or_not_P_OF pos thm = thm RS (if pos then @{thm if_P} else @{thm if_not_P});

fun mk_nchotomy_tac n exhaust =
  HEADGOAL (rtac allI THEN' rtac exhaust THEN'
    EVERY' (maps (fn k => [rtac (mk_disjIN n k), REPEAT_DETERM o rtac exI, atac]) (1 upto n)));

fun mk_unique_disc_def_tac m uexhaust =
  HEADGOAL (EVERY' [rtac iffI, rtac uexhaust, REPEAT_DETERM_N m o rtac exI, atac, rtac refl]);

fun mk_alternate_disc_def_tac ctxt k other_disc_def distinct uexhaust =
  HEADGOAL (EVERY' ([rtac (other_disc_def RS @{thm arg_cong[of _ _ Not]} RS trans),
    rtac @{thm iffI_np}, REPEAT_DETERM o etac exE,
    hyp_subst_tac ctxt, SELECT_GOAL (unfold_thms_tac ctxt [not_ex]), REPEAT_DETERM o rtac allI,
    rtac distinct, rtac uexhaust] @
    (([etac notE, REPEAT_DETERM o rtac exI, atac], [REPEAT_DETERM o rtac exI, atac])
     |> k = 1 ? swap |> op @)));

fun mk_half_distinct_disc_tac ctxt m discD disc' =
  HEADGOAL (dtac discD THEN' REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac ctxt THEN'
    rtac disc');

fun mk_other_half_distinct_disc_tac half = HEADGOAL (etac @{thm contrapos_pn} THEN' etac half);

fun mk_exhaust_disc_or_sel_tac n exhaust destIs =
  HEADGOAL (rtac exhaust THEN'
    EVERY' (map2 (fn k => fn destI => dtac destI THEN'
      select_prem_tac n (etac meta_mp) k THEN' atac) (1 upto n) destIs));

val mk_exhaust_disc_tac = mk_exhaust_disc_or_sel_tac;

fun mk_exhaust_sel_tac n exhaust_disc collapses =
  mk_exhaust_disc_or_sel_tac n exhaust_disc collapses ORELSE
  HEADGOAL (etac meta_mp THEN' resolve_tac collapses);

fun mk_collapse_tac ctxt m discD sels =
  HEADGOAL (dtac discD THEN'
    (if m = 0 then
       atac
     else
       REPEAT_DETERM_N m o etac exE THEN' hyp_subst_tac ctxt THEN'
       SELECT_GOAL (unfold_thms_tac ctxt sels) THEN' rtac refl));

fun mk_expand_tac ctxt n ms uexhaust_disc vexhaust_disc uncollapses distinct_discsss
    distinct_discsss' =
  if ms = [0] then
    HEADGOAL (rtac (@{thm trans_sym} OF (replicate 2 (the_single uncollapses))) THEN'
      TRY o EVERY' [rtac uexhaust_disc, atac, rtac vexhaust_disc, atac])
  else
    let val ks = 1 upto n in
      HEADGOAL (rtac uexhaust_disc THEN'
        EVERY' (@{map 5} (fn k => fn m => fn distinct_discss => fn distinct_discss' => fn uuncollapse =>
          EVERY' [rtac (uuncollapse RS trans) THEN' TRY o atac, rtac sym, rtac vexhaust_disc,
            EVERY' (@{map 4} (fn k' => fn distinct_discs => fn distinct_discs' => fn vuncollapse =>
              EVERY'
                (if k' = k then
                   [rtac (vuncollapse RS trans), TRY o atac] @
                   (if m = 0 then
                      [rtac refl]
                    else
                      [if n = 1 then K all_tac else EVERY' [dtac meta_mp, atac, dtac meta_mp, atac],
                       REPEAT_DETERM_N (Int.max (0, m - 1)) o etac conjE,
                       asm_simp_tac (ss_only [] ctxt)])
                 else
                   [dtac (the_single (if k = n then distinct_discs else distinct_discs')),
                    etac (if k = n then @{thm iff_contradict(1)} else @{thm iff_contradict(2)}),
                    atac, atac]))
              ks distinct_discss distinct_discss' uncollapses)])
          ks ms distinct_discsss distinct_discsss' uncollapses))
    end;

fun mk_case_same_ctr_tac ctxt injects =
  REPEAT_DETERM o etac exE THEN' etac conjE THEN'
    (case injects of
      [] => atac
    | [inject] => dtac (inject RS iffD1) THEN' REPEAT_DETERM o etac conjE THEN'
        hyp_subst_tac ctxt THEN' rtac refl);

fun mk_case_distinct_ctrs_tac ctxt distincts =
  REPEAT_DETERM o etac exE THEN' etac conjE THEN' full_simp_tac (ss_only distincts ctxt);

fun mk_case_tac ctxt n k case_def injects distinctss =
  let
    val case_def' = mk_unabs_def (n + 1) (case_def RS meta_eq_to_obj_eq);
    val ks = 1 upto n;
  in
    HEADGOAL (rtac (case_def' RS trans) THEN' rtac @{thm the_equality} THEN'
      rtac (mk_disjIN n k) THEN' REPEAT_DETERM o rtac exI THEN' rtac conjI THEN' rtac refl THEN'
      rtac refl THEN'
      EVERY' (map2 (fn k' => fn distincts =>
        (if k' < n then etac disjE else K all_tac) THEN'
        (if k' = k then mk_case_same_ctr_tac ctxt injects
         else mk_case_distinct_ctrs_tac ctxt distincts)) ks distinctss))
  end;

fun mk_case_distrib_tac ctxt ct exhaust cases =
  HEADGOAL (rtac (cterm_instantiate_pos [SOME ct] exhaust)) THEN
  ALLGOALS (hyp_subst_tac ctxt THEN' SELECT_GOAL (unfold_thms_tac ctxt cases) THEN' rtac refl);

fun mk_case_cong_tac ctxt uexhaust cases =
  HEADGOAL (rtac uexhaust THEN'
    EVERY' (maps (fn casex => [dtac sym, asm_simp_tac (ss_only [casex] ctxt)]) cases));

fun mk_case_eq_if_tac ctxt n uexhaust cases discss' selss =
  HEADGOAL (rtac uexhaust THEN'
    EVERY' (@{map 3} (fn casex => fn if_discs => fn sels =>
        EVERY' [hyp_subst_tac ctxt, SELECT_GOAL (unfold_thms_tac ctxt (if_discs @ sels)),
          rtac casex])
      cases (map2 (seq_conds if_P_or_not_P_OF n) (1 upto n) discss') selss));

fun mk_split_tac ctxt uexhaust cases selss injectss distinctsss =
  HEADGOAL (rtac uexhaust) THEN
  ALLGOALS (fn k => (hyp_subst_tac ctxt THEN'
     simp_tac (ss_only (@{thms simp_thms} @ cases @ nth selss (k - 1) @ nth injectss (k - 1) @
       flat (nth distinctsss (k - 1))) ctxt)) k) THEN
  ALLGOALS (clean_blast_tac ctxt);

val split_asm_thms = @{thms imp_conv_disj de_Morgan_conj de_Morgan_disj not_not not_ex};

fun mk_split_asm_tac ctxt split =
  HEADGOAL (rtac (split RS trans)) THEN unfold_thms_tac ctxt split_asm_thms THEN
  HEADGOAL (rtac refl);

end;

structure Ctr_Sugar_General_Tactics : CTR_SUGAR_GENERAL_TACTICS = Ctr_Sugar_Tactics;
