(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Tactics for wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR_GENERAL_TACTICS =
sig
  val select_prem_tac: Proof.context -> int -> (int -> tactic) -> int -> int -> tactic
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
  val mk_disc_eq_case_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> thm list ->
    tactic
  val mk_exhaust_disc_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_exhaust_sel_tac: Proof.context -> int -> thm -> thm list -> tactic
  val mk_expand_tac: Proof.context -> int -> int list -> thm -> thm -> thm list ->
    thm list list list -> thm list list list -> tactic
  val mk_half_distinct_disc_tac: Proof.context -> int -> thm -> thm -> tactic
  val mk_nchotomy_tac: Proof.context -> int -> thm -> tactic
  val mk_other_half_distinct_disc_tac: Proof.context -> thm -> tactic
  val mk_split_tac: Proof.context -> thm -> thm list -> thm list list -> thm list list ->
    thm list list list -> tactic
  val mk_split_asm_tac: Proof.context -> thm -> tactic
  val mk_unique_disc_def_tac: Proof.context -> int -> thm -> tactic
end;

structure Ctr_Sugar_Tactics : CTR_SUGAR_TACTICS =
struct

open Ctr_Sugar_Util

val meta_mp = @{thm meta_mp};

fun select_prem_tac ctxt n tac k = DETERM o (EVERY' [REPEAT_DETERM_N (k - 1) o etac ctxt thin_rl,
  tac, REPEAT_DETERM_N (n - k) o etac ctxt thin_rl]);

val unfold_thms_tac = Local_Defs.unfold0_tac;

fun if_P_or_not_P_OF pos thm = thm RS (if pos then @{thm if_P} else @{thm if_not_P});

fun mk_nchotomy_tac ctxt n exhaust =
  HEADGOAL (rtac ctxt allI THEN' rtac ctxt exhaust THEN'
    EVERY' (maps (fn k =>
        [rtac ctxt (mk_disjIN n k), REPEAT_DETERM o rtac ctxt exI, assume_tac ctxt])
      (1 upto n)));

fun mk_unique_disc_def_tac ctxt m uexhaust =
  HEADGOAL (EVERY'
    [rtac ctxt iffI, rtac ctxt uexhaust, REPEAT_DETERM_N m o rtac ctxt exI,
      assume_tac ctxt, rtac ctxt refl]);

fun mk_alternate_disc_def_tac ctxt k other_disc_def distinct uexhaust =
  HEADGOAL (EVERY' ([rtac ctxt (other_disc_def RS @{thm arg_cong[of _ _ Not]} RS trans),
    rtac ctxt @{thm iffI_np}, REPEAT_DETERM o etac ctxt exE,
    hyp_subst_tac ctxt, SELECT_GOAL (unfold_thms_tac ctxt [not_ex]), REPEAT_DETERM o rtac ctxt allI,
    rtac ctxt distinct, rtac ctxt uexhaust] @
    (([etac ctxt notE, REPEAT_DETERM o rtac ctxt exI, assume_tac ctxt],
      [REPEAT_DETERM o rtac ctxt exI, assume_tac ctxt])
     |> k = 1 ? swap |> op @)));

fun mk_half_distinct_disc_tac ctxt m discD disc' =
  HEADGOAL (dtac ctxt discD THEN' REPEAT_DETERM_N m o etac ctxt exE THEN' hyp_subst_tac ctxt THEN'
    rtac ctxt disc');

fun mk_other_half_distinct_disc_tac ctxt half =
  HEADGOAL (etac ctxt @{thm contrapos_pn} THEN' etac ctxt half);

fun mk_exhaust_disc_or_sel_tac ctxt n exhaust destIs =
  HEADGOAL (rtac ctxt exhaust THEN'
    EVERY' (map2 (fn k => fn destI => dtac ctxt destI THEN'
      select_prem_tac ctxt n (etac ctxt meta_mp) k THEN' assume_tac ctxt) (1 upto n) destIs));

val mk_exhaust_disc_tac = mk_exhaust_disc_or_sel_tac;

fun mk_exhaust_sel_tac ctxt n exhaust_disc collapses =
  mk_exhaust_disc_or_sel_tac ctxt n exhaust_disc collapses ORELSE
  HEADGOAL (etac ctxt meta_mp THEN' resolve_tac ctxt collapses);

fun mk_collapse_tac ctxt m discD sels =
  HEADGOAL (dtac ctxt discD THEN'
    (if m = 0 then
       assume_tac ctxt
     else
       REPEAT_DETERM_N m o etac ctxt exE THEN' hyp_subst_tac ctxt THEN'
       SELECT_GOAL (unfold_thms_tac ctxt sels) THEN' rtac ctxt refl));

fun mk_disc_eq_case_tac ctxt ct exhaust discs distincts cases =
  HEADGOAL Goal.conjunction_tac THEN
  ALLGOALS (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust) THEN_ALL_NEW
    (hyp_subst_tac ctxt THEN'
     SELECT_GOAL (unfold_thms_tac ctxt (@{thms not_True_eq_False not_False_eq_True} @ cases @
       ((refl :: discs @ distincts) RL [eqTrueI, eqFalseI]))) THEN'
     resolve_tac ctxt @{thms TrueI True_not_False False_not_True}));

fun mk_expand_tac ctxt n ms uexhaust_disc vexhaust_disc uncollapses distinct_discsss
    distinct_discsss' =
  if ms = [0] then
    HEADGOAL (rtac ctxt (@{thm trans_sym} OF (replicate 2 (the_single uncollapses))) THEN'
      TRY o
      EVERY' [rtac ctxt uexhaust_disc, assume_tac ctxt, rtac ctxt vexhaust_disc, assume_tac ctxt])
  else
    let val ks = 1 upto n in
      HEADGOAL (rtac ctxt uexhaust_disc THEN'
        EVERY' (@{map 5} (fn k => fn m => fn distinct_discss => fn distinct_discss' =>
            fn uuncollapse =>
          EVERY' [rtac ctxt (uuncollapse RS trans) THEN'
            TRY o assume_tac ctxt, rtac ctxt sym, rtac ctxt vexhaust_disc,
            EVERY' (@{map 4} (fn k' => fn distinct_discs => fn distinct_discs' => fn vuncollapse =>
              EVERY'
                (if k' = k then
                   [rtac ctxt (vuncollapse RS trans), TRY o assume_tac ctxt] @
                   (if m = 0 then
                      [rtac ctxt refl]
                    else
                      [if n = 1 then
                         K all_tac
                       else
                         EVERY' [dtac ctxt meta_mp, assume_tac ctxt, dtac ctxt meta_mp,
                           assume_tac ctxt],
                         REPEAT_DETERM_N (Int.max (0, m - 1)) o etac ctxt conjE,
                         asm_simp_tac (ss_only [] ctxt)])
                 else
                   [dtac ctxt (the_single (if k = n then distinct_discs else distinct_discs')),
                    etac ctxt (if k = n then @{thm iff_contradict(1)}
                      else @{thm iff_contradict(2)}),
                    assume_tac ctxt, assume_tac ctxt]))
              ks distinct_discss distinct_discss' uncollapses)])
          ks ms distinct_discsss distinct_discsss' uncollapses))
    end;

fun mk_case_same_ctr_tac ctxt injects =
  REPEAT_DETERM o etac ctxt exE THEN' etac ctxt conjE THEN'
    (case injects of
      [] => assume_tac ctxt
    | [inject] => dtac ctxt (inject RS iffD1) THEN' REPEAT_DETERM o etac ctxt conjE THEN'
        hyp_subst_tac ctxt THEN' rtac ctxt refl);

fun mk_case_distinct_ctrs_tac ctxt distincts =
  REPEAT_DETERM o etac ctxt exE THEN' etac ctxt conjE THEN' full_simp_tac (ss_only distincts ctxt);

fun mk_case_tac ctxt n k case_def injects distinctss =
  let
    val case_def' = mk_unabs_def (n + 1) (HOLogic.mk_obj_eq case_def);
    val ks = 1 upto n;
  in
    HEADGOAL (rtac ctxt (case_def' RS trans) THEN' rtac ctxt @{thm the_equality} THEN'
      rtac ctxt (mk_disjIN n k) THEN' REPEAT_DETERM o rtac ctxt exI THEN' rtac ctxt conjI THEN'
      rtac ctxt refl THEN' rtac ctxt refl THEN'
      EVERY' (map2 (fn k' => fn distincts =>
        (if k' < n then etac ctxt disjE else K all_tac) THEN'
        (if k' = k then mk_case_same_ctr_tac ctxt injects
         else mk_case_distinct_ctrs_tac ctxt distincts)) ks distinctss))
  end;

fun mk_case_distrib_tac ctxt ct exhaust cases =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust)) THEN
  ALLGOALS (hyp_subst_tac ctxt THEN' SELECT_GOAL (unfold_thms_tac ctxt cases) THEN' rtac ctxt refl);

fun mk_case_cong_tac ctxt uexhaust cases =
  HEADGOAL (rtac ctxt uexhaust THEN'
    EVERY' (maps (fn casex => [dtac ctxt sym, asm_simp_tac (ss_only [casex] ctxt)]) cases));

fun mk_case_eq_if_tac ctxt n uexhaust cases discss' selss =
  HEADGOAL (rtac ctxt uexhaust THEN'
    EVERY' (@{map 3} (fn casex => fn if_discs => fn sels =>
        EVERY' [hyp_subst_tac ctxt, SELECT_GOAL (unfold_thms_tac ctxt (if_discs @ sels)),
          rtac ctxt casex])
      cases (map2 (seq_conds if_P_or_not_P_OF n) (1 upto n) discss') selss));

fun mk_split_tac ctxt uexhaust cases selss injectss distinctsss =
  HEADGOAL (rtac ctxt uexhaust) THEN
  ALLGOALS (fn k => (hyp_subst_tac ctxt THEN'
    simp_tac (ss_only (@{thms simp_thms} @ cases @ nth selss (k - 1) @ nth injectss (k - 1) @
      flat (nth distinctsss (k - 1))) ctxt)) k) THEN
  ALLGOALS (etac ctxt thin_rl THEN' rtac ctxt iffI THEN'
    REPEAT_DETERM o rtac ctxt allI THEN' rtac ctxt impI THEN'
    REPEAT_DETERM o etac ctxt conjE THEN'
    hyp_subst_tac ctxt THEN' assume_tac ctxt THEN'
    REPEAT_DETERM o etac ctxt allE THEN' etac ctxt impE THEN'
    REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl) THEN'
    rtac ctxt refl THEN' assume_tac ctxt);

val split_asm_thms = @{thms imp_conv_disj de_Morgan_conj de_Morgan_disj not_not not_ex};

fun mk_split_asm_tac ctxt split =
  HEADGOAL (rtac ctxt (split RS trans)) THEN unfold_thms_tac ctxt split_asm_thms THEN
  HEADGOAL (rtac ctxt refl);

end;

structure Ctr_Sugar_General_Tactics : CTR_SUGAR_GENERAL_TACTICS = Ctr_Sugar_Tactics;
