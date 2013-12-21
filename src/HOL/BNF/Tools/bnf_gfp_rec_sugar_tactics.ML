(*  Title:      HOL/BNF/Tools/bnf_gfp_rec_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Tactics for corecursor sugar.
*)

signature BNF_GFP_REC_SUGAR_TACTICS =
sig
  val mk_primcorec_assumption_tac: Proof.context -> thm list -> int -> tactic
  val mk_primcorec_code_of_raw_code_tac: Proof.context -> thm list -> thm list -> thm -> tactic
  val mk_primcorec_ctr_of_dtr_tac: Proof.context -> int -> thm -> thm option -> thm list -> tactic
  val mk_primcorec_disc_tac: Proof.context -> thm list -> thm -> int -> int -> thm list list list ->
    tactic
  val mk_primcorec_exhaust_tac: int -> thm -> tactic
  val mk_primcorec_raw_code_of_ctr_tac: Proof.context -> thm list -> thm list -> thm list ->
    thm list -> int list -> thm list -> thm option -> tactic
  val mk_primcorec_sel_tac: Proof.context -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm -> int -> int -> thm list list list -> tactic
end;

structure BNF_GFP_Rec_Sugar_Tactics : BNF_GFP_REC_SUGAR_TACTICS =
struct

open BNF_Util
open BNF_Tactics

val falseEs = @{thms not_TrueE FalseE};
val Let_def = @{thm Let_def};
val neq_eq_eq_contradict = @{thm neq_eq_eq_contradict};
val split_if = @{thm split_if};
val split_if_asm = @{thm split_if_asm};
val split_connectI = @{thms allI impI conjI};

fun mk_primcorec_exhaust_tac n nchotomy =
  let val ks = 1 upto n in
    HEADGOAL (cut_tac nchotomy THEN'
     EVERY' (map (fn k =>
        (if k < n then etac disjE else K all_tac) THEN'
        REPEAT o (etac conjE THEN' dtac meta_mp THEN' atac) THEN'
        dtac meta_mp THEN' atac THEN' atac)
      ks))
  end;

fun mk_primcorec_assumption_tac ctxt discIs =
  SELECT_GOAL (unfold_thms_tac ctxt
      @{thms not_not not_False_eq_True not_True_eq_False de_Morgan_conj de_Morgan_disj} THEN
    SOLVE (HEADGOAL (REPEAT o (rtac refl ORELSE' atac ORELSE' etac conjE ORELSE'
    eresolve_tac falseEs ORELSE'
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

fun mk_primcorec_sel_tac ctxt defs distincts splits split_asms map_idents map_comps f_sel k m
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
      (@{thms id_def o_def split_def sum.cases} @ map_comps @ map_idents)))));

fun mk_primcorec_ctr_of_dtr_tac ctxt m collapse maybe_disc_f sel_fs =
  HEADGOAL (rtac ((if null sel_fs then collapse else collapse RS sym) RS trans) THEN'
    (the_default (K all_tac) (Option.map rtac maybe_disc_f)) THEN' REPEAT_DETERM_N m o atac) THEN
  unfold_thms_tac ctxt (Let_def :: sel_fs) THEN HEADGOAL (rtac refl);

fun inst_split_eq ctxt split =
  (case prop_of split of
    @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ (Var (_, Type (_, [T, _])) $ _) $ _) =>
    let
      val s = Name.uu;
      val eq = Abs (Name.uu, T, HOLogic.mk_eq (Free (s, T), Bound 0));
      val split' = Drule.instantiate' [] [SOME (certify ctxt eq)] split;
    in
      Thm.generalize ([], [s]) (Thm.maxidx_of split' + 1) split'
    end
  | _ => split);

fun distinct_in_prems_tac distincts =
  eresolve_tac (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN' atac;

fun mk_primcorec_raw_code_of_ctr_single_tac ctxt distincts discIs splits split_asms m f_ctr =
  let
    val splits' =
      map (fn th => th RS iffD2) (@{thm split_if_eq2} :: map (inst_split_eq ctxt) splits)
  in
    HEADGOAL (REPEAT o (resolve_tac (splits' @ split_connectI))) THEN
    mk_primcorec_prelude ctxt [] (f_ctr RS trans) THEN
    HEADGOAL ((REPEAT_DETERM_N m o mk_primcorec_assumption_tac ctxt discIs) THEN'
      SELECT_GOAL (SOLVE (HEADGOAL (REPEAT_DETERM o
      (rtac refl ORELSE' atac ORELSE'
       resolve_tac (@{thm Code.abort_def} :: split_connectI) ORELSE'
       Splitter.split_tac (split_if :: splits) ORELSE'
       Splitter.split_asm_tac (split_if_asm :: split_asms) ORELSE'
       mk_primcorec_assumption_tac ctxt discIs ORELSE'
       distinct_in_prems_tac distincts ORELSE'
       (TRY o dresolve_tac discIs) THEN' etac notE THEN' atac)))))
  end;

fun rulify_nchotomy n = funpow (n - 1) (fn thm => thm RS @{thm Meson.make_pos_rule'});

fun mk_primcorec_raw_code_of_ctr_tac ctxt distincts discIs splits split_asms ms f_ctrs
    maybe_nchotomy =
  let
    val n = length ms;
    val (ms', f_ctrs') =
      (case maybe_nchotomy of
        NONE => (ms, f_ctrs)
      | SOME nchotomy =>
        (ms |> split_last ||> K [n - 1] |> op @,
         f_ctrs
         |> split_last
         ||> unfold_thms ctxt @{thms atomize_conjL}
         ||> (fn thm => [rulify_nchotomy n nchotomy RS thm])
         |> op @));
  in
    EVERY (map2 (mk_primcorec_raw_code_of_ctr_single_tac ctxt distincts discIs splits split_asms)
      ms' f_ctrs') THEN
    IF_UNSOLVED (unfold_thms_tac ctxt @{thms Code.abort_def} THEN
      HEADGOAL (REPEAT_DETERM o resolve_tac (refl :: split_connectI)))
  end;

fun mk_primcorec_code_of_raw_code_tac ctxt distincts splits raw =
  HEADGOAL (rtac raw ORELSE' rtac (raw RS trans) THEN'
    SELECT_GOAL (unfold_thms_tac ctxt [Let_def]) THEN' REPEAT_DETERM o
    (rtac refl ORELSE' atac ORELSE'
     resolve_tac split_connectI ORELSE'
     Splitter.split_tac (split_if :: splits) ORELSE'
     distinct_in_prems_tac distincts ORELSE'
     rtac sym THEN' atac ORELSE'
     etac notE THEN' atac));

end;
