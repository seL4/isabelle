(*  Title:      HOL/Tools/BNF/bnf_gfp_rec_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Tactics for corecursor sugar.
*)

signature BNF_GFP_REC_SUGAR_TACTICS =
sig
  val mk_primcorec_assumption_tac: Proof.context -> thm list -> int -> tactic
  val mk_primcorec_code_tac: Proof.context -> thm list -> thm list -> thm -> tactic
  val mk_primcorec_ctr_tac: Proof.context -> int -> thm -> thm option -> thm list -> tactic
  val mk_primcorec_disc_tac: Proof.context -> thm list -> thm -> int -> int -> thm list list list ->
    tactic
  val mk_primcorec_disc_iff_tac: Proof.context -> string list -> thm -> thm list -> thm list list ->
    thm list -> tactic
  val mk_primcorec_exhaust_tac: Proof.context -> string list -> int -> thm -> tactic
  val mk_primcorec_nchotomy_tac: Proof.context -> thm list -> tactic
  val mk_primcorec_raw_code_tac: Proof.context -> thm list -> thm list -> thm list -> thm list ->
    int list -> thm list -> thm option -> tactic
  val mk_primcorec_sel_tac: Proof.context -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm -> int -> int -> thm list list list -> tactic
end;

structure BNF_GFP_Rec_Sugar_Tactics : BNF_GFP_REC_SUGAR_TACTICS =
struct

open BNF_Util
open BNF_Tactics
open BNF_FP_Util

val atomize_conjL = @{thm atomize_conjL};
val falseEs = @{thms not_TrueE FalseE};
val neq_eq_eq_contradict = @{thm neq_eq_eq_contradict};
val split_if = @{thm split_if};
val split_if_asm = @{thm split_if_asm};
val split_connectI = @{thms allI impI conjI};
val unfold_lets = @{thms Let_def[abs_def] split_beta}

fun exhaust_inst_as_projs ctxt frees thm =
  let
    val num_frees = length frees;
    val fs = Term.add_vars (prop_of thm) [] |> filter (can dest_funT o snd);
    fun find s = find_index (curry (op =) s) frees;
    fun mk_cfp (f as ((s, _), T)) =
      (certify ctxt (Var f), certify ctxt (mk_proj T num_frees (find s)));
    val cfps = map mk_cfp fs;
  in
    Drule.cterm_instantiate cfps thm
  end;

val exhaust_inst_as_projs_tac = PRIMITIVE oo exhaust_inst_as_projs;

fun distinct_in_prems_tac distincts =
  eresolve_tac (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN' atac;

fun mk_primcorec_nchotomy_tac ctxt disc_exhausts =
  HEADGOAL (Method.insert_tac disc_exhausts THEN' clean_blast_tac ctxt);

fun mk_primcorec_exhaust_tac ctxt frees n nchotomy =
  let val ks = 1 upto n in
    HEADGOAL (atac ORELSE'
      cut_tac nchotomy THEN'
      K (exhaust_inst_as_projs_tac ctxt frees) THEN'
      EVERY' (map (fn k =>
          (if k < n then etac disjE else K all_tac) THEN'
          REPEAT o (dtac meta_mp THEN' atac ORELSE'
            etac conjE THEN' dtac meta_mp THEN' atac ORELSE'
            atac))
        ks))
  end;

fun mk_primcorec_assumption_tac ctxt discIs =
  SELECT_GOAL (unfold_thms_tac ctxt @{thms fst_conv snd_conv not_not not_False_eq_True
      not_True_eq_False de_Morgan_conj de_Morgan_disj} THEN
    SOLVE (HEADGOAL (REPEAT o (rtac refl ORELSE' atac ORELSE' etac conjE ORELSE'
    eresolve_tac falseEs ORELSE'
    resolve_tac @{thms TrueI conjI disjI1 disjI2} ORELSE'
    dresolve_tac discIs THEN' atac ORELSE'
    etac notE THEN' atac ORELSE'
    etac disjE))));

val ss_fst_snd_conv = simpset_of (ss_only @{thms fst_conv snd_conv} @{context});

fun case_atac ctxt = simp_tac (put_simpset ss_fst_snd_conv ctxt);

fun same_case_tac ctxt m =
  HEADGOAL (if m = 0 then rtac TrueI
    else REPEAT_DETERM_N (m - 1) o (rtac conjI THEN' case_atac ctxt) THEN' case_atac ctxt);

fun different_case_tac ctxt m exclude =
  HEADGOAL (if m = 0 then
      mk_primcorec_assumption_tac ctxt []
    else
      dtac exclude THEN' (REPEAT_DETERM_N (m - 1) o case_atac ctxt) THEN'
      mk_primcorec_assumption_tac ctxt []);

fun cases_tac ctxt k m excludesss =
  let val n = length excludesss in
    EVERY (map (fn [] => if k = n then all_tac else same_case_tac ctxt m
        | [exclude] => different_case_tac ctxt m exclude)
      (take k (nth excludesss (k - 1))))
  end;

fun prelude_tac ctxt defs thm =
  unfold_thms_tac ctxt defs THEN HEADGOAL (rtac thm) THEN unfold_thms_tac ctxt unfold_lets;

fun mk_primcorec_disc_tac ctxt defs disc_corec k m excludesss =
  prelude_tac ctxt defs disc_corec THEN cases_tac ctxt k m excludesss;

fun mk_primcorec_disc_iff_tac ctxt fun_exhaust_frees fun_exhaust fun_discs fun_discss
    disc_excludes =
  HEADGOAL (rtac iffI THEN'
    rtac fun_exhaust THEN'
    K (exhaust_inst_as_projs_tac ctxt fun_exhaust_frees) THEN'
    EVERY' (map (fn [] => etac FalseE
        | fun_discs' as [fun_disc'] =>
          if eq_list Thm.eq_thm (fun_discs', fun_discs) then
            REPEAT_DETERM o etac conjI THEN' (atac ORELSE' rtac TrueI)
          else
            rtac FalseE THEN'
            (rotate_tac 1 THEN' dtac fun_disc' THEN' REPEAT_DETERM o atac ORELSE'
             cut_tac fun_disc') THEN'
            dresolve_tac disc_excludes THEN' etac notE THEN' atac)
      fun_discss) THEN'
    (etac FalseE ORELSE'
     resolve_tac (map (unfold_thms ctxt [atomize_conjL]) fun_discs) THEN_MAYBE' atac));

fun mk_primcorec_sel_tac ctxt defs distincts splits split_asms mapsx map_idents map_comps fun_sel k
    m excludesss =
  prelude_tac ctxt defs (fun_sel RS trans) THEN
  cases_tac ctxt k m excludesss THEN
  HEADGOAL (REPEAT_DETERM o (rtac refl ORELSE' rtac ext ORELSE'
    eresolve_tac falseEs ORELSE'
    resolve_tac split_connectI ORELSE'
    Splitter.split_asm_tac (split_if_asm :: split_asms) ORELSE'
    Splitter.split_tac (split_if :: splits) ORELSE'
    eresolve_tac (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN' atac ORELSE'
    etac notE THEN' atac ORELSE'
    (CHANGED o SELECT_GOAL (unfold_thms_tac ctxt (@{thms fst_conv snd_conv id_def o_def split_def
       sum.cases} @ mapsx @ map_comps @ map_idents)))));

fun mk_primcorec_ctr_tac ctxt m collapse disc_fun_opt sel_funs =
  HEADGOAL (rtac ((if null sel_funs then collapse else collapse RS sym) RS trans) THEN'
    (the_default (K all_tac) (Option.map rtac disc_fun_opt)) THEN' REPEAT_DETERM_N m o atac) THEN
  unfold_thms_tac ctxt (@{thm split_def} :: unfold_lets @ sel_funs) THEN HEADGOAL (rtac refl);

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

fun raw_code_single_tac ctxt distincts discIs splits split_asms m fun_ctr =
  let
    val splits' =
      map (fn th => th RS iffD2) (@{thm split_if_eq2} :: map (inst_split_eq ctxt) splits)
  in
    HEADGOAL (REPEAT o (resolve_tac (splits' @ split_connectI))) THEN
    prelude_tac ctxt [] (fun_ctr RS trans) THEN
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

fun mk_primcorec_raw_code_tac ctxt distincts discIs splits split_asms ms fun_ctrs nchotomy_opt =
  let
    val n = length ms;
    val (ms', fun_ctrs') =
      (case nchotomy_opt of
        NONE => (ms, fun_ctrs)
      | SOME nchotomy =>
        (ms |> split_last ||> K [n - 1] |> op @,
         fun_ctrs
         |> split_last
         ||> unfold_thms ctxt [atomize_conjL]
         ||> (fn thm => [rulify_nchotomy n nchotomy RS thm] handle THM _ => [thm])
         |> op @));
  in
    EVERY (map2 (raw_code_single_tac ctxt distincts discIs splits split_asms) ms' fun_ctrs') THEN
    IF_UNSOLVED (unfold_thms_tac ctxt @{thms Code.abort_def} THEN
      HEADGOAL (REPEAT_DETERM o resolve_tac (refl :: split_connectI)))
  end;

fun mk_primcorec_code_tac ctxt distincts splits raw =
  HEADGOAL (rtac raw ORELSE' rtac (raw RS trans) THEN'
    SELECT_GOAL (unfold_thms_tac ctxt unfold_lets) THEN' REPEAT_DETERM o
    (rtac refl ORELSE' atac ORELSE'
     resolve_tac split_connectI ORELSE'
     Splitter.split_tac (split_if :: splits) ORELSE'
     distinct_in_prems_tac distincts ORELSE'
     rtac sym THEN' atac ORELSE'
     etac notE THEN' atac));

end;
