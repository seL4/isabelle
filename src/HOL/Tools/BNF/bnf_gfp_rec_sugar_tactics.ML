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
val if_split = @{thm if_split};
val if_split_asm = @{thm if_split_asm};
val split_connectI = @{thms allI impI conjI};
val unfold_lets = @{thms Let_def[abs_def] split_beta}

fun exhaust_inst_as_projs ctxt frees thm =
  let
    val num_frees = length frees;
    val fs = Term.add_vars (Thm.prop_of thm) [] |> filter (can dest_funT o snd);
    fun find x = find_index (curry (op =) x) frees;
    fun mk_inst ((x, i), T) = ((x, i), Thm.cterm_of ctxt (mk_proj T num_frees (find x)));
  in infer_instantiate ctxt (map mk_inst fs) thm end;

val exhaust_inst_as_projs_tac = PRIMITIVE oo exhaust_inst_as_projs;

fun distinct_in_prems_tac ctxt distincts =
  eresolve_tac ctxt (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN'
  assume_tac ctxt;

fun mk_primcorec_nchotomy_tac ctxt exhaust_discs =
  HEADGOAL (Method.insert_tac ctxt exhaust_discs THEN' clean_blast_tac ctxt);

fun mk_primcorec_exhaust_tac ctxt frees n nchotomy =
  let val ks = 1 upto n in
    HEADGOAL (assume_tac ctxt ORELSE'
      cut_tac nchotomy THEN'
      K (exhaust_inst_as_projs_tac ctxt frees) THEN'
      EVERY' (map (fn k =>
          (if k < n then etac ctxt disjE else K all_tac) THEN'
          REPEAT o (dtac ctxt meta_mp THEN' assume_tac ctxt ORELSE'
            etac ctxt conjE THEN' dtac ctxt meta_mp THEN' assume_tac ctxt ORELSE'
            assume_tac ctxt))
        ks))
  end;

fun mk_primcorec_assumption_tac ctxt discIs =
  SELECT_GOAL (unfold_thms_tac ctxt @{thms fst_conv snd_conv not_not not_False_eq_True
      not_True_eq_False de_Morgan_conj de_Morgan_disj} THEN
    SOLVE (HEADGOAL (REPEAT o (rtac ctxt refl ORELSE' assume_tac ctxt ORELSE'
    etac ctxt conjE ORELSE'
    eresolve_tac ctxt falseEs ORELSE'
    resolve_tac ctxt @{thms TrueI conjI disjI1 disjI2} ORELSE'
    dresolve_tac ctxt discIs THEN' assume_tac ctxt ORELSE'
    etac ctxt notE THEN' assume_tac ctxt ORELSE'
    etac ctxt disjE))));

fun ss_fst_snd_conv ctxt =
  Raw_Simplifier.simpset_of (ss_only @{thms fst_conv snd_conv} ctxt);

fun case_atac ctxt =
  Simplifier.full_simp_tac (put_simpset (ss_fst_snd_conv ctxt) ctxt);

fun same_case_tac ctxt m =
  HEADGOAL (if m = 0 then rtac ctxt TrueI
    else REPEAT_DETERM_N (m - 1) o (rtac ctxt conjI THEN' case_atac ctxt) THEN' case_atac ctxt);

fun different_case_tac ctxt m exclude =
  HEADGOAL (if m = 0 then
      mk_primcorec_assumption_tac ctxt []
    else
      dtac ctxt exclude THEN' (REPEAT_DETERM_N (m - 1) o case_atac ctxt) THEN'
      mk_primcorec_assumption_tac ctxt []);

fun cases_tac ctxt k m excludesss =
  let val n = length excludesss in
    EVERY (map (fn [] => if k = n then all_tac else same_case_tac ctxt m
        | [exclude] => different_case_tac ctxt m exclude)
      (take k (nth excludesss (k - 1))))
  end;

fun prelude_tac ctxt fun_defs thm =
  unfold_thms_tac ctxt fun_defs THEN HEADGOAL (rtac ctxt thm) THEN unfold_thms_tac ctxt unfold_lets;

fun mk_primcorec_disc_tac ctxt fun_defs corec_disc k m excludesss =
  prelude_tac ctxt fun_defs corec_disc THEN cases_tac ctxt k m excludesss;

fun mk_primcorec_disc_iff_tac ctxt fun_exhaust_frees fun_exhaust fun_discs fun_discss
    distinct_discs =
  HEADGOAL (rtac ctxt iffI THEN'
    rtac ctxt fun_exhaust THEN'
    K (exhaust_inst_as_projs_tac ctxt fun_exhaust_frees) THEN'
    EVERY' (map (fn [] => etac ctxt FalseE
        | fun_discs' as [fun_disc'] =>
          if eq_list Thm.eq_thm (fun_discs', fun_discs) then
            REPEAT_DETERM o etac ctxt conjI THEN' (assume_tac ctxt ORELSE' rtac ctxt TrueI)
          else
            rtac ctxt FalseE THEN'
            (rotate_tac 1 THEN' dtac ctxt fun_disc' THEN' REPEAT o assume_tac ctxt ORELSE'
             cut_tac fun_disc') THEN'
            dresolve_tac ctxt distinct_discs THEN' etac ctxt notE THEN' assume_tac ctxt)
      fun_discss) THEN'
    (etac ctxt FalseE ORELSE'
     resolve_tac ctxt
      (map (unfold_thms ctxt [atomize_conjL]) fun_discs) THEN_MAYBE' assume_tac ctxt));

fun mk_primcorec_sel_tac ctxt fun_defs distincts splits split_asms mapsx map_ident0s map_comps
    fun_sel k m excludesss =
  prelude_tac ctxt fun_defs (fun_sel RS trans) THEN
  cases_tac ctxt k m excludesss THEN
  HEADGOAL (REPEAT_DETERM o (rtac ctxt refl ORELSE'
    eresolve_tac ctxt falseEs ORELSE'
    resolve_tac ctxt split_connectI ORELSE'
    Splitter.split_asm_tac ctxt (if_split_asm :: split_asms) ORELSE'
    Splitter.split_tac ctxt (if_split :: splits) ORELSE'
    eresolve_tac ctxt (map (fn thm => thm RS neq_eq_eq_contradict) distincts) THEN'
    assume_tac ctxt ORELSE'
    etac ctxt notE THEN' assume_tac ctxt ORELSE'
    (CHANGED o SELECT_GOAL (unfold_thms_tac ctxt (@{thms fst_conv snd_conv id_def comp_def split_def
         sum.case sum.sel sum.distinct[THEN eq_False[THEN iffD2]]} @
       mapsx @ map_ident0s @ map_comps))) ORELSE'
    fo_rtac ctxt @{thm cong} ORELSE'
    rtac ctxt @{thm ext} ORELSE'
    mk_primcorec_assumption_tac ctxt []));

fun mk_primcorec_ctr_tac ctxt m collapse disc_fun_opt sel_funs =
  HEADGOAL (rtac ctxt ((if null sel_funs then collapse else collapse RS sym) RS trans) THEN'
    (the_default (K all_tac) (Option.map (rtac ctxt) disc_fun_opt)) THEN'
    REPEAT_DETERM_N m o assume_tac ctxt) THEN
  unfold_thms_tac ctxt (@{thm split_def} :: unfold_lets @ sel_funs) THEN HEADGOAL (rtac ctxt refl);

fun inst_split_eq ctxt split =
  (case Thm.prop_of split of
    \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (Var (_, Type (_, [T, _])) $ _) $ _) =>
    let
      val s = Name.uu;
      val eq = Abs (Name.uu, T, HOLogic.mk_eq (Free (s, T), Bound 0));
    in
      Thm.instantiate' [] [SOME (Thm.cterm_of ctxt eq)] split
      |> Drule.generalize (Names.empty, Names.make_set [s])
    end
  | _ => split);

fun raw_code_single_tac ctxt distincts discIs splits split_asms m fun_ctr =
  let
    val splits' =
      map (fn th => th RS iffD2) (@{thm if_split_eq2} :: map (inst_split_eq ctxt) splits);
  in
    HEADGOAL (REPEAT o (resolve_tac ctxt (splits' @ split_connectI))) THEN
    prelude_tac ctxt [] (fun_ctr RS trans) THEN
    HEADGOAL ((REPEAT_DETERM_N m o mk_primcorec_assumption_tac ctxt discIs) THEN'
      SELECT_GOAL (SOLVE (HEADGOAL (REPEAT_DETERM o
      (rtac ctxt refl ORELSE' assume_tac ctxt ORELSE'
       resolve_tac ctxt (@{thm Code.abort_def} :: split_connectI) ORELSE'
       Splitter.split_tac ctxt (if_split :: splits) ORELSE'
       Splitter.split_asm_tac ctxt (if_split_asm :: split_asms) ORELSE'
       mk_primcorec_assumption_tac ctxt discIs ORELSE'
       distinct_in_prems_tac ctxt distincts ORELSE'
       (TRY o dresolve_tac ctxt discIs) THEN' etac ctxt notE THEN' assume_tac ctxt)))))
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
      HEADGOAL (REPEAT_DETERM o resolve_tac ctxt (refl :: split_connectI)))
  end;

fun mk_primcorec_code_tac ctxt distincts splits raw =
  HEADGOAL (rtac ctxt raw ORELSE' rtac ctxt (raw RS trans) THEN'
    SELECT_GOAL (unfold_thms_tac ctxt unfold_lets) THEN' REPEAT_DETERM o
    (rtac ctxt refl ORELSE' assume_tac ctxt ORELSE'
     resolve_tac ctxt split_connectI ORELSE'
     Splitter.split_tac ctxt (if_split :: splits) ORELSE'
     distinct_in_prems_tac ctxt distincts ORELSE'
     rtac ctxt sym THEN' assume_tac ctxt ORELSE'
     etac ctxt notE THEN' assume_tac ctxt));

end;
