(*  Title:      HOL/Codatatype/Tools/bnf_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

General tactics for bounded natural functors.
*)

signature BNF_TACTICS =
sig
  val select_prem_tac: int -> (int -> tactic) -> int -> int -> tactic
  val fo_rtac: thm -> Proof.context -> int -> tactic
  val subst_tac: Proof.context -> thm list -> int -> tactic
  val substs_tac: Proof.context -> thm list -> int -> tactic

  val mk_flatten_assoc_tac: (int -> tactic) -> thm -> thm -> thm -> tactic
  val mk_rotate_eq_tac: (int -> tactic) -> thm -> thm -> thm -> thm -> ''a list -> ''a list ->
    int -> tactic

  val mk_Abs_bij_thm: Proof.context -> thm -> thm -> thm -> thm
  val mk_Abs_inj_thm: thm -> thm -> thm
  val mk_Abs_inverse_thm: thm -> thm -> thm
  val mk_T_I: thm -> thm
  val mk_T_subset1: thm -> thm
  val mk_T_subset2: thm -> thm

  val mk_Card_order_tac: thm -> tactic
  val mk_collect_set_natural_tac: Proof.context -> thm list -> tactic
  val mk_id': thm -> thm
  val mk_comp': thm -> thm
  val mk_in_mono_tac: int -> tactic
  val mk_map_comp_id_tac: thm -> tactic
  val mk_map_cong_tac: int -> thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_map_congL_tac: int -> thm -> thm -> tactic
  val mk_map_wppull_tac: thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_map_wpull_tac: thm -> thm list -> thm -> tactic
  val mk_set_natural': thm -> thm
  val mk_simple_wit_tac: thm list -> tactic

  val mk_pred_unfold_tac: thm -> thm list -> thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_rel_Gr_tac: thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rel_Id_tac: int -> thm -> thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_rel_O_tac: thm -> thm -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_in_rel_tac: thm -> int -> {prems: 'b, context: Proof.context} -> tactic
  val mk_rel_converse_tac: thm -> tactic
  val mk_rel_converse_le_tac: thm -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rel_mono_tac: thm -> thm -> {prems: 'a, context: Proof.context} -> tactic
end;

structure BNF_Tactics : BNF_TACTICS =
struct

open BNF_Util

val set_mp = @{thm set_mp};

fun select_prem_tac n tac k = DETERM o (EVERY' [REPEAT_DETERM_N (k - 1) o etac thin_rl,
  tac, REPEAT_DETERM_N (n - k) o etac thin_rl]);

(*stolen from Christian Urban's Cookbook*)
fun fo_rtac thm = Subgoal.FOCUS (fn {concl, ...} =>
  let
    val concl_pat = Drule.strip_imp_concl (cprop_of thm)
    val insts = Thm.first_order_match (concl_pat, concl)
  in
    rtac (Drule.instantiate_normalize insts thm) 1
  end);

(*unlike "unfold_tac", succeeds when the RHS contains schematic variables not in the LHS*)
fun subst_tac ctxt = EqSubst.eqsubst_tac ctxt [0];
fun substs_tac ctxt = REPEAT_DETERM oo subst_tac ctxt;



(* Theorems for typedefs with UNIV as representing set *)

(*equivalent to UNIV_I for the representing set of the particular type T*)
fun mk_T_subset1 def = set_mp OF [def RS meta_eq_to_obj_eq RS equalityD2];
fun mk_T_subset2 def = set_mp OF [def RS meta_eq_to_obj_eq RS equalityD1];
fun mk_T_I def = UNIV_I RS mk_T_subset1 def;

fun mk_Abs_inverse_thm def inv = mk_T_I def RS inv;
fun mk_Abs_inj_thm def inj = inj OF (replicate 2 (mk_T_I def));
fun mk_Abs_bij_thm ctxt def inj surj = rule_by_tactic ctxt ((rtac surj THEN' etac exI) 1)
  (mk_Abs_inj_thm def inj RS @{thm bijI});



(* General tactic generators *)

(*applies assoc rule to the lhs of an equation as long as possible*)
fun mk_flatten_assoc_tac refl_tac trans assoc cong = rtac trans 1 THEN
  REPEAT_DETERM (CHANGED ((FIRST' [rtac trans THEN' rtac assoc, rtac cong THEN' refl_tac]) 1)) THEN
  refl_tac 1;

(*proves two sides of an equation to be equal assuming both are flattened and rhs can be obtained
from lhs by the given permutation of monoms*)
fun mk_rotate_eq_tac refl_tac trans assoc com cong =
  let
    fun gen_tac [] [] = K all_tac
      | gen_tac [x] [y] = if x = y then refl_tac else error "mk_rotate_eq_tac: different lists"
      | gen_tac (x :: xs) (y :: ys) = if x = y
        then rtac cong THEN' refl_tac THEN' gen_tac xs ys
        else rtac trans THEN' rtac com THEN'
          K (mk_flatten_assoc_tac refl_tac trans assoc cong) THEN'
          gen_tac (xs @ [x]) (y :: ys)
      | gen_tac _ _ = error "mk_rotate_eq_tac: different lists";
  in
    gen_tac
  end;

fun mk_Card_order_tac card_order =
  (rtac conjE THEN'
  rtac @{thm card_order_on_Card_order} THEN'
  rtac card_order THEN'
  atac) 1;

fun mk_id' id = mk_trans (fun_cong OF [id]) @{thm id_apply};
fun mk_comp' comp = @{thm o_eq_dest_lhs} OF [mk_sym comp];
fun mk_set_natural' set_natural = set_natural RS @{thm pointfreeE};
fun mk_in_mono_tac n = if n = 0 then rtac @{thm subset_UNIV} 1
  else (rtac subsetI THEN'
  rtac CollectI) 1 THEN
  REPEAT_DETERM (eresolve_tac [CollectE, conjE] 1) THEN
  REPEAT_DETERM_N (n - 1)
    ((rtac conjI THEN' etac subset_trans THEN' atac) 1) THEN
  (etac subset_trans THEN' atac) 1;

fun mk_map_wpull_tac comp_in_alt inner_map_wpulls outer_map_wpull =
  (rtac (@{thm wpull_cong} OF (replicate 3 comp_in_alt)) THEN' rtac outer_map_wpull) 1 THEN
  WRAP (fn thm => rtac thm 1 THEN REPEAT_DETERM (atac 1)) (K all_tac) inner_map_wpulls all_tac THEN
  TRY (REPEAT_DETERM (atac 1 ORELSE rtac @{thm wpull_id} 1));

fun mk_collect_set_natural_tac ctxt set_naturals =
  substs_tac ctxt (@{thms collect_o image_insert image_empty} @ set_naturals) 1 THEN rtac refl 1;

fun mk_simple_wit_tac wit_thms = ALLGOALS (atac ORELSE' eresolve_tac (@{thm emptyE} :: wit_thms));

fun mk_map_comp_id_tac map_comp =
  (rtac trans THEN' rtac map_comp) 1 THEN
  REPEAT_DETERM (stac @{thm o_id} 1) THEN
  rtac refl 1;

fun mk_map_congL_tac passive map_cong map_id' =
  (rtac trans THEN' rtac map_cong THEN' EVERY' (replicate passive (rtac refl))) 1 THEN
  REPEAT_DETERM (EVERY' [rtac trans, etac bspec, atac, rtac sym, rtac @{thm id_apply}] 1) THEN
  rtac map_id' 1;

fun mk_map_wppull_tac map_id map_cong map_wpull map_comp set_naturals =
  if null set_naturals then
    EVERY' [rtac @{thm wppull_id}, rtac map_wpull, rtac map_id, rtac map_id] 1
  else EVERY' [REPEAT_DETERM o etac conjE, REPEAT_DETERM o dtac @{thm wppull_thePull},
    REPEAT_DETERM o etac exE, rtac @{thm wpull_wppull}, rtac map_wpull,
    REPEAT_DETERM o rtac @{thm wpull_thePull}, rtac ballI,
    REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac conjI, rtac CollectI,
    CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
      rtac @{thm image_subsetI}, rtac conjunct1, etac bspec, etac set_mp, atac])
      set_naturals,
    CONJ_WRAP' (fn thm => EVERY' [rtac (map_comp RS trans), rtac (map_comp RS trans),
      rtac (map_comp RS trans RS sym), rtac map_cong,
      REPEAT_DETERM_N (length set_naturals) o EVERY' [rtac (o_apply RS trans),
        rtac (o_apply RS trans RS sym), rtac (o_apply RS trans), rtac thm,
        rtac conjunct2, etac bspec, etac set_mp, atac]]) [conjunct1, conjunct2]] 1;

fun mk_rel_Gr_tac rel_def map_id map_cong map_wpull in_cong map_id' map_comp set_naturals
  {context = ctxt, prems = _} =
  let
    val n = length set_naturals;
  in
    if null set_naturals then
      Local_Defs.unfold_tac ctxt [rel_def] THEN EVERY' [rtac @{thm Gr_UNIV_id}, rtac map_id] 1
    else Local_Defs.unfold_tac ctxt [rel_def, @{thm Gr_def}] THEN
      EVERY' [rtac equalityI, rtac subsetI,
        REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE, @{thm relcompE}, @{thm converseE}],
        REPEAT_DETERM o dtac @{thm Pair_eq[THEN subst, of "%x. x"]},
        REPEAT_DETERM o etac conjE, hyp_subst_tac,
        rtac CollectI, rtac exI, rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl,
        rtac sym, rtac trans, rtac map_comp, rtac map_cong,
        REPEAT_DETERM_N n o EVERY' [dtac @{thm set_rev_mp}, atac,
          REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
          rtac (o_apply RS trans), rtac (@{thm fst_conv} RS arg_cong RS trans),
          rtac (@{thm snd_conv} RS sym)],
        rtac CollectI,
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
          rtac @{thm image_subsetI}, dtac @{thm set_rev_mp}, atac,
          REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
          stac @{thm fst_conv}, atac]) set_naturals,
        rtac @{thm subrelI}, etac CollectE, REPEAT_DETERM o eresolve_tac [exE, conjE],
        REPEAT_DETERM o dtac @{thm Pair_eq[THEN subst, of "%x. x"]},
        REPEAT_DETERM o etac conjE, hyp_subst_tac,
        rtac allE, rtac subst, rtac @{thm wpull_def}, rtac map_wpull,
        REPEAT_DETERM_N n o rtac @{thm wpull_Gr}, etac allE, etac impE, rtac conjI, atac,
        rtac conjI, REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
          rtac @{thm image_mono}, atac]) set_naturals,
        rtac sym, rtac map_id', REPEAT_DETERM o eresolve_tac [bexE, conjE],
        rtac @{thm relcompI}, rtac @{thm converseI},
        REPEAT_DETERM_N 2 o EVERY' [rtac CollectI, rtac exI,
          rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl, etac sym,
          etac @{thm set_rev_mp}, rtac equalityD1, rtac in_cong,
          REPEAT_DETERM_N n o rtac @{thm Gr_def}]] 1
  end;

fun mk_rel_Id_tac n rel_Gr map_id {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt [rel_Gr, @{thm Id_alt}] THEN
  subst_tac ctxt [map_id] 1 THEN
    (if n = 0 then rtac refl 1
    else EVERY' [rtac @{thm arg_cong2[of _ _ _ _ Gr]},
      rtac equalityI, rtac @{thm subset_UNIV}, rtac subsetI, rtac CollectI,
      CONJ_WRAP' (K (rtac @{thm subset_UNIV})) (1 upto n), rtac refl] 1);

fun mk_rel_mono_tac rel_def in_mono {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt [rel_def] THEN
    EVERY' [rtac @{thm relcomp_mono}, rtac @{thm iffD2[OF converse_mono]},
      rtac @{thm Gr_mono}, rtac in_mono, REPEAT_DETERM o atac,
      rtac @{thm Gr_mono}, rtac in_mono, REPEAT_DETERM o atac] 1;

fun mk_map_cong_tac m map_cong {context = ctxt, prems = _} =
  EVERY' [rtac mp, rtac map_cong,
    CONJ_WRAP' (K (rtac ballI THEN' Goal.assume_rule_tac ctxt)) (1 upto m)] 1;

fun mk_rel_converse_le_tac rel_def rel_Id map_cong map_comp set_naturals
  {context = ctxt, prems = _} =
  let
    val n = length set_naturals;
  in
    if null set_naturals then
      Local_Defs.unfold_tac ctxt [rel_Id] THEN rtac equalityD2 1 THEN rtac @{thm converse_Id} 1
    else Local_Defs.unfold_tac ctxt [rel_def, @{thm Gr_def}] THEN
      EVERY' [rtac @{thm subrelI},
        REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE, @{thm relcompE}, @{thm converseE}],
        REPEAT_DETERM o dtac @{thm Pair_eq[THEN subst, of "%x. x"]},
        REPEAT_DETERM o etac conjE, hyp_subst_tac, rtac @{thm converseI},
        rtac @{thm relcompI}, rtac @{thm converseI},
        EVERY' (map (fn thm => EVERY' [rtac CollectI, rtac exI,
          rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl, rtac trans,
          rtac map_cong, REPEAT_DETERM_N n o rtac thm,
          rtac (map_comp RS sym), rtac CollectI,
          CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
            etac @{thm flip_rel}]) set_naturals]) [@{thm snd_fst_flip}, @{thm fst_snd_flip}])] 1
  end;

fun mk_rel_converse_tac le_converse =
  EVERY' [rtac equalityI, rtac le_converse, rtac @{thm xt1(6)}, rtac @{thm converse_shift},
    rtac le_converse, REPEAT_DETERM o stac @{thm converse_converse}, rtac subset_refl] 1;

fun mk_rel_O_tac rel_def rel_Id map_cong map_wppull map_comp set_naturals
  {context = ctxt, prems = _} =
  let
    val n = length set_naturals;
    fun in_tac nthO_in = rtac CollectI THEN'
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
          rtac @{thm image_subsetI}, rtac nthO_in, etac set_mp, atac]) set_naturals;
  in
    if null set_naturals then Local_Defs.unfold_tac ctxt [rel_Id] THEN rtac (@{thm Id_O_R} RS sym) 1
    else Local_Defs.unfold_tac ctxt [rel_def, @{thm Gr_def}] THEN
      EVERY' [rtac equalityI, rtac @{thm subrelI},
        REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE, @{thm relcompE}, @{thm converseE}],
        REPEAT_DETERM o dtac @{thm Pair_eq[THEN subst, of "%x. x"]},
        REPEAT_DETERM o etac conjE, hyp_subst_tac,
        rtac @{thm relcompI}, rtac @{thm relcompI}, rtac @{thm converseI},
        rtac CollectI, rtac exI, rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl,
        rtac sym, rtac trans, rtac map_comp, rtac sym, rtac map_cong,
        REPEAT_DETERM_N n o rtac @{thm fst_fstO},
        in_tac @{thm fstO_in},
        rtac CollectI, rtac exI, rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl,
        rtac sym, rtac trans, rtac map_comp, rtac map_cong,
        REPEAT_DETERM_N n o EVERY' [rtac trans, rtac o_apply, rtac ballE, rtac subst,
          rtac @{thm csquare_def}, rtac @{thm csquare_fstO_sndO}, atac, etac notE,
          etac set_mp, atac],
        in_tac @{thm fstO_in},
        rtac @{thm relcompI}, rtac @{thm converseI},
        rtac CollectI, rtac exI, rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl,
        rtac sym, rtac trans, rtac map_comp, rtac map_cong,
        REPEAT_DETERM_N n o rtac o_apply,
        in_tac @{thm sndO_in},
        rtac CollectI, rtac exI, rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl,
        rtac sym, rtac trans, rtac map_comp, rtac sym, rtac map_cong,
        REPEAT_DETERM_N n o rtac @{thm snd_sndO},
        in_tac @{thm sndO_in},
        rtac @{thm subrelI},
        REPEAT_DETERM o eresolve_tac [CollectE, @{thm relcompE}, @{thm converseE}],
        REPEAT_DETERM o eresolve_tac [exE, conjE],
        REPEAT_DETERM o dtac @{thm Pair_eq[THEN subst, of "%x. x"]},
        REPEAT_DETERM o etac conjE, hyp_subst_tac,
        rtac allE, rtac subst, rtac @{thm wppull_def}, rtac map_wppull,
        CONJ_WRAP' (K (rtac @{thm wppull_fstO_sndO})) set_naturals,
        etac allE, etac impE, etac conjI, etac conjI, atac,
        REPEAT_DETERM o eresolve_tac [bexE, conjE],
        rtac @{thm relcompI}, rtac @{thm converseI},
        EVERY' (map (fn thm => EVERY' [rtac CollectI, rtac exI,
          rtac conjI, stac @{thm Pair_eq}, rtac conjI, rtac refl, rtac sym, rtac trans,
          rtac trans, rtac map_cong, REPEAT_DETERM_N n o rtac thm,
          rtac (map_comp RS sym), atac, atac]) [@{thm fst_fstO}, @{thm snd_sndO}])] 1
  end;

fun mk_in_rel_tac rel_def m {context = ctxt, prems = _} =
  let
    val ls' = replicate (Int.max (1, m)) ();
  in
    Local_Defs.unfold_tac ctxt (rel_def ::
      @{thms Gr_def converse_unfold relcomp_unfold mem_Collect_eq prod.cases Pair_eq}) THEN
    EVERY' [rtac iffI, REPEAT_DETERM o eresolve_tac [exE, conjE], hyp_subst_tac, rtac exI,
      rtac conjI, CONJ_WRAP' (K atac) ls', rtac conjI, rtac refl, rtac refl,
      REPEAT_DETERM o eresolve_tac [exE, conjE], rtac exI, rtac conjI,
      REPEAT_DETERM_N 2 o EVERY' [rtac exI, rtac conjI, etac @{thm conjI[OF refl sym]},
        CONJ_WRAP' (K atac) ls']] 1
  end;

fun mk_pred_unfold_tac pred_def pred_defs rel_unfold {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt (@{thm mem_Collect_eq_split} :: pred_def :: pred_defs) THEN
  rtac rel_unfold 1;

end;
