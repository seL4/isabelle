(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_transfer.ML
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2014

Parametricity of primitively (co)recursive functions.
*)

signature BNF_FP_REC_SUGAR_TRANSFER =
sig
  val primrec_transfer_interpretation: BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context ->
    Proof.context
  val primcorec_transfer_interpretation: BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context ->
    Proof.context
end;

structure BNF_FP_Rec_Sugar_Transfer : BNF_FP_REC_SUGAR_TRANSFER =
struct

open Ctr_Sugar_Util
open Ctr_Sugar_Tactics
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_Rec_Sugar_Util

val transferN = "transfer";

fun mk_primrec_transfer_tac ctxt def =
  Ctr_Sugar_Tactics.unfold_thms_tac ctxt [def] THEN
  HEADGOAL (Transfer.transfer_prover_tac ctxt);

fun mk_primcorec_transfer_tac apply_transfer ctxt f_def corec_def type_definitions
    dtor_corec_transfers rel_pre_defs disc_eq_cases cases case_distribs case_congs =
  let
    fun instantiate_with_lambda thm =
      let
        val prop = Thm.prop_of thm;
        val @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ (Var (_, fT) $ _) $ _) = prop;
        val T = range_type fT;
        val j = Term.maxidx_of_term prop + 1;
        val cond = Var (("x", j), HOLogic.boolT);
        val then_branch = Var (("t", j), T);
        val else_branch = Var (("e", j), T);
        val lambda = Term.lambda cond (mk_If cond then_branch else_branch);
      in
        cterm_instantiate_pos [SOME (certify ctxt lambda)] thm
      end;

    val transfer_rules =
      @{thm Abs_transfer[OF BNF_Composition.type_definition_id_bnf_UNIV
        BNF_Composition.type_definition_id_bnf_UNIV]} ::
      map (fn thm => @{thm Abs_transfer} OF [thm, thm]) type_definitions @
      map (Local_Defs.unfold ctxt rel_pre_defs) dtor_corec_transfers;
    val add_transfer_rule = Thm.attribute_declaration Transfer.transfer_add;
    val ctxt' = Context.proof_map (fold add_transfer_rule transfer_rules) ctxt;

    val case_distribs = map instantiate_with_lambda case_distribs;
    val simps = case_distribs @ disc_eq_cases @ cases @ @{thms if_True if_False};
    val simp_ctxt = put_simpset (simpset_of (ss_only simps ctxt)) ctxt';
  in
    unfold_thms_tac ctxt ([f_def, corec_def] @ @{thms split_beta if_conn}) THEN
    HEADGOAL (simp_tac (fold Simplifier.add_cong case_congs simp_ctxt)) THEN
    (if apply_transfer then HEADGOAL (Transfer.transfer_prover_tac ctxt') else all_tac)
  end;

fun massage_simple_notes base =
  filter_out (null o #2)
  #> map (fn (thmN, thms, f_attrs) =>
    ((Binding.qualify true base (Binding.name thmN), []),
     map_index (fn (i, thm) => ([thm], f_attrs i)) thms));

fun fp_sugar_of_bnf ctxt = fp_sugar_of ctxt o (fn Type (s, _) => s) o T_of_bnf;

fun bnf_depth_first_traverse ctxt f T z =
  (case T of
    Type (s, innerTs) =>
    (case bnf_of ctxt s of
      NONE => z
    | SOME bnf => let val z' = f bnf z in
        fold (bnf_depth_first_traverse ctxt f) innerTs z'
      end)
  | _ => z)

fun if_all_bnfs ctxt Ts f g =
  let val bnfs = map_filter (fn Type (s, _) => BNF_Def.bnf_of ctxt s | _ => NONE) Ts in
    if length bnfs = length Ts then f bnfs else g
  end;

fun mk_goal lthy f =
  let
    val skematic_Ts = Term.add_tvarsT (fastype_of f) [];

    val ((As, Bs), names_lthy) = lthy
      |> Ctr_Sugar_Util.mk_TFrees' (map snd skematic_Ts)
      ||>> Ctr_Sugar_Util.mk_TFrees' (map snd skematic_Ts);

    val (Rs, names_lthy) =
      Ctr_Sugar_Util.mk_Frees "R" (map2 BNF_Util.mk_pred2T As Bs) names_lthy;

    val fA = Term.subst_TVars (map fst skematic_Ts ~~ As) f;
    val fB = Term.subst_TVars (map fst skematic_Ts ~~ Bs) f;
  in
    (BNF_FP_Def_Sugar.mk_parametricity_goal lthy Rs fA fB, names_lthy)
  end;

fun prove_parametricity_if_bnf prove {transfers, fun_names, funs, fun_defs, fpTs} lthy =
  fold_index (fn (n, (((transfer, f_names), f), def)) => fn lthy =>
      if not transfer then
        lthy
      else
        if_all_bnfs lthy fpTs
          (fn bnfs => fn () => prove n bnfs f_names f def lthy)
          (fn () => error "Function is not parametric" (*FIXME: wording*)) ())
    (transfers ~~ fun_names ~~ funs ~~ fun_defs) lthy;

fun prim_co_rec_transfer_interpretation prove =
  prove_parametricity_if_bnf (fn n => fn bnfs => fn f_name => fn f => fn def => fn lthy =>
    (case try (prove n bnfs f def) lthy of
      NONE => error "Failed to prove parametricity"
    | SOME thm =>
      let
        val notes = [(transferN, [thm], K @{attributes [transfer_rule]})]
          |> massage_simple_notes f_name;
      in
        snd (Local_Theory.notes notes lthy)
      end));

val primrec_transfer_interpretation = prim_co_rec_transfer_interpretation
  (fn _ => fn _ => fn f => fn def => fn lthy =>
     let val (goal, names_lthy) = mk_goal lthy f in
       Goal.prove lthy [] [] goal (fn {context = ctxt, prems = _} =>
         mk_primrec_transfer_tac ctxt def)
       |> singleton (Proof_Context.export names_lthy lthy)
       |> Thm.close_derivation
     end);

val primcorec_transfer_interpretation = prim_co_rec_transfer_interpretation
  (fn n => fn bnfs => fn f => fn def => fn lthy =>
     let
       val fp_sugars = map (the o fp_sugar_of_bnf lthy) bnfs;
       val (goal, names_lthy) = mk_goal lthy f;
       val (disc_eq_cases, case_thms, case_distribs, case_congs) =
         bnf_depth_first_traverse lthy (fn bnf => fn quad =>
           let
             fun add_thms (disc_eq_cases0, case_thms0, case_distribs0, case_congs0)
                {fp_ctr_sugar = {ctr_sugar = {disc_eq_cases, case_thms, case_distribs, case_cong,
                   ...}, ...}, ...} =
               (union Thm.eq_thm disc_eq_cases disc_eq_cases0,
                union Thm.eq_thm case_thms case_thms0,
                union Thm.eq_thm case_distribs case_distribs0,
                insert Thm.eq_thm case_cong case_congs0);
           in
             Option.map (add_thms quad) (fp_sugar_of_bnf lthy bnf)
             |> the_default quad
           end) (fastype_of f) ([], [], [], []);
     in
       Goal.prove lthy [] [] goal (fn {context = ctxt, prems = _} =>
         mk_primcorec_transfer_tac true ctxt def
         (#co_rec_def (#fp_co_induct_sugar (nth fp_sugars n)))
         (map (#type_definition o #absT_info) fp_sugars)
         (maps (#xtor_co_rec_transfers o #fp_res) fp_sugars)
         (map (rel_def_of_bnf o #pre_bnf) fp_sugars)
         disc_eq_cases case_thms case_distribs case_congs)
       |> singleton (Proof_Context.export names_lthy lthy)
       |> Thm.close_derivation
     end);

val _ = Theory.setup (BNF_LFP_Rec_Sugar.primrec_interpretation Transfer_BNF.transfer_plugin
  primrec_transfer_interpretation);

end;
