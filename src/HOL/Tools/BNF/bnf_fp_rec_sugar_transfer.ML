(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_transfer.ML
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2014

Parametricity of primitively (co)recursive functions.
*)

(* DO NOT FORGET TO DOCUMENT THIS NEW PLUGIN!!! *)

signature BNF_FP_REC_SUGAR_TRANSFER =
sig

val primrec_transfer_pluginN : string
val primcorec_transfer_pluginN : string

val primrec_transfer_interpretation:
  BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context -> Proof.context
val primcorec_transfer_interpretation:
  BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context -> Proof.context

end;

structure BNF_FP_Rec_Sugar_Transfer : BNF_FP_REC_SUGAR_TRANSFER =
struct

open BNF_Def
open BNF_FP_Def_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_FP_Util
open Ctr_Sugar_Tactics
open Ctr_Sugar_Util

val primrec_transfer_pluginN = Plugin_Name.declare_setup @{binding primrec_transfer};
val primcorec_transfer_pluginN = Plugin_Name.declare_setup @{binding primcorec_transfer};

fun mk_primrec_transfer_tac ctxt def =
  Ctr_Sugar_Tactics.unfold_thms_tac ctxt [def] THEN
  HEADGOAL (Transfer.transfer_prover_tac ctxt);

fun mk_primcorec_transfer_tac apply_transfer ctxt f_def corec_def type_definitions
  dtor_corec_transfers rel_pre_defs disc_eq_cases cases case_distribs case_congs =
  let
    fun instantiate_with_lambda thm =
      let
        val prop = Thm.prop_of thm;
        val @{const Trueprop} $
          (Const (@{const_name HOL.eq}, _) $
            (Var (_, fT) $ _) $ _) = prop;
        val T = range_type fT;
        val idx = Term.maxidx_of_term prop + 1;
        val bool_expr = Var (("x", idx), HOLogic.boolT);
        val then_expr = Var (("t", idx), T);
        val else_expr = Var (("e", idx), T);
        val lambda = Term.lambda bool_expr (mk_If bool_expr then_expr else_expr);
      in
        cterm_instantiate_pos [SOME (certify ctxt lambda)] thm
      end;

    val transfer_rules =
      @{thm Abs_transfer[OF
        BNF_Composition.type_definition_id_bnf_UNIV
        BNF_Composition.type_definition_id_bnf_UNIV]} ::
      map (fn thm => @{thm Abs_transfer} OF [thm, thm]) type_definitions @
      map (Local_Defs.unfold ctxt rel_pre_defs) dtor_corec_transfers;
    val add_transfer_rule = Thm.attribute_declaration Transfer.transfer_add
    val ctxt' = Context.proof_map (fold add_transfer_rule transfer_rules) ctxt

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

val cat_somes = map the o filter is_some
fun maybe_apply z = the_default z oo Option.map

fun bnf_depth_first_traverse ctxt f T z =
  case T of
    Type (s, innerTs) =>
    (case bnf_of ctxt s of
      NONE => z
    | SOME bnf => let val z' = f bnf z in
        fold (bnf_depth_first_traverse ctxt f) innerTs z'
      end)
  | _ => z

fun if_all_bnfs ctxt Ts f g =
  let
    val bnfs = cat_somes (map (fn T =>
      case T of Type (s, _) => BNF_Def.bnf_of ctxt s | _ => NONE) Ts);
  in
    if length bnfs = length Ts then f bnfs else g
  end;

fun mk_goal lthy f =
  let
    val skematicTs = Term.add_tvarsT (fastype_of f) [];

    val ((As, Bs), names_lthy) = lthy
      |> Ctr_Sugar_Util.mk_TFrees' (map snd skematicTs)
      ||>> Ctr_Sugar_Util.mk_TFrees' (map snd skematicTs);

    val (Rs, names_lthy) =
      Ctr_Sugar_Util.mk_Frees "R" (map2 BNF_Util.mk_pred2T As Bs) names_lthy;

    val fA = Term.subst_TVars (map fst skematicTs ~~ As) f;
    val fB = Term.subst_TVars (map fst skematicTs ~~ Bs) f;
  in
    (BNF_FP_Def_Sugar.mk_parametricity_goal lthy Rs fA fB, names_lthy)
  end;

fun prove_parametricity_if_bnf prove {transfers, fun_names, funs, fun_defs, fpTs} lthy =
  fold_index (fn (n, (((transfer, f_names), f), def)) => fn lthy =>
      if not transfer then lthy
      else
        if_all_bnfs lthy fpTs
          (fn bnfs => fn () => prove n bnfs f_names f def lthy)
          (fn () => let val _ = error "Function is not parametric." in lthy end) ())
    (transfers ~~ fun_names ~~ funs ~~ fun_defs) lthy;

fun prim_co_rec_transfer_interpretation prove =
  prove_parametricity_if_bnf (fn n => fn bnfs => fn f_name => fn f => fn def => fn lthy =>
    case try (prove n bnfs f def) lthy of
      NONE => error "Failed to prove parametricity."
    | SOME thm =>
      let
        val notes =
          [("transfer", [thm], K @{attributes [transfer_rule]})]
          |> massage_simple_notes f_name;
      in
        snd (Local_Theory.notes notes lthy)
      end);

val primrec_transfer_interpretation = prim_co_rec_transfer_interpretation
  (fn n => fn bnfs => fn f => fn def => fn lthy =>
     let
       val (goal, names_lthy) = mk_goal lthy f;
     in
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
         bnf_depth_first_traverse lthy (fn bnf => fn xs =>
           let
             fun add_thms (xs, ys, zs, ws) (fp_sugar : fp_sugar) =
               let
                 val ctr_sugar = #ctr_sugar (#fp_ctr_sugar fp_sugar);
                 val xs' = #disc_eq_cases ctr_sugar;
                 val ys' = #case_thms ctr_sugar;
                 val zs' = #case_distribs ctr_sugar;
                 val w = #case_cong ctr_sugar;
                 val union' = union Thm.eq_thm;
                 val insert' = insert Thm.eq_thm;
               in
                 (union' xs' xs, union' ys' ys, union' zs' zs, insert' w ws)
               end;
           in
             maybe_apply xs (add_thms xs) (fp_sugar_of_bnf lthy bnf)
           end) (fastype_of f) ([], [], [], []);
     in
       Goal.prove lthy [] [] goal (fn {context = ctxt, prems = _} =>
         mk_primcorec_transfer_tac true ctxt def
         (#co_rec_def (#fp_co_induct_sugar (nth fp_sugars n)))
         (map (#type_definition o #absT_info) fp_sugars)
         (flat (map (#xtor_co_rec_transfers o #fp_res) fp_sugars))
         (map (rel_def_of_bnf o #pre_bnf) fp_sugars)
         disc_eq_cases case_thms case_distribs case_congs)
       |> singleton (Proof_Context.export names_lthy lthy)
       |> Thm.close_derivation
     end);

end
