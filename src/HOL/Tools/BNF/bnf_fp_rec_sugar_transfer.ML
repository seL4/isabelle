(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_transfer.ML
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2014

Parametricity of primitively (co)recursive functions.
*)

signature BNF_FP_REC_SUGAR_TRANSFER =
sig
  val set_transfer_rule_attrs: thm list -> local_theory -> local_theory

  val lfp_rec_sugar_transfer_interpretation: BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context ->
    Proof.context
  val gfp_rec_sugar_transfer_interpretation: BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> Proof.context ->
    Proof.context
end;

structure BNF_FP_Rec_Sugar_Transfer : BNF_FP_REC_SUGAR_TRANSFER =
struct

open Ctr_Sugar_Util
open Ctr_Sugar_Tactics
open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_LFP_Rec_Sugar

val transferN = "transfer";

val transfer_rule_attrs = @{attributes [transfer_rule]};

fun set_transfer_rule_attrs thms =
  snd o Local_Theory.notes [(Binding.empty_atts, [(thms, transfer_rule_attrs)])];

fun mk_lfp_rec_sugar_transfer_tac ctxt def =
  unfold_thms_tac ctxt [def] THEN HEADGOAL (Transfer.transfer_prover_tac ctxt);

fun mk_gfp_rec_sugar_transfer_tac ctxt f_def corec_def type_definitions dtor_corec_transfers
    rel_pre_defs disc_eq_cases cases case_distribs case_congs =
  let
    fun instantiate_with_lambda thm =
      let
        val prop as \<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>HOL.eq _ for \<open>Var (_, fT) $ _\<close> _\<close>\<close>\<close> =
          Thm.prop_of thm;
        val T = range_type fT;
        val j = Term.maxidx_of_term prop + 1;
        val cond = Var (("x", j), HOLogic.boolT);
        val then_branch = Var (("t", j), T);
        val else_branch = Var (("e", j), T);
        val lam = Term.lambda cond (mk_If cond then_branch else_branch);
      in
        infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt lam)] thm
      end;

    val transfer_rules =
      @{thm Abs_transfer[OF type_definition_id_bnf_UNIV type_definition_id_bnf_UNIV]} ::
      map (fn thm => @{thm Abs_transfer} OF [thm, thm]) type_definitions @
      map (Local_Defs.unfold0 ctxt rel_pre_defs) dtor_corec_transfers;
    val add_transfer_rule = Thm.attribute_declaration Transfer.transfer_add;
    val ctxt' = Context.proof_map (fold add_transfer_rule transfer_rules) ctxt;

    val case_distribs = map instantiate_with_lambda case_distribs;
    val simps = case_distribs @ disc_eq_cases @ cases @ @{thms if_True if_False};
    val ctxt'' = put_simpset (simpset_of (ss_only simps ctxt)) ctxt';
  in
    unfold_thms_tac ctxt ([f_def, corec_def] @ @{thms split_beta if_conn}) THEN
    HEADGOAL (simp_tac (fold Simplifier.add_cong case_congs ctxt'')) THEN
    HEADGOAL (Transfer.transfer_prover_tac ctxt')
  end;

fun massage_simple_notes base =
  filter_out (null o #2)
  #> map (fn (thmN, thms, f_attrs) =>
    ((Binding.qualify true base (Binding.name thmN), []),
     map_index (fn (kk, thm) => ([thm], f_attrs kk)) thms));

fun fp_sugar_of_bnf ctxt = fp_sugar_of ctxt o (fn Type (s, _) => s) o T_of_bnf;

fun bnf_depth_first_traverse ctxt f T =
  (case T of
    Type (s, Ts) =>
    (case bnf_of ctxt s of
      NONE => I
    | SOME bnf => fold (bnf_depth_first_traverse ctxt f) Ts o f bnf)
  | _ => I);

fun mk_goal lthy f =
  let
    val skematic_Ts = Term.add_tvarsT (fastype_of f) [];

    val ((As, Bs), names_lthy) = lthy
      |> mk_TFrees' (map snd skematic_Ts)
      ||>> mk_TFrees' (map snd skematic_Ts);

    val ((Rs, Rs'), names_lthy) = mk_Frees' "R" (map2 mk_pred2T As Bs) names_lthy;

    val fA = Term.subst_TVars (map fst skematic_Ts ~~ As) f;
    val fB = Term.subst_TVars (map fst skematic_Ts ~~ Bs) f;

    val goal = mk_parametricity_goal lthy Rs fA fB;
    val used_Rs = Term.add_frees goal [];
    val subst = map (dest_pred2T o snd) (filter_out (member (op =) used_Rs) Rs');
  in
    (goal |> Term.subst_atomic_types subst, names_lthy)
  end;

fun fp_rec_sugar_transfer_interpretation prove {transfers, fun_names, funs, fun_defs, fpTs} =
  fold_index (fn (kk, (((transfer, fun_name), funx), fun_def)) => fn lthy =>
      if transfer then
        (case try (map the) (map (fn Type (s, _) => bnf_of lthy s | _ => NONE) fpTs) of
          NONE => error "No transfer rule possible"
        | SOME bnfs =>
          (case try (prove kk bnfs funx fun_def) lthy of
            NONE => error "Failed to prove transfer rule"
          | SOME thm =>
            let
              val notes = [(transferN, [thm], K @{attributes [transfer_rule]})]
                |> massage_simple_notes fun_name;
            in
              snd (Local_Theory.notes notes lthy)
            end))
      else
        lthy)
    (transfers ~~ fun_names ~~ funs ~~ fun_defs);

val lfp_rec_sugar_transfer_interpretation = fp_rec_sugar_transfer_interpretation
  (fn _ => fn _ => fn f => fn def => fn lthy =>
    let
      val (goal, _) = mk_goal lthy f;
      val vars = Variable.add_free_names lthy goal [];
    in
      Goal.prove lthy vars [] goal (fn {context = ctxt, prems = _} =>
        mk_lfp_rec_sugar_transfer_tac ctxt def)
      |> Thm.close_derivation \<^here>
    end);

val gfp_rec_sugar_transfer_interpretation = fp_rec_sugar_transfer_interpretation
  (fn kk => fn bnfs => fn f => fn def => fn lthy =>
     let
       val fp_sugars = map (the o fp_sugar_of_bnf lthy) bnfs;
       val (goal, _) = mk_goal lthy f;
       val vars = Variable.add_free_names lthy goal [];
       val (disc_eq_cases, case_thms, case_distribs, case_congs) =
         bnf_depth_first_traverse lthy (fn bnf =>
             (case fp_sugar_of_bnf lthy bnf of
               NONE => I
             | SOME {fp_ctr_sugar = {ctr_sugar = {disc_eq_cases, case_thms, case_distribs,
                 case_cong, ...}, ...}, ...} =>
               (fn (disc_eq_cases0, case_thms0, case_distribs0, case_congs0) =>
                  (union Thm.eq_thm disc_eq_cases disc_eq_cases0,
                   union Thm.eq_thm case_thms case_thms0,
                   union Thm.eq_thm case_distribs case_distribs0,
                   insert Thm.eq_thm case_cong case_congs0))))
           (fastype_of f) ([], [], [], []);
     in
       Goal.prove lthy vars [] goal (fn {context = ctxt, prems = _} =>
         mk_gfp_rec_sugar_transfer_tac ctxt def
           (#co_rec_def (the (#fp_co_induct_sugar (nth fp_sugars kk))))
           (map (#type_definition o #absT_info) fp_sugars)
           (maps (#xtor_co_rec_transfers o #fp_res) fp_sugars)
           (map (rel_def_of_bnf o #pre_bnf) fp_sugars)
           disc_eq_cases case_thms case_distribs case_congs)
       |> Thm.close_derivation \<^here>
     end);

val _ = Theory.setup (lfp_rec_sugar_interpretation transfer_plugin
  lfp_rec_sugar_transfer_interpretation);

end;
