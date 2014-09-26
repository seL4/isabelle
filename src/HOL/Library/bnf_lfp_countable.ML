(*  Title:      HOL/Library/bnf_lfp_countable.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Countability tactic for BNF datatypes.
*)

signature BNF_LFP_COUNTABLE =
sig
  val derive_encode_injectives_thms: Proof.context -> string list -> thm list
  val countable_datatype_tac: Proof.context -> tactic
end;

structure BNF_LFP_Countable : BNF_LFP_COUNTABLE =
struct

open BNF_FP_Rec_Sugar_Util
open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_FP_Util
open BNF_FP_Def_Sugar

val countableS = @{sort countable};

fun nchotomy_tac nchotomy =
  HEADGOAL (rtac (nchotomy RS @{thm all_reg[rotated]}) THEN'
    REPEAT_ALL_NEW (resolve_tac [allI, impI] ORELSE' eresolve_tac [exE, disjE]));

fun meta_spec_mp_tac 0 = K all_tac
  | meta_spec_mp_tac depth =
    dtac meta_spec THEN' meta_spec_mp_tac (depth - 1) THEN' dtac meta_mp THEN' atac;

val use_induction_hypothesis_tac =
  DEEPEN (1, 64 (* large number *))
    (fn depth => meta_spec_mp_tac depth THEN' etac allE THEN' etac impE THEN' atac THEN' atac) 0;

val same_ctr_simps = @{thms sum_encode_eq prod_encode_eq sum.inject prod.inject to_nat_split
  id_apply snd_conv simp_thms};
val distinct_ctrs_simps = @{thms sum_encode_eq sum.inject sum.distinct simp_thms};

fun same_ctr_tac ctxt injects recs map_congs' inj_map_strongs' =
  HEADGOAL (asm_full_simp_tac
      (ss_only (injects @ recs @ map_congs' @ same_ctr_simps) ctxt) THEN_MAYBE'
    TRY o REPEAT_ALL_NEW (rtac conjI) THEN_ALL_NEW
    REPEAT_ALL_NEW (eresolve_tac (conjE :: inj_map_strongs')) THEN_ALL_NEW
    (atac ORELSE' use_induction_hypothesis_tac));

fun distinct_ctrs_tac ctxt recs =
  HEADGOAL (asm_full_simp_tac (ss_only (recs @ distinct_ctrs_simps) ctxt));

fun mk_encode_injective_tac ctxt n nchotomy injects recs map_comps' inj_map_strongs' =
  let val ks = 1 upto n in
    EVERY (maps (fn k => nchotomy_tac nchotomy :: map (fn k' =>
      if k = k' then same_ctr_tac ctxt injects recs map_comps' inj_map_strongs'
      else distinct_ctrs_tac ctxt recs) ks) ks)
  end;

fun mk_encode_injectives_tac ctxt ns induct nchotomys injectss recss map_comps' inj_map_strongs' =
  HEADGOAL (rtac induct) THEN
  EVERY (map4 (fn n => fn nchotomy => fn injects => fn recs =>
      mk_encode_injective_tac ctxt n nchotomy injects recs map_comps' inj_map_strongs')
    ns nchotomys injectss recss);

fun endgame_tac ctxt encode_injectives =
  unfold_thms_tac ctxt @{thms inj_on_def ball_UNIV} THEN
  ALLGOALS (rtac exI THEN' rtac allI THEN' resolve_tac encode_injectives);

fun encode_sumN n k t =
  Balanced_Tree.access {init = t,
      left = fn t => @{const sum_encode} $ (@{const Inl (nat, nat)} $ t),
      right = fn t => @{const sum_encode} $ (@{const Inr (nat, nat)} $ t)}
    n k;

fun encode_tuple [] = @{term "0 :: nat"}
  | encode_tuple ts =
    Balanced_Tree.make (fn (t, u) => @{const prod_encode} $ (@{const Pair (nat, nat)} $ u $ t)) ts;

fun mk_encode_funs ctxt fpTs ns ctrss0 recs0 =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun check_countable T =
      Sign.of_sort thy (T, countableS) orelse
      raise TYPE ("Type is not of sort " ^ Syntax.string_of_sort ctxt countableS, [T], []);

    fun mk_to_nat_checked T =
      Const (@{const_name to_nat}, tap check_countable T --> HOLogic.natT);

    val nn = length ns;
    val recs as rec1 :: _ = map2 (mk_co_rec thy Least_FP (replicate nn HOLogic.natT)) fpTs recs0;
    val arg_Ts = binder_fun_types (fastype_of rec1);
    val arg_Tss = Library.unflat ctrss0 arg_Ts;

    fun mk_U (Type (@{type_name prod}, [T1, T2])) =
        if member (op =) fpTs T1 then T2 else HOLogic.mk_prodT (mk_U T1, mk_U T2)
      | mk_U (Type (s, Ts)) = Type (s, map mk_U Ts)
      | mk_U T = T;

    fun mk_nat (j, T) =
      if T = HOLogic.natT then
        SOME (Bound j)
      else if member (op =) fpTs T then
        NONE
      else if exists_subtype_in fpTs T then
        let val U = mk_U T in
          SOME (mk_to_nat_checked U $ (build_map ctxt [] (snd_const o fst) (T, U) $ Bound j))
        end
      else
        SOME (mk_to_nat_checked T $ Bound j);

    fun mk_arg n (k, arg_T) =
      let
        val bound_Ts = rev (binder_types arg_T);
        val nats = map_filter mk_nat (tag_list 0 bound_Ts);
      in
        fold (fn T => fn t => Abs (Name.uu, T, t)) bound_Ts (encode_sumN n k (encode_tuple nats))
      end;

    val argss = map2 (map o mk_arg) ns (map (tag_list 1) arg_Tss);
  in
    map (fn recx => Term.list_comb (recx, flat argss)) recs
  end;

fun derive_encode_injectives_thms _ [] = []
  | derive_encode_injectives_thms ctxt fpT_names0 =
    let
      fun not_datatype s = error (quote s ^ " is not a datatype");
      fun not_mutually_recursive ss = error (commas ss ^ " are not mutually recursive datatypes");

      fun lfp_sugar_of s =
        (case fp_sugar_of ctxt s of
          SOME (fp_sugar as {fp = Least_FP, ...}) => fp_sugar
        | _ => not_datatype s);

      val fpTs0 as Type (_, var_As) :: _ =
        map (#T o lfp_sugar_of o fst o dest_Type) (#Ts (#fp_res (lfp_sugar_of (hd fpT_names0))));
      val fpT_names = map (fst o dest_Type) fpTs0;

      val (As_names, _) = Variable.variant_fixes (map (fn TVar ((s, _), _) => s) var_As) ctxt;
      val As =
        map2 (fn s => fn TVar (_, S) => TFree (s, union (op =) countableS S))
          As_names var_As;
      val fpTs = map (fn s => Type (s, As)) fpT_names;

      val _ = subset (op =) (fpT_names0, fpT_names) orelse not_mutually_recursive fpT_names0;

      fun mk_conjunct fpT x encode_fun =
        HOLogic.all_const fpT $ Abs (Name.uu, fpT,
          HOLogic.mk_imp (HOLogic.mk_eq (encode_fun $ x, encode_fun $ Bound 0),
            HOLogic.eq_const fpT $ x $ Bound 0));

      val fp_sugars as {fp_nesting_bnfs, common_co_inducts = induct :: _, ...} :: _ =
        map (the o fp_sugar_of ctxt o fst o dest_Type) fpTs0;
      val ctr_sugars = map (#ctr_sugar o #fp_ctr_sugar) fp_sugars;

      val ctrss0 = map #ctrs ctr_sugars;
      val ns = map length ctrss0;
      val recs0 = map #co_rec fp_sugars;
      val nchotomys = map #nchotomy ctr_sugars;
      val injectss = map #injects ctr_sugars;
      val rec_thmss = map (#co_rec_thms o #fp_co_induct_sugar) fp_sugars;
      val map_comps' = map (unfold_thms ctxt @{thms comp_def} o map_comp_of_bnf) fp_nesting_bnfs;
      val inj_map_strongs' = map (Thm.permute_prems 0 ~1 o inj_map_strong_of_bnf) fp_nesting_bnfs;

      val (xs, names_ctxt) = ctxt |> mk_Frees "x" fpTs;

      val conjuncts = map3 mk_conjunct fpTs xs (mk_encode_funs ctxt fpTs ns ctrss0 recs0);
      val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj conjuncts);
    in
      Goal.prove (*no sorry*) ctxt [] [] goal (fn {context = ctxt, prems = _} =>
        mk_encode_injectives_tac ctxt ns induct nchotomys injectss rec_thmss map_comps'
          inj_map_strongs')
      |> HOLogic.conj_elims
      |> Proof_Context.export names_ctxt ctxt
      |> map Thm.close_derivation
    end;

fun get_countable_goal_type_name (@{const Trueprop} $ (Const (@{const_name Ex}, _)
    $ Abs (_, Type (_, [Type (s, _), _]), Const (@{const_name inj_on}, _) $ Bound 0
        $ Const (@{const_name top}, _)))) = s
  | get_countable_goal_type_name _ = error "Wrong goal format for datatype countability tactic";

fun core_countable_datatype_tac ctxt st =
  let val T_names = map get_countable_goal_type_name (Thm.prems_of st) in
    endgame_tac ctxt (derive_encode_injectives_thms ctxt T_names) st
  end;

fun countable_datatype_tac ctxt =
  TRY (Class.intro_classes_tac []) THEN core_countable_datatype_tac ctxt;

end;
