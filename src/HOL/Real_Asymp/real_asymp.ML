signature REAL_ASYMP = sig
val tac : bool -> Proof.context -> int -> tactic
end

functor Real_Asymp (Exp : EXPANSION_INTERFACE) : REAL_ASYMP = struct

open Lazy_Eval

val dest_arg = dest_comb #> snd

fun prove_limit_at_top ectxt f filter =
  let
    val ctxt = get_ctxt ectxt
    val basis = Asymptotic_Basis.default_basis
    val prover =
      case filter of
        Const (@{const_name "Topological_Spaces.nhds"}, _) $ _ => SOME Exp.prove_nhds
      | @{term "at (0 :: real)"} => SOME Exp.prove_at_0
      | @{term "at_left (0 :: real)"} => SOME Exp.prove_at_left_0
      | @{term "at_right (0 :: real)"} => SOME Exp.prove_at_right_0
      | @{term "at_infinity :: real filter"} => SOME Exp.prove_at_infinity
      | @{term "at_top :: real filter"} => SOME Exp.prove_at_top
      | @{term "at_bot :: real filter"} => SOME Exp.prove_at_bot
      | _ => NONE
    val lim_thm = Option.map (fn prover => prover ectxt (Exp.expand_term ectxt f basis)) prover
  in
    case lim_thm of
      NONE => no_tac
    | SOME lim_thm =>
        HEADGOAL (
          resolve_tac ctxt [lim_thm, lim_thm RS @{thm filterlim_mono'}]
          THEN_ALL_NEW (TRY o resolve_tac ctxt @{thms at_within_le_nhds at_within_le_at nhds_leI}))
  end

fun prove_eventually_at_top ectxt p =
  case Envir.eta_long [] p of
    Abs (x, @{typ Real.real}, Const (rel, _) $ f $ g) => ((
      let
        val (f, g) = apply2 (fn t => Abs (x, @{typ Real.real}, t)) (f, g)
        val _ = if rel = @{const_name "Orderings.less"} 
                    orelse rel = @{const_name "Orderings.less_eq"} then ()
                  else raise TERM ("prove_eventually_at_top", [p])
        val ctxt = get_ctxt ectxt
        val basis = Asymptotic_Basis.default_basis
        val ([thm1, thm2], basis) = Exp.expand_terms ectxt [f, g] basis
        val thm = Exp.prove_eventually_less ectxt (thm1, thm2, basis)
      in
        HEADGOAL (resolve_tac ctxt [thm, thm RS @{thm eventually_lt_imp_eventually_le}])
      end)
    handle TERM _ => no_tac | THM _ => no_tac)
  | _ => raise TERM ("prove_eventually_at_top", [p])

fun prove_landau ectxt l f g =
  let
    val ctxt = get_ctxt ectxt
    val l' = l |> dest_Const |> fst
    val basis = Asymptotic_Basis.default_basis
    val ([thm1, thm2], basis) = Exp.expand_terms ectxt [f, g] basis
    val prover =
      case l' of
        @{const_name smallo} => Exp.prove_smallo
      | @{const_name bigo} => Exp.prove_bigo
      | @{const_name bigtheta} => Exp.prove_bigtheta
      | @{const_name asymp_equiv} => Exp.prove_asymp_equiv
      | _ => raise TERM ("prove_landau", [f, g])
  in
    HEADGOAL (resolve_tac ctxt [prover ectxt (thm1, thm2, basis)])
  end

val filter_substs = 
  @{thms at_left_to_top at_right_to_top at_left_to_top' at_right_to_top' at_bot_mirror}
val filterlim_substs = map (fn thm => thm RS @{thm filterlim_conv_filtermap}) filter_substs
val eventually_substs = map (fn thm => thm RS @{thm eventually_conv_filtermap}) filter_substs

fun changed_conv conv ct =
  let
    val thm = conv ct
  in
    if Thm.is_reflexive thm then raise CTERM ("changed_conv", [ct]) else thm
  end

val repeat'_conv = Conv.repeat_conv o changed_conv

fun preproc_exp_log_natintfun_conv ctxt =
  let
    fun reify_power_conv x _ ct =
      let
        val thm = Conv.rewr_conv @{thm reify_power} ct
      in
        if exists_subterm (fn t => t aconv x) (Thm.term_of ct |> dest_arg) then
          thm
        else
          raise CTERM ("reify_power_conv", [ct])
      end
    fun conv (x, ctxt) =
      let
        val thms1 =
           Named_Theorems.get ctxt @{named_theorems real_asymp_nat_reify}
        val thms2 =
           Named_Theorems.get ctxt @{named_theorems real_asymp_int_reify}
        val ctxt' = put_simpset HOL_basic_ss ctxt addsimps (thms1 @ thms2)
      in
        repeat'_conv (
          Simplifier.rewrite ctxt'
          then_conv Conv.bottom_conv (Conv.try_conv o reify_power_conv (Thm.term_of x)) ctxt)
      end
  in
    Thm.eta_long_conversion
    then_conv Conv.abs_conv conv ctxt 
    then_conv Thm.eta_conversion
  end

fun preproc_tac ctxt =
  let
    fun natint_tac {context = ctxt, concl = goal, ...} =
      let
        val conv = preproc_exp_log_natintfun_conv ctxt
        val conv =
          case Thm.term_of goal of
            @{term "HOL.Trueprop"} $ t => (case t of
              Const (@{const_name Filter.filterlim}, _) $ _ $ _ $ _ =>
                Conv.fun_conv (Conv.fun_conv (Conv.arg_conv conv))
            | Const (@{const_name Filter.eventually}, _) $ _ $ _ =>
                Conv.fun_conv (Conv.arg_conv conv)
            | Const (@{const_name Set.member}, _) $ _ $ (_ $ _ $ _) =>
                Conv.combination_conv (Conv.arg_conv conv) (Conv.arg_conv conv)
            | Const (@{const_name Landau_Symbols.asymp_equiv}, _) $ _ $ _ $ _ =>
                Conv.combination_conv (Conv.fun_conv (Conv.arg_conv conv)) conv
            | _ => Conv.all_conv)
          | _ => Conv.all_conv
      in
        HEADGOAL (CONVERSION (Conv.try_conv (Conv.arg_conv conv)))
      end
  in
    SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms real_asymp_preproc})
    THEN' TRY o resolve_tac ctxt @{thms real_asymp_real_nat_transfer real_asymp_real_int_transfer}
    THEN' TRY o resolve_tac ctxt 
      @{thms filterlim_at_leftI filterlim_at_rightI filterlim_atI' landau_reduce_to_top}
    THEN' TRY o resolve_tac ctxt @{thms smallo_imp_smallomega bigo_imp_bigomega}
    THEN' TRY o Subgoal.FOCUS_PREMS natint_tac ctxt
    THEN' TRY o resolve_tac ctxt @{thms real_asymp_nat_intros real_asymp_int_intros}
  end

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b

fun prove_eventually ectxt p filter =
  case filter of
    @{term "Filter.at_top :: real filter"} => (prove_eventually_at_top ectxt p
      handle TERM _ => no_tac | THM _ => no_tac)
  | _ => HEADGOAL (CONVERSION (Conv.rewrs_conv eventually_substs) 
         THEN' tac' (#verbose (#ctxt ectxt)) (Inr ectxt))
and prove_limit ectxt f filter filter' =
  case filter' of
    @{term "Filter.at_top :: real filter"} => (prove_limit_at_top ectxt f filter 
      handle TERM _ => no_tac | THM _ => no_tac)
  | _ => HEADGOAL (CONVERSION (Conv.rewrs_conv filterlim_substs) 
         THEN' tac' (#verbose (#ctxt ectxt)) (Inr ectxt))
and tac' verbose ctxt_or_ectxt =
  let
    val ctxt = case ctxt_or_ectxt of Inl ctxt => ctxt | Inr ectxt => get_ctxt ectxt
    fun tac {context = ctxt, prems, concl = goal, ...} =
      (if verbose then print_tac ctxt "real_asymp: Goal after preprocessing" else all_tac) THEN
      let
        val ectxt = 
          case ctxt_or_ectxt of 
            Inl _ => 
              Multiseries_Expansion.mk_eval_ctxt ctxt |> add_facts prems |> set_verbose verbose
          | Inr ectxt => ectxt
      in
        case Thm.term_of goal of
          @{term "HOL.Trueprop"} $ t => ((case t of
            @{term "Filter.filterlim :: (real \<Rightarrow> real) \<Rightarrow> _"} $ f $ filter $ filter' =>
              (prove_limit ectxt f filter filter' handle TERM _ => no_tac | THM _ => no_tac)
          | @{term "Filter.eventually :: (real \<Rightarrow> bool) \<Rightarrow> _"} $ p $ filter =>
              (prove_eventually ectxt p filter handle TERM _ => no_tac | THM _ => no_tac)
          | @{term "Set.member :: (real => real) => _"} $ f $ 
              (l $ @{term "at_top :: real filter"} $ g) =>
                (prove_landau ectxt l f g handle TERM _ => no_tac | THM _ => no_tac)
          | (l as @{term "Landau_Symbols.asymp_equiv :: (real\<Rightarrow>real)\<Rightarrow>_"}) $ f $ _ $ g =>
              (prove_landau ectxt l f g handle TERM _ => no_tac | THM _ => no_tac)
          | _ => no_tac) THEN distinct_subgoals_tac)
        | _ => no_tac
      end
    fun tac' i = Subgoal.FOCUS_PREMS tac ctxt i handle TERM _ => no_tac | THM _ => no_tac
    val at_tac =
      HEADGOAL (resolve_tac ctxt 
        @{thms filterlim_split_at eventually_at_left_at_right_imp_at landau_at_top_imp_at
                 asymp_equiv_at_top_imp_at})
      THEN PARALLEL_ALLGOALS tac'
  in
    (preproc_tac ctxt
     THEN' preproc_tac ctxt
     THEN' (SELECT_GOAL at_tac ORELSE' tac'))
    THEN_ALL_NEW (TRY o SELECT_GOAL (SOLVE (HEADGOAL (Simplifier.asm_full_simp_tac ctxt))))
  end
and tac verbose ctxt = tac' verbose (Inl ctxt)

end

structure Real_Asymp_Basic = Real_Asymp(Multiseries_Expansion_Basic)
