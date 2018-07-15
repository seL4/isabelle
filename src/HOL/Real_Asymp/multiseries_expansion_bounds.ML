signature MULTISERIES_EXPANSION =
sig
include MULTISERIES_EXPANSION;

type lower_bound_thm = thm;
type upper_bound_thm = thm;

datatype limit_result = Exact_Limit of term | Limit_Bounds of term option * term option

type lower_bound = expansion_thm * lower_bound_thm;
type upper_bound = expansion_thm * upper_bound_thm;
datatype bounds = 
  Exact of expansion_thm | Bounds of lower_bound option * upper_bound option

val is_vacuous : bounds -> bool
val lift_bounds : basis -> bounds -> bounds
val get_expanded_fun_bounds : bounds -> term

val find_smaller_expansion :
  Lazy_Eval.eval_ctxt -> thm * thm * Asymptotic_Basis.basis -> thm * thm * thm
val find_greater_expansion :
  Lazy_Eval.eval_ctxt -> thm * thm * Asymptotic_Basis.basis -> thm * thm * thm

val mult_expansion_bounds :
  Lazy_Eval.eval_ctxt -> Asymptotic_Basis.basis -> bounds -> bounds -> bounds
val powr_expansion_bounds :
  Lazy_Eval.eval_ctxt -> Asymptotic_Basis.basis -> bounds -> bounds -> bounds * basis
val powr_nat_expansion_bounds :
  Lazy_Eval.eval_ctxt -> Asymptotic_Basis.basis -> bounds -> bounds -> bounds * basis
val powr_const_expansion_bounds : Lazy_Eval.eval_ctxt -> bounds * term * basis -> bounds
val power_expansion_bounds : Lazy_Eval.eval_ctxt -> bounds * term * basis -> bounds

val sgn_expansion_bounds : Lazy_Eval.eval_ctxt -> bounds * basis -> bounds

val expand_term_bounds : Lazy_Eval.eval_ctxt -> term -> basis -> bounds * basis
val expand_terms_bounds : Lazy_Eval.eval_ctxt -> term list -> basis -> bounds list * basis

val prove_nhds_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_infinity_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_top_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_bot_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_0_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_right_0_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_at_left_0_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm
val prove_eventually_nonzero_bounds : Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> thm

val prove_eventually_less_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm
val prove_eventually_greater_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm

val prove_smallo_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm
val prove_bigo_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm
val prove_bigtheta_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm
val prove_asymp_equiv_bounds :
  Lazy_Eval.eval_ctxt -> bounds * bounds * Asymptotic_Basis.basis -> thm

val limit_of_expansion_bounds :
  Lazy_Eval.eval_ctxt -> bounds * Asymptotic_Basis.basis -> limit_result

end

structure Multiseries_Expansion : MULTISERIES_EXPANSION =
struct

open Multiseries_Expansion;
open Exp_Log_Expression;
open Asymptotic_Basis;

type lower_bound_thm = thm;
type upper_bound_thm = thm;

datatype limit_result = Exact_Limit of term | Limit_Bounds of term option * term option

type lower_bound = expansion_thm * lower_bound_thm;
type upper_bound = expansion_thm * upper_bound_thm;
datatype bounds = 
  Exact of expansion_thm | Bounds of lower_bound option * upper_bound option

fun is_vacuous (Bounds (NONE, NONE)) = true
  | is_vacuous _ = false

fun mk_const_expansion ectxt basis c =
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val thm = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt c)] 
                @{thm expands_to_const}
  in
    thm OF [get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]
  end

fun dest_eventually (Const (@{const_name "Filter.eventually"}, _) $ p $ f) = (p, f)
  | dest_eventually t = raise TERM ("dest_eventually", [t])

fun dest_binop (f $ a $ b) = (f, a, b)
  | dest_binop t = raise TERM ("dest_binop", [t])

fun get_lbound_from_thm thm =
  thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_eventually |> fst
  |> strip_abs |> snd |> dest_binop |> #2

fun get_ubound_from_thm thm =
  thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_eventually |> fst
  |> strip_abs |> snd |> dest_binop |> #3

fun transfer_bounds eq_thm (Exact thm) = 
      Exact (@{thm expands_to_meta_eq_cong'} OF [thm, eq_thm])
  | transfer_bounds eq_thm (Bounds (lb, ub)) =
      Bounds 
        (Option.map (apsnd (fn thm => @{thm transfer_lower_bound} OF [thm, eq_thm])) lb,
         Option.map (apsnd (fn thm => @{thm transfer_upper_bound} OF [thm, eq_thm])) ub)

fun dest_le (@{term "(<=) :: real => _"} $ l $ r) = (l, r)
  | dest_le t = raise TERM ("dest_le", [t])

fun abconv (t, t') = Envir.beta_eta_contract t aconv Envir.beta_eta_contract t'

val realT = @{typ "Real.real"}

fun check_bounds e (Exact thm) = let val _ = check_expansion e thm in Exact thm end
  | check_bounds e (Bounds bnds) =
      let
        fun msg lower = if lower then "check_lower_bound" else "check_upper_bound"
        fun check lower (exp_thm, le_thm) =
          let
            val (expanded_fun, bound_fun) =
              le_thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_eventually |> fst
                |> strip_abs |> snd |> dest_le |> (if lower then swap else I) 
                |> apply2 (fn t => Abs ("x", realT, t))
          in
            if not (abconv (get_expanded_fun exp_thm, bound_fun)) then
              raise TERM (msg lower, map Thm.concl_of [exp_thm, le_thm])
            else if not (abconv (expr_to_term e, expanded_fun)) then
              raise TERM (msg lower, [expr_to_term e, Thm.concl_of le_thm])
            else
              ()
          end
        val _ = (Option.map (check true) (fst bnds), Option.map (check false) (snd bnds))
      in
        Bounds bnds
      end

fun cong_bounds eq_thm (Exact thm) = 
      Exact (@{thm expands_to_cong_reverse} OF [eq_thm, thm])
  | cong_bounds eq_thm (Bounds (lb, ub)) =
      Bounds 
        (Option.map (apsnd (fn thm => @{thm lower_bound_cong} OF [eq_thm, thm])) lb,
         Option.map (apsnd (fn thm => @{thm upper_bound_cong} OF [eq_thm, thm])) ub)

fun mk_trivial_bounds ectxt f thm basis =
  let
    val eq_thm = Thm.reflexive (Thm.cterm_of (Lazy_Eval.get_ctxt ectxt) f)
    val lb_thm = @{thm trivial_boundsI(1)} OF [thm, eq_thm]
    val ub_thm = @{thm trivial_boundsI(2)} OF [thm, eq_thm]
    val lb = get_lbound_from_thm lb_thm
    val ub = get_ubound_from_thm ub_thm
    val (lthm, uthm) = apply2 (mk_const_expansion ectxt basis) (lb, ub)
  in
    Bounds (SOME (lthm, lb_thm), SOME (uthm, ub_thm))
  end

fun get_basis_size basis = length (get_basis_list basis)

fun trim_expansion_while_pos ectxt (thm, basis) =
  let
    val n = get_basis_size basis
    val es = SOME (replicate n @{term "0 :: real"})
  in
    trim_expansion_while_greater false es false NONE ectxt (thm, basis)
  end

fun lift_bounds basis (Exact thm) = Exact (lift basis thm)
  | lift_bounds basis (Bounds bnds) =
      bnds |> apply2 (Option.map (apfst (lift basis))) |> Bounds 

fun mono_bound mono_thm thm = @{thm mono_bound} OF [mono_thm, thm]

fun get_lower_bound (Bounds (lb, _)) = lb
  | get_lower_bound (Exact thm) = SOME (thm, thm RS @{thm exact_to_bound})

fun get_upper_bound (Bounds (_, ub)) = ub
  | get_upper_bound (Exact thm) = SOME (thm, thm RS @{thm exact_to_bound})      

fun get_expanded_fun_bounds_aux f (_, thm) =
  let
    val t = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_comb |> fst |> dest_comb |> snd
  in
    case Envir.eta_long [] t of
      Abs (x, T, @{term "(<=) :: real => _"} $ lhs $ rhs) => Abs (x, T, f (lhs, rhs))
    | _ => raise THM ("get_expanded_fun_bounds", 0, [thm])
  end

fun get_expanded_fun_bounds (Exact thm) = get_expanded_fun thm
  | get_expanded_fun_bounds (Bounds (NONE, NONE)) = raise TERM ("get_expanded_fun_bounds", [])
  | get_expanded_fun_bounds (Bounds (SOME l, _)) =
      get_expanded_fun_bounds_aux snd l
  | get_expanded_fun_bounds (Bounds (_, SOME u)) =
      get_expanded_fun_bounds_aux fst u

fun expand_add_bounds _ [thm, _] (Exact thm1, Exact thm2) basis =
      Exact (thm OF [get_basis_wf_thm basis, thm1, thm2])
  | expand_add_bounds swap [thm1, thm2] bnds basis =
      let
        fun comb (SOME (a, b), SOME (c, d)) =
              SOME (thm1 OF [get_basis_wf_thm basis, a, c], thm2 OF [b, d])
          | comb _ = NONE
        val ((a, b), (c, d)) = (apply2 get_lower_bound bnds, apply2 get_upper_bound bnds)
      in
        if swap then
          Bounds (comb (a, d), comb (c, b))
        else
          Bounds (comb (a, b), comb (c, d))
      end
  | expand_add_bounds _ _ _ _ = raise Match

fun mk_refl_thm ectxt t =
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val ct = Thm.cterm_of ctxt t
  in
    Drule.infer_instantiate' ctxt [SOME ct] @{thm eventually_le_self}
  end
  

fun find_smaller_expansion ectxt (thm1, thm2, basis) =
      case compare_expansions ectxt (thm1, thm2, basis) of
        (LESS, less_thm, thm1, _) =>
          (thm1, mk_refl_thm ectxt (get_expanded_fun thm1), less_thm RS @{thm eventually_less_imp_le})
      | (GREATER, gt_thm, _, thm2) =>
          (thm2, gt_thm RS @{thm eventually_less_imp_le}, mk_refl_thm ectxt (get_expanded_fun thm2))
      | (EQUAL, eq_thm, thm1, _) =>
          (thm1, mk_refl_thm ectxt (get_expanded_fun thm1), eq_thm RS @{thm eventually_eq_imp_le})

fun find_greater_expansion ectxt (thm1, thm2, basis) =
      case compare_expansions ectxt (@{print} (thm1, thm2, basis)) of
        (LESS, less_thm, _, thm2) =>
          (thm2, less_thm RS @{thm eventually_less_imp_le}, mk_refl_thm ectxt (get_expanded_fun thm2))
      | (GREATER, gt_thm, thm1, _) =>
          (thm1, mk_refl_thm ectxt (get_expanded_fun thm1), gt_thm RS @{thm eventually_less_imp_le})
      | (EQUAL, eq_thm, thm1, _) =>
          (thm1, mk_refl_thm ectxt (get_expanded_fun thm1), eq_thm RS @{thm eventually_eq_imp_ge})

fun determine_sign ectxt (thm, basis) =
  case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
    SOME zero_thm => (thm, zero_thm, (true, true))
  | NONE => (
      case trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis) of
        (thm, IsPos, SOME pos_thm) =>
          (thm, @{thm expands_to_imp_eventually_pos} OF [get_basis_wf_thm basis, thm, pos_thm],
            (false, true))
      | (thm, IsNeg, SOME neg_thm) =>
          (thm, @{thm expands_to_imp_eventually_neg} OF [get_basis_wf_thm basis, thm, neg_thm],
            (true, false))
      | _ => raise TERM ("Unexpected zeroness result in determine_sign", []))

val mult_bounds_thms = @{thms mult_bounds_real[eventuallized]}
fun mult_bounds_thm n = List.nth (mult_bounds_thms, n)

val powr_bounds_thms = @{thms powr_bounds_real[eventuallized]}
fun powr_bounds_thm n = List.nth (powr_bounds_thms, n)

fun mk_nonstrict_thm [thm1, thm2] sgn_thm = (
      case Thm.concl_of sgn_thm |> HOLogic.dest_Trueprop of
        Const (@{const_name "Filter.eventually"}, _) $ t $ _ => (
          case Envir.eta_long [] t of
            Abs (_, _, Const (@{const_name "HOL.eq"}, _) $ _ $ _) => sgn_thm RS thm1
          | _ => sgn_thm RS thm2)
      | _ => sgn_thm RS thm2)
  | mk_nonstrict_thm _ _ = raise Match    


val mk_nonneg_thm = mk_nonstrict_thm @{thms eventually_eq_imp_ge eventually_less_imp_le}
val mk_nonpos_thm = mk_nonstrict_thm @{thms eventually_eq_imp_le eventually_less_imp_le}

fun mult_expansion_bounds_right basis
      ((l1_thm, l1_le_thm), (u1_thm, u1_ge_thm)) (thm2, sgn_thm, sgns) =
  let
    val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [l1_le_thm, u1_ge_thm]
    fun mult_expansions (thm1, thm2) =
      @{thm expands_to_mult} OF [get_basis_wf_thm basis, thm1, thm2]
  in
    if snd sgns then
      (mult_expansions (l1_thm, thm2), mult_expansions (u1_thm, thm2),
        @{thm mult_right_bounds(1)[eventuallized]} OF [in_bounds_thm, mk_nonneg_thm sgn_thm])
    else
      (mult_expansions (u1_thm, thm2), mult_expansions (l1_thm, thm2),
        @{thm mult_right_bounds(2)[eventuallized]} OF [in_bounds_thm, mk_nonpos_thm sgn_thm])
  end

fun mult_expansion_bounds_left basis
      (thm1, sgn_thm, sgns) ((l2_thm, l2_le_thm), (u2_thm, u2_ge_thm)) =
  let
    val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [l2_le_thm, u2_ge_thm]
    fun mult_expansions (thm1, thm2) =
      @{thm expands_to_mult} OF [get_basis_wf_thm basis, thm1, thm2]
  in
    if snd sgns then
      (mult_expansions (thm1, l2_thm), mult_expansions (thm1, u2_thm),
        @{thm mult_left_bounds(1)[eventuallized]} OF [in_bounds_thm, mk_nonneg_thm sgn_thm])
    else
      (mult_expansions (thm1, u2_thm), mult_expansions (thm1, l2_thm),
        @{thm mult_left_bounds(2)[eventuallized]} OF [in_bounds_thm, mk_nonpos_thm sgn_thm])
  end

fun mult_expansion_bounds_2 ectxt basis
     ((l1, l1_le_thm, l1sgn_thm, l1_sgn), (u1, u1_ge_thm, u1sgn_thm, u1_sgn))
     ((l2, l2_le_thm, l2sgn_thm, l2_sgn), (u2, u2_ge_thm, u2sgn_thm, u2_sgn)) =
  let
    val sgns = (l1_sgn, u1_sgn, l2_sgn, u2_sgn)
    val in_bounds_thms =
      map (fn thms => @{thm eventually_atLeastAtMostI} OF thms)
        [[l1_le_thm, u1_ge_thm], [l2_le_thm, u2_ge_thm]]
    fun mult_expansions (thm1, thm2) =
      @{thm expands_to_mult} OF [get_basis_wf_thm basis, thm1, thm2]
  in
    case sgns of
      ((_, true), _, (_, true), _) =>
        (mult_expansions (l1, l2), mult_expansions (u1, u2),
          mult_bounds_thm 0 OF ([mk_nonneg_thm l1sgn_thm, mk_nonneg_thm l2sgn_thm] @ in_bounds_thms))
    | (_, (true, _), (_, true), _) =>
        (mult_expansions (l1, u2), mult_expansions (u1, l2),
          mult_bounds_thm 1 OF ([mk_nonpos_thm u1sgn_thm, mk_nonneg_thm l2sgn_thm] @ in_bounds_thms))
    | ((_, true), _, _, (true, _)) =>
        (mult_expansions (u1, l2), mult_expansions (l1, u2),
          mult_bounds_thm 2 OF ([mk_nonneg_thm l1sgn_thm, mk_nonpos_thm u2sgn_thm] @ in_bounds_thms))
    | (_, (true, _), _, (true, _)) =>
        (mult_expansions (u1, u2), mult_expansions (l1, l2),
        mult_bounds_thm 3 OF ([mk_nonpos_thm u1sgn_thm, mk_nonpos_thm u2sgn_thm] @ in_bounds_thms))
    | ((true, _), (_, true), (_, true), _) =>
        (mult_expansions (l1, u2), mult_expansions (u1, u2),
        mult_bounds_thm 4 OF ([mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonneg_thm l2sgn_thm] @ in_bounds_thms))
    | ((true, _), (_, true), _, (true, _)) =>
        (mult_expansions (u1, l2), mult_expansions (l1, l2),
        mult_bounds_thm 5 OF ([mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonpos_thm u2sgn_thm] @ in_bounds_thms))
    | ((_, true), _, (true, _), (_, true)) =>
        (mult_expansions (u1, l2), mult_expansions (u1, u2),
        mult_bounds_thm 6 OF ([mk_nonneg_thm l1sgn_thm, mk_nonpos_thm l2sgn_thm, mk_nonneg_thm u2sgn_thm] @ in_bounds_thms))
    | (_, (true, _), (true, _), (_, true)) =>
        (mult_expansions (l1, u2), mult_expansions (l1, l2),
        mult_bounds_thm 7 OF ([mk_nonpos_thm u1sgn_thm, mk_nonpos_thm l2sgn_thm, mk_nonneg_thm u2sgn_thm] @ in_bounds_thms))
    | ((true, _), (_, true), (true, _), (_, true)) =>
        let
          val l1u2 = mult_expansions (l1, u2)
          val u1l2 = mult_expansions (u1, l2)
          val l1l2 = mult_expansions (l1, l2)
          val u1u2 = mult_expansions (u1, u2)
          val (l, lthm1, lthm2) = find_smaller_expansion ectxt (l1u2, u1l2, basis)
          val (u, uthm1, uthm2) = find_greater_expansion ectxt (l1l2, u1u2, basis)
        in
          (l, u, mult_bounds_thm 8 OF
            ([mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonpos_thm l2sgn_thm, 
                mk_nonneg_thm u2sgn_thm, lthm1, lthm2, uthm1, uthm2] @ in_bounds_thms))
        end
        
    | _ => raise Match
  end

fun convert_bounds (lthm, uthm, in_bounds_thm) =
  Bounds (SOME (lthm, in_bounds_thm RS @{thm eventually_atLeastAtMostD(1)}),
    SOME (uthm, in_bounds_thm RS @{thm eventually_atLeastAtMostD(2)}))

fun convert_bounds' (Exact thm) = (thm, thm, thm RS @{thm expands_to_trivial_bounds})
  | convert_bounds' (Bounds (SOME (lthm, ge_thm), SOME (uthm, le_thm))) =
      (lthm, uthm, @{thm eventually_in_atLeastAtMostI} OF [ge_thm, le_thm])

fun mult_expansion_bounds _ basis (Exact thm1) (Exact thm2) =
      Exact (@{thm expands_to_mult} OF [get_basis_wf_thm basis, thm1, thm2])
  | mult_expansion_bounds ectxt basis (Bounds (SOME l1, SOME u1)) (Exact thm2) =
      mult_expansion_bounds_right basis (l1, u1) (determine_sign ectxt (thm2, basis))
      |> convert_bounds
  | mult_expansion_bounds ectxt basis (Exact thm1) (Bounds (SOME l2, SOME u2)) =
      mult_expansion_bounds_left basis (determine_sign ectxt (thm1, basis)) (l2, u2)
      |> convert_bounds
  | mult_expansion_bounds ectxt basis (Bounds (SOME l1, SOME u1)) (Bounds (SOME l2, SOME u2)) =
      let
        fun prep (thm, le_thm) =
          case determine_sign ectxt (thm, basis) of
            (thm, sgn_thm, sgns) => (thm, le_thm, sgn_thm, sgns)
      in
        mult_expansion_bounds_2 ectxt basis (prep l1, prep u1) (prep l2, prep u2)
        |> convert_bounds
      end
  | mult_expansion_bounds _ _ _ _ = Bounds (NONE, NONE)

fun inverse_expansion ectxt basis thm = 
      case trim_expansion true (SOME Simple_Trim) ectxt (thm, basis) of
        (thm, _, SOME trimmed_thm) =>
          @{thm expands_to_inverse} OF [trimmed_thm, get_basis_wf_thm basis, thm]
      | _ => raise TERM ("zero denominator", [get_expanded_fun thm])

fun divide_expansion ectxt basis thm1 thm2 =
      case trim_expansion true (SOME Simple_Trim) ectxt (thm2, basis) of
        (thm2, _, SOME trimmed_thm) =>
          @{thm expands_to_divide} OF [trimmed_thm, get_basis_wf_thm basis, thm1, thm2]

fun forget_trimmedness_sign trimmed_thm =
  case Thm.concl_of trimmed_thm |> HOLogic.dest_Trueprop of
    Const (@{const_name Multiseries_Expansion.trimmed}, _) $ _ => trimmed_thm
  | Const (@{const_name Multiseries_Expansion.trimmed_pos}, _) $ _ =>
      trimmed_thm RS @{thm trimmed_pos_imp_trimmed}
  | Const (@{const_name Multiseries_Expansion.trimmed_neg}, _) $ _ =>
      trimmed_thm RS @{thm trimmed_neg_imp_trimmed}
  | _ => raise THM ("forget_trimmedness_sign", 0, [trimmed_thm])

fun inverse_expansion_bounds ectxt basis (Exact thm) =
      Exact (inverse_expansion ectxt basis thm)
  | inverse_expansion_bounds ectxt basis (Bounds (SOME (lthm, le_thm), SOME (uthm, ge_thm))) =
      let
        fun trim thm = trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis)
        fun inverse thm trimmed_thm = @{thm expands_to_inverse} OF
          [forget_trimmedness_sign trimmed_thm, get_basis_wf_thm basis, thm]
      in
        case (trim lthm, trim uthm) of
          ((lthm, IsPos, SOME trimmed_thm1), (uthm, _, SOME trimmed_thm2)) =>
            (inverse uthm trimmed_thm2, inverse lthm trimmed_thm1,
               @{thm inverse_bounds_real(1)[eventuallized, OF expands_to_imp_eventually_pos]} OF
                 [get_basis_wf_thm basis, lthm, trimmed_thm1, le_thm, ge_thm]) |> convert_bounds
        | ((lthm, _, SOME trimmed_thm1), (uthm, IsNeg, SOME trimmed_thm2)) =>
            (inverse uthm trimmed_thm2, inverse lthm trimmed_thm1,
               @{thm inverse_bounds_real(2)[eventuallized, OF expands_to_imp_eventually_neg]} OF
                 [get_basis_wf_thm basis, uthm, trimmed_thm2, le_thm, ge_thm]) |> convert_bounds
        | _ => raise TERM ("zero denominator", map get_expanded_fun [lthm, uthm])
      end
  | inverse_expansion_bounds _ _ _ = Bounds (NONE, NONE)

fun trimmed_thm_to_inverse_sgn_thm basis thm trimmed_thm =
  case trimmed_thm |> Thm.concl_of |> HOLogic.dest_Trueprop of
    Const (@{const_name "Multiseries_Expansion.trimmed_pos"}, _) $ _ =>
      @{thm pos_imp_inverse_pos[eventuallized, OF expands_to_imp_eventually_pos]} OF
        [get_basis_wf_thm basis, thm, trimmed_thm]
  | Const (@{const_name "Multiseries_Expansion.trimmed_neg"}, _) $ _ =>
      @{thm neg_imp_inverse_neg[eventuallized, OF expands_to_imp_eventually_neg]} OF
        [get_basis_wf_thm basis, thm, trimmed_thm]
  | _ => raise THM ("trimmed_thm_to_inverse_sgn_thm", 0, [trimmed_thm])

fun transfer_divide_bounds (lthm, uthm, in_bounds_thm) =
  let
    val f = Conv.fconv_rule (Conv.try_conv (Conv.rewr_conv @{thm transfer_divide_bounds(4)}))
    val conv = Conv.repeat_conv (Conv.rewrs_conv @{thms transfer_divide_bounds(1-3)})
  in
    (f lthm, f uthm, Conv.fconv_rule conv in_bounds_thm)
  end

fun divide_expansion_bounds ectxt basis (Exact thm1) (Exact thm2) =
      Exact (divide_expansion ectxt basis thm1 thm2)
  | divide_expansion_bounds ectxt basis (Bounds (SOME l1, SOME u1)) (Exact thm2) =
      let
        val (thm2, sgn, SOME trimmed_thm) = trim_expansion true (SOME Sgn_Trim) ectxt (thm2, basis)
        val thm2' = @{thm expands_to_inverse} OF 
          [forget_trimmedness_sign trimmed_thm, get_basis_wf_thm basis, thm2]
        val sgn_thm = trimmed_thm_to_inverse_sgn_thm basis thm2 trimmed_thm
      in
        mult_expansion_bounds_right basis (l1, u1) (thm2', sgn_thm, (sgn = IsNeg, sgn = IsPos))
        |> transfer_divide_bounds
        |> convert_bounds
      end
  | divide_expansion_bounds ectxt basis bnds1 (Bounds (SOME (lthm, ge_thm), SOME (uthm, le_thm))) =
      let
        fun trim thm =
          case trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis) of
            (thm, sgn, SOME trimmed_thm) => (thm, sgn, trimmed_thm)
          | _ => raise TERM ("zero divisor", [get_expanded_fun thm])
        fun inverse thm trimmed_thm = @{thm expands_to_inverse} OF
          [forget_trimmedness_sign trimmed_thm, get_basis_wf_thm basis, thm]

        val (lthm, sgnl, ltrimmed_thm) = trim lthm
        val (uthm, sgnu, utrimmed_thm) = trim uthm
        val (uthm', lthm') = (inverse lthm ltrimmed_thm, inverse uthm utrimmed_thm)
        val in_bounds_thm' =
          if sgnl = IsPos then
            @{thm inverse_bounds_real(1)[eventuallized, OF expands_to_imp_eventually_pos]} OF
                 [get_basis_wf_thm basis, lthm, ltrimmed_thm, ge_thm, le_thm]
          else if sgnu = IsNeg then
            @{thm inverse_bounds_real(2)[eventuallized, OF expands_to_imp_eventually_neg]} OF
                 [get_basis_wf_thm basis, uthm, utrimmed_thm, ge_thm, le_thm]
          else
            raise TERM ("zero divisor", map get_expanded_fun [lthm, uthm])
        val [ge_thm', le_thm'] =
          map (fn thm => in_bounds_thm' RS thm) @{thms eventually_atLeastAtMostD}
        val bnds2' = ((lthm', ge_thm'), (uthm', le_thm'))
        val usgn_thm' = trimmed_thm_to_inverse_sgn_thm basis lthm ltrimmed_thm
        val lsgn_thm' = trimmed_thm_to_inverse_sgn_thm basis uthm utrimmed_thm
      in
        case bnds1 of
          Exact thm1 =>
            (mult_expansion_bounds_left basis (determine_sign ectxt (thm1, basis)) bnds2')
            |> transfer_divide_bounds
            |> convert_bounds
        | Bounds (SOME l1, SOME u1) =>
            let
              fun prep (thm, le_thm) =
                case determine_sign ectxt (thm, basis) of
                  (thm, sgn_thm, sgns) => (thm, le_thm, sgn_thm, sgns)
            in
              mult_expansion_bounds_2 ectxt basis (prep l1, prep u1)
                ((lthm', ge_thm', lsgn_thm', (sgnl = IsNeg, sgnl = IsPos)),
                 (uthm', le_thm', usgn_thm', (sgnu = IsNeg, sgnu = IsPos)))
              |> transfer_divide_bounds
              |> convert_bounds
            end
        | _ => Bounds (NONE, NONE)
      end
  | divide_expansion_bounds _ _ _ _ = Bounds (NONE, NONE)

fun abs_expansion ectxt basis thm =
      let
        val (thm, nz, SOME trimmed_thm) = trim_expansion true (SOME Sgn_Trim) ectxt (thm, basis)
        val thm' =
          case nz of 
            IsPos => @{thm expands_to_abs_pos} 
          | IsNeg => @{thm expands_to_abs_neg}
          | _ => raise TERM ("Unexpected trim result during expansion of abs", [])
      in
        thm' OF [trimmed_thm, get_basis_wf_thm basis, thm]
      end

fun abs_trivial_bounds ectxt f =
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
  in
    Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm eventually_abs_ge_0}
  end

fun abs_expansion_bounds ectxt basis (Exact thm) = Exact (abs_expansion ectxt basis thm)
  | abs_expansion_bounds ectxt basis (bnds as Bounds (SOME (lthm, ge_thm), NONE)) =
      let
        val (lthm, lsgn_thm, lsgns) = determine_sign ectxt (lthm, basis)
        val lbnd =
          if snd lsgns then
            (lthm, @{thm eventually_le_abs_nonneg} OF [mk_nonneg_thm lsgn_thm, ge_thm])
          else
            (zero_expansion basis, abs_trivial_bounds ectxt (get_expanded_fun_bounds bnds))
      in
        Bounds (SOME lbnd, NONE)
      end
  | abs_expansion_bounds ectxt basis (bnds as Bounds (NONE, SOME (uthm, le_thm))) =
      let
        val (uthm, usgn_thm, usgns) = determine_sign ectxt (uthm, basis)
        val lbnd =
          if fst usgns then
            (@{thm expands_to_uminus} OF [get_basis_wf_thm basis, uthm],
               @{thm eventually_le_abs_nonpos} OF [mk_nonpos_thm usgn_thm, le_thm])
          else
            (zero_expansion basis, abs_trivial_bounds ectxt (get_expanded_fun_bounds bnds))
      in
        Bounds (SOME lbnd, NONE)
      end
  | abs_expansion_bounds ectxt basis (Bounds (SOME (lthm, ge_thm), SOME (uthm, le_thm))) =
      let
        val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [ge_thm, le_thm]
        val (lthm, lsgn_thm, lsgns) = determine_sign ectxt (lthm, basis)
        val (uthm, usgn_thm, usgns) = determine_sign ectxt (uthm, basis)
        fun minus thm = @{thm expands_to_uminus} OF [get_basis_wf_thm basis, thm]
      in (
        case (lsgns, usgns) of
          ((_, true), _) =>
            (lthm, uthm,
               @{thm nonneg_abs_bounds[eventuallized]} OF [mk_nonneg_thm lsgn_thm, in_bounds_thm])
        | (_, (true, _)) =>
            (minus uthm, minus lthm,
               @{thm nonpos_abs_bounds[eventuallized]} OF [mk_nonpos_thm usgn_thm, in_bounds_thm])
        | ((true, _), (_, true)) => (
            case find_greater_expansion ectxt (minus lthm, uthm, basis) of
              (u'_thm, le_thm1, le_thm2) =>
                (mk_const_expansion ectxt basis @{term "0::real"}, u'_thm,
                  @{thm indet_abs_bounds[eventuallized]} OF 
                    [mk_nonpos_thm lsgn_thm, mk_nonneg_thm usgn_thm, 
                       in_bounds_thm, le_thm1, le_thm2]))
        | _ => raise TERM ("Unexpected zeroness result in abs_expansion_bounds", []))
        |> convert_bounds
      end
  | abs_expansion_bounds _ _ _ = Bounds (NONE, NONE) (* TODO *)

fun abs_expansion_lower_bound ectxt basis (Exact thm) =
      let
        val thm' = abs_expansion ectxt basis thm
      in
        (thm', thm RS @{thm expands_to_abs_nonneg}, thm' RS @{thm exact_to_bound})
      end
  | abs_expansion_lower_bound ectxt basis (Bounds (SOME (lthm, ge_thm), SOME (uthm, le_thm))) =
      let
        val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [ge_thm, le_thm]
        val (lthm, lsgn_thm, lsgns) = determine_sign ectxt (lthm, basis)
        val (uthm, usgn_thm, usgns) = determine_sign ectxt (uthm, basis)
        fun minus thm = @{thm expands_to_uminus} OF [get_basis_wf_thm basis, thm]
        val [absthm1, absthm2] =
          @{thms eventually_atLeastAtMostD(1)[OF nonneg_abs_bounds[eventuallized]]
                 eventually_atLeastAtMostD(1)[OF nonpos_abs_bounds[eventuallized]]}
      in (
        case (lsgns, usgns) of
          ((_, true), _) =>
            (lthm, mk_nonneg_thm lsgn_thm,
               absthm1 OF [mk_nonneg_thm lsgn_thm, in_bounds_thm])
        | (_, (true, _)) =>
            (minus uthm, mk_nonpos_thm usgn_thm RS @{thm eventually_nonpos_flip},
               absthm2 OF [mk_nonpos_thm usgn_thm, in_bounds_thm])
        | ((true, _), (_, true)) => raise TERM ("abs_expansion_lower_bound", [])
        | _ => raise TERM ("Unexpected zeroness result in abs_expansion_bounds", []))
      end
  | abs_expansion_lower_bound _ _ _ = raise TERM ("abs_expansion_lower_bound", [])

fun powr_expansion_bounds_right ectxt basis
      ((l1_thm, l1_le_thm), (u1_thm, u1_ge_thm)) (thm2, sgn_thm, g_sgns) =
  let
    val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [l1_le_thm, u1_ge_thm]
    val (l1_thm, l1_sgn_thm, l1_sgns) = determine_sign ectxt (l1_thm, basis)
    val l1_sgn_thm = if snd g_sgns then mk_nonneg_thm l1_sgn_thm else l1_sgn_thm
    val (l_thm, basis') = powr_expansion ectxt (l1_thm, thm2, basis)
    val (u_thm, basis'') = powr_expansion ectxt (lift basis' u1_thm, lift basis' thm2, basis')
    val l_thm = lift basis'' l_thm
  in
    if (snd g_sgns andalso not (snd l1_sgns)) orelse (not (snd g_sgns) andalso fst l1_sgns) then
      raise TERM ("Non-positive base in powr.", [])
    else if snd g_sgns then
      ((l_thm, u_thm, @{thm powr_right_bounds(1)[eventuallized]}
          OF [l1_sgn_thm, in_bounds_thm, mk_nonneg_thm sgn_thm]), basis'')
    else
      ((u_thm, l_thm, @{thm powr_right_bounds(2)[eventuallized]}
          OF [l1_sgn_thm, in_bounds_thm, mk_nonpos_thm sgn_thm]), basis'')
  end

fun compare_expansion_to_1 ectxt (thm, basis) =
  prove_asymptotic_relation ectxt (thm, const_expansion ectxt basis @{term "1 :: real"}, basis)

fun powr_expansion_bounds_left ectxt basis
      thm1 ((l2_thm, l2_le_thm), (u2_thm, u2_ge_thm)) =
  let
    val in_bounds_thm = @{thm eventually_atLeastAtMostI} OF [l2_le_thm, u2_ge_thm]
    val (thm1, _, SOME trimmed_pos_thm) = trim_expansion true (SOME Pos_Trim) ectxt (thm1, basis)
    val pos_thm = @{thm expands_to_imp_eventually_pos} OF
      [get_basis_wf_thm basis, thm1, trimmed_pos_thm]
    val (l_thm, basis') = powr_expansion ectxt (thm1, l2_thm, basis)
    val (u_thm, basis'') = powr_expansion ectxt (lift basis' thm1, lift basis' u2_thm, basis')
    val l_thm = lift basis'' l_thm
    val (cmp_1, cmp_1_thm) = compare_expansion_to_1 ectxt (thm1, basis)
  in
    case cmp_1 of
      LESS =>
        ((u_thm, l_thm, @{thm powr_left_bounds(2)[eventuallized]} OF
          [pos_thm, in_bounds_thm, mk_nonpos_thm cmp_1_thm]), basis'')
    | _ =>
        ((l_thm, u_thm, @{thm powr_left_bounds(1)[eventuallized]} OF
          [pos_thm, in_bounds_thm, mk_nonneg_thm cmp_1_thm]), basis'')
  end

fun powr_expansion_bounds_2 ectxt basis
     ((l1, l1_le_thm, l1pos_thm, l1_sgn), (u1, u1_ge_thm, _, _))
     ((l2, l2_le_thm, l2sgn_thm, l2_sgn), (u2, u2_ge_thm, u2sgn_thm, u2_sgn)) =
  let
    fun do_force_pos () =
      if fst l1_sgn then raise TERM ("Non-positive base in power", []) else ()

    fun compare_expansion_to_1' thm =
      let
        val (cmp, sgn_thm) = compare_expansion_to_1 ectxt (thm, basis)
        val sgn = (cmp <> GREATER, cmp <> LESS)
      in
        (sgn, sgn_thm)
      end
    val (l1_sgn, l1sgn_thm) = compare_expansion_to_1' l1
    val (u1_sgn, u1sgn_thm) = compare_expansion_to_1' u1

    val sgns = (l1_sgn, u1_sgn, l2_sgn, u2_sgn)
    val in_bounds_thms =
      map (fn thms => @{thm eventually_atLeastAtMostI} OF thms)
        [[l1_le_thm, u1_ge_thm], [l2_le_thm, u2_ge_thm]]
    fun f n force_pos (a, b) (c, d) thms =
      let
        val _ = if force_pos then do_force_pos () else ()
        val l1pos_thm = if force_pos then l1pos_thm else mk_nonneg_thm l1pos_thm
        val (thm1, basis1) = powr_expansion ectxt (a, b, basis)
        val (thm2, basis2) = powr_expansion ectxt (lift basis1 c, lift basis1 d, basis1)
        val thm1 = lift basis2 thm1
      in
        ((thm1, thm2, powr_bounds_thm n OF (l1pos_thm :: thms @ in_bounds_thms)), basis2)
      end
  in
    case sgns of
      ((_, true), _, (_, true), _) =>
         f 0 false (l1, l2) (u1, u2) [mk_nonneg_thm l1sgn_thm, mk_nonneg_thm l2sgn_thm]
    | (_, (true, _), (_, true), _) =>
        f 1 false (l1, u2) (u1, l2) [mk_nonpos_thm u1sgn_thm, mk_nonneg_thm l2sgn_thm]
    | ((_, true), _, _, (true, _)) =>
        f 2 false (u1, l2) (l1, u2) [mk_nonneg_thm l1sgn_thm, mk_nonpos_thm u2sgn_thm]
    | (_, (true, _), _, (true, _)) =>
        f 3 true (u1, u2) (l1, l2) [mk_nonpos_thm u1sgn_thm, mk_nonpos_thm u2sgn_thm]
    | ((true, _), (_, true), (_, true), _) =>
        f 4 false (l1, u2) (u1, u2) 
          [mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonneg_thm l2sgn_thm]
    | ((true, _), (_, true), _, (true, _)) =>
        f 5 true (u1, l2) (l1, l2)
          [mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonpos_thm u2sgn_thm]
    | ((_, true), _, (true, _), (_, true)) =>
        f 6 false (u1, l2) (u1, u2)
          [mk_nonneg_thm l1sgn_thm, mk_nonpos_thm l2sgn_thm, mk_nonneg_thm u2sgn_thm]
    | (_, (true, _), (true, _), (_, true)) =>
        f 7 true (l1, u2) (l1, l2)
          [mk_nonpos_thm u1sgn_thm, mk_nonpos_thm l2sgn_thm, mk_nonneg_thm u2sgn_thm]
    | ((true, _), (_, true), (true, _), (_, true)) =>
        let
          val _ = do_force_pos ()
          val (l1u2, basis1) = powr_expansion ectxt (l1, u2, basis)
          val (u1l2, basis2) = powr_expansion ectxt (lift basis1 u1, lift basis1 l2, basis1)
          val (l1l2, basis3) = powr_expansion ectxt (lift basis2 l1, lift basis2 l2, basis2)
          val (u1u2, basis4) = powr_expansion ectxt (lift basis3 u1, lift basis3 u2, basis3)
          val [l1u2, u1l2, l1l2] = map (lift basis4) [l1u2, u1l2, l1l2]
          (* TODO The bases might blow up unnecessarily a bit here *)
          val (l, lthm1, lthm2) = find_smaller_expansion ectxt (l1u2, u1l2, basis4)
          val (u, uthm1, uthm2) = find_greater_expansion ectxt (l1l2, u1u2, basis4)
        in
          ((l, u, powr_bounds_thm 8 OF
            ([l1pos_thm, mk_nonpos_thm l1sgn_thm, mk_nonneg_thm u1sgn_thm, mk_nonpos_thm l2sgn_thm, 
                mk_nonneg_thm u2sgn_thm, lthm1, lthm2, uthm1, uthm2] @ in_bounds_thms)), basis4)
        end
        
    | _ => raise Match
  end

fun powr_expansion_bounds_aux ectxt basis (Exact thm1) (Exact thm2) =
      powr_expansion ectxt (thm1, thm2, basis) |> apfst Exact
  | powr_expansion_bounds_aux ectxt basis (Bounds (SOME l1, SOME u1)) (Exact thm2) =
      powr_expansion_bounds_right ectxt basis (l1, u1) (determine_sign ectxt (thm2, basis))
      |> apfst convert_bounds
  | powr_expansion_bounds_aux ectxt basis (Exact thm1) (Bounds (SOME l2, SOME u2)) =
      powr_expansion_bounds_left ectxt basis thm1 (l2, u2)
      |> apfst convert_bounds
  | powr_expansion_bounds_aux ectxt basis (Bounds (SOME l1, SOME u1)) (Bounds (SOME l2, SOME u2)) =
      let
        fun prep (thm, le_thm) =
          case determine_sign ectxt (thm, basis) of
            (thm, sgn_thm, sgns) => (thm, le_thm, sgn_thm, sgns)
      in
        powr_expansion_bounds_2 ectxt basis (prep l1, prep u1) (prep l2, prep u2)
        |> apfst convert_bounds
      end
  | powr_expansion_bounds_aux _ basis _ _ = (Bounds (NONE, NONE), basis)

fun powr_expansion_bounds ectxt basis bnds1 bnds2 =
  case ev_zeroness_oracle ectxt (get_expanded_fun_bounds bnds1) of
    SOME zero_thm => 
      let
        val t = Thm.cterm_of (Lazy_Eval.get_ctxt ectxt) (get_expanded_fun_bounds bnds2)
        val thm = @{thm expands_to_powr_0} OF
          [zero_thm, Thm.reflexive t, get_basis_wf_thm basis, mk_expansion_level_eq_thm basis]
      in
        (Exact thm, basis)
      end
  | NONE => powr_expansion_bounds_aux ectxt basis bnds1 bnds2

val powr_nat_bounds_transfer_le = @{thms powr_nat_bounds_transfer_le[eventuallized]}
fun powr_nat_bounds_transfer_le' n = List.nth (powr_nat_bounds_transfer_le, n - 1)

fun powr_nat_expansion_bounds ectxt basis bnds1 bnds2 =
  let
    fun aux (Exact thm1) (Exact thm2) =
          apfst Exact (powr_nat_expansion ectxt (thm1, thm2, basis))
      | aux bnds1 bnds2 =
          case get_lower_bound bnds1 of
            NONE => (Bounds (NONE, NONE), basis)
          | SOME (lthm1, ge_thm1) =>
              let
                val (lthm1, l1_sgn_thm, sgns1) = determine_sign ectxt (lthm1, basis)
                val bnds1 =
                  case bnds1 of
                    Exact _ => Exact lthm1
                  | Bounds (SOME (_, ge_thm), upper) => Bounds (SOME (lthm1, ge_thm), upper)
                  | _ => raise Match
                val _ = if not (snd sgns1) then
                  raise TERM ("Unexpected sign in powr_nat_expansion_bounds", []) else ()
                val (bnds, basis') = powr_expansion_bounds ectxt basis bnds1 bnds2
                val lower = Option.map (apsnd (fn ge_thm' =>
                  @{thm powr_nat_bounds_transfer_ge[eventuallized]} OF
                    [mk_nonneg_thm l1_sgn_thm, ge_thm1, ge_thm'])) (get_lower_bound bnds)
                fun determine_sign' NONE = NONE
                  | determine_sign' (SOME (thm, le_thm)) =
                      case determine_sign ectxt (thm, basis) of
                        (thm, sgn_thm, sgns) => SOME (thm, sgn_thm, sgns, le_thm)
                fun do_transfer n thms = powr_nat_bounds_transfer_le' n OF thms
                fun transfer_upper (uthm', le_thm') =
                  if not (fst sgns1) then
                    (uthm', do_transfer 1 [l1_sgn_thm, ge_thm1, le_thm'])
                  else
                    case determine_sign' (get_lower_bound bnds2) of
                      SOME (_, l2_sgn_thm, (false, true), ge_thm2) =>
                        (uthm', do_transfer 2 
                           [mk_nonneg_thm l1_sgn_thm, l2_sgn_thm, ge_thm1, ge_thm2, le_thm'])
                    | _ => (
                        case determine_sign' (get_upper_bound bnds2) of
                          SOME (_, u2_sgn_thm, (true, false), le_thm2) =>
                            (uthm', do_transfer 3
                               [mk_nonneg_thm l1_sgn_thm, u2_sgn_thm, ge_thm1, le_thm2, le_thm'])
                        | _ =>
                            let
                              val (uthm'', le_u'_thm1, le_u'_thm2) = find_greater_expansion ectxt 
                                (uthm', const_expansion ectxt basis @{term "1::real"}, basis)
                            in
                              (uthm'', do_transfer 4
                               [mk_nonneg_thm l1_sgn_thm, ge_thm1, le_thm', le_u'_thm1, le_u'_thm2])
                            end)
              in
                (Bounds (lower, Option.map transfer_upper (get_upper_bound bnds)), basis')
              end
  in
    case get_lower_bound bnds1 of
      SOME (lthm, _) =>
        let
          val (lthm, _, sgns) = determine_sign ectxt (lthm, basis)
          val bnds1 =
            case bnds1 of
              Exact _ => Exact lthm
            | Bounds (SOME (_, le_thm), upper) => Bounds (SOME (lthm, le_thm), upper)
            | _ => raise Match
        in
          case sgns of
            (_, true) => aux bnds1 bnds2
          | _ =>
              let
                val abs_bnds = abs_expansion_bounds ectxt basis bnds1
                fun transfer (NONE, _) = (Bounds (NONE, NONE), basis)
                  | transfer (SOME (uthm, le_thm), basis) =
                      let
                        val neg_uthm = @{thm expands_to_uminus} OF [get_basis_wf_thm basis, uthm]
                        val [ge_thm, le_thm] =
                          map (fn thm => le_thm RS thm) @{thms powr_nat_bounds_transfer_abs}
                      in
                        (Bounds (SOME (neg_uthm, ge_thm), SOME (uthm, le_thm)), basis)
                      end
              in
                aux abs_bnds bnds2
                |> apfst get_upper_bound (* TODO better bounds possible *)
                |> transfer
              end
        end
    | _ => (Bounds (NONE, NONE), basis)
  end

fun ln_expansion_bounds' ectxt (lthm, ltrimmed_thm, lb_thm) ub basis =
      let
        val (lthm', basis') = ln_expansion ectxt ltrimmed_thm lthm basis
        val wf_thm = get_basis_wf_thm basis
        val lb_thm' = @{thm expands_to_lb_ln} OF [lthm, ltrimmed_thm, wf_thm, lb_thm]
      in
        case ub of
          NONE => (Bounds (SOME (lthm', lb_thm'), NONE), basis')
        | SOME (uthm, utrimmed_thm, ub_thm) =>
            let
              val lifting = mk_lifting (extract_basis_list uthm) basis'
              val uthm = lift_expands_to_thm lifting uthm
              val utrimmed_thm = lift_trimmed_pos_thm lifting utrimmed_thm
              val (uthm, _, utrimmed_thm) = retrim_pos_expansion ectxt (uthm, basis', utrimmed_thm)
              val (uthm', basis'') = ln_expansion ectxt utrimmed_thm uthm basis'
              val lthm' = lift basis'' lthm'
              val ub_thm' = @{thm expands_to_ub_ln} OF [lthm, ltrimmed_thm, wf_thm, lb_thm, ub_thm]
            in
              (Bounds (SOME (lthm', lb_thm'), SOME (uthm', ub_thm')), basis'')
            end
      end

fun floor_expansion_bounds ectxt (bnds, basis) =
      let
        val wf_thm = get_basis_wf_thm basis
        fun mk_lb (exp_thm, le_thm) =
          let
            val exp_thm' = @{thm expands_to_minus} OF
              [wf_thm, exp_thm, const_expansion ectxt basis @{term "1::real"}]
            val le_thm = @{thm rfloor_bound(1)} OF [le_thm]
          in
            (exp_thm', le_thm)
          end
        val mk_ub = apsnd (fn thm => @{thm rfloor_bound(2)} OF [thm])
        val bnds' =
          Bounds (Option.map mk_lb (get_lower_bound bnds), Option.map mk_ub (get_upper_bound bnds))
      in
        (bnds', basis)
      end

fun ceiling_expansion_bounds ectxt (bnds, basis) =
      let
        val wf_thm = get_basis_wf_thm basis
        fun mk_ub (exp_thm, le_thm) =
          let
            val exp_thm' = @{thm expands_to_add} OF
              [wf_thm, exp_thm, const_expansion ectxt basis @{term "1::real"}]
            val le_thm = @{thm rceil_bound(2)} OF [le_thm]
          in
            (exp_thm', le_thm)
          end
        val mk_lb = apsnd (fn thm => @{thm rceil_bound(1)} OF [thm])
        val bnds' =
          Bounds (Option.map mk_lb (get_lower_bound bnds), Option.map mk_ub (get_upper_bound bnds))
      in
        (bnds', basis)
      end

fun natmod_expansion_bounds _ (Bounds (NONE, NONE), _, _) = Bounds (NONE, NONE)
  | natmod_expansion_bounds _ (_, Bounds (NONE, NONE), _) = Bounds (NONE, NONE)
  | natmod_expansion_bounds ectxt (bnds1, bnds2, basis) =
  let
    val (f, g) = apply2 (Thm.reflexive o Thm.cterm_of (Lazy_Eval.get_ctxt ectxt) o
      get_expanded_fun_bounds) (bnds1, bnds2)
    val ge_lower_thm = @{thm natmod_trivial_lower_bound} OF [f, g]
    fun minus1 thm = @{thm expands_to_minus} OF
          [get_basis_wf_thm basis, thm, const_expansion ectxt basis @{term "1::real"}]
    fun find_upper uthm1 le1_thm u_nonneg_thm =
      let
        val upper1 = (uthm1, @{thm natmod_upper_bound'} OF [g, u_nonneg_thm, le1_thm])
        val upper2 =
          case (get_lower_bound bnds2, get_upper_bound bnds2) of
            (SOME (lthm2, ge2_thm), SOME (uthm2, le2_thm)) => (
              case determine_sign ectxt (minus1 lthm2, basis) of
                (_, sgn_thm, (_, true)) => SOME (minus1 uthm2,
                  @{thm natmod_upper_bound} OF [f, ge2_thm, le2_thm, mk_nonneg_thm sgn_thm])
              | _ => NONE)
          | _ => NONE
      in
        case upper2 of
          NONE => upper1
        | SOME upper2 =>
            case compare_expansions ectxt (fst upper1, fst upper2, basis) of
              (GREATER, _, _, _) => upper2
            | _ => upper1
      end
  in
    case get_upper_bound bnds1 of
      NONE => Bounds (SOME (zero_expansion basis, ge_lower_thm) , NONE)
    | SOME (uthm1, le1_thm) =>
        case determine_sign ectxt (uthm1, basis) of
          (_, sgn_thm, (true, _)) => Exact (@{thm expands_to_natmod_nonpos} OF
            [g, mk_nonpos_thm sgn_thm, le1_thm, zero_expansion basis])
        | (uthm1, sgn_thm, (_, true)) =>
            Bounds (SOME (zero_expansion basis, ge_lower_thm),
              SOME (find_upper uthm1 le1_thm (mk_nonneg_thm sgn_thm)))
        | _ => raise TERM ("Unexpected result in natmod_expansion_bounds", [])
  end

fun sin_cos_expansion thm _ [] =
      (thm RS @{thm expands_to_sin_real}, thm RS @{thm expands_to_cos_real})
  | sin_cos_expansion thm basis ((IsNeg, neg_thm) :: _) =
      let
        val neg_thm = @{thm compare_reals_diff_sgnD(1)} OF [neg_thm]
        val [thm1, thm2] = 
          map (fn thm' => thm' OF [neg_thm, get_basis_wf_thm basis, thm]) 
            @{thms expands_to_sin_ms_neg_exp expands_to_cos_ms_neg_exp}
      in
        (thm1, thm2)
      end
  | sin_cos_expansion thm basis ((IsZero, zero_thm) :: e_thms) =
      let
        val zero_thm = @{thm compare_reals_diff_sgnD(2)} OF [zero_thm]
        val thm' = expands_to_hd thm
        val (sin_thm, cos_thm) = (sin_cos_expansion thm' (tl_basis basis) e_thms)
        fun mk_thm thm' = 
          (thm' OF [zero_thm, get_basis_wf_thm basis, thm, sin_thm, cos_thm]) |> solve_eval_eq
        val [thm1, thm2] = 
          map mk_thm @{thms expands_to_sin_ms_zero_exp expands_to_cos_ms_zero_exp}
      in
        (thm1, thm2)
      end
  | sin_cos_expansion _ _ _ = raise Match

fun ln_expansion_bounds ectxt (Exact thm, basis) =
          let
            val (thm, _, trimmed_thm) = trim_expansion true (SOME Pos_Trim) ectxt (thm, basis)
          in
            case trimmed_thm of
              NONE => raise TERM ("ln_expansion_bounds", [get_expanded_fun thm])
            | SOME trimmed_thm => 
                ln_expansion ectxt trimmed_thm thm basis |> apfst Exact
          end
  | ln_expansion_bounds _ (Bounds (NONE, _), _) =
      raise TERM ("ln_expansion_bounds", [])
  | ln_expansion_bounds ectxt (Bounds (SOME (lthm, lb_thm), ub), basis) =
      let
        fun trim thm = trim_expansion true (SOME Pos_Trim) ectxt (thm, basis)
        val (lthm, _, trimmed_thm) = trim lthm
        val ub =
          Option.mapPartial (fn (uthm, ub_thm) => 
            case trim uthm of 
              (uthm, _, SOME trimmed_thm) => SOME (uthm, trimmed_thm, ub_thm)
            | _ => NONE)
          ub
      in
        case trimmed_thm of
          NONE => raise TERM ("ln_expansion_bounds", [get_expanded_fun lthm])
        | SOME trimmed_thm => ln_expansion_bounds' ectxt (lthm, trimmed_thm, lb_thm) ub basis
      end

fun powr_const_expansion_bounds ectxt (Exact thm, p, basis) =
      Exact (powr_const_expansion ectxt (thm, p, basis))
  | powr_const_expansion_bounds _ (Bounds (NONE, NONE), _, _) = Bounds (NONE, NONE)
  | powr_const_expansion_bounds ectxt (bnds as Bounds (NONE, _), p, basis) =
      Bounds (SOME (zero_expansion basis, @{thm eventually_powr_const_nonneg} OF
        map (Thm.reflexive o Thm.cterm_of (Lazy_Eval.get_ctxt ectxt))
                   [get_expanded_fun_bounds bnds, p]), NONE)
  | powr_const_expansion_bounds ectxt (bnds as Bounds (SOME (lthm, ge_thm), upper), p, basis) =
      let
        val (lthm, lsgn_thm, sgns) = determine_sign ectxt (lthm, basis)
        val _ = if snd sgns then ()
          else raise TERM ("Negative base for powr.", [])
        val (sgn, SOME sgn_thm) = zeroness_oracle true (SOME Sgn_Trim) ectxt p
      in
        if sgn = IsNeg andalso fst sgns then
          Bounds (SOME (zero_expansion basis,
            @{thm eventually_powr_const_nonneg} OF
                 map (Thm.reflexive o Thm.cterm_of (Lazy_Eval.get_ctxt ectxt))
                   [get_expanded_fun_bounds bnds, p]), NONE)
        else
          let
            val sgn_thm =
              case sgn of
                IsPos => sgn_thm RS @{thm less_imp_le}
              | IsZero => sgn_thm RS @{thm eq_zero_imp_nonneg}
              | IsNeg => sgn_thm RS @{thm less_imp_le}
              | _ => raise TERM ("Unexpected zeroness result in powr_const_expansion_bounds", [])
            val lthm' = powr_const_expansion ectxt (lthm, p, basis)
            val lbnd = (lthm',
              if sgn <> IsNeg then
                @{thm eventually_powr_const_mono_nonneg[OF _ _ eventually_le_self]} OF
                  [sgn_thm, mk_nonneg_thm lsgn_thm, ge_thm]
              else
                @{thm eventually_powr_const_mono_nonpos[OF _ _ eventually_le_self]} OF
                  [sgn_thm, lsgn_thm, ge_thm])
            fun transfer_upper_bound (uthm, le_thm) =
              (powr_const_expansion ectxt (uthm, p, basis),
                 if sgn <> IsNeg then
                   @{thm eventually_powr_const_mono_nonneg} OF
                     [sgn_thm, mk_nonneg_thm lsgn_thm, ge_thm, le_thm]
                 else
                   @{thm eventually_powr_const_mono_nonpos} OF
                     [sgn_thm, lsgn_thm, ge_thm, le_thm])
          in
            Bounds ((SOME lbnd, Option.map transfer_upper_bound upper) |>
              (if sgn = IsNeg then swap else I))
          end
      end
        handle Bind => raise TERM ("Unexpected zeroness result in powr_const_expansion_bounds", [])


(* TODO stub *)
fun nonneg_power_expansion_bounds ectxt (Bounds (SOME (lthm, ge_thm), upper), n, basis) =
      let
        val (lthm, lsgn_thm, l1sgns) = determine_sign ectxt (lthm, basis)
        val _ = if not (snd l1sgns) then
          raise TERM ("Unexpected zeroness result in nonneg_power_expansion_bounds", []) else ()
        val nonneg_thm = mk_nonneg_thm lsgn_thm
        val ctxt = Lazy_Eval.get_ctxt ectxt
        val n_thm = Thm.reflexive (Thm.cterm_of ctxt n)
        val lbnd =
          (power_expansion ectxt (lthm, n, basis),
             @{thm eventually_power_mono[OF _ eventually_le_self]} OF
               [nonneg_thm, ge_thm, n_thm])
        fun transfer_upper (uthm, le_thm) =
          (power_expansion ectxt (uthm, n, basis),
             @{thm eventually_power_mono} OF
               [nonneg_thm, ge_thm, le_thm, n_thm])
      in
        Bounds (SOME lbnd, Option.map transfer_upper upper)
      end
  | nonneg_power_expansion_bounds _ _ = Bounds (NONE, NONE)

fun odd_power_expansion_bounds ectxt odd_thm (bnds, n, basis) =
      let
        fun transfer (thm, le_thm) =
          (power_expansion ectxt (thm, n, basis),
             @{thm eventually_mono_power_odd} OF [odd_thm, le_thm])
      in
        bnds |> apply2 (Option.map transfer) |> Bounds
      end

fun get_parity' ectxt t =
  let
    (* TODO: Throw a tactic at it *)
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val par = get_parity (Thm.cterm_of ctxt t)
    fun is_unknown Unknown_Parity = true
      | is_unknown _ = false
    val _ =
       if not (is_unknown par) orelse not (#verbose (#ctxt ectxt)) then () else
         let
           val p = Pretty.str ("real_asymp failed to determine whether the following term " ^
             "is even or odd:")
           val p = Pretty.chunks [p, Pretty.indent 2 (Syntax.pretty_term ctxt t)]
         in
           Pretty.writeln p
         end
  in
    par
  end

fun reflexive ectxt t = Thm.reflexive (Thm.cterm_of (Lazy_Eval.get_ctxt ectxt) t)

fun unknown_parity_power_expansion_lower_bound ectxt ((SOME (lthm, ge_thm), _), n, basis) =
      let
        val lpow_thm = power_expansion ectxt (lthm, n, basis)
        val (lthm', le_thm1, le_thm2) =
          find_smaller_expansion ectxt (lpow_thm, zero_expansion basis, basis)
      in
        SOME (lthm', @{thm eventually_lower_bound_power_indet} OF [ge_thm, le_thm1, le_thm2])
      end
  | unknown_parity_power_expansion_lower_bound _ _ = NONE

fun unknown_parity_power_expansion_upper_bound ectxt
    ((SOME (lthm, ge_thm), SOME (uthm, le_thm)), n, basis) =
      let
        val lthm = @{thm expands_to_uminus} OF [get_basis_wf_thm basis, lthm]
        val (uthm', ge_thm1, ge_thm2) =
          find_greater_expansion ectxt (lthm, uthm, basis)
        val uthm' = power_expansion ectxt (uthm', n, basis)
      in
        SOME (uthm', @{thm eventually_upper_bound_power_indet} OF 
          [ge_thm, le_thm, ge_thm1, ge_thm2, reflexive ectxt n])
      end
  | unknown_parity_power_expansion_upper_bound _ _ = NONE

fun even_power_expansion_bounds ectxt even_thm (bnds, n, basis) =
  let
    fun handle_indet_case bnds =
      let
        val lower = (zero_expansion basis, @{thm eventually_lower_bound_power_even_indet} OF
          [even_thm, reflexive ectxt (get_expanded_fun_bounds (Bounds bnds))])
        val upper = unknown_parity_power_expansion_upper_bound ectxt (bnds, n, basis)
      in
        (SOME lower, upper)
      end
  in
    case snd bnds of
      NONE => handle_indet_case bnds
    | SOME (uthm, le_thm) =>
        let
          val (uthm, usgn_thm, usgns) = determine_sign ectxt (uthm, basis)
          val bnds = (fst bnds, SOME (uthm, le_thm))
        in
          if fst usgns then
            let
              val lthm' = power_expansion ectxt (uthm, n, basis)
              val ge_thm' = @{thm eventually_lower_bound_power_even_nonpos} OF
                [even_thm, mk_nonpos_thm usgn_thm, le_thm]
              fun transfer_lower_bound (lthm, ge_thm) =
                (power_expansion ectxt (lthm, n, basis),
                   @{thm eventually_upper_bound_power_even_nonpos} OF
                     [even_thm, mk_nonpos_thm usgn_thm, ge_thm, le_thm])
            in
              (SOME (lthm', ge_thm'), Option.map transfer_lower_bound (fst bnds))
            end
          else
            handle_indet_case bnds
        end
  end
  
fun power_expansion_bounds ectxt (Exact thm, n, basis) =
      Exact (power_expansion ectxt (thm, n, basis))
  | power_expansion_bounds ectxt (Bounds bnds, n, basis) =
      let
        val parity = get_parity' ectxt n
        fun handle_non_nonneg_case bnds = Bounds (
          case parity of
            Odd _ => raise Match
          | Even even_thm => even_power_expansion_bounds ectxt even_thm (bnds, n, basis)
          | Unknown_Parity =>
              (unknown_parity_power_expansion_lower_bound ectxt (bnds, n, basis),
               unknown_parity_power_expansion_upper_bound ectxt (bnds, n, basis)))
      in
        case parity of
          Odd odd_thm => odd_power_expansion_bounds ectxt odd_thm (bnds, n, basis)
        | _ =>
          case fst bnds of
            NONE => handle_non_nonneg_case bnds
          | SOME (lthm, ge_thm) =>
              let
                val (lthm, lsgn_thm, lsgns) = determine_sign ectxt (lthm, basis)
                val bnds = (SOME (lthm, ge_thm), snd bnds)
              in
                if snd lsgns then
                  let
                    val nthm = reflexive ectxt n
                    val lthm' = power_expansion ectxt (lthm, n, basis)
                    val ge_thm' = @{thm eventually_power_mono[OF _ eventually_le_self]} OF
                      [mk_nonneg_thm lsgn_thm, ge_thm, nthm]
                    fun transfer_upper (uthm, le_thm) =
                      (power_expansion ectxt (uthm, n, basis),
                         @{thm eventually_power_mono} OF
                           [mk_nonneg_thm lsgn_thm, ge_thm, le_thm, nthm])
                  in
                    Bounds (SOME (lthm', ge_thm'), Option.map transfer_upper (snd bnds))
                  end
                else
                  handle_non_nonneg_case bnds
              end
      end

fun sgn_expansion_bounds ectxt (Exact thm, basis) =
      Exact (sgn_expansion ectxt (thm, basis))
  | sgn_expansion_bounds ectxt (Bounds bnds, basis) =
      let
        fun aux (thm, le_thm) =
          (sgn_expansion ectxt (thm, basis), mono_bound @{thm mono_sgn_real} le_thm)
        val (lower, upper) = apply2 (Option.map aux) bnds
        fun get_bound_exp (SOME (thm, _)) = SOME (get_expansion thm)
          | get_bound_exp _ = NONE
        fun is_const (SOME (Const (@{const_name "Multiseries_Expansion.const_expansion"}, _) $ c'),
              c) = c aconv c'
          | is_const _ = false
        fun aconv' (SOME a, SOME b) = a aconv b
          | aconv' _ = false
      in
        if is_const (get_bound_exp lower, @{term "\<lambda>x::real. 1 :: real"}) then
          let
            val SOME (lthm, ge_thm) = lower
          in
            Exact (@{thm eventually_sgn_ge_1D} OF [ge_thm, lthm])
          end
        else if is_const (get_bound_exp upper, @{term "\<lambda>x::real. -1 :: real"}) then
          let
            val SOME (uthm, le_thm) = upper
          in
            Exact (@{thm eventually_sgn_le_neg1D} OF [le_thm, uthm])
          end
        else if aconv' (apply2 get_bound_exp (lower, upper)) then
          let
            val (SOME (lthm, ge_thm), SOME (uthm, le_thm)) = (lower, upper)
          in
            Exact (@{thm expands_to_squeeze} OF [ge_thm, le_thm, lthm, uthm])
          end
        else
          Bounds (lower, upper)
      end

fun sin_cos_expansion_bounds sin ectxt e basis =
      let
        val f = if sin then fst else snd
        fun trivial_bounds basis =
          mk_trivial_bounds ectxt (expr_to_term e) 
            (if sin then @{thm trivial_bounds_sin} else @{thm trivial_bounds_cos}) basis
        fun mk_expansion (thm, basis') =
          case trim_expansion_while_pos ectxt (thm, basis') of
            (_, Trimmed _, _) => (trivial_bounds basis, basis)
          | (thm, Aborted _, e_thms) => 
              (Exact (f (sin_cos_expansion thm basis' e_thms)), basis')
      in
        case expand_bounds' ectxt e basis of
          (Exact thm, basis') => mk_expansion (thm, basis')
        | _ => (trivial_bounds basis, basis)
     end

and mono_expansion mono_thm expand_fun ectxt e basis =
      case expand_bounds' ectxt e basis of
        (Exact thm, basis) => expand_fun ectxt thm basis |> apfst Exact
      | (Bounds (SOME (lthm, lb_thm), NONE), basis) =>
          expand_fun ectxt lthm basis
          |> apfst (fn lthm => Bounds (SOME (lthm, mono_bound mono_thm lb_thm), NONE))
      | (Bounds (NONE, SOME (uthm, ub_thm)), basis) =>
          expand_fun ectxt uthm basis
          |> apfst (fn uthm => Bounds (NONE, SOME (uthm, mono_bound mono_thm ub_thm)))
      | (Bounds (SOME (lthm, lb_thm), SOME (uthm, ub_thm)), basis) =>
          let
            val (lthm', basis') = expand_fun ectxt lthm basis
            val (uthm', basis'') = expand_fun ectxt (lift basis' uthm) basis'
            val lthm' = lift basis'' lthm'
            val (lb_thm', ub_thm') = apply2 (mono_bound mono_thm) (lb_thm, ub_thm)
          in
            (Bounds (SOME (lthm', lb_thm'), SOME (uthm', ub_thm')), basis'')
          end
      | x => x

and minmax_expansion_bounds max thm ectxt (e1, e2) basis =
      case try_prove_ev_eq ectxt (apply2 expr_to_term (e1, e2)) of
        SOME eq_thm =>
          let
            val eq_thm' =
              eq_thm RS (if max then @{thm max_eventually_eq} else @{thm min_eventually_eq})
          in
            expand_bounds' ectxt e1 basis |> apfst (cong_bounds eq_thm')
          end
      | NONE =>
          let
            val (bnds1, basis') = expand_bounds' ectxt e1 basis
            val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
            val bnds1 = lift_bounds basis'' bnds1
            fun f (thm1, thm2) = 
              (if max then max_expansion else min_expansion) ectxt (thm1, thm2, basis'')
            fun handle_bound (SOME (exp_thm1, le_thm1), SOME (exp_thm2, le_thm2)) =
                  SOME (f (exp_thm1, exp_thm2), thm OF [le_thm1, le_thm2])
              | handle_bound _ = NONE
            val bnds = (bnds1, bnds2)
            val bnds =
              case (bnds1, bnds2) of
                (Exact thm1, Exact thm2) => Exact (f (thm1, thm2))
              | _ =>
                Bounds (handle_bound (apply2 get_lower_bound bnds), 
                  handle_bound (apply2 get_upper_bound bnds))
          in
            (bnds, basis'')
          end

and expand_bin_bounds swap thms ectxt (e1, e2) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
        val bnds = expand_add_bounds swap thms (bnds1, bnds2) basis''
      in
        (bnds, basis'')
      end

and expand_bounds'' ectxt (Add e12) basis =
      expand_bin_bounds false @{thms expands_to_add combine_bounds_add} ectxt e12 basis
  | expand_bounds'' ectxt (Minus e12) basis =
      expand_bin_bounds true @{thms expands_to_minus combine_bounds_diff} ectxt e12 basis
  | expand_bounds'' ectxt (Uminus e) basis = (
      case expand_bounds' ectxt e basis of
        (Exact thm, basis) =>
          (Exact (@{thm expands_to_uminus} OF [get_basis_wf_thm basis, thm]), basis)
      | (Bounds bnds, basis) =>
          let
            fun flip (thm1, thm2) = 
              (@{thm expands_to_uminus} OF [get_basis_wf_thm basis, thm1],
                 @{thm bounds_uminus} OF [thm2])
          in
            (Bounds (apply2 (Option.map flip) (swap bnds)), basis)
          end)
  | expand_bounds'' ectxt (Mult (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
        val bnds = mult_expansion_bounds ectxt basis'' bnds1 bnds2
     in
       (bnds, basis'')
     end
  | expand_bounds'' ectxt (Powr (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
     in
       powr_expansion_bounds ectxt basis'' bnds1 bnds2
     end
  | expand_bounds'' ectxt (Powr_Nat (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
     in
       powr_nat_expansion_bounds ectxt basis'' bnds1 bnds2
     end
  | expand_bounds'' ectxt (Powr' (e, p)) basis =
      let
        val (bnds, basis') = expand_bounds' ectxt e basis
      in
        (powr_const_expansion_bounds ectxt (bnds, p, basis'), basis')
      end
  | expand_bounds'' ectxt (Power (e, n)) basis =
      let
        val (bnds, basis') = expand_bounds' ectxt e basis
      in
        (power_expansion_bounds ectxt (bnds, n, basis'), basis')
      end
  | expand_bounds'' ectxt (Root (e, n)) basis =
      mono_expansion (reflexive ectxt n RS @{thm mono_root_real})
        (fn ectxt => fn thm => fn basis => (root_expansion ectxt (thm, n, basis), basis))
        ectxt e basis
  | expand_bounds'' ectxt (Inverse e) basis =
      let
        val (bnds, basis') = expand_bounds' ectxt e basis
      in
        (inverse_expansion_bounds ectxt basis' bnds, basis')
      end
  | expand_bounds'' ectxt (Div (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
      in
        (divide_expansion_bounds ectxt basis'' bnds1 bnds2, basis'')
      end
  | expand_bounds'' ectxt (Sin e) basis =
      sin_cos_expansion_bounds true ectxt e basis
  | expand_bounds'' ectxt (Cos e) basis =
      sin_cos_expansion_bounds false ectxt e basis
  | expand_bounds'' ectxt (Exp e) basis =
      mono_expansion @{thm mono_exp_real} exp_expansion ectxt e basis
  | expand_bounds'' ectxt (Ln e) basis =
      ln_expansion_bounds ectxt (expand_bounds' ectxt e basis)
  | expand_bounds'' ectxt (ExpLn e) basis =
      let
        val (bnds, basis') = expand_bounds' ectxt e basis
      in
        case get_lower_bound bnds of
          NONE => (Bounds (NONE, NONE), basis)
        | SOME (lthm, ge_thm) =>
            case trim_expansion true (SOME Pos_Trim) ectxt (lthm, basis') of
              (_, _, NONE) => raise TERM ("Non-positive function under logarithm.", [])
            | (lthm, _, SOME trimmed_thm) =>
                let   
                  val bnds =
                    case bnds of
                      Exact _ => Exact lthm
                    | Bounds (_, upper) => Bounds (SOME (lthm, ge_thm), upper)
                  val eq_thm = @{thm expands_to_imp_exp_ln_eq} OF
                    [lthm, ge_thm, trimmed_thm, get_basis_wf_thm basis]
                in
                  (cong_bounds eq_thm bnds, basis')
                end
      end
  | expand_bounds'' ectxt (LnPowr (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
      in
        case get_lower_bound bnds1 of
          NONE => (Bounds (NONE, NONE), basis)
        | SOME (lthm, ge_thm) =>
            case trim_expansion true (SOME Pos_Trim) ectxt (lthm, basis'') of
              (_, _, NONE) => raise TERM ("Non-positive base for powr.", [])
            | (lthm, _, SOME trimmed_thm) =>
                let   
                  val bnds1 =
                    case bnds1 of
                      Exact _ => Exact lthm
                    | Bounds (_, upper) => Bounds (SOME (lthm, ge_thm), upper)
                  val eq_thm = @{thm expands_to_imp_ln_powr_eq} OF
                    [lthm, ge_thm, trimmed_thm, get_basis_wf_thm basis'']
                  val (ln_bnds, basis''') = ln_expansion_bounds ectxt (bnds1, basis'')
                  val bnds2 = lift_bounds basis''' bnds2
                  val bnds = mult_expansion_bounds ectxt basis''' ln_bnds bnds2
                in
                  (cong_bounds eq_thm bnds, basis''')
                end
      end
  | expand_bounds'' ectxt (Absolute e) basis =
     let
       val (bnds, basis') = expand_bounds' ectxt e basis
     in
       (abs_expansion_bounds ectxt basis' bnds, basis')
     end
  | expand_bounds'' ectxt (Sgn e) basis =
     let
       val (bnds, basis') = expand_bounds' ectxt e basis
     in
       (sgn_expansion_bounds ectxt (bnds, basis'), basis')
     end
  | expand_bounds'' ectxt (Min e12) basis =
      minmax_expansion_bounds false @{thm combine_bounds_min} ectxt e12 basis
  | expand_bounds'' ectxt (Max e12) basis =
      minmax_expansion_bounds true @{thm combine_bounds_max} ectxt e12 basis
  | expand_bounds'' ectxt (Floor e) basis =
      floor_expansion_bounds ectxt (expand_bounds' ectxt e basis)
  | expand_bounds'' ectxt (Ceiling e) basis =
      ceiling_expansion_bounds ectxt (expand_bounds' ectxt e basis)
  | expand_bounds'' ectxt (Frac e) basis =
      (mk_trivial_bounds ectxt (expr_to_term e) @{thm trivial_bounds_frac} basis, basis)
  | expand_bounds'' ectxt (NatMod (e1, e2)) basis =
      let
        val (bnds1, basis') = expand_bounds' ectxt e1 basis
        val (bnds2, basis'') = expand_bounds' ectxt e2 basis'
        val bnds1 = lift_bounds basis'' bnds1
      in
        (natmod_expansion_bounds ectxt (bnds1, bnds2, basis''), basis'')
      end
  | expand_bounds'' ectxt (ArcTan e) basis =
      mono_expansion @{thm mono_arctan_real} 
        (fn ectxt => fn thm => fn basis => (arctan_expansion ectxt basis thm, basis)) ectxt e basis
  | expand_bounds'' ectxt e basis =
      expand ectxt e basis |> apfst Exact

and expand_bounds' ectxt e basis =
      expand_bounds'' ectxt e basis |> apfst (check_bounds e)

fun expand_term_bounds ectxt t basis =
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val (e, eq_thm) = reify ctxt t
    val (bounds, basis) = expand_bounds' ectxt e basis
  in
    (transfer_bounds eq_thm bounds, basis)
  end

fun expand_terms_bounds ectxt ts basis =
  let
    val ctxt = Lazy_Eval.get_ctxt ectxt
    val e_eq_thms = map (reify ctxt) ts
    fun step (e, eq_thm) (bndss, basis) =
      let
        val (bnds, basis) = expand_bounds' ectxt e basis
        val bnds = transfer_bounds eq_thm bnds
      in
        (bnds :: bndss, basis)
      end
    val (thms, basis) = fold step e_eq_thms ([], basis)
    fun lift bnds = lift_bounds basis bnds
  in
    (map lift (rev thms), basis)
  end

fun prove_nhds_bounds ectxt (Exact thm, basis) = prove_nhds ectxt (thm, basis)
  | prove_nhds_bounds ectxt (Bounds (SOME (lthm, ge_thm), SOME (uthm, le_thm)), basis) =
      let
        fun extract_limit thm =
          thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_comb |> fst |> dest_comb |> snd
            |> dest_comb |> snd
        val llim_thm = prove_nhds ectxt (lthm, basis)
        val ulim_thm = prove_nhds ectxt (uthm, basis)
        val (lim1, lim2) = apply2 extract_limit (llim_thm, ulim_thm)
        val eq_thm = the (try_prove_real_eq true ectxt (lim1, lim2))
      in
        @{thm tendsto_sandwich'} OF [ge_thm, le_thm, llim_thm, ulim_thm, eq_thm]
      end
  | prove_nhds_bounds _ _ = raise TERM ("prove_nhds_bounds", [])

fun prove_at_top_bounds ectxt (Exact thm, basis) = prove_at_top ectxt (thm, basis)
  | prove_at_top_bounds ectxt (Bounds (SOME (lthm, ge_thm), _), basis) =
      let
        val llim_thm = prove_at_top ectxt (lthm, basis)
      in
        @{thm filterlim_at_top_mono} OF [llim_thm, ge_thm]
      end
  | prove_at_top_bounds _ _ = raise TERM ("prove_at_top_bounds", [])

fun prove_at_bot_bounds ectxt (Exact thm, basis) = prove_at_bot ectxt (thm, basis)
  | prove_at_bot_bounds ectxt (Bounds (_, SOME (uthm, le_thm)), basis) =
      let
        val ulim_thm = prove_at_bot ectxt (uthm, basis)
      in
        @{thm filterlim_at_bot_mono} OF [ulim_thm, le_thm]
      end
  | prove_at_bot_bounds _ _ = raise TERM ("prove_at_bot_bounds", [])

fun prove_at_infinity_bounds ectxt (Exact thm, basis) = prove_at_infinity ectxt (thm, basis)
  | prove_at_infinity_bounds ectxt (Bounds (lb, ub), basis) =
      let
        val wf_thm = get_basis_wf_thm basis
        fun assert_nz (SOME (thm, le_thm)) = (
          case ev_zeroness_oracle ectxt (get_expanded_fun thm) of
            SOME _ => NONE
          | NONE => SOME (thm, le_thm))
        | assert_nz NONE = NONE
        fun lb_at_top (lthm, ge_thm) =
          case trim_expansion true (SOME Sgn_Trim) ectxt (lthm, basis) of
            (lthm, IsPos, SOME trimmed_thm) => SOME
              let
                val lim_thm = prove_at_infinity ectxt (lthm, basis)
                val pos_thm = @{thm expands_to_imp_eventually_pos} OF [wf_thm, lthm, trimmed_thm]
                val lim_thm' =
                  @{thm filterlim_at_infinity_imp_filterlim_at_top} OF [lim_thm, pos_thm]
              in
                @{thm filterlim_at_top_imp_at_infinity[OF filterlim_at_top_mono]}
                  OF [lim_thm', ge_thm]
              end
          | _ => NONE
        fun ub_at_top (uthm, le_thm) =
          case trim_expansion true (SOME Sgn_Trim) ectxt (uthm, basis) of
            (uthm, IsNeg, SOME trimmed_thm) => SOME
              let
                val lim_thm = prove_at_infinity ectxt (uthm, basis)
                val neg_thm = @{thm expands_to_imp_eventually_neg} OF [wf_thm, uthm, trimmed_thm]
                val lim_thm' =
                  @{thm filterlim_at_infinity_imp_filterlim_at_bot} OF [lim_thm, neg_thm]
              in
                @{thm filterlim_at_bot_imp_at_infinity[OF filterlim_at_bot_mono]}
                  OF [lim_thm', le_thm]
              end
          | _ => NONE
      in
        case Option.mapPartial lb_at_top (assert_nz lb) of
          SOME thm => thm
        | NONE =>
            case Option.mapPartial ub_at_top (assert_nz ub) of
              SOME thm => thm
            | NONE => raise TERM ("prove_at_infinity_bounds", [])
      end

fun prove_eventually_pos_lower_bound ectxt basis (lthm, ge_thm) =
      case trim_expansion true (SOME Sgn_Trim) ectxt (lthm, basis) of
        (lthm, IsPos, SOME trimmed_thm) =>
          SOME (@{thm eventually_less_le} OF [@{thm expands_to_imp_eventually_pos} OF
            [get_basis_wf_thm basis, lthm, trimmed_thm], ge_thm])
      | _ => NONE


fun prove_eventually_neg_upper_bound ectxt basis (uthm, le_thm) =
      case trim_expansion true (SOME Sgn_Trim) ectxt (uthm, basis) of
        (uthm, IsNeg, SOME trimmed_thm) =>
          SOME (@{thm eventually_le_less} OF [le_thm, @{thm expands_to_imp_eventually_neg} OF
            [get_basis_wf_thm basis, uthm, trimmed_thm]])
      | _ => NONE

fun prove_eventually_nonzero_bounds ectxt (Exact thm, basis) = (
      case trim_expansion true (SOME Simple_Trim) ectxt (thm, basis) of
        (thm, _, SOME trimmed_thm) =>
          @{thm expands_to_imp_eventually_nz} OF [get_basis_wf_thm basis, thm, trimmed_thm]
      |  _ => raise TERM ("prove_eventually_nonzero", []))
  | prove_eventually_nonzero_bounds ectxt (Bounds (l, u), basis) =
      case Option.mapPartial (prove_eventually_pos_lower_bound ectxt basis) l of
        SOME thm => thm RS @{thm eventually_pos_imp_nz}
      | NONE =>
          case Option.mapPartial (prove_eventually_neg_upper_bound ectxt basis) u of
            SOME thm => thm RS @{thm eventually_neg_imp_nz}
          | NONE => raise TERM ("prove_eventually_nonzero", [])

fun prove_at_0_bounds ectxt (Exact thm, basis) = prove_at_0 ectxt (thm, basis)
  | prove_at_0_bounds ectxt (Bounds bnds, basis) =
      let
        val lim_thm = prove_nhds_bounds ectxt (Bounds bnds, basis)
        val nz_thm = prove_eventually_nonzero_bounds ectxt (Bounds bnds, basis)
      in
        @{thm Topological_Spaces.filterlim_atI} OF [lim_thm, nz_thm]
      end

fun prove_at_right_0_bounds ectxt (Exact thm, basis) = prove_at_right_0 ectxt (thm, basis)
  | prove_at_right_0_bounds ectxt (Bounds (SOME l, SOME u), basis) =
      let
        val lim_thm = prove_nhds_bounds ectxt (Bounds (SOME l, SOME u), basis)
      in
        case prove_eventually_pos_lower_bound ectxt basis l of
          SOME pos_thm => @{thm tendsto_imp_filterlim_at_right} OF [lim_thm, pos_thm]
        | NONE => raise TERM ("prove_at_right_0_bounds", [])
      end
  | prove_at_right_0_bounds _ _ = raise TERM ("prove_at_right_0_bounds", [])

fun prove_at_left_0_bounds ectxt (Exact thm, basis) = prove_at_left_0 ectxt (thm, basis)
  | prove_at_left_0_bounds ectxt (Bounds (SOME l, SOME u), basis) =
      let
        val lim_thm = prove_nhds_bounds ectxt (Bounds (SOME l, SOME u), basis)
      in
        case prove_eventually_neg_upper_bound ectxt basis u of
          SOME neg_thm => @{thm tendsto_imp_filterlim_at_left} OF [lim_thm, neg_thm]
        | NONE => raise TERM ("prove_at_left_0_bounds", [])
      end
  | prove_at_left_0_bounds _ _ = raise TERM ("prove_at_left_0_bounds", [])

fun prove_eventually_less_bounds ectxt (bnds1, bnds2, basis) =
      case (get_upper_bound bnds1, get_lower_bound bnds2) of
        (SOME (ub1_thm, le_ub1_thm), SOME (lb2_thm, ge_lb2_thm)) =>
          let
            val thm = prove_eventually_less ectxt (ub1_thm, lb2_thm, basis)
          in
            @{thm eventually_le_less[OF _ eventually_less_le]} OF [le_ub1_thm, thm, ge_lb2_thm]
          end
     | _ => raise TERM ("prove_asymptotically_less_bounds", [])

fun prove_eventually_greater_bounds ectxt (bnds1, bnds2, basis) =
      prove_eventually_less_bounds ectxt (bnds2, bnds1, basis)



fun prove_o_bounds small ectxt (Exact thm1, Exact thm2, basis) =
      (if small then prove_smallo else prove_bigo) ectxt (thm1, thm2, basis)
  | prove_o_bounds small ectxt (bnds1, bnds2, basis) =
      let
        val exact = if small then prove_smallo else prove_bigo
        val s = if small then "prove_smallo_bounds" else "prove_bigo_bounds"
        val (l2thm', nonneg_thm, ge2_thm) = abs_expansion_lower_bound ectxt basis bnds2
        val ((l1thm, ge1_thm), (u1thm, le1_thm)) =
          case bnds1 of
            Exact thm1 => 
              let val x = (exact ectxt (thm1, l2thm', basis), thm1 RS @{thm exact_to_bound})
              in (x, x) end
          | Bounds (SOME (l1thm, ge1_thm), SOME (u1thm, le1_thm)) =>
              ((exact ectxt (l1thm, l2thm', basis), ge1_thm),
               (exact ectxt (u1thm, l2thm', basis), le1_thm))
          | _ => raise TERM (s, [])
        val impthm = if small then @{thm bounds_smallo_imp_smallo} else @{thm bounds_bigo_imp_bigo}
      in
        impthm OF [ge1_thm, le1_thm, ge2_thm, nonneg_thm, l1thm, u1thm]
      end

val prove_smallo_bounds = prove_o_bounds true
val prove_bigo_bounds = prove_o_bounds false

fun prove_bigtheta_bounds ectxt (Exact thm1, Exact thm2, basis) =
      prove_bigtheta ectxt (thm1, thm2, basis)
  | prove_bigtheta_bounds ectxt (bnds1, bnds2, basis) =
      let (* TODO inefficient *)
        val thms = 
          Par_List.map (fn x => prove_bigo_bounds ectxt x) 
            [(bnds1, bnds2, basis), (bnds2, bnds1, basis)]
      in
        @{thm bigthetaI[unfolded bigomega_iff_bigo]} OF thms
      end

fun prove_asymp_equivs ectxt basis =
      Par_List.map (fn (thm1, thm2) => prove_asymp_equiv ectxt (thm1, thm2, basis))

fun prove_asymp_equiv_bounds ectxt (Exact thm1, Exact thm2, basis) =
      prove_asymp_equiv ectxt (thm1, thm2, basis)
  | prove_asymp_equiv_bounds ectxt (Exact thm1, 
        Bounds (SOME (l2, ge2_thm), SOME (u2, le2_thm)), basis) =
      let
        val thms = prove_asymp_equivs ectxt basis [(thm1, l2), (thm1, u2)]
      in
        @{thm asymp_equiv_sandwich_real'[OF _ _ eventually_atLeastAtMostI]} OF
          (thms @ [ge2_thm, le2_thm])
      end
  | prove_asymp_equiv_bounds ectxt (Bounds (SOME (l1, ge1_thm), SOME (u1, le1_thm)), 
        Exact thm2, basis) =
      let
        val thms = prove_asymp_equivs ectxt basis [(l1, thm2), (u1, thm2)]
      in
        @{thm asymp_equiv_sandwich_real[OF _ _ eventually_atLeastAtMostI]} OF
          (thms @ [ge1_thm, le1_thm])
      end
  | prove_asymp_equiv_bounds ectxt (Bounds (SOME (l1, ge1_thm), SOME (u1, le1_thm)), 
        Bounds (SOME (l2, ge2_thm), SOME (u2, le2_thm)), basis) =
      let
        val thms = prove_asymp_equivs ectxt basis [(l1, u1), (u1, l2), (l2, u2)]
      in
        @{thm asymp_equiv_sandwich_real''
            [OF _ _ _ eventually_atLeastAtMostI eventually_atLeastAtMostI]} OF
          (thms @ [ge1_thm, le1_thm, ge2_thm, le2_thm])
      end
  | prove_asymp_equiv_bounds _ _ = raise TERM ("prove_asymp_equiv_bounds", [])

val dest_fun = dest_comb #> fst
val dest_arg = dest_comb #> snd
val concl_of' = Thm.concl_of #> HOLogic.dest_Trueprop

fun lim_eq ectxt (l1, l2) = (l1 aconv l2) orelse
  case (l1, l2) of
    (Const (@{const_name nhds}, _) $ a, Const (@{const_name nhds}, _) $ b) => (
      case try_prove_real_eq false ectxt (a, b) of
        SOME _ => true
      | _ => false)
  | _ => false

fun limit_of_expansion_bounds ectxt (bnds, basis) =
  let
    fun get_limit thm =
      limit_of_expansion (true, true) ectxt (thm, basis) |> snd |> concl_of' |> dest_fun |> dest_arg
  in
    case bnds of
      Exact thm => get_limit thm |> Exact_Limit
    | Bounds (l, u) =>
        let
          val (llim, ulim) = apply2 (Option.map (fst #> get_limit)) (l, u)
        in
          case (llim, ulim) of
            (SOME llim', SOME ulim') =>
              if lim_eq ectxt (llim', ulim') then Exact_Limit llim' else Limit_Bounds (llim, ulim)
          | _ => Limit_Bounds (llim, ulim)
        end
  end

end

structure Multiseries_Expansion_Bounds : EXPANSION_INTERFACE =
struct
open Multiseries_Expansion;

type T = bounds

val expand_term = expand_term_bounds
val expand_terms = expand_terms_bounds

val prove_nhds = prove_nhds_bounds
val prove_at_infinity = prove_at_infinity_bounds
val prove_at_top = prove_at_top_bounds
val prove_at_bot = prove_at_bot_bounds
val prove_at_0 = prove_at_0_bounds
val prove_at_right_0 = prove_at_right_0_bounds
val prove_at_left_0 = prove_at_left_0_bounds
val prove_eventually_nonzero = prove_eventually_nonzero_bounds

val prove_eventually_less = prove_eventually_less_bounds
val prove_eventually_greater = prove_eventually_greater_bounds

val prove_smallo = prove_smallo_bounds
val prove_bigo = prove_bigo_bounds
val prove_bigtheta = prove_bigtheta_bounds
val prove_asymp_equiv = prove_asymp_equiv_bounds

end

structure Real_Asymp_Bounds = Real_Asymp(Multiseries_Expansion_Bounds)