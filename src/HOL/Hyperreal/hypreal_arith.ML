(*  Title:      HOL/Hyperreal/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type hypreal.
*)

(*FIXME DELETE*)
val hypreal_mult_less_mono2 = thm"hypreal_mult_less_mono2";

val hypreal_mult_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::hypreal")] mult_left_mono;


val hypreal_number_of = thm "hypreal_number_of";
val hypreal_numeral_0_eq_0 = thm "hypreal_numeral_0_eq_0";
val hypreal_numeral_1_eq_1 = thm "hypreal_numeral_1_eq_1";
val hypreal_number_of_def = thm "hypreal_number_of_def";
val add_hypreal_number_of = thm "add_hypreal_number_of";
val minus_hypreal_number_of = thm "minus_hypreal_number_of";
val diff_hypreal_number_of = thm "diff_hypreal_number_of";
val mult_hypreal_number_of = thm "mult_hypreal_number_of";
val hypreal_mult_2 = thm "hypreal_mult_2";
val hypreal_mult_2_right = thm "hypreal_mult_2_right";
val eq_hypreal_number_of = thm "eq_hypreal_number_of";
val less_hypreal_number_of = thm "less_hypreal_number_of";
val hypreal_minus_1_eq_m1 = thm "hypreal_minus_1_eq_m1";
val hypreal_mult_minus1 = thm "hypreal_mult_minus1";
val hypreal_mult_minus1_right = thm "hypreal_mult_minus1_right";
val hypreal_add_number_of_left = thm "hypreal_add_number_of_left";
val hypreal_mult_number_of_left = thm "hypreal_mult_number_of_left";
val hypreal_add_number_of_diff1 = thm "hypreal_add_number_of_diff1";
val hypreal_add_number_of_diff2 = thm "hypreal_add_number_of_diff2";

(*Maps 0 to Numeral0 and 1 to Numeral1 and -(Numeral1) to -1*)
val hypreal_numeral_ss =
    real_numeral_ss addsimps [hypreal_numeral_0_eq_0 RS sym,
                              hypreal_numeral_1_eq_1 RS sym,
                              hypreal_minus_1_eq_m1]

fun rename_numerals th =
    asm_full_simplify hypreal_numeral_ss (Thm.transfer (the_context ()) th)


structure Hyperreal_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [hypreal_numeral_0_eq_0 RS sym,
                    hypreal_numeral_1_eq_1 RS sym]

(*Utilities*)

val hyprealT = Type("HyperDef.hypreal",[])

fun mk_numeral n = HOLogic.number_of_const hyprealT $ HOLogic.mk_bin n

val dest_numeral = Real_Numeral_Simprocs.dest_numeral

val find_first_numeral = Real_Numeral_Simprocs.find_first_numeral

val zero = mk_numeral 0
val mk_plus = Real_Numeral_Simprocs.mk_plus

val uminus_const = Const ("uminus", hyprealT --> hyprealT)

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts)

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts)

val dest_plus = HOLogic.dest_bin "op +" hyprealT

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts

fun dest_sum t = dest_summing (true, t, [])

val mk_diff = HOLogic.mk_binop "op -"
val dest_diff = HOLogic.dest_bin "op -" hyprealT

val one = mk_numeral 1
val mk_times = HOLogic.mk_binop "op *"

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts)

val dest_times = HOLogic.dest_bin "op *" hyprealT

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t]

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, ts) = mk_times (mk_numeral k, ts)

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const ("uminus", _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term.term_ord (dest_prod t)
        val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod ts') end

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff 1 t
        in  if u aconv u' then (n, rev past @ terms)
                          else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms


(*Simplify Numeral0+n, n+Numeral0, Numeral1*n, n*Numeral1*)
val add_0s = map rename_numerals
                 [hypreal_add_zero_left, hypreal_add_zero_right]
val mult_1s = map rename_numerals [hypreal_mult_1, hypreal_mult_1_right] @
              [hypreal_mult_minus1, hypreal_mult_minus1_right]

(*To perform binary arithmetic*)
val bin_simps =
    [hypreal_numeral_0_eq_0 RS sym, hypreal_numeral_1_eq_1 RS sym,
     add_hypreal_number_of, hypreal_add_number_of_left,
     minus_hypreal_number_of,
     diff_hypreal_number_of, mult_hypreal_number_of,
     hypreal_mult_number_of_left] @ bin_arith_simps @ bin_rel_simps

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [hypreal_add_number_of_left, add_hypreal_number_of]

(*To evaluate binary negations of coefficients*)
val hypreal_minus_simps = NCons_simps @
                   [hypreal_minus_1_eq_m1, minus_hypreal_number_of,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min]

(*To let us treat subtraction as addition*)
val diff_simps = [hypreal_diff_def, minus_add_distrib, minus_minus]

(*push the unary minus down: - x * y = x * - y *)
val hypreal_minus_mult_eq_1_to_2 =
    [minus_mult_left RS sym, minus_mult_right] MRS trans
    |> standard

(*to extract again any uncancelled minuses*)
val hypreal_minus_from_mult_simps =
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym]

(*combine unary minus with numeric literals, however nested within a product*)
val hypreal_mult_minus_simps =
    [hypreal_mult_assoc, minus_mult_left, hypreal_minus_mult_eq_1_to_2]

(*Final simplification: cancel + and *  *)
val simplify_meta_eq =
    Int_Numeral_Simprocs.simplify_meta_eq
         [hypreal_add_zero_left, hypreal_add_zero_right,
          mult_zero_left, mult_zero_right, mult_1, mult_1_right]

val prep_simproc = Real_Numeral_Simprocs.prep_simproc

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hypreal_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val bal_add1 = eq_add_iff1 RS trans
  val bal_add2 = eq_add_iff2 RS trans
)

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" hyprealT
  val bal_add1 = less_add_iff1 RS trans
  val bal_add2 = less_add_iff2 RS trans
)

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" hyprealT
  val bal_add1 = le_add_iff1 RS trans
  val bal_add2 = le_add_iff2 RS trans
)

val cancel_numerals =
  map prep_simproc
   [("hyprealeq_cancel_numerals",
     ["(l::hypreal) + m = n", "(l::hypreal) = m + n",
      "(l::hypreal) - m = n", "(l::hypreal) = m - n",
      "(l::hypreal) * m = n", "(l::hypreal) = m * n"],
     EqCancelNumerals.proc),
    ("hyprealless_cancel_numerals",
     ["(l::hypreal) + m < n", "(l::hypreal) < m + n",
      "(l::hypreal) - m < n", "(l::hypreal) < m - n",
      "(l::hypreal) * m < n", "(l::hypreal) < m * n"],
     LessCancelNumerals.proc),
    ("hyprealle_cancel_numerals",
     ["(l::hypreal) + m <= n", "(l::hypreal) <= m + n",
      "(l::hypreal) - m <= n", "(l::hypreal) <= m - n",
      "(l::hypreal) * m <= n", "(l::hypreal) <= m * n"],
     LeCancelNumerals.proc)]


structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = combine_common_factor RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                   diff_simps@hypreal_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData)

val combine_numerals =
  prep_simproc
    ("hypreal_combine_numerals", ["(i::hypreal) + j", "(i::hypreal) - j"], CombineNumerals.proc)


(** Declarations for ExtractCommonTerm **)

(*this version ALWAYS includes a trailing one*)
fun long_mk_prod []        = one
  | long_mk_prod (t :: ts) = mk_times (t, mk_prod ts)

(*Find first term that matches u*)
fun find_first past u []         = raise TERM("find_first", [])
  | find_first past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first (t::past) u terms
        handle TERM _ => find_first (t::past) u terms

(*Final simplification: cancel + and *  *)
fun cancel_simplify_meta_eq cancel_th th =
    Int_Numeral_Simprocs.simplify_meta_eq
        [mult_1, mult_1_right]
        (([th, cancel_th]) MRS trans)

(*** Making constant folding work for 0 and 1 too ***)

structure HyperrealAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = hypreal_numeral_0_eq_0
  val numeral_1_eq_1  = hypreal_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure HyperrealAbstractNumerals =
  AbstractNumeralsFun (HyperrealAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("hypreal_add_eval_numerals",
     ["(m::hypreal) + 1", "(m::hypreal) + number_of v"],
     HyperrealAbstractNumerals.proc add_hypreal_number_of),
    ("hypreal_diff_eval_numerals",
     ["(m::hypreal) - 1", "(m::hypreal) - number_of v"],
     HyperrealAbstractNumerals.proc diff_hypreal_number_of),
    ("hypreal_eq_eval_numerals",
     ["(m::hypreal) = 0", "(m::hypreal) = 1", "(m::hypreal) = number_of v"],
     HyperrealAbstractNumerals.proc eq_hypreal_number_of),
    ("hypreal_less_eval_numerals",
     ["(m::hypreal) < 0", "(m::hypreal) < 1", "(m::hypreal) < number_of v"],
     HyperrealAbstractNumerals.proc less_hypreal_number_of),
    ("hypreal_le_eval_numerals",
     ["(m::hypreal) <= 0", "(m::hypreal) <= 1", "(m::hypreal) <= number_of v"],
     HyperrealAbstractNumerals.proc le_number_of_eq_not_less)]

end;

Addsimprocs Hyperreal_Numeral_Simprocs.eval_numerals;
Addsimprocs Hyperreal_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Hyperreal_Numeral_Simprocs.combine_numerals];




(**** Constant folding for hypreal plus and times ****)

(*We do not need
    structure Hyperreal_Plus_Assoc = Assoc_Fold (Hyperreal_Plus_Assoc_Data)
  because combine_numerals does the same thing*)

structure Hyperreal_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = Hyperreal_Numeral_Simprocs.hyprealT
  val plus   = Const ("op *", [T,T] ---> T)
  val add_ac = mult_ac
end;

structure Hyperreal_Times_Assoc = Assoc_Fold (Hyperreal_Times_Assoc_Data);

Addsimprocs [Hyperreal_Times_Assoc.conv];



(**** Simprocs for numeric literals ****)


(****Common factor cancellation****)

local
  open Hyperreal_Numeral_Simprocs
in

val rel_hypreal_number_of = [eq_hypreal_number_of, less_hypreal_number_of,
                             le_number_of_eq_not_less];

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  =
         ALLGOALS (simp_tac (HOL_ss addsimps rel_hypreal_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hyprealT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val cancel = mult_cancel_left RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" hyprealT
  val cancel = mult_less_cancel_left RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" hyprealT
  val cancel = mult_le_cancel_left RS trans
  val neg_exchanges = true
)

val hypreal_cancel_numeral_factors_relations =
  map prep_simproc
   [("hyprealeq_cancel_numeral_factor",
     ["(l::hypreal) * m = n", "(l::hypreal) = m * n"],
     EqCancelNumeralFactor.proc),
    ("hyprealless_cancel_numeral_factor",
     ["(l::hypreal) * m < n", "(l::hypreal) < m * n"],
     LessCancelNumeralFactor.proc),
    ("hyprealle_cancel_numeral_factor",
     ["(l::hypreal) * m <= n", "(l::hypreal) <= m * n"],
     LeCancelNumeralFactor.proc)];

val hypreal_cancel_numeral_factors_divide = prep_simproc
        ("hyprealdiv_cancel_numeral_factor",
         ["((l::hypreal) * m) / n", "(l::hypreal) / (m * n)",
          "((number_of v)::hypreal) / (number_of w)"],
         DivCancelNumeralFactor.proc);

val hypreal_cancel_numeral_factors =
    hypreal_cancel_numeral_factors_relations @
    [hypreal_cancel_numeral_factors_divide];

end;

Addsimprocs hypreal_cancel_numeral_factors;



(** Declarations for ExtractCommonTerm **)

local
  open Hyperreal_Numeral_Simprocs
in

structure CancelFactorCommon =
  struct
  val mk_sum            = long_mk_prod
  val dest_sum          = dest_prod
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first        = find_first []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@mult_ac))
  end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_cancel_left
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hyprealT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
);

val hypreal_cancel_factor =
  map prep_simproc
   [("hypreal_eq_cancel_factor", ["(l::hypreal) * m = n", "(l::hypreal) = m * n"],
     EqCancelFactor.proc),
    ("hypreal_divide_cancel_factor", ["((l::hypreal) * m) / n", "(l::hypreal) / (m * n)"],
     DivideCancelFactor.proc)];

end;

Addsimprocs hypreal_cancel_factor;




(****Instantiation of the generic linear arithmetic package****)


local

(* reduce contradictory <= to False *)
val add_rules =
    [hypreal_numeral_0_eq_0, hypreal_numeral_1_eq_1,
     add_hypreal_number_of, minus_hypreal_number_of, diff_hypreal_number_of,
     mult_hypreal_number_of, eq_hypreal_number_of, less_hypreal_number_of];

val simprocs = [Hyperreal_Times_Assoc.conv, 
                Hyperreal_Numeral_Simprocs.combine_numerals,
                hypreal_cancel_numeral_factors_divide]@
               Hyperreal_Numeral_Simprocs.cancel_numerals @
               Hyperreal_Numeral_Simprocs.eval_numerals;

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val hypreal_mult_mono_thms =
 [(rotate_prems 1 hypreal_mult_less_mono2,
   cvar(hypreal_mult_less_mono2, hd(prems_of hypreal_mult_less_mono2))),
  (hypreal_mult_left_mono,
   cvar(hypreal_mult_left_mono, hd(tl(prems_of hypreal_mult_left_mono))))]

val real_inj_thms = [hypreal_of_real_le_iff RS iffD2, 
                     hypreal_of_real_less_iff RS iffD2,
                     hypreal_of_real_eq_iff RS iffD2];

in

val fast_hypreal_arith_simproc =
    Simplifier.simproc (Theory.sign_of (the_context ()))
      "fast_hypreal_arith" 
      ["(m::hypreal) < n", "(m::hypreal) <= n", "(m::hypreal) = n"]
    Fast_Arith.lin_arith_prover;

val hypreal_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ hypreal_mult_mono_thms,
    inj_thms = inj_thms @ real_inj_thms, 
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the hypreals are dense!*)
    simpset = simpset addsimps add_rules
                      addsimprocs simprocs}),
  arith_inj_const ("HyperDef.hypreal_of_real", 
                   HOLogic.realT --> Hyperreal_Numeral_Simprocs.hyprealT),
  arith_discrete ("HyperDef.hypreal",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_hypreal_arith_simproc]];

end;



