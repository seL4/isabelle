(* Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
   Copyright   2000  University of Cambridge

Simprocs for the (integer) numerals.
*)

(*To quote from Provers/Arith/cancel_numeral_factor.ML:

Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

signature NUMERAL_SIMPROCS =
sig
  val trans_tac: Proof.context -> thm option -> tactic
  val assoc_fold: Proof.context -> cterm -> thm option
  val combine_numerals: Proof.context -> cterm -> thm option
  val eq_cancel_numerals: Proof.context -> cterm -> thm option
  val less_cancel_numerals: Proof.context -> cterm -> thm option
  val le_cancel_numerals: Proof.context -> cterm -> thm option
  val eq_cancel_factor: Proof.context -> cterm -> thm option
  val le_cancel_factor: Proof.context -> cterm -> thm option
  val less_cancel_factor: Proof.context -> cterm -> thm option
  val div_cancel_factor: Proof.context -> cterm -> thm option
  val mod_cancel_factor: Proof.context -> cterm -> thm option
  val dvd_cancel_factor: Proof.context -> cterm -> thm option
  val divide_cancel_factor: Proof.context -> cterm -> thm option
  val eq_cancel_numeral_factor: Proof.context -> cterm -> thm option
  val less_cancel_numeral_factor: Proof.context -> cterm -> thm option
  val le_cancel_numeral_factor: Proof.context -> cterm -> thm option
  val div_cancel_numeral_factor: Proof.context -> cterm -> thm option
  val divide_cancel_numeral_factor: Proof.context -> cterm -> thm option
  val field_combine_numerals: Proof.context -> cterm -> thm option
  val field_divide_cancel_numeral_factor: simproc
  val num_ss: simpset
  val field_comp_conv: Proof.context -> conv
end;

structure Numeral_Simprocs : NUMERAL_SIMPROCS =
struct

fun trans_tac _ NONE  = all_tac
  | trans_tac ctxt (SOME th) = ALLGOALS (resolve_tac ctxt [th RS trans]);

val mk_number = Arith_Data.mk_number;
val mk_sum = Arith_Data.mk_sum;
val long_mk_sum = Arith_Data.long_mk_sum;
val dest_sum = Arith_Data.dest_sum;

val mk_times = HOLogic.mk_binop \<^const_name>\<open>Groups.times\<close>;

fun one_of T = Const(\<^const_name>\<open>Groups.one\<close>, T);

(* build product with trailing 1 rather than Numeral 1 in order to avoid the
   unnecessary restriction to type class number_ring
   which is not required for cancellation of common factors in divisions.
   UPDATE: this reasoning no longer applies (number_ring is gone)
*)
fun mk_prod T =
  let val one = one_of T
  fun mk [] = one
    | mk [t] = t
    | mk (t :: ts) = if t = one then mk ts else mk_times (t, mk ts)
  in mk end;

(*This version ALWAYS includes a trailing one*)
fun long_mk_prod T []        = one_of T
  | long_mk_prod T (t :: ts) = mk_times (t, mk_prod T ts);

val dest_times = HOLogic.dest_bin \<^const_name>\<open>Groups.times\<close> dummyT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in dest_prod t @ dest_prod u end
      handle TERM _ => [t];

fun find_first_numeral past (t::terms) =
        ((snd (HOLogic.dest_number t), rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, t) = mk_times (mk_number (Term.fastype_of t) k, t);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term_Ord.term_ord (dest_prod t)
        val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod (Term.fastype_of t) ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff 1 t
        in if u aconv u' then (n, rev past @ terms)
                         else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms;

(*Fractions as pairs of ints. Can't use Rat.rat because the representation
  needs to preserve negative values in the denominator.*)
fun mk_frac (p, q) = if q = 0 then raise Div else (p, q);

(*Don't reduce fractions; sums must be proved by rule add_frac_eq.
  Fractions are reduced later by the cancel_numeral_factor simproc.*)
fun add_frac ((p1, q1), (p2, q2)) = (p1 * q2 + p2 * q1, q1 * q2);

val mk_divide = HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close>;

(*Build term (p / q) * t*)
fun mk_fcoeff ((p, q), t) =
  let val T = Term.fastype_of t
  in mk_times (mk_divide (mk_number T p, mk_number T q), t) end;

(*Express t as a product of a fraction with other sorted terms*)
fun dest_fcoeff sign (Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ t) = dest_fcoeff (~sign) t
  | dest_fcoeff sign (Const (\<^const_name>\<open>Rings.divide\<close>, _) $ t $ u) =
    let val (p, t') = dest_coeff sign t
        val (q, u') = dest_coeff 1 u
    in (mk_frac (p, q), mk_divide (t', u')) end
  | dest_fcoeff sign t =
    let val (p, t') = dest_coeff sign t
        val T = Term.fastype_of t
    in (mk_frac (p, 1), mk_divide (t', one_of T)) end;


(** New term ordering so that AC-rewriting brings numerals to the front **)

(*Order integers by absolute value and then by sign. The standard integer
  ordering is not well-founded.*)
fun num_ord (i,j) =
  (case int_ord (abs i, abs j) of
    EQUAL => int_ord (Int.sign i, Int.sign j)
  | ord => ord);

(*This resembles Term_Ord.term_ord, but it puts binary numerals before other
  non-atomic terms.*)
local open Term
in
fun numterm_ord (t, u) =
    case (try HOLogic.dest_number t, try HOLogic.dest_number u) of
      (SOME (_, i), SOME (_, j)) => num_ord (i, j)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | _ => (
      case (t, u) of
        (Abs (_, T, t), Abs(_, U, u)) =>
        (prod_ord numterm_ord Term_Ord.typ_ord ((t, T), (u, U)))
      | _ => (
        case int_ord (size_of_term t, size_of_term u) of
          EQUAL =>
          let val (f, ts) = strip_comb t and (g, us) = strip_comb u in
            (prod_ord Term_Ord.hd_ord numterms_ord ((f, ts), (g, us)))
          end
        | ord => ord))
and numterms_ord (ts, us) = list_ord numterm_ord (ts, us)
end;

val num_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context> |> Simplifier.set_term_ord numterm_ord);

(*Maps 1 to Numeral1 so that arithmetic isn't complicated by the abstract 1.*)
val numeral_syms = [@{thm numeral_One} RS sym];

(*Simplify 0+n, n+0, Numeral1*n, n*Numeral1, 1*x, x*1, x/1 *)
val add_0s =  @{thms add_0_left add_0_right};
val mult_1s = @{thms mult_1s divide_numeral_1 mult_1_left mult_1_right mult_minus1 mult_minus1_right div_by_1};

(* For post-simplification of the rhs of simproc-generated rules *)
val post_simps =
    [@{thm numeral_One},
     @{thm add_0_left}, @{thm add_0_right},
     @{thm mult_zero_left}, @{thm mult_zero_right},
     @{thm mult_1_left}, @{thm mult_1_right},
     @{thm mult_minus1}, @{thm mult_minus1_right}]

val field_post_simps =
    post_simps @ [@{thm div_0}, @{thm div_by_1}]

(*Simplify inverse Numeral1*)
val inverse_1s = [@{thm inverse_numeral_1}];

(*To perform binary arithmetic.  The "left" rewriting handles patterns
  created by the Numeral_Simprocs, such as 3 * (5 * x). *)
val simps =
    [@{thm numeral_One} RS sym] @
    @{thms add_numeral_left} @
    @{thms add_neg_numeral_left} @
    @{thms mult_numeral_left} @
    @{thms arith_simps} @ @{thms rel_simps};

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_simps =
  subtract Thm.eq_thm
    (@{thms add_numeral_left} @
     @{thms add_neg_numeral_left} @
     @{thms numeral_plus_numeral} @
     @{thms add_neg_numeral_simps}) simps;

(*To evaluate binary negations of coefficients*)
val minus_simps = [@{thm minus_zero}, @{thm minus_minus}];

(*To let us treat subtraction as addition*)
val diff_simps = [@{thm diff_conv_add_uminus}, @{thm minus_add_distrib}, @{thm minus_minus}];

(*To let us treat division as multiplication*)
val divide_simps = [@{thm divide_inverse}, @{thm inverse_mult_distrib}, @{thm inverse_inverse_eq}];

(*to extract again any uncancelled minuses*)
val minus_from_mult_simps =
    [@{thm minus_minus}, @{thm mult_minus_left}, @{thm mult_minus_right}];

(*combine unary minus with numeric literals, however nested within a product*)
val mult_minus_simps =
    [@{thm mult.assoc}, @{thm minus_mult_right}, @{thm minus_mult_commute}, @{thm numeral_times_minus_swap}];

val norm_ss1 =
  simpset_of (put_simpset num_ss \<^context>
    addsimps numeral_syms @ add_0s @ mult_1s @
    diff_simps @ minus_simps @ @{thms ac_simps})

val norm_ss2 =
  simpset_of (put_simpset num_ss \<^context>
    addsimps non_add_simps @ mult_minus_simps)

val norm_ss3 =
  simpset_of (put_simpset num_ss \<^context>
    addsimps minus_from_mult_simps @ @{thms ac_simps} @ @{thms ac_simps minus_mult_commute})

structure CancelNumeralsCommon =
struct
  val mk_sum = mk_sum
  val dest_sum = dest_sum
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff 1
  val find_first_coeff = find_first_coeff []
  val trans_tac = trans_tac

  fun norm_tac ctxt =
    ALLGOALS (simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss3 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps add_0s @ simps)
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq post_simps
  val prove_conv = Arith_Data.prove_conv
end;

structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> dummyT
  val bal_add1 = @{thm eq_add_iff1} RS trans
  val bal_add2 = @{thm eq_add_iff2} RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> dummyT
  val bal_add1 = @{thm less_add_iff1} RS trans
  val bal_add2 = @{thm less_add_iff2} RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> dummyT
  val bal_add1 = @{thm le_add_iff1} RS trans
  val bal_add2 = @{thm le_add_iff2} RS trans
);

val eq_cancel_numerals = EqCancelNumerals.proc
val less_cancel_numerals = LessCancelNumerals.proc
val le_cancel_numerals = LeCancelNumerals.proc

structure CombineNumeralsData =
struct
  type coeff = int
  val iszero = (fn x => x = 0)
  val add  = op +
  val mk_sum = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum = dest_sum
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff 1
  val left_distrib = @{thm combine_common_factor} RS trans
  val prove_conv = Arith_Data.prove_conv_nohyps
  val trans_tac = trans_tac

  fun norm_tac ctxt =
    ALLGOALS (simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss3 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps add_0s @ simps)
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq post_simps
end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

(*Version for fields, where coefficients can be fractions*)
structure FieldCombineNumeralsData =
struct
  type coeff = int * int
  val iszero = (fn (p, _) => p = 0)
  val add = add_frac
  val mk_sum = long_mk_sum
  val dest_sum = dest_sum
  val mk_coeff = mk_fcoeff
  val dest_coeff = dest_fcoeff 1
  val left_distrib = @{thm combine_common_factor} RS trans
  val prove_conv = Arith_Data.prove_conv_nohyps
  val trans_tac = trans_tac

  val norm_ss1a =
    simpset_of (put_simpset norm_ss1 \<^context> addsimps inverse_1s @ divide_simps)
  fun norm_tac ctxt =
    ALLGOALS (simp_tac (put_simpset norm_ss1a ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss3 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context>
      addsimps add_0s @ simps @ [@{thm add_frac_eq}, @{thm not_False_eq_True}])
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq field_post_simps
end;

structure FieldCombineNumerals = CombineNumeralsFun(FieldCombineNumeralsData);

val combine_numerals = CombineNumerals.proc

val field_combine_numerals = FieldCombineNumerals.proc


(** Constant folding for multiplication in semirings **)

(*We do not need folding for addition: combine_numerals does the same thing*)

structure Semiring_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val assoc_ss = simpset_of (put_simpset HOL_basic_ss \<^context> addsimps @{thms ac_simps minus_mult_commute})
  val eq_reflection = eq_reflection
  val is_numeral = can HOLogic.dest_number
end;

structure Semiring_Times_Assoc = Assoc_Fold (Semiring_Times_Assoc_Data);

fun assoc_fold ctxt ct = Semiring_Times_Assoc.proc ctxt (Thm.term_of ct)

structure CancelNumeralFactorCommon =
struct
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff 1
  val trans_tac = trans_tac

  val norm_ss1 =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps minus_from_mult_simps @ mult_1s)
  val norm_ss2 =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps simps @ mult_minus_simps)
  val norm_ss3 =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps @{thms ac_simps minus_mult_commute numeral_times_minus_swap})
  fun norm_tac ctxt =
    ALLGOALS (simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (simp_tac (put_simpset norm_ss3 ctxt))

  (* simp_thms are necessary because some of the cancellation rules below
  (e.g. mult_less_cancel_left) introduce various logical connectives *)
  val numeral_simp_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps simps @ @{thms simp_thms})
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq
    ([@{thm Nat.add_0}, @{thm Nat.add_0_right}] @ post_simps)
  val prove_conv = Arith_Data.prove_conv
end

(*Version for semiring_div*)
structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Rings.divide\<close> dummyT
  val cancel = @{thm div_mult_mult1} RS trans
  val neg_exchanges = false
)

(*Version for fields*)
structure DivideCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Rings.divide\<close> dummyT
  val cancel = @{thm mult_divide_mult_cancel_left} RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> dummyT
  val cancel = @{thm mult_cancel_left} RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> dummyT
  val cancel = @{thm mult_less_cancel_left} RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
(
  open CancelNumeralFactorCommon
  val mk_bal = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> dummyT
  val cancel = @{thm mult_le_cancel_left} RS trans
  val neg_exchanges = true
)

val eq_cancel_numeral_factor = EqCancelNumeralFactor.proc
val less_cancel_numeral_factor = LessCancelNumeralFactor.proc
val le_cancel_numeral_factor = LeCancelNumeralFactor.proc
val div_cancel_numeral_factor = DivCancelNumeralFactor.proc
val divide_cancel_numeral_factor = DivideCancelNumeralFactor.proc

val field_divide_cancel_numeral_factor =
  Simplifier.make_simproc \<^context> "field_divide_cancel_numeral_factor"
   {lhss =
     [\<^term>\<open>((l::'a::field) * m) / n\<close>,
      \<^term>\<open>(l::'a::field) / (m * n)\<close>,
      \<^term>\<open>((numeral v)::'a::field) / (numeral w)\<close>,
      \<^term>\<open>((numeral v)::'a::field) / (- numeral w)\<close>,
      \<^term>\<open>((- numeral v)::'a::field) / (numeral w)\<close>,
      \<^term>\<open>((- numeral v)::'a::field) / (- numeral w)\<close>],
    proc = K DivideCancelNumeralFactor.proc}

val field_cancel_numeral_factors =
  [Simplifier.make_simproc \<^context> "field_eq_cancel_numeral_factor"
    {lhss =
       [\<^term>\<open>(l::'a::field) * m = n\<close>,
        \<^term>\<open>(l::'a::field) = m * n\<close>],
      proc = K EqCancelNumeralFactor.proc},
   field_divide_cancel_numeral_factor]


(** Declarations for ExtractCommonTerm **)

(*Find first term that matches u*)
fun find_first_t past u []         = raise TERM ("find_first_t", [])
  | find_first_t past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first_t (t::past) u terms
        handle TERM _ => find_first_t (t::past) u terms;

(** Final simplification for the CancelFactor simprocs **)
val simplify_one = Arith_Data.simplify_meta_eq
  [@{thm mult_1_left}, @{thm mult_1_right}, @{thm div_by_1}, @{thm numeral_One}];

fun cancel_simplify_meta_eq ctxt cancel_th th =
    simplify_one ctxt (([th, cancel_th]) MRS trans);

local
  val Tp_Eq = Thm.reflexive (Thm.cterm_of \<^theory_context>\<open>HOL\<close> HOLogic.Trueprop)
  fun Eq_True_elim Eq =
    Thm.equal_elim (Thm.combination Tp_Eq (Thm.symmetric Eq)) @{thm TrueI}
in
fun sign_conv pos_th neg_th ctxt t =
  let val T = fastype_of t;
      val zero = Const(\<^const_name>\<open>Groups.zero\<close>, T);
      val less = Const(\<^const_name>\<open>Orderings.less\<close>, [T,T] ---> HOLogic.boolT);
      val pos = less $ zero $ t and neg = less $ t $ zero
      fun prove p =
        SOME (Eq_True_elim (Simplifier.asm_rewrite ctxt (Thm.cterm_of ctxt p)))
        handle THM _ => NONE
    in case prove pos of
         SOME th => SOME(th RS pos_th)
       | NONE => (case prove neg of
                    SOME th => SOME(th RS neg_th)
                  | NONE => NONE)
    end;
end

structure CancelFactorCommon =
struct
  val mk_sum = long_mk_prod
  val dest_sum = dest_prod
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff
  val find_first = find_first_t []
  val trans_tac = trans_tac
  val norm_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps mult_1s @ @{thms ac_simps minus_mult_commute})
  fun norm_tac ctxt =
    ALLGOALS (simp_tac (put_simpset norm_ss ctxt))
  val simplify_meta_eq  = cancel_simplify_meta_eq
  fun mk_eq (a, b) = HOLogic.mk_Trueprop (HOLogic.mk_eq (a, b))
end;

(*mult_cancel_left requires a ring with no zero divisors.*)
structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> dummyT
  fun simp_conv _ _ = SOME @{thm mult_cancel_left}
);

(*for ordered rings*)
structure LeCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> dummyT
  val simp_conv = sign_conv
    @{thm mult_le_cancel_left_pos} @{thm mult_le_cancel_left_neg}
);

(*for ordered rings*)
structure LessCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> dummyT
  val simp_conv = sign_conv
    @{thm mult_less_cancel_left_pos} @{thm mult_less_cancel_left_neg}
);

(*for semirings with division*)
structure DivCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Rings.divide\<close> dummyT
  fun simp_conv _ _ = SOME @{thm div_mult_mult1_if}
);

structure ModCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>modulo\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>modulo\<close> dummyT
  fun simp_conv _ _ = SOME @{thm mod_mult_mult1}
);

(*for idoms*)
structure DvdCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Rings.dvd\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Rings.dvd\<close> dummyT
  fun simp_conv _ _ = SOME @{thm dvd_mult_cancel_left}
);

(*Version for all fields, including unordered ones (type complex).*)
structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Rings.divide\<close> dummyT
  fun simp_conv _ _ = SOME @{thm mult_divide_mult_cancel_left_if}
);

fun eq_cancel_factor ctxt ct = EqCancelFactor.proc ctxt (Thm.term_of ct)
fun le_cancel_factor ctxt ct = LeCancelFactor.proc ctxt (Thm.term_of ct)
fun less_cancel_factor ctxt ct = LessCancelFactor.proc ctxt (Thm.term_of ct)
fun div_cancel_factor ctxt ct = DivCancelFactor.proc ctxt (Thm.term_of ct)
fun mod_cancel_factor ctxt ct = ModCancelFactor.proc ctxt (Thm.term_of ct)
fun dvd_cancel_factor ctxt ct = DvdCancelFactor.proc ctxt (Thm.term_of ct)
fun divide_cancel_factor ctxt ct = DivideCancelFactor.proc ctxt (Thm.term_of ct)

local

val cterm_of = Thm.cterm_of \<^context>;
fun tvar S = (("'a", 0), S);

val zero_tvar = tvar \<^sort>\<open>zero\<close>;
val zero = cterm_of (Const (\<^const_name>\<open>zero_class.zero\<close>, TVar zero_tvar));

val type_tvar = tvar \<^sort>\<open>type\<close>;
val geq = cterm_of (Const (\<^const_name>\<open>HOL.eq\<close>, TVar type_tvar --> TVar type_tvar --> \<^typ>\<open>bool\<close>));

val add_frac_eq = mk_meta_eq @{thm "add_frac_eq"}
val add_frac_num = mk_meta_eq @{thm "add_frac_num"}
val add_num_frac = mk_meta_eq @{thm "add_num_frac"}

fun prove_nz ctxt T t =
  let
    val z = Thm.instantiate_cterm (TVars.make [(zero_tvar, T)], Vars.empty) zero
    val eq = Thm.instantiate_cterm (TVars.make [(type_tvar, T)], Vars.empty) geq
    val th =
      Simplifier.rewrite (ctxt addsimps @{thms simp_thms})
        (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply \<^cterm>\<open>Not\<close>
          (Thm.apply (Thm.apply eq t) z)))
  in Thm.equal_elim (Thm.symmetric th) TrueI end

fun proc ctxt ct =
  let
    val ((x,y),(w,z)) =
         (Thm.dest_binop #> (fn (a,b) => (Thm.dest_binop a, Thm.dest_binop b))) ct
    val _ = map (HOLogic.dest_number o Thm.term_of) [x,y,z,w]
    val T = Thm.ctyp_of_cterm x
    val [y_nz, z_nz] = map (prove_nz ctxt T) [y, z]
    val th = Thm.instantiate' [SOME T] (map SOME [y,z,x,w]) add_frac_eq
  in SOME (Thm.implies_elim (Thm.implies_elim th y_nz) z_nz) end
  handle CTERM _ => NONE | TERM _ => NONE | THM _ => NONE

fun proc2 ctxt ct =
  let
    val (l,r) = Thm.dest_binop ct
    val T = Thm.ctyp_of_cterm l
  in (case (Thm.term_of l, Thm.term_of r) of
      (Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_, _) =>
        let val (x,y) = Thm.dest_binop l val z = r
            val _ = map (HOLogic.dest_number o Thm.term_of) [x,y,z]
            val ynz = prove_nz ctxt T y
        in SOME (Thm.implies_elim (Thm.instantiate' [SOME T] (map SOME [y,x,z]) add_frac_num) ynz)
        end
     | (_, Const (\<^const_name>\<open>Rings.divide\<close>,_)$_$_) =>
        let val (x,y) = Thm.dest_binop r val z = l
            val _ = map (HOLogic.dest_number o Thm.term_of) [x,y,z]
            val ynz = prove_nz ctxt T y
        in SOME (Thm.implies_elim (Thm.instantiate' [SOME T] (map SOME [y,z,x]) add_num_frac) ynz)
        end
     | _ => NONE)
  end
  handle CTERM _ => NONE | TERM _ => NONE | THM _ => NONE

fun is_number (Const(\<^const_name>\<open>Rings.divide\<close>,_)$a$b) = is_number a andalso is_number b
  | is_number t = can HOLogic.dest_number t

val is_number = is_number o Thm.term_of

fun proc3 ctxt ct =
  (case Thm.term_of ct of
    Const(\<^const_name>\<open>Orderings.less\<close>,_)$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_less_eq"}
      in SOME (mk_meta_eq th) end
  | Const(\<^const_name>\<open>Orderings.less_eq\<close>,_)$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_le_eq"}
      in SOME (mk_meta_eq th) end
  | Const(\<^const_name>\<open>HOL.eq\<close>,_)$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_eq_eq"}
      in SOME (mk_meta_eq th) end
  | Const(\<^const_name>\<open>Orderings.less\<close>,_)$_$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "less_divide_eq"}
      in SOME (mk_meta_eq th) end
  | Const(\<^const_name>\<open>Orderings.less_eq\<close>,_)$_$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "le_divide_eq"}
      in SOME (mk_meta_eq th) end
  | Const(\<^const_name>\<open>HOL.eq\<close>,_)$_$(Const(\<^const_name>\<open>Rings.divide\<close>,_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = Thm.ctyp_of_cterm c
        val th = Thm.instantiate' [SOME T] (map SOME [a,b,c]) @{thm "eq_divide_eq"}
      in SOME (mk_meta_eq th) end
  | _ => NONE) handle TERM _ => NONE | CTERM _ => NONE | THM _ => NONE

val add_frac_frac_simproc =
  Simplifier.make_simproc \<^context> "add_frac_frac_simproc"
   {lhss = [\<^term>\<open>(x::'a::field) / y + (w::'a::field) / z\<close>],
    proc = K proc}

val add_frac_num_simproc =
  Simplifier.make_simproc \<^context> "add_frac_num_simproc"
   {lhss = [\<^term>\<open>(x::'a::field) / y + z\<close>, \<^term>\<open>z + (x::'a::field) / y\<close>],
    proc = K proc2}

val ord_frac_simproc =
  Simplifier.make_simproc \<^context> "ord_frac_simproc"
   {lhss =
     [\<^term>\<open>(a::'a::{field,ord}) / b < c\<close>,
      \<^term>\<open>(a::'a::{field,ord}) / b \<le> c\<close>,
      \<^term>\<open>c < (a::'a::{field,ord}) / b\<close>,
      \<^term>\<open>c \<le> (a::'a::{field,ord}) / b\<close>,
      \<^term>\<open>c = (a::'a::{field,ord}) / b\<close>,
      \<^term>\<open>(a::'a::{field, ord}) / b = c\<close>],
    proc = K proc3}

val ths =
 [@{thm "mult_numeral_1"}, @{thm "mult_numeral_1_right"},
  @{thm "divide_numeral_1"},
  @{thm "div_by_0"}, @{thm div_0},
  @{thm "divide_divide_eq_left"},
  @{thm "times_divide_eq_left"}, @{thm "times_divide_eq_right"},
  @{thm "times_divide_times_eq"},
  @{thm "divide_divide_eq_right"},
  @{thm diff_conv_add_uminus}, @{thm "minus_divide_left"},
  @{thm "add_divide_distrib"} RS sym,
  @{thm Fields.field_divide_inverse} RS sym, @{thm inverse_divide},
  Conv.fconv_rule (Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv (mk_meta_eq @{thm mult.commute}))))
  (@{thm Fields.field_divide_inverse} RS sym)]

val field_comp_ss =
  simpset_of
    (put_simpset HOL_basic_ss \<^context>
      addsimps @{thms "semiring_norm"}
      addsimps ths addsimps @{thms simp_thms}
      addsimprocs field_cancel_numeral_factors
      addsimprocs [add_frac_frac_simproc, add_frac_num_simproc, ord_frac_simproc]
      |> Simplifier.add_cong @{thm "if_weak_cong"})

in

fun field_comp_conv ctxt =
  Simplifier.rewrite (put_simpset field_comp_ss ctxt)
  then_conv
  Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps [@{thm numeral_One}])

end

end;
