(*  Title:      HOL/Real/rat_arith0.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2004 University of Cambridge

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type rat.
*)

(*FIXME DELETE*)
val rat_mult_strict_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::rat")] mult_strict_left_mono;

val rat_mult_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::rat")] mult_left_mono;


val rat_number_of_def = thm "rat_number_of_def";
val diff_rat_def = thm "diff_rat_def";

val rat_of_int_zero = thm "rat_of_int_zero";
val rat_of_int_one = thm "rat_of_int_one";
val rat_of_int_add_distrib = thm "rat_of_int_add_distrib";
val rat_of_int_minus_distrib = thm "rat_of_int_minus_distrib";
val rat_of_int_diff_distrib = thm "rat_of_int_diff_distrib";
val rat_of_int_mult_distrib = thm "rat_of_int_mult_distrib";
val rat_inject = thm "rat_inject";
val rat_of_int_zero_cancel = thm "rat_of_int_zero_cancel";
val rat_of_int_less_iff = thm "rat_of_int_less_iff";
val rat_of_int_le_iff = thm "rat_of_int_le_iff";

val number_of_rat = thm "number_of_rat";
val rat_numeral_0_eq_0 = thm "rat_numeral_0_eq_0";
val rat_numeral_1_eq_1 = thm "rat_numeral_1_eq_1";
val add_rat_number_of = thm "add_rat_number_of";
val minus_rat_number_of = thm "minus_rat_number_of";
val diff_rat_number_of = thm "diff_rat_number_of";
val mult_rat_number_of = thm "mult_rat_number_of";
val rat_mult_2 = thm "rat_mult_2";
val rat_mult_2_right = thm "rat_mult_2_right";
val eq_rat_number_of = thm "eq_rat_number_of";
val less_rat_number_of = thm "less_rat_number_of";
val rat_minus_1_eq_m1 = thm "rat_minus_1_eq_m1";
val rat_mult_minus1 = thm "rat_mult_minus1";
val rat_mult_minus1_right = thm "rat_mult_minus1_right";
val rat_add_number_of_left = thm "rat_add_number_of_left";
val rat_mult_number_of_left = thm "rat_mult_number_of_left";
val rat_add_number_of_diff1 = thm "rat_add_number_of_diff1";
val rat_add_number_of_diff2 = thm "rat_add_number_of_diff2";

val rat_add_0_left = thm "rat_add_0_left";
val rat_add_0_right = thm "rat_add_0_right";
val rat_mult_1_left = thm "rat_mult_1_left";
val rat_mult_1_right = thm "rat_mult_1_right";

(*Maps 0 to Numeral0 and 1 to Numeral1 and -(Numeral1) to -1*)
val rat_numeral_ss =
    HOL_ss addsimps [rat_numeral_0_eq_0 RS sym, rat_numeral_1_eq_1 RS sym,
                     rat_minus_1_eq_m1];

fun rename_numerals th =
    asm_full_simplify rat_numeral_ss (Thm.transfer (the_context ()) th);


structure Rat_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [rat_numeral_0_eq_0 RS sym, rat_numeral_1_eq_1 RS sym];

(*Utilities*)

val ratT = Type("Rational.rat", []);

fun mk_numeral n = HOLogic.number_of_const ratT $ HOLogic.mk_bin n;

(*Decodes a binary rat constant, or 0, 1*)
val dest_numeral = Int_Numeral_Simprocs.dest_numeral;
val find_first_numeral = Int_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", ratT --> ratT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" ratT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" ratT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" ratT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, ts) = mk_times (mk_numeral k, ts);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const ("uminus", _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term.term_ord (dest_prod t)
        val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff 1 t
        in  if u aconv u' then (n, rev past @ terms)
                          else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify Numeral0+n, n+Numeral0, Numeral1*n, n*Numeral1*)
val add_0s  = map rename_numerals [rat_add_0_left, rat_add_0_right];
val mult_1s = map rename_numerals [rat_mult_1_left, rat_mult_1_right] @
              [rat_mult_minus1, rat_mult_minus1_right];

(*To perform binary arithmetic*)
val bin_simps =
    [rat_numeral_0_eq_0 RS sym, rat_numeral_1_eq_1 RS sym,
     add_rat_number_of, rat_add_number_of_left, minus_rat_number_of,
     diff_rat_number_of, mult_rat_number_of, rat_mult_number_of_left] @
    bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [rat_add_number_of_left, add_rat_number_of];

(*To evaluate binary negations of coefficients*)
val rat_minus_simps = NCons_simps @
                   [rat_minus_1_eq_m1, minus_rat_number_of,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [diff_rat_def, minus_add_distrib, minus_minus];

(*to extract again any uncancelled minuses*)
val rat_minus_from_mult_simps =
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val rat_mult_minus_simps =
    [mult_assoc, minus_mult_left, minus_mult_commute];

(*Apply the given rewrite (if present) just once*)
fun trans_tac None      = all_tac
  | trans_tac (Some th) = ALLGOALS (rtac (th RS trans));

(*Final simplification: cancel + and *  *)
val simplify_meta_eq =
    Int_Numeral_Simprocs.simplify_meta_eq
         [add_0, add_0_right,
          mult_zero_left, mult_zero_right, mult_1, mult_1_right];

fun prep_simproc (name, pats, proc) =
  Simplifier.simproc (Theory.sign_of (the_context ())) name pats proc;

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         rat_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@rat_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps rat_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" ratT
  val bal_add1 = eq_add_iff1 RS trans
  val bal_add2 = eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" ratT
  val bal_add1 = less_add_iff1 RS trans
  val bal_add2 = less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" ratT
  val bal_add1 = le_add_iff1 RS trans
  val bal_add2 = le_add_iff2 RS trans
);

val cancel_numerals =
  map prep_simproc
   [("rateq_cancel_numerals",
     ["(l::rat) + m = n", "(l::rat) = m + n",
      "(l::rat) - m = n", "(l::rat) = m - n",
      "(l::rat) * m = n", "(l::rat) = m * n"],
     EqCancelNumerals.proc),
    ("ratless_cancel_numerals",
     ["(l::rat) + m < n", "(l::rat) < m + n",
      "(l::rat) - m < n", "(l::rat) < m - n",
      "(l::rat) * m < n", "(l::rat) < m * n"],
     LessCancelNumerals.proc),
    ("ratle_cancel_numerals",
     ["(l::rat) + m <= n", "(l::rat) <= m + n",
      "(l::rat) - m <= n", "(l::rat) <= m - n",
      "(l::rat) * m <= n", "(l::rat) <= m * n"],
     LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = combine_common_factor RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                   diff_simps@rat_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@rat_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps rat_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  =
        Int_Numeral_Simprocs.simplify_meta_eq (add_0s@mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc ("rat_combine_numerals", ["(i::rat) + j", "(i::rat) - j"], CombineNumerals.proc);


(** Declarations for ExtractCommonTerm **)

(*this version ALWAYS includes a trailing one*)
fun long_mk_prod []        = one
  | long_mk_prod (t :: ts) = mk_times (t, mk_prod ts);

(*Find first term that matches u*)
fun find_first past u []         = raise TERM("find_first", [])
  | find_first past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first (t::past) u terms
        handle TERM _ => find_first (t::past) u terms;

(*Final simplification: cancel + and *  *)
fun cancel_simplify_meta_eq cancel_th th =
    Int_Numeral_Simprocs.simplify_meta_eq
        [rat_mult_1_left, rat_mult_1_right]
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure RatAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = rat_numeral_0_eq_0
  val numeral_1_eq_1  = rat_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure RatAbstractNumerals = AbstractNumeralsFun (RatAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("rat_add_eval_numerals",
     ["(m::rat) + 1", "(m::rat) + number_of v"],
     RatAbstractNumerals.proc add_rat_number_of),
    ("rat_diff_eval_numerals",
     ["(m::rat) - 1", "(m::rat) - number_of v"],
     RatAbstractNumerals.proc diff_rat_number_of),
    ("rat_eq_eval_numerals",
     ["(m::rat) = 0", "(m::rat) = 1", "(m::rat) = number_of v"],
     RatAbstractNumerals.proc eq_rat_number_of),
    ("rat_less_eval_numerals",
     ["(m::rat) < 0", "(m::rat) < 1", "(m::rat) < number_of v"],
     RatAbstractNumerals.proc less_rat_number_of),
    ("rat_le_eval_numerals",
     ["(m::rat) <= 0", "(m::rat) <= 1", "(m::rat) <= number_of v"],
     RatAbstractNumerals.proc le_number_of_eq_not_less)]

end;


Addsimprocs Rat_Numeral_Simprocs.eval_numerals;
Addsimprocs Rat_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Rat_Numeral_Simprocs.combine_numerals];



(** Constant folding for rat plus and times **)

(*We do not need
    structure Rat_Plus_Assoc = Assoc_Fold (Rat_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Rat_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = Rat_Numeral_Simprocs.ratT
  val plus   = Const ("op *", [Rat_Numeral_Simprocs.ratT,Rat_Numeral_Simprocs.ratT] ---> Rat_Numeral_Simprocs.ratT)
  val add_ac = mult_ac
end;

structure Rat_Times_Assoc = Assoc_Fold (Rat_Times_Assoc_Data);

Addsimprocs [Rat_Times_Assoc.conv];


(****Common factor cancellation****)

(*To quote from Provers/Arith/cancel_numeral_factor.ML:

This simproc Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

local
  open Rat_Numeral_Simprocs
in

val rel_rat_number_of = [eq_rat_number_of, less_rat_number_of,
                          le_number_of_eq_not_less]

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps rat_minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@rat_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  =
         ALLGOALS (simp_tac (HOL_ss addsimps rel_rat_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" Rat_Numeral_Simprocs.ratT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Rat_Numeral_Simprocs.ratT
  val cancel = mult_cancel_left RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" Rat_Numeral_Simprocs.ratT
  val cancel = mult_less_cancel_left RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" Rat_Numeral_Simprocs.ratT
  val cancel = mult_le_cancel_left RS trans
  val neg_exchanges = true
)

val rat_cancel_numeral_factors_relations =
  map prep_simproc
   [("rateq_cancel_numeral_factor",
     ["(l::rat) * m = n", "(l::rat) = m * n"],
     EqCancelNumeralFactor.proc),
    ("ratless_cancel_numeral_factor",
     ["(l::rat) * m < n", "(l::rat) < m * n"],
     LessCancelNumeralFactor.proc),
    ("ratle_cancel_numeral_factor",
     ["(l::rat) * m <= n", "(l::rat) <= m * n"],
     LeCancelNumeralFactor.proc)]

val rat_cancel_numeral_factors_divide = prep_simproc
        ("ratdiv_cancel_numeral_factor",
         ["((l::rat) * m) / n", "(l::rat) / (m * n)",
          "((number_of v)::rat) / (number_of w)"],
         DivCancelNumeralFactor.proc)

val rat_cancel_numeral_factors =
    rat_cancel_numeral_factors_relations @
    [rat_cancel_numeral_factors_divide]

end;

Addsimprocs rat_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "0 <= (y::rat) * -2";
test "9*x = 12 * (y::rat)";
test "(9*x) / (12 * (y::rat)) = z";
test "9*x < 12 * (y::rat)";
test "9*x <= 12 * (y::rat)";

test "-99*x = 132 * (y::rat)";
test "(-99*x) / (132 * (y::rat)) = z";
test "-99*x < 132 * (y::rat)";
test "-99*x <= 132 * (y::rat)";

test "999*x = -396 * (y::rat)";
test "(999*x) / (-396 * (y::rat)) = z";
test "999*x < -396 * (y::rat)";
test "999*x <= -396 * (y::rat)";

test  "(- ((2::rat) * x) <= 2 * y)";
test "-99*x = -81 * (y::rat)";
test "(-99*x) / (-81 * (y::rat)) = z";
test "-99*x <= -81 * (y::rat)";
test "-99*x < -81 * (y::rat)";

test "-2 * x = -1 * (y::rat)";
test "-2 * x = -(y::rat)";
test "(-2 * x) / (-1 * (y::rat)) = z";
test "-2 * x < -(y::rat)";
test "-2 * x <= -1 * (y::rat)";
test "-x < -23 * (y::rat)";
test "-x <= -23 * (y::rat)";
*)


(** Declarations for ExtractCommonTerm **)

local
  open Rat_Numeral_Simprocs
in

structure CancelFactorCommon =
  struct
  val mk_sum            = long_mk_prod
  val dest_sum          = dest_prod
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first        = find_first []
  val trans_tac         = trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@mult_ac))
  end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Rat_Numeral_Simprocs.ratT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_cancel_left
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" Rat_Numeral_Simprocs.ratT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
);

val rat_cancel_factor =
  map prep_simproc
   [("rat_eq_cancel_factor", ["(l::rat) * m = n", "(l::rat) = m * n"], EqCancelFactor.proc),
    ("rat_divide_cancel_factor", ["((l::rat) * m) / n", "(l::rat) / (m * n)"],
     DivideCancelFactor.proc)];

end;

Addsimprocs rat_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1));

test "x*k = k*(y::rat)";
test "k = k*(y::rat)";
test "a*(b*c) = (b::rat)";
test "a*(b*c) = d*(b::rat)*(x*a)";


test "(x*k) / (k*(y::rat)) = (uu::rat)";
test "(k) / (k*(y::rat)) = (uu::rat)";
test "(a*(b*c)) / ((b::rat)) = (uu::rat)";
test "(a*(b*c)) / (d*(b::rat)*(x*a)) = (uu::rat)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::rat)*(x*a)/z";
*)



(****Instantiation of the generic linear arithmetic package****)

val add_zero_left = thm"Ring_and_Field.add_0";
val add_zero_right = thm"Ring_and_Field.add_0_right";


local

(* reduce contradictory <= to False *)
val add_rules = 
    [order_less_irrefl, rat_numeral_0_eq_0, rat_numeral_1_eq_1,
     rat_minus_1_eq_m1, 
     add_rat_number_of, minus_rat_number_of, diff_rat_number_of,
     mult_rat_number_of, eq_rat_number_of, less_rat_number_of,
     le_number_of_eq_not_less, diff_minus,
     minus_add_distrib, minus_minus, mult_assoc, minus_zero,
     add_zero_left, add_zero_right, left_minus, right_minus,
     mult_zero_left, mult_zero_right, mult_1, mult_1_right,
     minus_mult_left RS sym, minus_mult_right RS sym];

val simprocs = [Rat_Times_Assoc.conv, Rat_Numeral_Simprocs.combine_numerals,
                rat_cancel_numeral_factors_divide]@
               Rat_Numeral_Simprocs.cancel_numerals @
               Rat_Numeral_Simprocs.eval_numerals;

val mono_ss = simpset() addsimps
                [add_mono,add_strict_mono,add_less_le_mono,add_le_less_mono];

val add_mono_thms_rat =
  map (fn s => prove_goal (the_context ()) s
                 (fn prems => [cut_facts_tac prems 1, asm_simp_tac mono_ss 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::rat)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::rat)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::rat)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::rat)",
     "(i < j) & (k = l)   ==> i + k < j + (l::rat)",
     "(i = j) & (k < l)   ==> i + k < j + (l::rat)",
     "(i < j) & (k <= l)  ==> i + k < j + (l::rat)",
     "(i <= j) & (k < l)  ==> i + k < j + (l::rat)",
     "(i < j) & (k < l)   ==> i + k < j + (l::rat)"];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val rat_mult_mono_thms =
 [(rat_mult_strict_left_mono,
   cvar(rat_mult_strict_left_mono, hd(tl(prems_of rat_mult_strict_left_mono)))),
  (rat_mult_left_mono,
   cvar(rat_mult_left_mono, hd(tl(prems_of rat_mult_left_mono))))]

(* reduce contradictory <= to False *)
val simps = [True_implies_equals,
             inst "a" "(number_of ?v)::rat" right_distrib,
             divide_1,times_divide_eq_right,times_divide_eq_left,
         rat_of_int_zero, rat_of_int_one, rat_of_int_add_distrib,
         rat_of_int_minus_distrib, rat_of_int_diff_distrib,
         rat_of_int_mult_distrib, number_of_rat RS sym];

in

val fast_rat_arith_simproc = Simplifier.simproc (Theory.sign_of (the_context ()))
  "fast_rat_arith" ["(m::rat) < n","(m::rat) <= n", "(m::rat) = n"]
  Fast_Arith.lin_arith_prover;

val int_inj_thms = [rat_of_int_le_iff RS iffD2, rat_of_int_less_iff RS iffD2,
                    rat_inject RS iffD2];

val rat_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_rat,
    mult_mono_thms = mult_mono_thms @ rat_mult_mono_thms,
    inj_thms = (***int_inj_thms @*???**)  inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the rats are dense!*)
    simpset = simpset addsimps add_rules
                      addsimps simps
                      addsimprocs simprocs}),
(*???
  arith_inj_const ("Rational.rat", HOLogic.intT --> Rat_Numeral_Simprocs.ratT),
???*)
  arith_discrete ("Rational.rat",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_rat_arith_simproc]];


end;


