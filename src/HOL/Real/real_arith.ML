(*  Title:      HOL/Real/real_arith0.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type real.
*)

(*FIXME DELETE*)
val real_mult_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::real")] mult_left_mono;

val real_numeral_0_eq_0 = thm "real_numeral_0_eq_0";
val real_numeral_1_eq_1 = thm "real_numeral_1_eq_1";
val real_number_of_def = thm "real_number_of_def";
val add_real_number_of = thm "add_real_number_of";
val minus_real_number_of = thm "minus_real_number_of";
val diff_real_number_of = thm "diff_real_number_of";
val mult_real_number_of = thm "mult_real_number_of";
val real_mult_2 = thm "real_mult_2";
val real_mult_2_right = thm "real_mult_2_right";
val eq_real_number_of = thm "eq_real_number_of";
val less_real_number_of = thm "less_real_number_of";
val real_minus_1_eq_m1 = thm "real_minus_1_eq_m1";
val real_mult_minus1 = thm "real_mult_minus1";
val real_mult_minus1_right = thm "real_mult_minus1_right";
val zero_less_real_of_nat_iff = thm "zero_less_real_of_nat_iff";
val zero_le_real_of_nat_iff = thm "zero_le_real_of_nat_iff";
val real_add_number_of_left = thm "real_add_number_of_left";
val real_mult_number_of_left = thm "real_mult_number_of_left";
val real_add_number_of_diff1 = thm "real_add_number_of_diff1";
val real_add_number_of_diff2 = thm "real_add_number_of_diff2";
val real_of_nat_number_of = thm "real_of_nat_number_of";

(*Maps 0 to Numeral0 and 1 to Numeral1 and -(Numeral1) to -1*)
val real_numeral_ss =
    HOL_ss addsimps [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym,
                     real_minus_1_eq_m1];

fun rename_numerals th =
    asm_full_simplify real_numeral_ss (Thm.transfer (the_context ()) th);


structure Real_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym];

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.realT $ HOLogic.mk_bin n;

(*Decodes a binary real constant, or 0, 1*)
val dest_numeral = Int_Numeral_Simprocs.dest_numeral;
val find_first_numeral = Int_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", HOLogic.realT --> HOLogic.realT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.realT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" HOLogic.realT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.realT;

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
val add_0s  = map rename_numerals [real_add_zero_left, real_add_zero_right];
val mult_1s = map rename_numerals [real_mult_1, real_mult_1_right] @
              [real_mult_minus1, real_mult_minus1_right];

(*To perform binary arithmetic*)
val bin_simps =
    [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym,
     add_real_number_of, real_add_number_of_left, minus_real_number_of,
     diff_real_number_of, mult_real_number_of, real_mult_number_of_left] @
    bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [real_add_number_of_left, add_real_number_of];

(*To evaluate binary negations of coefficients*)
val real_minus_simps = NCons_simps @
                   [real_minus_1_eq_m1, minus_real_number_of,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [real_diff_def, minus_add_distrib, minus_minus];

(*to extract again any uncancelled minuses*)
val real_minus_from_mult_simps =
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val real_mult_minus_simps =
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
                                         real_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@real_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps real_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val bal_add1 = eq_add_iff1 RS trans
  val bal_add2 = eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.realT
  val bal_add1 = less_add_iff1 RS trans
  val bal_add2 = less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.realT
  val bal_add1 = le_add_iff1 RS trans
  val bal_add2 = le_add_iff2 RS trans
);

val cancel_numerals =
  map prep_simproc
   [("realeq_cancel_numerals",
     ["(l::real) + m = n", "(l::real) = m + n",
      "(l::real) - m = n", "(l::real) = m - n",
      "(l::real) * m = n", "(l::real) = m * n"],
     EqCancelNumerals.proc),
    ("realless_cancel_numerals",
     ["(l::real) + m < n", "(l::real) < m + n",
      "(l::real) - m < n", "(l::real) < m - n",
      "(l::real) * m < n", "(l::real) < m * n"],
     LessCancelNumerals.proc),
    ("realle_cancel_numerals",
     ["(l::real) + m <= n", "(l::real) <= m + n",
      "(l::real) - m <= n", "(l::real) <= m - n",
      "(l::real) * m <= n", "(l::real) <= m * n"],
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
                                   diff_simps@real_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@real_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps real_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  =
        Int_Numeral_Simprocs.simplify_meta_eq (add_0s@mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc ("real_combine_numerals", ["(i::real) + j", "(i::real) - j"], CombineNumerals.proc);


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
        [real_mult_1, real_mult_1_right]
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure RealAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = real_numeral_0_eq_0
  val numeral_1_eq_1  = real_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure RealAbstractNumerals = AbstractNumeralsFun (RealAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("real_add_eval_numerals",
     ["(m::real) + 1", "(m::real) + number_of v"],
     RealAbstractNumerals.proc add_real_number_of),
    ("real_diff_eval_numerals",
     ["(m::real) - 1", "(m::real) - number_of v"],
     RealAbstractNumerals.proc diff_real_number_of),
    ("real_eq_eval_numerals",
     ["(m::real) = 0", "(m::real) = 1", "(m::real) = number_of v"],
     RealAbstractNumerals.proc eq_real_number_of),
    ("real_less_eval_numerals",
     ["(m::real) < 0", "(m::real) < 1", "(m::real) < number_of v"],
     RealAbstractNumerals.proc less_real_number_of),
    ("real_le_eval_numerals",
     ["(m::real) <= 0", "(m::real) <= 1", "(m::real) <= number_of v"],
     RealAbstractNumerals.proc le_number_of_eq_not_less)]

end;


Addsimprocs Real_Numeral_Simprocs.eval_numerals;
Addsimprocs Real_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Real_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::real)";

test "2*u = (u::real)";
test "(i + j + 12 + (k::real)) - 15 = y";
test "(i + j + 12 + (k::real)) - 5 = y";

test "y - b < (b::real)";
test "y - (3*b + c) < (b::real) - 2*c";

test "(2*x - (u*v) + y) - v*3*u = (w::real)";
test "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::real)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::real)";
test "u*v - (x*u*v + (u*v)*4 + y) = (w::real)";

test "(i + j + 12 + (k::real)) = u + 15 + y";
test "(i + j*2 + 12 + (k::real)) = j + 5 + y";

test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::real)";

test "a + -(b+c) + b = (d::real)";
test "a + -(b+c) - b = (d::real)";

(*negative numerals*)
test "(i + j + -2 + (k::real)) - (u + 5 + y) = zz";
test "(i + j + -3 + (k::real)) < u + 5 + y";
test "(i + j + 3 + (k::real)) < u + -6 + y";
test "(i + j + -12 + (k::real)) - 15 = y";
test "(i + j + 12 + (k::real)) - -15 = y";
test "(i + j + -12 + (k::real)) - -15 = y";
*)


(** Constant folding for real plus and times **)

(*We do not need
    structure Real_Plus_Assoc = Assoc_Fold (Real_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Real_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = HOLogic.realT
  val plus   = Const ("op *", [HOLogic.realT,HOLogic.realT] ---> HOLogic.realT)
  val add_ac = mult_ac
end;

structure Real_Times_Assoc = Assoc_Fold (Real_Times_Assoc_Data);

Addsimprocs [Real_Times_Assoc.conv];


(****Common factor cancellation****)

(*To quote from Provers/Arith/cancel_numeral_factor.ML:

This simproc Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

local
  open Real_Numeral_Simprocs
in

val rel_real_number_of = [eq_real_number_of, less_real_number_of,
                          le_number_of_eq_not_less]

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps real_minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@real_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  =
         ALLGOALS (simp_tac (HOL_ss addsimps rel_real_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" HOLogic.realT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val cancel = mult_cancel_left RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.realT
  val cancel = mult_less_cancel_left RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.realT
  val cancel = mult_le_cancel_left RS trans
  val neg_exchanges = true
)

val real_cancel_numeral_factors_relations =
  map prep_simproc
   [("realeq_cancel_numeral_factor",
     ["(l::real) * m = n", "(l::real) = m * n"],
     EqCancelNumeralFactor.proc),
    ("realless_cancel_numeral_factor",
     ["(l::real) * m < n", "(l::real) < m * n"],
     LessCancelNumeralFactor.proc),
    ("realle_cancel_numeral_factor",
     ["(l::real) * m <= n", "(l::real) <= m * n"],
     LeCancelNumeralFactor.proc)]

val real_cancel_numeral_factors_divide = prep_simproc
        ("realdiv_cancel_numeral_factor",
         ["((l::real) * m) / n", "(l::real) / (m * n)",
          "((number_of v)::real) / (number_of w)"],
         DivCancelNumeralFactor.proc)

val real_cancel_numeral_factors =
    real_cancel_numeral_factors_relations @
    [real_cancel_numeral_factors_divide]

end;

Addsimprocs real_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "0 <= (y::real) * -2";
test "9*x = 12 * (y::real)";
test "(9*x) / (12 * (y::real)) = z";
test "9*x < 12 * (y::real)";
test "9*x <= 12 * (y::real)";

test "-99*x = 132 * (y::real)";
test "(-99*x) / (132 * (y::real)) = z";
test "-99*x < 132 * (y::real)";
test "-99*x <= 132 * (y::real)";

test "999*x = -396 * (y::real)";
test "(999*x) / (-396 * (y::real)) = z";
test "999*x < -396 * (y::real)";
test "999*x <= -396 * (y::real)";

test  "(- ((2::real) * x) <= 2 * y)";
test "-99*x = -81 * (y::real)";
test "(-99*x) / (-81 * (y::real)) = z";
test "-99*x <= -81 * (y::real)";
test "-99*x < -81 * (y::real)";

test "-2 * x = -1 * (y::real)";
test "-2 * x = -(y::real)";
test "(-2 * x) / (-1 * (y::real)) = z";
test "-2 * x < -(y::real)";
test "-2 * x <= -1 * (y::real)";
test "-x < -23 * (y::real)";
test "-x <= -23 * (y::real)";
*)


(** Declarations for ExtractCommonTerm **)

local
  open Real_Numeral_Simprocs
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
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_cancel_left
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" HOLogic.realT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
);

val real_cancel_factor =
  map prep_simproc
   [("real_eq_cancel_factor", ["(l::real) * m = n", "(l::real) = m * n"], EqCancelFactor.proc),
    ("real_divide_cancel_factor", ["((l::real) * m) / n", "(l::real) / (m * n)"],
     DivideCancelFactor.proc)];

end;

Addsimprocs real_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1));

test "x*k = k*(y::real)";
test "k = k*(y::real)";
test "a*(b*c) = (b::real)";
test "a*(b*c) = d*(b::real)*(x*a)";


test "(x*k) / (k*(y::real)) = (uu::real)";
test "(k) / (k*(y::real)) = (uu::real)";
test "(a*(b*c)) / ((b::real)) = (uu::real)";
test "(a*(b*c)) / (d*(b::real)*(x*a)) = (uu::real)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::real)*(x*a)/z";
*)



(****Instantiation of the generic linear arithmetic package****)

local

(* reduce contradictory <= to False *)
val add_rules = 
    [real_numeral_0_eq_0, real_numeral_1_eq_1,
     add_real_number_of, minus_real_number_of, diff_real_number_of,
     mult_real_number_of, eq_real_number_of, less_real_number_of];

val simprocs = [Real_Times_Assoc.conv, Real_Numeral_Simprocs.combine_numerals,
                real_cancel_numeral_factors_divide]@
               Real_Numeral_Simprocs.cancel_numerals @
               Real_Numeral_Simprocs.eval_numerals;

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_left_mono,
   cvar(real_mult_left_mono, hd(tl(prems_of real_mult_left_mono))))]

val simps = [real_of_nat_zero, real_of_nat_Suc, real_of_nat_add, 
       real_of_nat_mult, real_of_int_zero, real_of_one, real_of_int_add RS sym,
       real_of_int_minus RS sym, real_of_int_diff RS sym,
       real_of_int_mult RS sym, symmetric real_number_of_def];

val int_inj_thms = [real_of_int_le_iff RS iffD2, real_of_int_less_iff RS iffD2,
                    real_of_int_inject RS iffD2];

val nat_inj_thms = [real_of_nat_le_iff RS iffD2, real_of_nat_less_iff RS iffD2,
                    real_of_nat_inject RS iffD2];

in

val fast_real_arith_simproc = Simplifier.simproc (Theory.sign_of (the_context ()))
  "fast_real_arith" ["(m::real) < n","(m::real) <= n", "(m::real) = n"]
  Fast_Arith.lin_arith_prover;

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = int_inj_thms @ nat_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the reals are dense!*)
    simpset = simpset addsimps add_rules
                      addsimps simps
                      addsimprocs simprocs}),
  arith_inj_const ("RealDef.real", HOLogic.natT --> HOLogic.realT),
  arith_inj_const ("RealDef.real", HOLogic.intT --> HOLogic.realT),
  arith_discrete ("RealDef.real",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_real_arith_simproc]];

(* some thms for injection nat => real:
real_of_nat_zero
?zero_eq_numeral_0
real_of_nat_add
*)

end;


(* Some test data [omitting examples that assume the ordering to be discrete!]
Goal "!!a::real. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b <= i+j; a<=b; i<=j |] ==> a+a <= j+j";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> 6*a <= 5*l+i";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a < b+(1::real)";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a-(3::real) < b";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a-(1::real) < b";
by (fast_arith_tac 1);
qed "";

*)



