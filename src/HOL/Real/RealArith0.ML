(*  Title:      HOL/Real/RealArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Common factor cancellation
*)

val real_diff_minus_eq = thm"real_diff_minus_eq";
val real_inverse_eq_divide = thm"real_inverse_eq_divide";
val real_0_le_divide_iff = thm"real_0_le_divide_iff";
val real_mult_less_cancel2 = thm"real_mult_less_cancel2";
val real_mult_le_cancel2 = thm"real_mult_le_cancel2";
val real_mult_less_cancel1 = thm"real_mult_less_cancel1";
val real_mult_le_cancel1 = thm"real_mult_le_cancel1";
val real_mult_eq_cancel1 = thm"real_mult_eq_cancel1";
val real_mult_eq_cancel2 = thm"real_mult_eq_cancel2";
val real_mult_div_cancel1 = thm"real_mult_div_cancel1";
val real_mult_div_cancel_disj = thm"real_mult_div_cancel_disj";


local
  open Real_Numeral_Simprocs
in

val rel_real_number_of = [eq_real_number_of, less_real_number_of,
                          le_real_number_of_eq_not_less]

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps real_minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@real_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps real_mult_ac))
  val numeral_simp_tac  =
         ALLGOALS (simp_tac (HOL_ss addsimps rel_real_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" HOLogic.realT
  val cancel = real_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val cancel = real_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.realT
  val cancel = real_mult_less_cancel1 RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.realT
  val cancel = real_mult_le_cancel1 RS trans
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
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@real_mult_ac))
  end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val simplify_meta_eq  = cancel_simplify_meta_eq real_mult_eq_cancel1
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" HOLogic.realT
  val simplify_meta_eq  = cancel_simplify_meta_eq real_mult_div_cancel_disj
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

val real_add_minus_iff = thm"real_add_minus_iff";
val real_add_eq_0_iff = thm"real_add_eq_0_iff";
val real_add_less_0_iff = thm"real_add_less_0_iff";
val real_0_less_add_iff = thm"real_0_less_add_iff";
val real_add_le_0_iff = thm"real_add_le_0_iff";
val real_0_le_add_iff = thm"real_0_le_add_iff";
val real_0_less_diff_iff = thm"real_0_less_diff_iff";
val real_0_le_diff_iff = thm"real_0_le_diff_iff";
val real_divide_eq_cancel2 = thm"real_divide_eq_cancel2";
val real_divide_eq_cancel1 = thm"real_divide_eq_cancel1";
val real_inverse_less_iff = thm"real_inverse_less_iff";
val real_inverse_le_iff = thm"real_inverse_le_iff";
val real_divide_1 = thm"real_divide_1";
val real_divide_minus1 = thm"real_divide_minus1";
val real_minus1_divide = thm"real_minus1_divide";
val real_lbound_gt_zero = thm"real_lbound_gt_zero";
val real_less_half_sum = thm"real_less_half_sum";
val real_gt_half_sum = thm"real_gt_half_sum";
val real_dense = thm"real_dense";

val pos_real_less_divide_eq = thm"pos_real_less_divide_eq";
val neg_real_less_divide_eq = thm"neg_real_less_divide_eq";
val pos_real_divide_less_eq = thm"pos_real_divide_less_eq";
val neg_real_divide_less_eq = thm"neg_real_divide_less_eq";
val pos_real_le_divide_eq = thm"pos_real_le_divide_eq";
val neg_real_le_divide_eq = thm"neg_real_le_divide_eq";
val pos_real_divide_le_eq = thm"pos_real_divide_le_eq";
val neg_real_divide_le_eq = thm"neg_real_divide_le_eq";
val real_eq_divide_eq = thm"real_eq_divide_eq";
val real_divide_eq_eq = thm"real_divide_eq_eq";
