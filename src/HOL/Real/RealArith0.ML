(*  Title:      HOL/Real/RealArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Common factor cancellation
*)

val real_diff_minus_eq = thm"real_diff_minus_eq";
val real_0_divide = thm"real_0_divide";
val real_0_less_inverse_iff = thm"real_0_less_inverse_iff";
val real_inverse_less_0_iff = thm"real_inverse_less_0_iff";
val real_0_le_inverse_iff = thm"real_0_le_inverse_iff";
val real_inverse_le_0_iff = thm"real_inverse_le_0_iff";
val real_inverse_eq_divide = thm"real_inverse_eq_divide";
val real_0_less_divide_iff = thm"real_0_less_divide_iff";
val real_divide_less_0_iff = thm"real_divide_less_0_iff";
val real_0_le_divide_iff = thm"real_0_le_divide_iff";
val real_divide_le_0_iff = thm"real_divide_le_0_iff";
val real_inverse_zero_iff = thm"real_inverse_zero_iff";
val real_divide_eq_0_iff = thm"real_divide_eq_0_iff";
val real_divide_self_eq = thm"real_divide_self_eq";
val real_minus_less_minus = thm"real_minus_less_minus";
val real_mult_less_mono1_neg = thm"real_mult_less_mono1_neg";
val real_mult_less_mono2_neg = thm"real_mult_less_mono2_neg";
val real_mult_le_mono1_neg = thm"real_mult_le_mono1_neg";
val real_mult_le_mono2_neg = thm"real_mult_le_mono2_neg";
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


(*** Simplification of inequalities involving literal divisors ***)

Goal "0<z ==> ((x::real) <= y/z) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1);
by (Asm_simp_tac 1);
qed "pos_real_le_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_real_le_divide_eq];

Goal "z<0 ==> ((x::real) <= y/z) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1);
by (Asm_simp_tac 1);
qed "neg_real_le_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_real_le_divide_eq];

Goal "0<z ==> (y/z <= (x::real)) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1);
by (Asm_simp_tac 1);
qed "pos_real_divide_le_eq";
Addsimps [inst "z" "number_of ?w" pos_real_divide_le_eq];

Goal "z<0 ==> (y/z <= (x::real)) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1);
by (Asm_simp_tac 1);
qed "neg_real_divide_le_eq";
Addsimps [inst "z" "number_of ?w" neg_real_divide_le_eq];

Goal "0<z ==> ((x::real) < y/z) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1);
by (Asm_simp_tac 1);
qed "pos_real_less_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_real_less_divide_eq];

Goal "z<0 ==> ((x::real) < y/z) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1);
by (Asm_simp_tac 1);
qed "neg_real_less_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_real_less_divide_eq];

Goal "0<z ==> (y/z < (x::real)) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1);
by (Asm_simp_tac 1);
qed "pos_real_divide_less_eq";
Addsimps [inst "z" "number_of ?w" pos_real_divide_less_eq];

Goal "z<0 ==> (y/z < (x::real)) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1);
by (Asm_simp_tac 1);
qed "neg_real_divide_less_eq";
Addsimps [inst "z" "number_of ?w" neg_real_divide_less_eq];

Goal "z~=0 ==> ((x::real) = y/z) = (x*z = y)";
by (subgoal_tac "(x*z = y) = (x*z = (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_eq_cancel2 1);
by (Asm_simp_tac 1);
qed "real_eq_divide_eq";
Addsimps [inst "z" "number_of ?w" real_eq_divide_eq];

Goal "z~=0 ==> (y/z = (x::real)) = (y = x*z)";
by (subgoal_tac "(y = x*z) = ((y/z)*z = x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2);
by (etac ssubst 1);
by (stac real_mult_eq_cancel2 1);
by (Asm_simp_tac 1);
qed "real_divide_eq_eq";
Addsimps [inst "z" "number_of ?w" real_divide_eq_eq];

Goal "(m/k = n/k) = (k = 0 | m = (n::real))";
by (case_tac "k=0" 1);
by (asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO]) 1);
by (asm_simp_tac (simpset() addsimps [real_divide_eq_eq, real_eq_divide_eq,
                                      real_mult_eq_cancel2]) 1);
qed "real_divide_eq_cancel2";

Goal "(k/m = k/n) = (k = 0 | m = (n::real))";
by (case_tac "m=0 | n = 0" 1);
by (auto_tac (claset(),
              simpset() addsimps [DIVISION_BY_ZERO, real_divide_eq_eq,
                                  real_eq_divide_eq, real_mult_eq_cancel1]));
qed "real_divide_eq_cancel1";

Goal "[| 0 < r; 0 < x|] ==> (inverse x < inverse (r::real)) = (r < x)";
by (auto_tac (claset() addIs [real_inverse_less_swap], simpset()));
qed "real_inverse_less_iff";

Goal "[| 0 < r; 0 < x|] ==> (inverse x <= inverse r) = (r <= (x::real))";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
                                      real_inverse_less_iff]) 1);
qed "real_inverse_le_iff";

(** Division by 1, -1 **)

Goal "(x::real)/1 = x";
by (simp_tac (simpset() addsimps [real_divide_def]) 1);
qed "real_divide_1";
Addsimps [real_divide_1];

Goal "x/-1 = -(x::real)";
by (Simp_tac 1);
qed "real_divide_minus1";
Addsimps [real_divide_minus1];

Goal "-1/(x::real) = - (1/x)";
by (simp_tac (simpset() addsimps [real_divide_def, real_minus_inverse]) 1);
qed "real_minus1_divide";
Addsimps [real_minus1_divide];

Goal "[| (0::real) < d1; 0 < d2 |] ==> EX e. 0 < e & e < d1 & e < d2";
by (res_inst_tac [("x","(min d1 d2)/2")] exI 1);
by (asm_simp_tac (simpset() addsimps [min_def]) 1);
qed "real_lbound_gt_zero";

Goal "(inverse x = inverse y) = (x = (y::real))";
by (case_tac "x=0 | y=0" 1);
by (auto_tac (claset(),
              simpset() addsimps [real_inverse_eq_divide,
                                  DIVISION_BY_ZERO]));
by (dres_inst_tac [("f","%u. x*y*u")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "real_inverse_eq_iff";
Addsimps [real_inverse_eq_iff];

Goal "(z/x = z/y) = (z = 0 | x = (y::real))";
by (case_tac "x=0 | y=0" 1);
by (auto_tac (claset(),
              simpset() addsimps [DIVISION_BY_ZERO]));
by (dres_inst_tac [("f","%u. x*y*u")] arg_cong 1);
by Auto_tac;
qed "real_divide_eq_iff";
Addsimps [real_divide_eq_iff];


(*** General rewrites to improve automation, like those for type "int" ***)

(** The next several equations can make the simplifier loop! **)

Goal "(x < - y) = (y < - (x::real))";
by Auto_tac;
qed "real_less_minus";

Goal "(- x < y) = (- y < (x::real))";
by Auto_tac;
qed "real_minus_less";

Goal "(x <= - y) = (y <= - (x::real))";
by Auto_tac;
qed "real_le_minus";

Goal "(- x <= y) = (- y <= (x::real))";
by Auto_tac;
qed "real_minus_le";

Goal "(x = - y) = (y = - (x::real))";
by Auto_tac;
qed "real_equation_minus";

Goal "(- x = y) = (- (y::real) = x)";
by Auto_tac;
qed "real_minus_equation";


Goal "(x + - a = (0::real)) = (x=a)";
by (arith_tac 1);
qed "real_add_minus_iff";
Addsimps [real_add_minus_iff];

Goal "(-b = -a) = (b = (a::real))";
by (arith_tac 1);
qed "real_minus_eq_cancel";
Addsimps [real_minus_eq_cancel];


(*Distributive laws for literals*)
Addsimps (map (inst "w" "number_of ?v")
          [real_add_mult_distrib, real_add_mult_distrib2,
           real_diff_mult_distrib, real_diff_mult_distrib2]);

Addsimps (map (inst "x" "number_of ?v")
          [real_less_minus, real_le_minus, real_equation_minus]);
Addsimps (map (inst "y" "number_of ?v")
          [real_minus_less, real_minus_le, real_minus_equation]);

(*Equations and inequations involving 1*)
Addsimps (map (simplify (simpset()) o inst "x" "1")
          [real_less_minus, real_le_minus, real_equation_minus]);
Addsimps (map (simplify (simpset()) o inst "y" "1")
          [real_minus_less, real_minus_le, real_minus_equation]);

(*** Simprules combining x+y and 0 ***)

Goal "(x+y = (0::real)) = (y = -x)";
by Auto_tac;
qed "real_add_eq_0_iff";
AddIffs [real_add_eq_0_iff];

Goal "(x+y < (0::real)) = (y < -x)";
by Auto_tac;
qed "real_add_less_0_iff";
AddIffs [real_add_less_0_iff];

Goal "((0::real) < x+y) = (-x < y)";
by Auto_tac;
qed "real_0_less_add_iff";
AddIffs [real_0_less_add_iff];

Goal "(x+y <= (0::real)) = (y <= -x)";
by Auto_tac;
qed "real_add_le_0_iff";
AddIffs [real_add_le_0_iff];

Goal "((0::real) <= x+y) = (-x <= y)";
by Auto_tac;
qed "real_0_le_add_iff";
AddIffs [real_0_le_add_iff];


(** Simprules combining x-y and 0; see also real_less_iff_diff_less_0, etc.,
    in RealBin
**)

Goal "((0::real) < x-y) = (y < x)";
by Auto_tac;
qed "real_0_less_diff_iff";
AddIffs [real_0_less_diff_iff];

Goal "((0::real) <= x-y) = (y <= x)";
by Auto_tac;
qed "real_0_le_diff_iff";
AddIffs [real_0_le_diff_iff];

(*
FIXME: we should have this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric real_diff_def];
*)

Goal "-(x-y) = y - (x::real)";
by (arith_tac 1);
qed "real_minus_diff_eq";
Addsimps [real_minus_diff_eq];


(*** Density of the Reals ***)

Goal "x < y ==> x < (x+y) / (2::real)";
by Auto_tac;
qed "real_less_half_sum";

Goal "x < y ==> (x+y)/(2::real) < y";
by Auto_tac;
qed "real_gt_half_sum";

Goal "x < y ==> EX r::real. x < r & r < y";
by (blast_tac (claset() addSIs [real_less_half_sum, real_gt_half_sum]) 1);
qed "real_dense";


(*Replaces "inverse #nn" by 1/#nn *)
Addsimps [inst "x" "number_of ?w" real_inverse_eq_divide];


