(*  Title:      HOL/Real/real_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Simprocs: Common factor cancellation & Rational coefficient handling
*)


(** Misc ML bindings **)

val inverse_less_iff_less = thm"Ring_and_Field.inverse_less_iff_less";
val add_right_mono = thm"Ring_and_Field.add_right_mono";
val times_divide_eq_left = thm "times_divide_eq_left";
val times_divide_eq_right = thm "times_divide_eq_right";
val inverse_mult_distrib = thm "inverse_mult_distrib";
val minus_minus = thm "minus_minus";
val left_inverse = thm "left_inverse";
val right_inverse = thm "right_inverse";
val inverse_minus_eq = thm "inverse_minus_eq";
val minus_mult_left = thm "minus_mult_left";
val minus_mult_right = thm "minus_mult_right";

val pos_real_less_divide_eq = thm"pos_less_divide_eq";
val pos_real_divide_less_eq = thm"pos_divide_less_eq";
val pos_real_le_divide_eq = thm"pos_le_divide_eq";
val pos_real_divide_le_eq = thm"pos_divide_le_eq";


(****Common factor cancellation****)

(*To quote from Provers/Arith/cancel_numeral_factor.ML:

This simproc Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

val inverse_eq_divide = thm"Ring_and_Field.inverse_eq_divide";

val mult_less_cancel_left = thm"Ring_and_Field.mult_less_cancel_left";
val mult_le_cancel_left = thm"Ring_and_Field.mult_le_cancel_left";
val mult_less_cancel_right = thm"Ring_and_Field.mult_less_cancel_right";
val mult_le_cancel_right = thm"Ring_and_Field.mult_le_cancel_right";
val mult_cancel_left = thm"Ring_and_Field.mult_cancel_left";
val mult_cancel_right = thm"Ring_and_Field.mult_cancel_right";

val mult_divide_cancel_left = thm"Ring_and_Field.mult_divide_cancel_left";
val mult_divide_cancel_eq_if = thm"Ring_and_Field.mult_divide_cancel_eq_if";


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
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@real_mult_ac))
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

(****Augmentation of real linear arithmetic with 
     rational coefficient handling****)

val divide_1 = thm"divide_1";

val times_divide_eq_left = thm"times_divide_eq_left";
val times_divide_eq_right = thm"times_divide_eq_right";

local

(* reduce contradictory <= to False *)
val simps = [True_implies_equals,
             inst "w" "number_of ?v" real_add_mult_distrib2,
             divide_1,times_divide_eq_right,times_divide_eq_left];

val simprocs = [real_cancel_numeral_factors_divide,
                real_cancel_numeral_factors_divide];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_le_mono2,
   cvar(real_mult_le_mono2, hd(tl(prems_of real_mult_le_mono2))))]

in

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = inj_thms,
    lessD = lessD,
    simpset = simpset addsimps simps addsimprocs simprocs})];

end;

(*
Procedure "assoc_fold" needed?
*)
