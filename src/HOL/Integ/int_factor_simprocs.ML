(*  Title:      HOL/int_factor_simprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Factor cancellation simprocs for the integers (and for fields).

This file can't be combined with int_arith1 because it requires IntDiv.thy.
*)


(*To quote from Provers/Arith/cancel_numeral_factor.ML:

Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

val rel_number_of = [eq_number_of_eq, less_number_of_eq_neg, le_number_of_eq];

(** Factor cancellation theorems for integer division (div, not /) **)

Goal "!!k::int. k~=0 ==> (k*m) div (k*n) = (m div n)";
by (stac zdiv_zmult_zmult1 1);
by Auto_tac;
qed "int_mult_div_cancel1";

(*For ExtractCommonTermFun, cancelling common factors*)
Goal "(k*m) div (k*n) = (if k = (0::int) then 0 else m div n)";
by (simp_tac (simpset() addsimps [int_mult_div_cancel1]) 1);
qed "int_mult_div_cancel_disj";


local
  open Int_Numeral_Simprocs
in

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  =
         ALLGOALS (simp_tac (HOL_ss addsimps rel_number_of@bin_simps))
  val simplify_meta_eq  = 
	Int_Numeral_Simprocs.simplify_meta_eq
	     [add_0, add_0_right,
	      mult_zero_left, mult_zero_right, mult_1, mult_1_right];
  end

(*Version for integer division*)
structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.intT
  val cancel = int_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

(*Version for fields*)
structure FieldDivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" Term.dummyT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)

(*Version for ordered rings: mult_cancel_left requires an ordering*)
structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val cancel = mult_cancel_left RS trans
  val neg_exchanges = false
)

(*Version for (unordered) fields*)
structure FieldEqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val cancel = field_mult_cancel_left RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" Term.dummyT
  val cancel = mult_less_cancel_left RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" Term.dummyT
  val cancel = mult_le_cancel_left RS trans
  val neg_exchanges = true
)

val ring_cancel_numeral_factors =
  map Bin_Simprocs.prep_simproc
   [("ring_eq_cancel_numeral_factor",
     ["(l::'a::{ordered_ring,number_ring}) * m = n",
      "(l::'a::{ordered_ring,number_ring}) = m * n"],
     EqCancelNumeralFactor.proc),
    ("ring_less_cancel_numeral_factor",
     ["(l::'a::{ordered_ring,number_ring}) * m < n",
      "(l::'a::{ordered_ring,number_ring}) < m * n"],
     LessCancelNumeralFactor.proc),
    ("ring_le_cancel_numeral_factor",
     ["(l::'a::{ordered_ring,number_ring}) * m <= n",
      "(l::'a::{ordered_ring,number_ring}) <= m * n"],
     LeCancelNumeralFactor.proc),
    ("int_div_cancel_numeral_factors",
     ["((l::int) * m) div n", "(l::int) div (m * n)"],
     DivCancelNumeralFactor.proc)];


val field_cancel_numeral_factors =
  map Bin_Simprocs.prep_simproc
   [("field_eq_cancel_numeral_factor",
     ["(l::'a::{field,number_ring}) * m = n",
      "(l::'a::{field,number_ring}) = m * n"],
     FieldEqCancelNumeralFactor.proc),
    ("field_cancel_numeral_factor",
     ["((l::'a::{field,number_ring}) * m) / n",
      "(l::'a::{field,number_ring}) / (m * n)",
      "((number_of v)::'a::{field,number_ring}) / (number_of w)"],
     FieldDivCancelNumeralFactor.proc)]

end;

Addsimprocs ring_cancel_numeral_factors;
Addsimprocs field_cancel_numeral_factors;

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "9*x = 12 * (y::int)";
test "(9*x) div (12 * (y::int)) = z";
test "9*x < 12 * (y::int)";
test "9*x <= 12 * (y::int)";

test "-99*x = 132 * (y::int)";
test "(-99*x) div (132 * (y::int)) = z";
test "-99*x < 132 * (y::int)";
test "-99*x <= 132 * (y::int)";

test "999*x = -396 * (y::int)";
test "(999*x) div (-396 * (y::int)) = z";
test "999*x < -396 * (y::int)";
test "999*x <= -396 * (y::int)";

test "-99*x = -81 * (y::int)";
test "(-99*x) div (-81 * (y::int)) = z";
test "-99*x <= -81 * (y::int)";
test "-99*x < -81 * (y::int)";

test "-2 * x = -1 * (y::int)";
test "-2 * x = -(y::int)";
test "(-2 * x) div (-1 * (y::int)) = z";
test "-2 * x < -(y::int)";
test "-2 * x <= -1 * (y::int)";
test "-x < -23 * (y::int)";
test "-x <= -23 * (y::int)";
*)

(*And the same examples for fields such as rat or real:
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
  open Int_Numeral_Simprocs
in

(*Find first term that matches u*)
fun find_first past u []         = raise TERM("find_first", [])
  | find_first past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first (t::past) u terms
        handle TERM _ => find_first (t::past) u terms;

(*Final simplification: cancel + and *  *)
fun cancel_simplify_meta_eq cancel_th th =
    Int_Numeral_Simprocs.simplify_meta_eq
        [mult_1, mult_1_right]
        (([th, cancel_th]) MRS trans);

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

(*mult_cancel_left requires an ordered ring, such as int. The version in
  rat_arith.ML works for all fields.*)
structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.intT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_cancel_left
);

(*int_mult_div_cancel_disj is for integer division (div). The version in
  rat_arith.ML works for all fields, using real division (/).*)
structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.intT
  val simplify_meta_eq  = cancel_simplify_meta_eq int_mult_div_cancel_disj
);

val int_cancel_factor =
  map Bin_Simprocs.prep_simproc
   [("ring_eq_cancel_factor", ["(l::int) * m = n", "(l::int) = m * n"], 
    EqCancelFactor.proc),
    ("int_divide_cancel_factor", ["((l::int) * m) div n", "(l::int) div (m*n)"],
     DivideCancelFactor.proc)];

(** Versions for all fields, including unordered ones (type complex).*)

structure FieldEqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val simplify_meta_eq  = cancel_simplify_meta_eq field_mult_cancel_left
);

structure FieldDivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" Term.dummyT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
);

val field_cancel_factor =
  map Bin_Simprocs.prep_simproc
   [("field_eq_cancel_factor",
     ["(l::'a::field) * m = n", "(l::'a::field) = m * n"], 
     FieldEqCancelFactor.proc),
    ("field_divide_cancel_factor",
     ["((l::'a::field) * m) / n", "(l::'a::field) / (m * n)"],
     FieldDivideCancelFactor.proc)];

end;

Addsimprocs int_cancel_factor;
Addsimprocs field_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1));

test "x*k = k*(y::int)";
test "k = k*(y::int)";
test "a*(b*c) = (b::int)";
test "a*(b*c) = d*(b::int)*(x*a)";

test "(x*k) div (k*(y::int)) = (uu::int)";
test "(k) div (k*(y::int)) = (uu::int)";
test "(a*(b*c)) div ((b::int)) = (uu::int)";
test "(a*(b*c)) div (d*(b::int)*(x*a)) = (uu::int)";
*)

(*And the same examples for fields such as rat or real:
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
