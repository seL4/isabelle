(*  Title:      HOL/int_factor_simprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Factor cancellation simprocs for the integers.

This file can't be combined with int_arith1 because it requires IntDiv.thy.
*)

(** Factor cancellation theorems for "int" **)

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
     ALLGOALS (simp_tac (HOL_ss addsimps minus_from_mult_simps@mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps bin_simps))
  val simplify_meta_eq  = simplify_meta_eq mult_1s
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.intT
  val cancel = int_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.intT
  val cancel = mult_cancel_left RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.intT
  val cancel = mult_less_cancel_left RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.intT
  val cancel = mult_le_cancel_left RS trans
  val neg_exchanges = true
)

val int_cancel_numeral_factors =
  map Bin_Simprocs.prep_simproc
   [("inteq_cancel_numeral_factors", ["(l::int) * m = n", "(l::int) = m * n"],
     EqCancelNumeralFactor.proc),
    ("intless_cancel_numeral_factors", ["(l::int) * m < n", "(l::int) < m * n"],
     LessCancelNumeralFactor.proc),
    ("intle_cancel_numeral_factors", ["(l::int) * m <= n", "(l::int) <= m * n"],
     LeCancelNumeralFactor.proc),
    ("intdiv_cancel_numeral_factors", ["((l::int) * m) div n", "(l::int) div (m * n)"],
     DivCancelNumeralFactor.proc)];

end;

Addsimprocs int_cancel_numeral_factors;


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
   [("int_eq_cancel_factor", ["(l::int) * m = n", "(l::int) = m * n"], EqCancelFactor.proc),
    ("int_divide_cancel_factor", ["((l::int) * m) div n", "(l::int) div (m * n)"],
     DivideCancelFactor.proc)];

end;

Addsimprocs int_cancel_factor;


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

