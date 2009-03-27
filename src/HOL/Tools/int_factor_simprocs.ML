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

val rel_number_of = [@{thm eq_number_of_eq}, @{thm less_number_of}, @{thm le_number_of}];

local
  open Int_Numeral_Simprocs
in

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val trans_tac         = K Arith_Data.trans_tac

  val norm_ss1 = HOL_ss addsimps minus_from_mult_simps @ mult_1s
  val norm_ss2 = HOL_ss addsimps simps @ mult_minus_simps
  val norm_ss3 = HOL_ss addsimps @{thms mult_ac}
  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = HOL_ss addsimps rel_number_of @ simps
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq
    [@{thm add_0}, @{thm add_0_right}, @{thm mult_zero_left},
      @{thm mult_zero_right}, @{thm mult_Bit1}, @{thm mult_1_right}];
  end

(*Version for integer division*)
structure IntDivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binop @{const_name Divides.div}
  val dest_bal = HOLogic.dest_bin @{const_name Divides.div} HOLogic.intT
  val cancel = @{thm zdiv_zmult_zmult1} RS trans
  val neg_exchanges = false
)

(*Version for fields*)
structure DivideCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binop @{const_name HOL.divide}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.divide} Term.dummyT
  val cancel = @{thm mult_divide_mult_cancel_left} RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val cancel = @{thm mult_cancel_left} RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less} Term.dummyT
  val cancel = @{thm mult_less_cancel_left} RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less_eq} Term.dummyT
  val cancel = @{thm mult_le_cancel_left} RS trans
  val neg_exchanges = true
)

val cancel_numeral_factors =
  map Arith_Data.prep_simproc
   [("ring_eq_cancel_numeral_factor",
     ["(l::'a::{idom,number_ring}) * m = n",
      "(l::'a::{idom,number_ring}) = m * n"],
     K EqCancelNumeralFactor.proc),
    ("ring_less_cancel_numeral_factor",
     ["(l::'a::{ordered_idom,number_ring}) * m < n",
      "(l::'a::{ordered_idom,number_ring}) < m * n"],
     K LessCancelNumeralFactor.proc),
    ("ring_le_cancel_numeral_factor",
     ["(l::'a::{ordered_idom,number_ring}) * m <= n",
      "(l::'a::{ordered_idom,number_ring}) <= m * n"],
     K LeCancelNumeralFactor.proc),
    ("int_div_cancel_numeral_factors",
     ["((l::int) * m) div n", "(l::int) div (m * n)"],
     K IntDivCancelNumeralFactor.proc),
    ("divide_cancel_numeral_factor",
     ["((l::'a::{division_by_zero,field,number_ring}) * m) / n",
      "(l::'a::{division_by_zero,field,number_ring}) / (m * n)",
      "((number_of v)::'a::{division_by_zero,field,number_ring}) / (number_of w)"],
     K DivideCancelNumeralFactor.proc)];

(* referenced by rat_arith.ML *)
val field_cancel_numeral_factors =
  map Arith_Data.prep_simproc
   [("field_eq_cancel_numeral_factor",
     ["(l::'a::{field,number_ring}) * m = n",
      "(l::'a::{field,number_ring}) = m * n"],
     K EqCancelNumeralFactor.proc),
    ("field_cancel_numeral_factor",
     ["((l::'a::{division_by_zero,field,number_ring}) * m) / n",
      "(l::'a::{division_by_zero,field,number_ring}) / (m * n)",
      "((number_of v)::'a::{division_by_zero,field,number_ring}) / (number_of w)"],
     K DivideCancelNumeralFactor.proc)]

end;

Addsimprocs cancel_numeral_factors;

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
fun find_first_t past u []         = raise TERM ("find_first_t", [])
  | find_first_t past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first_t (t::past) u terms
        handle TERM _ => find_first_t (t::past) u terms;

(** Final simplification for the CancelFactor simprocs **)
val simplify_one = Arith_Data.simplify_meta_eq  
  [@{thm mult_1_left}, @{thm mult_1_right}, @{thm div_by_1}, @{thm numeral_1_eq_1}];

fun cancel_simplify_meta_eq ss cancel_th th =
    simplify_one ss (([th, cancel_th]) MRS trans);

local
  val Tp_Eq = Thm.reflexive(Thm.cterm_of (@{theory HOL}) HOLogic.Trueprop)
  fun Eq_True_elim Eq = 
    Thm.equal_elim (Thm.combination Tp_Eq (Thm.symmetric Eq)) @{thm TrueI}
in
fun sign_conv pos_th neg_th ss t =
  let val T = fastype_of t;
      val zero = Const(@{const_name HOL.zero}, T);
      val less = Const(@{const_name HOL.less}, [T,T] ---> HOLogic.boolT);
      val pos = less $ zero $ t and neg = less $ t $ zero
      fun prove p =
        Option.map Eq_True_elim (Lin_Arith.lin_arith_simproc ss p)
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
  val mk_sum            = long_mk_prod
  val dest_sum          = dest_prod
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first        = find_first_t []
  val trans_tac         = K Arith_Data.trans_tac
  val norm_ss = HOL_ss addsimps mult_1s @ @{thms mult_ac}
  fun norm_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss))
  val simplify_meta_eq  = cancel_simplify_meta_eq 
  end;

(*mult_cancel_left requires a ring with no zero divisors.*)
structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val simp_conv = K (K (SOME @{thm mult_cancel_left}))
);

(*for ordered rings*)
structure LeCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less_eq} Term.dummyT
  val simp_conv = sign_conv
    @{thm mult_le_cancel_left_pos} @{thm mult_le_cancel_left_neg}
);

(*for ordered rings*)
structure LessCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less} Term.dummyT
  val simp_conv = sign_conv
    @{thm mult_less_cancel_left_pos} @{thm mult_less_cancel_left_neg}
);

(*zdiv_zmult_zmult1_if is for integer division (div).*)
structure IntDivCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binop @{const_name Divides.div}
  val dest_bal = HOLogic.dest_bin @{const_name Divides.div} HOLogic.intT
  val simp_conv = K (K (SOME @{thm zdiv_zmult_zmult1_if}))
);

structure IntModCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binop @{const_name Divides.mod}
  val dest_bal = HOLogic.dest_bin @{const_name Divides.mod} HOLogic.intT
  val simp_conv = K (K (SOME @{thm zmod_zmult_zmult1}))
);

structure IntDvdCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name Ring_and_Field.dvd}
  val dest_bal = HOLogic.dest_bin @{const_name Ring_and_Field.dvd} Term.dummyT
  val simp_conv = K (K (SOME @{thm dvd_mult_cancel_left}))
);

(*Version for all fields, including unordered ones (type complex).*)
structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binop @{const_name HOL.divide}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.divide} Term.dummyT
  val simp_conv = K (K (SOME @{thm mult_divide_mult_cancel_left_if}))
);

val cancel_factors =
  map Arith_Data.prep_simproc
   [("ring_eq_cancel_factor",
     ["(l::'a::{idom}) * m = n",
      "(l::'a::{idom}) = m * n"],
     K EqCancelFactor.proc),
    ("ordered_ring_le_cancel_factor",
     ["(l::'a::ordered_ring) * m <= n",
      "(l::'a::ordered_ring) <= m * n"],
     K LeCancelFactor.proc),
    ("ordered_ring_less_cancel_factor",
     ["(l::'a::ordered_ring) * m < n",
      "(l::'a::ordered_ring) < m * n"],
     K LessCancelFactor.proc),
    ("int_div_cancel_factor",
     ["((l::int) * m) div n", "(l::int) div (m * n)"],
     K IntDivCancelFactor.proc),
    ("int_mod_cancel_factor",
     ["((l::int) * m) mod n", "(l::int) mod (m * n)"],
     K IntModCancelFactor.proc),
    ("dvd_cancel_factor",
     ["((l::'a::idom) * m) dvd n", "(l::'a::idom) dvd (m * n)"],
     K IntDvdCancelFactor.proc),
    ("divide_cancel_factor",
     ["((l::'a::{division_by_zero,field}) * m) / n",
      "(l::'a::{division_by_zero,field}) / (m * n)"],
     K DivideCancelFactor.proc)];

end;

Addsimprocs cancel_factors;


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
