(*  Title:      HOL/Hyperreal/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs: Common factor cancellation & Rational coefficient handling
*)

(****Common factor cancellation****)

local
  open Hyperreal_Numeral_Simprocs
in

val rel_hypreal_number_of = [eq_hypreal_number_of, less_hypreal_number_of,
                          le_hypreal_number_of_eq_not_less];

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


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "0 <= (y::hypreal) * -2";
test "9*x = 12 * (y::hypreal)";
test "(9*x) / (12 * (y::hypreal)) = z";
test "9*x < 12 * (y::hypreal)";
test "9*x <= 12 * (y::hypreal)";

test "-99*x = 123 * (y::hypreal)";
test "(-99*x) / (123 * (y::hypreal)) = z";
test "-99*x < 123 * (y::hypreal)";
test "-99*x <= 123 * (y::hypreal)";

test "999*x = -396 * (y::hypreal)";
test "(999*x) / (-396 * (y::hypreal)) = z";
test "999*x < -396 * (y::hypreal)";
test "999*x <= -396 * (y::hypreal)";

test "-99*x = -81 * (y::hypreal)";
test "(-99*x) / (-81 * (y::hypreal)) = z";
test "-99*x <= -81 * (y::hypreal)";
test "-99*x < -81 * (y::hypreal)";

test "-2 * x = -1 * (y::hypreal)";
test "-2 * x = -(y::hypreal)";
test "(-2 * x) / (-1 * (y::hypreal)) = z";
test "-2 * x < -(y::hypreal)";
test "-2 * x <= -1 * (y::hypreal)";
test "-x < -23 * (y::hypreal)";
test "-x <= -23 * (y::hypreal)";
*)


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


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1));

test "x*k = k*(y::hypreal)";
test "k = k*(y::hypreal)";
test "a*(b*c) = (b::hypreal)";
test "a*(b*c) = d*(b::hypreal)*(x*a)";


test "(x*k) / (k*(y::hypreal)) = (uu::hypreal)";
test "(k) / (k*(y::hypreal)) = (uu::hypreal)";
test "(a*(b*c)) / ((b::hypreal)) = (uu::hypreal)";
test "(a*(b*c)) / (d*(b::hypreal)*(x*a)) = (uu::hypreal)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::hypreal)*(x*a)/z";
*)


(****Augmentation of real linear arithmetic with 
     rational coefficient handling****)

local

(* reduce contradictory <= to False *)
val simps = [True_implies_equals,
             inst "a" "(number_of ?v)::hypreal" right_distrib,
             divide_1,times_divide_eq_right,times_divide_eq_left];

val simprocs = [hypreal_cancel_numeral_factors_divide];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val hypreal_mult_mono_thms =
 [(rotate_prems 1 hypreal_mult_less_mono2,
   cvar(hypreal_mult_less_mono2, hd(prems_of hypreal_mult_less_mono2))),
  (mult_left_mono,
   cvar(mult_left_mono, hd(tl(prems_of mult_left_mono))))]

in

val hypreal_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ hypreal_mult_mono_thms,
    inj_thms = inj_thms,
    lessD = lessD,
    simpset = simpset addsimps simps addsimprocs simprocs})];

end;

(*
Procedure "assoc_fold" needed?
*)
