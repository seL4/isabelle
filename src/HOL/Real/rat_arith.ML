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

	val le_number_of_eq = thm"le_number_of_eq";


(****Common factor cancellation****)

(*To quote from Provers/Arith/cancel_numeral_factor.ML:

This simproc Cancels common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.
*)

val rel_number_of = [eq_number_of_eq, less_number_of_eq_neg, le_number_of_eq]

local open Int_Numeral_Simprocs
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

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" Term.dummyT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
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

val field_cancel_numeral_factors_relations =
  map Bin_Simprocs.prep_simproc
   [("field_eq_cancel_numeral_factor",
     ["(l::'a::{field,number_ring}) * m = n",
      "(l::'a::{field,number_ring}) = m * n"],
     EqCancelNumeralFactor.proc),
    ("field_less_cancel_numeral_factor",
     ["(l::'a::{ordered_field,number_ring}) * m < n",
      "(l::'a::{ordered_field,number_ring}) < m * n"],
     LessCancelNumeralFactor.proc),
    ("field_le_cancel_numeral_factor",
     ["(l::'a::{ordered_field,number_ring}) * m <= n",
      "(l::'a::{ordered_field,number_ring}) <= m * n"],
     LeCancelNumeralFactor.proc)]

val field_cancel_numeral_factors_divide = 
    Bin_Simprocs.prep_simproc
        ("field_cancel_numeral_factor",
         ["((l::'a::{field,number_ring}) * m) / n",
          "(l::'a::{field,number_ring}) / (m * n)",
          "((number_of v)::'a::{field,number_ring}) / (number_of w)"],
         DivCancelNumeralFactor.proc)

val field_cancel_numeral_factors =
    field_cancel_numeral_factors_relations @
    [field_cancel_numeral_factors_divide]

end;

Addsimprocs field_cancel_numeral_factors;


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

local open Int_Numeral_Simprocs
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

(*This version works for all fields, including unordered ones (complex).
  The version declared in int_factor_simprocs.ML is for integers.*)
structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val simplify_meta_eq  = cancel_simplify_meta_eq field_mult_cancel_left
);


(*This version works for fields, with the generic divides operator (/).
  The version declared in int_factor_simprocs.ML for integers with div.*)
structure DivideCancelFactor = ExtractCommonTermFun
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
     EqCancelFactor.proc),
    ("field_divide_cancel_factor",
     ["((l::'a::field) * m) / n", "(l::'a::field) / (m * n)"],
     DivideCancelFactor.proc)];

end;

Addsimprocs field_cancel_factor;


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



(****Instantiation of the generic linear arithmetic package for fields****)


local

val simprocs = [field_cancel_numeral_factors_divide]

val mono_ss = simpset() addsimps
                [add_mono,add_strict_mono,add_less_le_mono,add_le_less_mono];

val add_mono_thms_ordered_field =
  map (fn s => prove_goal (the_context ()) s
                 (fn prems => [cut_facts_tac prems 1, asm_simp_tac mono_ss 1]))
    ["(i < j) & (k = l)   ==> i + k < j + (l::'a::ordered_field)",
     "(i = j) & (k < l)   ==> i + k < j + (l::'a::ordered_field)",
     "(i < j) & (k <= l)  ==> i + k < j + (l::'a::ordered_field)",
     "(i <= j) & (k < l)  ==> i + k < j + (l::'a::ordered_field)",
     "(i < j) & (k < l)   ==> i + k < j + (l::'a::ordered_field)"];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val rat_mult_mono_thms =
 [(rat_mult_strict_left_mono,
   cvar(rat_mult_strict_left_mono, hd(tl(prems_of rat_mult_strict_left_mono)))),
  (rat_mult_left_mono,
   cvar(rat_mult_left_mono, hd(tl(prems_of rat_mult_left_mono))))]

val simps = [order_less_irrefl, True_implies_equals,
             inst "a" "(number_of ?v)" right_distrib,
             divide_1, divide_zero_left,
             times_divide_eq_right, times_divide_eq_left,
	     of_int_0, of_int_1, of_int_add, of_int_minus, of_int_diff,
	     of_int_mult, of_int_of_nat_eq];

in

val fast_rat_arith_simproc = 
 Simplifier.simproc (Theory.sign_of(the_context()))
  "fast_rat_arith" ["(m::rat) < n","(m::rat) <= n", "(m::rat) = n"]
  Fast_Arith.lin_arith_prover;

val nat_inj_thms = [of_nat_le_iff RS iffD2, of_nat_less_iff RS iffD2,
                    of_nat_eq_iff RS iffD2];

val int_inj_thms = [of_int_le_iff RS iffD2, of_int_less_iff RS iffD2,
                    of_int_eq_iff RS iffD2];

val ratT = Type("Rational.rat", []);

val rat_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_ordered_field,
    mult_mono_thms = mult_mono_thms @ rat_mult_mono_thms,
    inj_thms = int_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the rats are dense!*)
    simpset = simpset addsimps simps
                      addsimprocs simprocs}),
  arith_inj_const("IntDef.of_nat", HOLogic.natT --> ratT),
  arith_inj_const("IntDef.of_int", HOLogic.intT --> ratT),
  arith_discrete ("Rational.rat",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_rat_arith_simproc]];

end;
