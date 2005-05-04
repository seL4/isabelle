(*  Title:      HOL/Real/rat_arith0.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2004 University of Cambridge

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type rat.
*)

(****Instantiation of the generic linear arithmetic package for fields****)

local

val simprocs = field_cancel_numeral_factors

val simps = [order_less_irrefl, neg_less_iff_less, True_implies_equals,
             inst "a" "(number_of ?v)" right_distrib,
             divide_1, divide_zero_left,
             times_divide_eq_right, times_divide_eq_left,
             minus_divide_left RS sym, minus_divide_right RS sym,
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
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD,
 neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = int_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the rats are dense!*)
    neqE =  neqE,
    simpset = simpset addsimps simps
                      addsimprocs simprocs}),
  arith_inj_const("IntDef.of_nat", HOLogic.natT --> ratT),
  arith_inj_const("IntDef.of_int", HOLogic.intT --> ratT),
  Simplifier.change_simpset_of (op addsimprocs) [fast_rat_arith_simproc]];

end;
