(*  Title:      HOL/Real/rat_arith0.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2004 University of Cambridge

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type rat.
*)

(*FIXME: these monomorphic versions are necessary because of a bug in the arith
  procedure*)
val rat_mult_strict_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::rat")] mult_strict_left_mono;

val rat_mult_left_mono =
 read_instantiate_sg(sign_of (the_context())) [("a","?a::rat")] mult_left_mono;


(****Instantiation of the generic linear arithmetic package for fields****)

local

val simprocs = field_cancel_numeral_factors

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
