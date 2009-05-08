(*  Title:      HOL/Real/rat_arith.ML
    Author:     Lawrence C Paulson
    Copyright   2004 University of Cambridge

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type rat.
*)

local

val simps =
 [@{thm order_less_irrefl}, @{thm neg_less_iff_less}, @{thm True_implies_equals},
  read_instantiate @{context} [(("a", 0), "(number_of ?v)")] @{thm right_distrib},
  @{thm divide_1}, @{thm divide_zero_left},
  @{thm times_divide_eq_right}, @{thm times_divide_eq_left},
  @{thm minus_divide_left} RS sym, @{thm minus_divide_right} RS sym,
  @{thm of_int_0}, @{thm of_int_1}, @{thm of_int_add},
  @{thm of_int_minus}, @{thm of_int_diff},
  @{thm of_int_mult}, @{thm of_int_of_nat_eq}]

val nat_inj_thms = [@{thm of_nat_le_iff} RS iffD2,
                    @{thm of_nat_eq_iff} RS iffD2]
(* not needed because x < (y::nat) can be rewritten as Suc x <= y:
                    of_nat_less_iff RS iffD2 *)

val int_inj_thms = [@{thm of_int_le_iff} RS iffD2,
                    @{thm of_int_eq_iff} RS iffD2]
(* not needed because x < (y::int) can be rewritten as x + 1 <= y:
                    of_int_less_iff RS iffD2 *)

in

val rat_arith_setup =
  Lin_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = int_inj_thms @ nat_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change lessD: the rats are dense!*)
    neqE =  neqE,
    simpset = simpset addsimps simps
                      addsimprocs Numeral_Simprocs.field_cancel_numeral_factors}) #>
  arith_inj_const (@{const_name of_nat}, @{typ "nat => rat"}) #>
  arith_inj_const (@{const_name of_int}, @{typ "int => rat"})

end;
