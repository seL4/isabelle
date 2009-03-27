(*  Title:      HOL/Real/real_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type real.
*)

local

val simps = [@{thm real_of_nat_zero}, @{thm real_of_nat_Suc}, @{thm real_of_nat_add},
             @{thm real_of_nat_mult}, @{thm real_of_int_zero}, @{thm real_of_one},
             @{thm real_of_int_add}, @{thm real_of_int_minus}, @{thm real_of_int_diff},
             @{thm real_of_int_mult}, @{thm real_of_int_of_nat_eq},
             @{thm real_of_nat_number_of}, @{thm real_number_of}]

val nat_inj_thms = [@{thm real_of_nat_le_iff} RS iffD2,
                    @{thm real_of_nat_inject} RS iffD2]
(* not needed because x < (y::nat) can be rewritten as Suc x <= y:
                    real_of_nat_less_iff RS iffD2 *)

val int_inj_thms = [@{thm real_of_int_le_iff} RS iffD2,
                    @{thm real_of_int_inject} RS iffD2]
(* not needed because x < (y::int) can be rewritten as x + 1 <= y:
                    real_of_int_less_iff RS iffD2 *)

in

val real_arith_setup =
  Lin_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = int_inj_thms @ nat_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change lessD: the reals are dense!*)
    neqE = neqE,
    simpset = simpset addsimps simps}) #>
  arith_inj_const (@{const_name real}, HOLogic.natT --> HOLogic.realT) #>
  arith_inj_const (@{const_name real}, HOLogic.intT --> HOLogic.realT)

end;
