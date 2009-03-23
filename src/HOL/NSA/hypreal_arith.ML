(*  Title:      HOL/NSA/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type hypreal.
*)

local

val simps = [thm "star_of_zero",
             thm "star_of_one",
             thm "star_of_number_of",
             thm "star_of_add",
             thm "star_of_minus",
             thm "star_of_diff",
             thm "star_of_mult"]

val real_inj_thms = [thm "star_of_le" RS iffD2,
                     thm "star_of_less" RS iffD2,
                     thm "star_of_eq" RS iffD2]

in

val hyprealT = Type ("StarDef.star", [HOLogic.realT]);

val fast_hypreal_arith_simproc =
    Simplifier.simproc (the_context ())
      "fast_hypreal_arith" 
      ["(m::hypreal) < n", "(m::hypreal) <= n", "(m::hypreal) = n"]
    (K Lin_Arith.lin_arith_simproc);

val hypreal_arith_setup =
  Lin_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = real_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change lessD: the hypreals are dense!*)
    neqE = neqE,
    simpset = simpset addsimps simps}) #>
  arith_inj_const ("StarDef.star_of", HOLogic.realT --> hyprealT) #>
  Simplifier.map_ss (fn ss => ss addsimprocs [fast_hypreal_arith_simproc]);

end;
