(*  Title:      HOL/Hyperreal/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type hypreal.
*)

(****Instantiation of the generic linear arithmetic package****)


local

val real_inj_thms = [thm "star_of_le" RS iffD2, 
                     thm "star_of_less" RS iffD2,
                     thm "star_of_eq" RS iffD2];

in

val hyprealT = Type("StarDef.star", [HOLogic.realT]);

val fast_hypreal_arith_simproc =
    Simplifier.simproc (Theory.sign_of (the_context ()))
      "fast_hypreal_arith" 
      ["(m::hypreal) < n", "(m::hypreal) <= n", "(m::hypreal) = n"]
    Fast_Arith.lin_arith_prover;

val hypreal_arith_setup =
  Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = inj_thms @ real_inj_thms, 
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the hypreals are dense!*)
    neqE = neqE,
    simpset = simpset}) #>
  arith_inj_const ("StarDef.star_of", HOLogic.realT --> hyprealT) #>
  (fn thy => (change_simpset_of thy (fn ss => ss addsimprocs [fast_hypreal_arith_simproc]); thy));

end;



