(*  Title:      HOL/Hyperreal/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type hypreal.
*)

(*FIXME DELETE*)
val hypreal_mult_less_mono2 = thm"hypreal_mult_less_mono2";

val hypreal_mult_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::hypreal")] mult_left_mono;


(****Instantiation of the generic linear arithmetic package****)


local

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val hypreal_mult_mono_thms =
 [(rotate_prems 1 hypreal_mult_less_mono2,
   cvar(hypreal_mult_less_mono2, hd(prems_of hypreal_mult_less_mono2))),
  (hypreal_mult_left_mono,
   cvar(hypreal_mult_left_mono, hd(tl(prems_of hypreal_mult_left_mono))))]

val real_inj_thms = [hypreal_of_real_le_iff RS iffD2, 
                     hypreal_of_real_less_iff RS iffD2,
                     hypreal_of_real_eq_iff RS iffD2];

in

val hyprealT = Type("Rational.hypreal", []);

val fast_hypreal_arith_simproc =
    Simplifier.simproc (Theory.sign_of (the_context ()))
      "fast_hypreal_arith" 
      ["(m::hypreal) < n", "(m::hypreal) <= n", "(m::hypreal) = n"]
    Fast_Arith.lin_arith_prover;

val hypreal_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ hypreal_mult_mono_thms,
    inj_thms = inj_thms @ real_inj_thms, 
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the hypreals are dense!*)
    simpset = simpset}),
  arith_inj_const ("HyperDef.hypreal_of_real", HOLogic.realT --> hyprealT),
  arith_discrete ("HyperDef.hypreal",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_hypreal_arith_simproc]];

end;



