(*  Title:      HOL/Real/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Augmentation of hypreal linear arithmetic with rational coefficient handling
*)

local

(* reduce contradictory <= to False *)
val simps = [True_implies_equals,inst "w" "number_of ?v" hypreal_add_mult_distrib2,
             hypreal_divide_1,hypreal_times_divide1_eq,hypreal_times_divide2_eq];

val simprocs = [hypreal_cancel_numeral_factors_divide];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val hypreal_mult_mono_thms =
 [(rotate_prems 1 hypreal_mult_less_mono2,
   cvar(hypreal_mult_less_mono2, hd(prems_of hypreal_mult_less_mono2))),
  (hypreal_mult_le_mono2,
   cvar(hypreal_mult_le_mono2, hd(tl(prems_of hypreal_mult_le_mono2))))]

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
