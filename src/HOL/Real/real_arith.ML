(*  Title:      HOL/Real/real_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Augmentation of real linear arithmetic with rational coefficient handling
*)

val real_divide_1 = thm"real_divide_1";

local

val times_divide_eq_left = thm"times_divide_eq_left";
val times_divide_eq_right = thm"times_divide_eq_right";

(* reduce contradictory <= to False *)
val simps = [True_implies_equals,
             inst "w" "number_of ?v" real_add_mult_distrib2,
             real_divide_1,times_divide_eq_right,times_divide_eq_left];

val simprocs = [real_cancel_numeral_factors_divide];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_le_mono2,
   cvar(real_mult_le_mono2, hd(tl(prems_of real_mult_le_mono2))))]

in

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = inj_thms,
    lessD = lessD,
    simpset = simpset addsimps simps addsimprocs simprocs})];

end;

(*
Procedure "assoc_fold" needed?
*)
