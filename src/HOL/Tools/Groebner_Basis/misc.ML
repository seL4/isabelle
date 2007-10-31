(*  Title:      HOL/Tools/Groebner_Basis/misc.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Very basic stuff for cterms.
*)

structure Misc =
struct

fun is_comb ct =
  (case Thm.term_of ct of
    _ $ _ => true
  | _ => false);

val concl = Thm.cprop_of #> Thm.dest_arg;

fun is_binop ct ct' =
  (case Thm.term_of ct' of
    c $ _ $ _ => term_of ct aconv c
  | _ => false);

fun dest_binop ct ct' =
  if is_binop ct ct' then Thm.dest_binop ct'
  else raise CTERM ("dest_binop: bad binop", [ct, ct'])

fun inst_thm inst = Thm.instantiate ([], inst);

end;
