(*  Title:      HOL/Calculation.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Setup transitivity rules for calculational proofs.
*)

theory Calculation = Int:


theorems[trans] = HOL.trans			(*  =  =  =  *)
theorems[trans] = HOL.ssubst                    (*  =  *  *  *)
theorems[trans] = HOL.subst[COMP swap_prems_rl]	(*  *  =  *  *)

theorems[trans] = Ord.order_trans		(*  <= <= <= *)
theorems[trans] = Ord.order_less_trans		(*  <  <  <  *)
theorems[trans] = Ord.order_le_less_trans	(*  <= <  <  *)
theorems[trans] = Ord.order_less_le_trans	(*  <  <= <  *)

theorems[trans] = Divides.dvd_trans		(* dvd dvd dvd *)


end
