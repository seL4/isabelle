(*  Title:      HOL/UNITY/State.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states using dependent types so that:
 - variables are typed.
 - the state space is uniform, common to all defined programs.
 - variables can be quantified over.
*)

State = UNITYMisc +

consts var::i
datatype var = Var("i:list(nat)")
         type_intrs "[list_nat_into_univ]"
consts
  type_of :: i=>i
  default_val :: i=>i

constdefs
  state   :: i
  "state == PROD x:var. cons(default_val(x), type_of(x))"
  st0     :: i
  "st0 == lam x:var. default_val(x)"
  
  st_set  :: i =>o
(* To prevent typing conditions like `A<=state' from
   being used in combination with the rules `constrains_weaken', etc. *)
  "st_set(A) == A<=state"

  st_compl :: i=>i
  "st_compl(A) == state-A"
  
end