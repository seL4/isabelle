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
  some    :: i
  state   :: i
  st_set  :: i =>o
translations
  "state" == "Pi(var, type_of)"

defs  
  (* To prevent typing conditions (like `A<=state') from
     being used in combination with the rules `constrains_weaken', etc. *)
  st_set_def "st_set(A) == A<=state"

rules
  some_assume "some:state"

(***
REMARKS:
  1. The reason of indexing variables by lists instead of integers is that,
at the time I was writing this theory, translations like `foo == Var(#1)'
mysteriously provoke a syntactical error. Such translations are used
for introducing variable names when specifying programs.

  2. State space `state' is required to be not empty. This requirement
can be achieved by definition: the space "PROD x:var. type_of(x) Un {0}"
includes the state `lam x:state. 0'. However, such definition leads to
complications later during program type-chinking. For example, to prove
that the assignment `foo:=#1' is well typed, for `foo' an integer
variable, we would have to show two things: (a) that #1 is an integer
but also (b) that #1 is different from 0. Hence axiom `some_assume'.
***)
end