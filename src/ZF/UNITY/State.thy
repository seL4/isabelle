(*  Title:      HOL/UNITY/State.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states using dependent types:
 - variables are typed.
 - the state space is uniform, common to all defined programs.
 - variables can be quantified over.

*)

State = UNITYMisc +

consts
    variable :: i

(**
  Variables are better represented using integers, but at the moment
  there is a problem with integer translations like "uu" == "Var(#0)", which
  are needed to give names to variables.
  So for the time being we are using lists of naturals to index variables.
  **)

datatype variable = Var("i:list(nat)")
  type_intrs "[list_nat_into_univ]"
  
consts
  state, action, some ::i
  type_of :: i=>i

translations
  (* The state space is a dependent type *)
 "state" == "Pi(variable, type_of)"

  (* Commands are relations over states *)
  "action" == "Pow(state*state)"

rules
  (** We might have defined the state space in a such way that it is already
  not empty by formation: for example "state==PROD x:variable. type_of(x) Un {0}"
  which contains the function (lam x:variable. 0) is a possible choice.
  However, we prefer the following way for simpler proofs by avoiding
  case splitting resulting from type_of(x) Un {0}.  **)

  some_in_state "some:state"

constdefs
  (* State conditions/predicates are sets of states *)
  condition :: i
  "condition == Pow(state)"
  
  actionSet :: i
  "actionSet == Pow(action)"

consts  
  Id :: i
translations
  "Id" == "Identity(state)"
end