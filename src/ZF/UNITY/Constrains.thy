(*  Title:      ZF/UNITY/Constrains.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Safety relations: restricted to the set of reachable states.

Theory ported from HOL.
*)

Constrains = UNITY +
consts traces :: "[i, i] => i"
  (* Initial states and program => (final state, reversed trace to it)... 
      the domain might also be state*list(state) *)
inductive 
  domains 
     "traces(init, acts)" <=
         "(init Un (UN act:acts. field(act)))*list(UN act:acts. field(act))"
  intrs 
         (*Initial trace is empty*)
    Init  "s: init ==> <s,[]> : traces(init,acts)"

    Acts  "[| act:acts;  <s,evs> : traces(init,acts);  <s,s'>: act |]
           ==> <s', Cons(s,evs)> : traces(init, acts)"
  
  type_intrs "list.intrs@[UnI1, UnI2, UN_I, fieldI2, fieldI1]"

  consts reachable :: "i=>i"

inductive
  domains
  "reachable(F)" <= "Init(F) Un (UN act:Acts(F). field(act))"
  intrs 
    Init  "s:Init(F) ==> s:reachable(F)"

    Acts  "[| act: Acts(F);  s:reachable(F);  <s,s'>: act |]
           ==> s':reachable(F)"

  type_intrs "[UnI1, UnI2, fieldI2, UN_I]"

  
consts
  Constrains :: "[i,i] => i"  (infixl "Co"     60)
  op_Unless  :: "[i, i] => i"  (infixl "Unless" 60)

defs
  Constrains_def
    "A Co B == {F:program. F:(reachable(F) Int A) co B &
		           A:condition & B:condition}"

  Unless_def
    "A Unless B == (A-B) Co (A Un B)"

constdefs
  Stable     :: "i => i"
    "Stable(A) == A Co A"
  (*Always is the weak form of "invariant"*)
  Always :: "i => i"
    "Always(A) == {F:program. Init(F) <= A} Int Stable(A)"

  (*
  The constant Increasing_on defines a weak form of the Charpentier's
  increasing notion.  It should not be confused with the ZF's
  increasing constant which have a different meaning.
  Increasing's parameters: a state function f,
  a domain A and a order relation r over the domain A.
  Should f be a meta function instead ?
  *)
  Increasing_on :: [i,i, i] => i  ("Increasing[_]'(_,_')")
  "Increasing[A](f, r) == {F:program. f:state->A &
			      part_order(A,r) &
			      F: (INT z:A. Stable({s:state.  <z, f`s>:r}))}"

end

