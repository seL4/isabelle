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
      the domain may also be state*list(state) *)
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
    "A Co B == {F:program. F:(reachable(F) Int A) co B}"

  Unless_def
    "A Unless B == (A-B) Co (A Un B)"

constdefs
  Stable     :: "i => i"
    "Stable(A) == A Co A"
  (*Always is the weak form of "invariant"*)
  Always :: "i => i"
    "Always(A) == initially(A) Int Stable(A)"

  (* Increasing is the weak from of increasing *)
  Increasing :: [i,i, i] => i 
  "Increasing(A, r, f) ==  INT a:A. Stable({s:state.  <a, f`s>:r})"
end

