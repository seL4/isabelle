(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)

Constrains = UNITY + 

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces init acts"  
  intrs 
         (*Initial trace is empty*)
    Init  "s: init ==> (s,[]) : traces init acts"

    Acts  "[| act: acts;  (s,evs) : traces init acts;  (s,s'): act |]
	   ==> (s', s#evs) : traces init acts"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intrs 
    Init  "s: Init F ==> s : reachable F"

    Acts  "[| act: Acts F;  s : reachable F;  (s,s'): act |]
	   ==> s' : reachable F"

consts
  Constrains :: "['a set, 'a set] => 'a program set"  (infixl "Co"     60)
  op_Unless  :: "['a set, 'a set] => 'a program set"  (infixl "Unless" 60)

defs
  Constrains_def
    "A Co B == {F. F : (reachable F Int A)  co  B}"

  Unless_def
    "A Unless B == (A-B) Co (A Un B)"

constdefs

  Stable     :: "'a set => 'a program set"
    "Stable A == A Co A"

  (*Always is the weak form of "invariant"*)
  Always :: "'a set => 'a program set"
    "Always A == {F. Init F <= A} Int Stable A"

  (*Polymorphic in both states and the meaning of <= *)
  Increasing :: "['a => 'b::{order}] => 'a program set"
    "Increasing f == INT z. Stable {s. z <= f s}"

end
