(*  Title: 	Substitutions/utermlemmas.thy
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Additional definitions for uterms that are not part of the basic inductive definition.
*)

UTLemmas = UTerm + Setplus +

consts

  vars_of       ::   "'a uterm=>'a set"
  "<:"          ::   "['a uterm,'a uterm]=>bool"   (infixl 54) 

rules  (*Definitions*)

  vars_of_def   "vars_of(t) == uterm_rec t (%x.{x}) (%x.{}) (%u v q r.q Un r)"
  occs_def      "s <: t == uterm_rec t (%x.False) (%x.False) (%u v q r.s=u | s=v | q | r)"

end
