(*  Title:      HOL/UNITY/ELT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

leadsTo strengthened with a specification of the allowable sets transient parts

TRY INSTEAD (to get rid of the {} and to gain strong induction)

  elt :: "['a set set, 'a program, 'a set] => ('a set) set"

inductive "elt CC F B"
  intrs 

    Weaken  "A <= B ==> A : elt CC F B"

    ETrans  "[| F : A ensures A';  A-A' : CC;  A' : elt CC F B |]
	     ==> A : elt CC F B"

    Union  "{A. A: S} : Pow (elt CC F B) ==> (Union S) : elt CC F B"

  monos Pow_mono
*)

ELT = Project +

consts

  (*LEADS-TO constant for the inductive definition*)
  elt :: "['a set set, 'a program] => ('a set * 'a set) set"


inductive "elt CC F"
  intrs 

    Basis  "[| F : A ensures B;  A-B : (insert {} CC) |] ==> (A,B) : elt CC F"

    Trans  "[| (A,B) : elt CC F;  (B,C) : elt CC F |] ==> (A,C) : elt CC F"

    Union  "{(A,B) | A. A: S} : Pow (elt CC F) ==> (Union S, B) : elt CC F"

  monos Pow_mono


constdefs
  
  (*the set of all sets determined by f alone*)
  givenBy :: "['a => 'b] => 'a set set"
    "givenBy f == range (%B. f-`` B)"

  (*visible version of the LEADS-TO relation*)
  leadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        ("(3_/ leadsTo[_]/ _)" [80,0,80] 80)
    "leadsETo A CC B == {F. (A,B) : elt CC F}"

  LeadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        ("(3_/ LeadsTo[_]/ _)" [80,0,80] 80)
    "LeadsETo A CC B ==
      {F. F : (reachable F Int A) leadsTo[(%C. reachable F Int C) `` CC] B}"

end
