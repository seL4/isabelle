(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

WFair = UNITY +

constdefs

  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "'a set => 'a program set"
    "transient A == {F. EX act: Acts F. A <= Domain act & act^^A <= Compl A}"

  ensures :: "['a set, 'a set] => 'a program set"
    "ensures A B == constrains (A-B) (A Un B) Int transient (A-B)"


consts leadsto :: "'a program => ('a set * 'a set) set"
  
inductive "leadsto F"
  intrs 

    Basis  "F : ensures A B ==> (A,B) : leadsto F"

    Trans  "[| (A,B) : leadsto F;  (B,C) : leadsto F |]
	   ==> (A,C) : leadsto F"

    (*Encoding using powerset of the desired axiom
       (!!A. A : S ==> (A,B) : leadsto F) ==> (Union S, B) : leadsto F
    *)
    Union  "(UN A:S. {(A,B)}) : Pow (leadsto F) ==> (Union S, B) : leadsto F"

  monos "[Pow_mono]"


  
constdefs (*visible version of the relation*)
  leadsTo :: "['a set, 'a set] => 'a program set"
    "leadsTo A B == {F. (A,B) : leadsto F}"
  
  (*wlt F B is the largest set that leads to B*)
  wlt :: "['a program, 'a set] => 'a set"
    "wlt F B == Union {A. F: leadsTo A B}"

end
