(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

WFair = Traces + Vimage +

constdefs

  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "[('a * 'a)set set, 'a set] => bool"
    "transient acts A == EX act:acts. A <= Domain act & act^^A <= Compl A"

  ensures :: "[('a * 'a)set set, 'a set, 'a set] => bool"
    "ensures acts A B == constrains acts (A-B) (A Un B) & transient acts (A-B)"
			(*(unless acts A B) would be equivalent*)

consts leadsTo :: "[('a * 'a)set set, 'a set, 'a set] => bool"
       leadsto :: "[('a * 'a)set set] => ('a set * 'a set) set"
  
translations
  "leadsTo acts A B" == "(A,B) : leadsto acts"

inductive "leadsto acts"
  intrs 

    Basis  "ensures acts A B ==> leadsTo acts A B"

    Trans  "[| leadsTo acts A B;  leadsTo acts B C |]
	   ==> leadsTo acts A C"

    (*Encoding using powerset of the desired axiom
       (!!A. A : S ==> leadsTo acts A B) ==> leadsTo acts (Union S) B
    *)
    Union  "(UN A:S. {(A,B)}) : Pow (leadsto acts)
	   ==> leadsTo acts (Union S) B"

  monos "[Pow_mono]"


(*wlt acts B is the largest set that leads to B*)
constdefs wlt :: "[('a * 'a)set set, 'a set] => 'a set"
  "wlt acts B == Union {A. leadsTo acts A B}"

end
