(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

WFair = Traces + Vimage +

constdefs

  transient :: "[('a * 'a)set set, 'a set] => bool"
    "transient Acts A == EX act:Acts. A <= Domain act & act^^A <= Compl A"

  ensures :: "[('a * 'a)set set, 'a set, 'a set] => bool"
    "ensures Acts A B == constrains Acts (A-B) (A Un B) & transient Acts (A-B)"

consts leadsTo :: "[('a * 'a)set set, 'a set, 'a set] => bool"
       leadsto :: "[('a * 'a)set set] => ('a set * 'a set) set"
  
translations
  "leadsTo Acts A B" == "(A,B) : leadsto Acts"

inductive "leadsto Acts"
  intrs 

    Basis  "ensures Acts A B ==> leadsTo Acts A B"

    Trans  "[| leadsTo Acts A B;  leadsTo Acts B C |]
	   ==> leadsTo Acts A C"

    Union  "(UN A:S. {(A,B)}) : Pow (leadsto Acts)
	   ==> leadsTo Acts (Union S) B"

  monos "[Pow_mono]"

constdefs wlt :: "[('a * 'a)set set, 'a set] => 'a set"
  "wlt Acts B == Union {A. leadsTo Acts A B}"

end
