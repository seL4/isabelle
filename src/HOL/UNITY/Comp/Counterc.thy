(*  Title:      HOL/UNITY/Counterc
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version with a full use of "compatibility "

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Counterc =  Comp +
types state
arities state :: term

consts
  C :: "state=>int"
  c :: "state=>nat=>int"

consts  
  sum  :: "[nat,state]=>int"
  sumj :: "[nat, nat, state]=>int"

primrec (* sum I s = sigma_{i<I}. c s i *)
  "sum 0 s = Numeral0"
  "sum (Suc i) s = (c s) i + sum i s"

primrec
  "sumj 0 i s = Numeral0"
  "sumj (Suc n) i s = (if n=i then sum n s else (c s) n + sumj n i s)"
  
types command = "(state*state)set"

constdefs
  a :: "nat=>command"
 "a i == {(s, s'). (c s') i = (c s) i + Numeral1 & (C s') = (C s) + Numeral1}"
 
  Component :: "nat => state program"
  "Component i == mk_program({s. C s = Numeral0 & (c s) i = Numeral0}, {a i},
	       UN G: preserves (%s. (c s) i). Acts G)"
end  
