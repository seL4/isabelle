(*  Title:      HOL/UNITY/Counter
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version close to the original. 

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Counter = UNITY_Main +

(* Variables are names *)
datatype name = C | c nat
types state = name=>int

consts  
  sum  :: "[nat,state]=>int"
  sumj :: "[nat, nat, state]=>int"

primrec (* sum I s = sigma_{i<I}. s (c i) *)
  "sum 0 s = 0"
  "sum (Suc i) s = s (c i) + sum i s"

primrec
  "sumj 0 i s = 0"
  "sumj (Suc n) i s = (if n=i then sum n s else s (c n) + sumj n i s)"
  
types command = "(state*state)set"

constdefs
  a :: "nat=>command"
 "a i == {(s, s'). s'=s(c i:= s (c i) + 1, C:= s C + 1)}"

  Component :: "nat => state program"
  "Component i ==
    mk_total_program({s. s C = 0 & s (c i) = 0}, {a i},
	             \\<Union>G \\<in> preserves (%s. s (c i)). Acts G)"

end  
