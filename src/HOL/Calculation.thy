(*  Title:      HOL/Calculation.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Setup transitivity rules for calculational proofs.  Note that in the
list below later rules have priority.
*)

theory Calculation = IntArith:

theorems [trans] = rev_mp mp

theorem [trans]: "[| s = t; P t |] ==> P s" 		    (*  =  x  x  *)
  by (rule ssubst)

theorem [trans]: "[| P s; s = t |] ==> P t"		    (*  x  =  x  *)
  by (rule subst)

theorems [trans] = dvd_trans                               (* dvd dvd dvd *)

theorem [trans]: "[| c:A; A <= B |] ==> c:B"
  by (rule subsetD)

theorem [trans]: "[| A <= B; c:A |] ==> c:B"
  by (rule subsetD)

theorem [trans]: "[| x ~= y; (x::'a::order) <= y |] ==> x < y"     (*  ~=  <=  < *)
  by (simp! add: order_less_le)

theorem [trans]: "[| (x::'a::order) <= y; x ~= y |] ==> x < y"     (*  <=  ~=  < *)
  by (simp! add: order_less_le)

theorem [trans]: "[| (x::'a::order) < y; y < x |] ==> P"   (*  <  >  P  *)
  by (rule order_less_asym)

theorems [trans] = order_less_trans                        (*  <  <  <  *)
theorems [trans] = order_le_less_trans                     (*  <= <  <  *)
theorems [trans] = order_less_le_trans                     (*  <  <= <  *)
theorems [trans] = order_trans                             (*  <= <= <= *)
theorems [trans] = order_antisym                           (*  <= >= =  *)

theorem [trans]: "[| x <= y; y = z |] ==> x <= z"	    (*  <= =  <= *)
  by (rule subst)

theorem [trans]: "[| x = y; y <= z |] ==> x <= z"	    (*  =  <= <= *)
  by (rule ssubst)

theorem [trans]: "[| x < y; y = z |] ==> x < z"	    (*  <  =  <  *)
  by (rule subst)

theorem [trans]: "[| x = y; y < z |] ==> x < z"	    (*  =  <  <  *)
  by (rule ssubst)

theorems [trans] = trans                                    (*  =  =  =  *)

theorems [elim??] = sym

end
