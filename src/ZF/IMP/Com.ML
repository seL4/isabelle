(*  Title:      ZF/IMP/Com.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

val type_cs = claset() addSDs [evala.dom_subset RS subsetD,
			      evalb.dom_subset RS subsetD,
			      evalc.dom_subset RS subsetD];

(**********     type_intrs for evala     **********)

val evala_type_intrs = 
 map (fn s => prove_goal Com.thy s (fn _ => [(fast_tac type_cs 1)]))
 ["!!a.<a,sigma> -a-> n ==> a:aexp",
  "!!a.<a,sigma> -a-> n ==> sigma:loc->nat",
  "!!a.<a,sigma> -a-> n ==> n:nat"];


(**********     type_intrs for evalb     **********)

val evalb_type_intrs = 
 map (fn s => prove_goal Com.thy s (fn _ => [(fast_tac type_cs 1)]))
 ["!!b.<b,sigma> -b-> w ==> b:bexp",
  "!!b.<b,sigma> -b-> w ==> sigma:loc->nat",
  "!!b.<b,sigma> -b-> w ==> w:bool"];


(**********     type_intrs for evalb     **********)

val evalc_type_intrs = 
 map (fn s => prove_goal Com.thy s (fn _ => [(fast_tac type_cs 1)]))
 ["!!c.<c,sigma> -c-> sigma' ==> c:com",
  "!!c.<c,sigma> -c-> sigma' ==> sigma:loc->nat",
  "!!c.<c,sigma> -c-> sigma' ==> sigma':loc->nat"];


val op_type_intrs = evala_type_intrs@evalb_type_intrs@evalc_type_intrs;


val aexp_elim_cases = 
   [
    evala.mk_cases "<N(n),sigma> -a-> i",
    evala.mk_cases "<X(x),sigma> -a-> i",
    evala.mk_cases "<Op1(f,e),sigma> -a-> i",
    evala.mk_cases "<Op2(f,a1,a2),sigma>  -a-> i"
   ];
