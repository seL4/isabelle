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
 ["!!a.<a,sigma> -a-> n ==> a \\<in> aexp",
  "!!a.<a,sigma> -a-> n ==> sigma \\<in> loc->nat",
  "!!a.<a,sigma> -a-> n ==> n \\<in> nat"];


(**********     type_intrs for evalb     **********)

val evalb_type_intrs = 
 map (fn s => prove_goal Com.thy s (fn _ => [(fast_tac type_cs 1)]))
 ["!!b.<b,sigma> -b-> w ==> b \\<in> bexp",
  "!!b.<b,sigma> -b-> w ==> sigma \\<in> loc->nat",
  "!!b.<b,sigma> -b-> w ==> w \\<in> bool"];


(**********     type_intrs for evalb     **********)

val evalc_type_intrs = 
 map (fn s => prove_goal Com.thy s (fn _ => [(fast_tac type_cs 1)]))
 ["!!c.<c,sigma> -c-> sigma' ==> c \\<in> com",
  "!!c.<c,sigma> -c-> sigma' ==> sigma \\<in> loc->nat",
  "!!c.<c,sigma> -c-> sigma' ==> sigma':loc->nat"];


val op_type_intrs = evala_type_intrs@evalb_type_intrs@evalc_type_intrs;


val aexp_elim_cases = 
   [
    evala.mk_cases "<N(n),sigma> -a-> i",
    evala.mk_cases "<X(x),sigma> -a-> i",
    evala.mk_cases "<Op1(f,e),sigma> -a-> i",
    evala.mk_cases "<Op2(f,a1,a2),sigma>  -a-> i"
   ];
