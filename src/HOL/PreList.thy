(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Wellfounded_Relations + NatSimprocs + Recdef + Relation_Power:

(*belongs to theory Divides*)
declare dvdI [intro?]  dvdE [elim?]  dvd_trans [trans]

(*belongs to theory Nat*)
lemmas less_induct = nat_less_induct [rule_format, case_names less]

(*belongs to theory Wellfounded_Recursion*)
lemmas wf_induct_rule = wf_induct [rule_format, case_names less, induct set: wf]

end
