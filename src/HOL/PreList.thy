(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + Wellfounded_Relations + NatSimprocs + Recdef + Record +
  Relation_Power:

(*belongs to theory Divides*)
declare dvdI [intro?]  dvdE [elim?]  dvd_trans [trans]

(*belongs to theory Nat*)
lemmas less_induct = nat_less_induct [rule_format, case_names less]

(*belongs to theory Wellfounded_Recursion*)
lemmas wf_induct_rule = wf_induct [rule_format, case_names less, induct set: wf]


(* generic summation indexed over nat *)

consts
  Summation :: "(nat => 'a::{zero, plus}) => nat => 'a"
primrec
  "Summation f 0 = 0"
  "Summation f (Suc n) = Summation f n + f n"

syntax
  "_Summation" :: "idt => nat => 'a => nat"    ("\<Sum>_<_. _" [0, 51, 10] 10)
translations
  "\<Sum>i < n. b" == "Summation (\<lambda>i. b) n"

theorem Summation_step:
    "0 < n ==> (\<Sum>i < n. f i) = (\<Sum>i < n - 1. f i) + f (n - 1)"
  by (induct n) simp_all

end
