(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + Wellfounded_Relations + NatSimprocs + Recdef + Record +
  Relation_Power + Calculation + SVC_Oracle:

(*belongs to theory HOL*)
declare case_split [cases type: bool]

(*belongs to theory Wellfounded_Recursion*)
declare wf_induct [induct set: wf]

(*belongs to theory Datatype_Universe; hides popular names *)
hide const Node Atom Leaf Numb Lim Funs Split Case


(*belongs to theory Nat, but requires Datatype*)
consts
  Summation :: "(nat => 'a::{zero,plus}) => nat => 'a"
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
