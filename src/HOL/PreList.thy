(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + Wellfounded_Relations + NatSimprocs + Recdef + Record +
  Relation_Power + Calculation + SVC_Oracle:

(*belongs to theory Datatype*)
declare case_split [cases type: bool]

(*belongs to theory Wellfounded_Recursion*)
declare wf_induct [induct set: wf]

(*belongs to theory Datatype_Universe; hides popular names *)
hide const Node Atom Leaf Numb Lim Funs Split Case
hide type node item

(*belongs to theory Datatype; canonical case/induct rules for 3-7 tuples*)
lemma prod_cases3 [cases type]: "(!!a b c. y = (a, b, c) ==> P) ==> P"
  apply (cases y)
  apply (case_tac b)
  apply blast
  done

lemma prod_induct3 [induct type]: "(!!a b c. P (a, b, c)) ==> P x"
  apply (cases x)
  apply blast
  done

lemma prod_cases4 [cases type]: "(!!a b c d. y = (a, b, c, d) ==> P) ==> P"
  apply (cases y)
  apply (case_tac c)
  apply blast
  done

lemma prod_induct4 [induct type]: "(!!a b c d. P (a, b, c, d)) ==> P x"
  apply (cases x)
  apply blast
  done

lemma prod_cases5 [cases type]: "(!!a b c d e. y = (a, b, c, d, e) ==> P) ==> P"
  apply (cases y)
  apply (case_tac d)
  apply blast
  done

lemma prod_induct5 [induct type]: "(!!a b c d e. P (a, b, c, d, e)) ==> P x"
  apply (cases x)
  apply blast
  done

lemma prod_cases6 [cases type]: "(!!a b c d e f. y = (a, b, c, d, e, f) ==> P) ==> P"
  apply (cases y)
  apply (case_tac e)
  apply blast
  done

lemma prod_induct6 [induct type]: "(!!a b c d e f. P (a, b, c, d, e, f)) ==> P x"
  apply (cases x)
  apply blast
  done

lemma prod_cases7 [cases type]: "(!!a b c d e f g. y = (a, b, c, d, e, f, g) ==> P) ==> P"
  apply (cases y)
  apply (case_tac f)
  apply blast
  done

lemma prod_induct7 [induct type]: "(!!a b c d e f g. P (a, b, c, d, e, f, g)) ==> P x"
  apply (cases x)
  apply blast
  done


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
