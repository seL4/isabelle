(*  Title:      HOL/Library/Nat_Infinity.thy
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*
  \title{Natural numbers with infinity}
  \author{David von Oheimb}
*}

theory Nat_Infinity = Main:

subsection "Definitions"

text {*
  We extend the standard natural numbers by a special value indicating
  infinity.  This includes extending the ordering relations @{term "op
  <"} and @{term "op \<le>"}.
*}

datatype inat = Fin nat | Infty

instance inat :: ord ..
instance inat :: zero ..

consts
  iSuc :: "inat => inat"

syntax (xsymbols)
  Infty :: inat    ("\<infinity>")

defs
  iZero_def: "0 == Fin 0"
  iSuc_def: "iSuc i == case i of Fin n  => Fin (Suc n) | \<infinity> => \<infinity>"
  iless_def: "m < n ==
    case m of Fin m1 => (case n of Fin n1 => m1 < n1 | \<infinity> => True)
    | \<infinity>  => False"
  ile_def: "(m::inat) \<le> n == \<not> (n < m)"

lemmas inat_defs = iZero_def iSuc_def iless_def ile_def
lemmas inat_splits = inat.split inat.split_asm

text {*
  Below is a not quite complete set of theorems.  Use method @{text
  "(simp add: inat_defs split:inat_splits, arith?)"} to prove new
  theorems or solve arithmetic subgoals involving @{typ inat} on the
  fly.
*}

subsection "Constructors"

lemma Fin_0: "Fin 0 = 0"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Infty_ne_i0 [simp]: "\<infinity> \<noteq> 0"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma i0_ne_Infty [simp]: "0 \<noteq> \<infinity>"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_Fin [simp]: "iSuc (Fin n) = Fin (Suc n)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_Infty [simp]: "iSuc \<infinity> = \<infinity>"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_ne_0 [simp]: "iSuc n \<noteq> 0"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_inject [simp]: "(iSuc x = iSuc y) = (x = y)"
  by (simp add:inat_defs split:inat_splits, arith?)


subsection "Ordering relations"

lemma Infty_ilessE [elim!]: "\<infinity> < Fin m ==> R"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_linear: "m < n \<or> m = n \<or> n < (m::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_not_refl [simp]: "\<not> n < (n::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_trans: "i < j ==> j < k ==> i < (k::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_not_sym: "n < m ==> \<not> m < (n::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Fin_iless_mono [simp]: "(Fin n < Fin m) = (n < m)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Fin_iless_Infty [simp]: "Fin n < \<infinity>"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Infty_eq [simp]: "n < \<infinity> = (n \<noteq> \<infinity>)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma i0_eq [simp]: "((0::inat) < n) = (n \<noteq> 0)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma i0_iless_iSuc [simp]: "0 < iSuc n"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma not_ilessi0 [simp]: "\<not> n < (0::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Fin_iless: "n < Fin m ==> \<exists>k. n = Fin k"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_mono [simp]: "iSuc n < iSuc m = (n < m)"
  by (simp add:inat_defs split:inat_splits, arith?)


(* ----------------------------------------------------------------------- *)

lemma ile_def2: "m \<le> n = (m < n \<or> m = (n::inat))"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ile_refl [simp]: "n \<le> (n::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ile_trans: "i \<le> j ==> j \<le> k ==> i \<le> (k::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ile_iless_trans: "i \<le> j ==> j < k ==> i < (k::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_ile_trans: "i < j ==> j \<le> k ==> i < (k::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Infty_ub [simp]: "n \<le> \<infinity>"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma i0_lb [simp]: "(0::inat) \<le> n"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Infty_ileE [elim!]: "\<infinity> \<le> Fin m ==> R"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Fin_ile_mono [simp]: "(Fin n \<le> Fin m) = (n \<le> m)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ilessI1: "n \<le> m ==> n \<noteq> m ==> n < (m::inat)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ileI1: "m < n ==> iSuc m \<le> n"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Suc_ile_eq: "Fin (Suc m) \<le> n = (Fin m < n)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iSuc_ile_mono [simp]: "iSuc n \<le> iSuc m = (n \<le> m)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma iless_Suc_eq [simp]: "Fin m < iSuc n = (Fin m \<le> n)"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma not_iSuc_ilei0 [simp]: "\<not> iSuc n \<le> 0"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma ile_iSuc [simp]: "n \<le> iSuc n"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma Fin_ile: "n \<le> Fin m ==> \<exists>k. n = Fin k"
  by (simp add:inat_defs split:inat_splits, arith?)

lemma chain_incr: "\<forall>i. \<exists>j. Y i < Y j ==> \<exists>j. Fin k < Y j"
  apply (induct_tac k)
   apply (simp (no_asm) only: Fin_0)
   apply (fast intro: ile_iless_trans i0_lb)
  apply (erule exE)
  apply (drule spec)
  apply (erule exE)
  apply (drule ileI1)
  apply (rule iSuc_Fin [THEN subst])
  apply (rule exI)
  apply (erule (1) ile_iless_trans)
  done

end
