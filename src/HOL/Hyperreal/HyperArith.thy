(*  Title:      HOL/HyperArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header{*Binary arithmetic and Simplification for the Hyperreals*}

theory HyperArith
imports HyperDef
uses ("hypreal_arith.ML")
begin

subsection{*Absolute Value Function for the Hyperreals*}

lemma hrabs_add_less:
     "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
by (simp add: abs_if split: split_if_asm)

lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::'a::abs_if) | abs x = -x"
by (simp add: abs_if)

lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: abs_if split add: split_if_asm)


subsection{*Embedding the Naturals into the Hyperreals*}

abbreviation
  hypreal_of_nat :: "nat => hypreal" where
  "hypreal_of_nat == of_nat"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
by (simp add: Nats_def image_def)

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

lemma hypreal_of_nat_eq:
     "hypreal_of_nat (n::nat) = hypreal_of_real (real n)"
by (simp add: real_of_nat_def)

lemma hypreal_of_nat:
     "hypreal_of_nat m = star_n (%n. real m)"
apply (fold star_of_def)
apply (simp add: real_of_nat_def)
done

(*
FIXME: we should declare this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric hypreal_diff_def]
*)


use "hypreal_arith.ML"

setup hypreal_arith_setup

end
