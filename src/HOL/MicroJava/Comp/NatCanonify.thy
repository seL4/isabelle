(*  Title:      HOL/MicroJava/Comp/NatCanonify.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)

theory NatCanonify = Main:

(************************************************************************)
  (* Canonizer for converting nat to int *)
(************************************************************************)

lemma nat_add_canonify: "(n1::nat) + n2 = nat ((int n1) + (int n2))"
by (simp add: nat_add_distrib)

lemma nat_mult_canonify: "(n1::nat) * n2 = nat ((int n1) * (int n2))"
by (simp add: nat_mult_distrib)

lemma nat_diff_canonify: "(n1::nat) - n2 = 
  nat (if (int n1) \<le> (int n2) then 0 else (int n1) - (int n2))"
by (simp add: zdiff_int nat_int)

lemma nat_le_canonify: "((n1::nat) \<le> n2) = ((int n1) \<le> (int n2))"
by arith

lemma nat_less_canonify: "((n1::nat) < n2) = ((int n1) < (int n2))"
by arith

lemma nat_eq_canonify: "((n1::nat) = n2) = ((int n1) = (int n2))"
by arith

lemma nat_if_canonify: "(if b then (n1::nat) else n2) =
  nat (if b then (int n1) else (int n2))"
by simp

lemma int_nat_canonify: "(int (nat n)) = (if 0 \<le> n then n else 0)"
by simp

lemmas nat_canonify = 
  nat_add_canonify nat_mult_canonify nat_diff_canonify 
  nat_le_canonify nat_less_canonify nat_eq_canonify nat_if_canonify 
  int_nat_canonify nat_int

end
