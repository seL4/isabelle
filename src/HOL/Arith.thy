(*  Title:      HOL/Arith.thy
    ID:         $Id$

Setup arithmetic proof procedures.
*)

theory Arith = Nat
files "arith_data.ML":

setup arith_setup

(*elimination of `-' on nat*)
lemma nat_diff_split:
    "P(a - b::nat) = (ALL d. (a<b --> P 0) & (a = b + d --> P d))"
  by (cases "a < b" rule: case_split) (auto simp add: diff_is_0_eq [RS iffD2])

ML {* val nat_diff_split = thm "nat_diff_split" *}

lemmas [arith_split] = nat_diff_split split_min split_max

end
