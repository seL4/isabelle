(*  Title:      HOL/NatArith.thy
    ID:         $Id$

Setup arithmetic proof procedures.
*)

theory NatArith = Nat
files "arith_data.ML":

setup arith_setup

(*elimination of `-' on nat*)
lemma nat_diff_split:
    "P(a - b::nat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
  by (cases "a<b" rule: case_split) (auto simp add: diff_is_0_eq [THEN iffD2])

(*elimination of `-' on nat in assumptions*)
lemma nat_diff_split_asm:
    "P(a - b::nat) = (~ (a < b & ~ P 0 | (EX d. a = b + d & ~ P d)))"
  by (simp split: nat_diff_split)

ML {*
 val nat_diff_split = thm "nat_diff_split";
 val nat_diff_split_asm = thm "nat_diff_split_asm";

(* TODO: use this for force_tac in Provers/clasip.ML *)
fun add_arith cs = cs addafter ("arith_tac", arith_tac);
*}

lemmas [arith_split] = nat_diff_split split_min split_max


end
