(*  Title:      HOL/NatArith.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
*)

header {* More arithmetic on natural numbers *}

theory NatArith
import Nat
files "arith_data.ML"
begin

setup arith_setup


lemma pred_nat_trancl_eq_le: "((m, n) : pred_nat^*) = (m <= n)"
by (simp add: less_eq reflcl_trancl [symmetric]
            del: reflcl_trancl, arith)

lemma nat_diff_split:
    "P(a - b::nat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text nat} *}
  by (cases "a<b" rule: case_split)
    (auto simp add: diff_is_0_eq [THEN iffD2])

lemma nat_diff_split_asm:
    "P(a - b::nat) = (~ (a < b & ~ P 0 | (EX d. a = b + d & ~ P d)))"
    -- {* elimination of @{text -} on @{text nat} in assumptions *}
  by (simp split: nat_diff_split)

ML {*
 val nat_diff_split = thm "nat_diff_split";
 val nat_diff_split_asm = thm "nat_diff_split_asm";
*}
(* Careful: arith_tac produces counter examples!
fun add_arith cs = cs addafter ("arith_tac", arith_tac);
TODO: use arith_tac for force_tac in Provers/clasimp.ML *)

lemmas [arith_split] = nat_diff_split split_min split_max

end
