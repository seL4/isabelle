(*  Title:      HOL/NatArith.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* More arithmetic on natural numbers *}

theory NatArith = Nat
files "arith_data.ML":

setup arith_setup


lemma pred_nat_trancl_eq_le: "((m, n) : pred_nat^*) = (m <= n)"
apply (simp add: less_eq reflcl_trancl [symmetric]
            del: reflcl_trancl)
apply arith
done

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

fun add_arith cs = cs addafter ("arith_tac", arith_tac);
*} (* TODO: use arith_tac for force_tac in Provers/clasip.ML *)

lemmas [arith_split] = nat_diff_split split_min split_max


subsubsection {* Generic summation indexed over natural numbers *}

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
