(*  Title:      HOL/NumberTheory/Fib.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

header {* The Fibonacci function *}

theory Fib = Primes:

text {*
  Fibonacci numbers: proofs of laws taken from:
  R. L. Graham, D. E. Knuth, O. Patashnik.  Concrete Mathematics.
  (Addison-Wesley, 1989)

  \bigskip
*}

consts fib :: "nat => nat"
recdef fib  less_than
  zero: "fib 0  = 0"
  one:  "fib 1' = 1'"
  Suc_Suc: "fib (Suc (Suc x)) = fib x + fib (Suc x)"

text {*
  \medskip The difficulty in these proofs is to ensure that the
  induction hypotheses are applied before the definition of @{term
  fib}.  Towards this end, the @{term fib} equations are not declared
  to the Simplifier and are applied very selectively at first.
*}

declare fib.Suc_Suc [simp del]

lemma fib_Suc3: "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
  apply (rule fib.Suc_Suc)
  done


text {* \medskip Concrete Mathematics, page 280 *}

lemma fib_add: "fib (Suc (n + k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  apply (induct n rule: fib.induct)
    prefer 3
    txt {* simplify the LHS just enough to apply the induction hypotheses *}
    apply (simp add: fib.Suc_Suc [of "Suc (m + n)", standard])
    apply (simp_all (no_asm_simp) add: fib.Suc_Suc add_mult_distrib add_mult_distrib2)
    done

lemma fib_Suc_neq_0 [simp]: "fib (Suc n) \<noteq> 0"
  apply (induct n rule: fib.induct)
    apply (simp_all add: fib.Suc_Suc)
  done

lemma [simp]: "0 < fib (Suc n)"
  apply (simp add: neq0_conv [symmetric])
  done

lemma fib_gr_0: "0 < n ==> 0 < fib n"
  apply (rule not0_implies_Suc [THEN exE])
   apply auto
  done


text {*
  \medskip Concrete Mathematics, page 278: Cassini's identity.  It is
  much easier to prove using integers!
*}

lemma fib_Cassini: "int (fib (Suc (Suc n)) * fib n) =
  (if n mod #2 = 0 then int (fib (Suc n) * fib (Suc n)) - #1
   else int (fib (Suc n) * fib (Suc n)) + #1)"
  apply (induct n rule: fib.induct)
    apply (simp add: fib.Suc_Suc)
   apply (simp add: fib.Suc_Suc mod_Suc)
  apply (simp add: fib.Suc_Suc
    add_mult_distrib add_mult_distrib2 mod_Suc zmult_int [symmetric] zmult_ac)
  apply (subgoal_tac "x mod #2 < #2", arith)
  apply simp
  done


text {* \medskip Towards Law 6.111 of Concrete Mathematics *}

lemma gcd_fib_Suc_eq_1: "gcd (fib n, fib (Suc n)) = 1'"
  apply (induct n rule: fib.induct)
    prefer 3
    apply (simp add: gcd_commute fib_Suc3)
   apply (simp_all add: fib.Suc_Suc)
  done

lemma gcd_fib_add: "gcd (fib m, fib (n + m)) = gcd (fib m, fib n)"
  apply (simp (no_asm) add: gcd_commute [of "fib m"])
  apply (case_tac "m = 0")
   apply simp
  apply (clarify dest!: not0_implies_Suc)
  apply (simp add: fib_add)
  apply (simp add: add_commute gcd_non_0)
  apply (simp add: gcd_non_0 [symmetric])
  apply (simp add: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  done

lemma gcd_fib_diff: "m \<le> n ==> gcd (fib m, fib (n - m)) = gcd (fib m, fib n)"
  apply (rule gcd_fib_add [symmetric, THEN trans])
  apply simp
  done

lemma gcd_fib_mod: "0 < m ==> gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)"
  apply (induct n rule: nat_less_induct)
  apply (subst mod_if)
  apply (simp add: gcd_fib_diff mod_geq not_less_iff_le diff_less)
  done

lemma fib_gcd: "fib (gcd (m, n)) = gcd (fib m, fib n)"  -- {* Law 6.111 *}
  apply (induct m n rule: gcd_induct)
   apply simp
  apply (simp add: gcd_non_0)
  apply (simp add: gcd_commute gcd_fib_mod)
  done

lemma fib_mult_eq_setsum:
    "fib (Suc n) * fib n = setsum (\<lambda>k. fib k * fib k) (atMost n)"
  apply (induct n rule: fib.induct)
    apply (auto simp add: atMost_Suc fib.Suc_Suc)
  apply (simp add: add_mult_distrib add_mult_distrib2)
  done

end
