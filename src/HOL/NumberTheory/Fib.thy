(*  ID:         $Id$
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
recdef fib  "measure (\<lambda>x. x)"
   zero:    "fib 0  = 0"
   one:     "fib (Suc 0) = Suc 0"
   Suc_Suc: "fib (Suc (Suc x)) = fib x + fib (Suc x)"

text {*
  \medskip The difficulty in these proofs is to ensure that the
  induction hypotheses are applied before the definition of @{term
  fib}.  Towards this end, the @{term fib} equations are not declared
  to the Simplifier and are applied very selectively at first.
*}

text{*We disable @{text fib.Suc_Suc} for simplification ...*}
declare fib.Suc_Suc [simp del]

text{*...then prove a version that has a more restrictive pattern.*}
lemma fib_Suc3: "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
  by (rule fib.Suc_Suc)


text {* \medskip Concrete Mathematics, page 280 *}

lemma fib_add: "fib (Suc (n + k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  apply (induct n rule: fib.induct)
    prefer 3
    txt {* simplify the LHS just enough to apply the induction hypotheses *}
    apply (simp add: fib_Suc3)
    apply (simp_all add: fib.Suc_Suc add_mult_distrib2)
    done

lemma fib_Suc_neq_0: "fib (Suc n) \<noteq> 0"
  apply (induct n rule: fib.induct)
    apply (simp_all add: fib.Suc_Suc)
  done

lemma fib_Suc_gr_0: "0 < fib (Suc n)"
  by (insert fib_Suc_neq_0 [of n], simp)  

lemma fib_gr_0: "0 < n ==> 0 < fib n"
  by (case_tac n, auto simp add: fib_Suc_gr_0) 


text {*
  \medskip Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
*}

lemma fib_Cassini_int:
 "int (fib (Suc (Suc n)) * fib n) =
  (if n mod 2 = 0 then int (fib (Suc n) * fib (Suc n)) - 1
   else int (fib (Suc n) * fib (Suc n)) + 1)"
  apply (induct n rule: fib.induct)
    apply (simp add: fib.Suc_Suc)
   apply (simp add: fib.Suc_Suc mod_Suc)
  apply (simp add: fib.Suc_Suc add_mult_distrib add_mult_distrib2
                   mod_Suc zmult_int [symmetric])
  apply presburger
  done

text{*We now obtain a version for the natural numbers via the coercion 
   function @{term int}.*}
theorem fib_Cassini:
 "fib (Suc (Suc n)) * fib n =
  (if n mod 2 = 0 then fib (Suc n) * fib (Suc n) - 1
   else fib (Suc n) * fib (Suc n) + 1)"
  apply (rule int_int_eq [THEN iffD1]) 
  apply (simp add: fib_Cassini_int) 
  apply (subst zdiff_int [symmetric]) 
   apply (insert fib_Suc_gr_0 [of n], simp_all)
  done


text {* \medskip Toward Law 6.111 of Concrete Mathematics *}

lemma gcd_fib_Suc_eq_1: "gcd (fib n, fib (Suc n)) = Suc 0"
  apply (induct n rule: fib.induct)
    prefer 3
    apply (simp add: gcd_commute fib_Suc3)
   apply (simp_all add: fib.Suc_Suc)
  done

lemma gcd_fib_add: "gcd (fib m, fib (n + m)) = gcd (fib m, fib n)"
  apply (simp add: gcd_commute [of "fib m"])
  apply (case_tac m)
   apply simp 
  apply (simp add: fib_add)
  apply (simp add: add_commute gcd_non_0 [OF fib_Suc_gr_0])
  apply (simp add: gcd_non_0 [OF fib_Suc_gr_0, symmetric])
  apply (simp add: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  done

lemma gcd_fib_diff: "m \<le> n ==> gcd (fib m, fib (n - m)) = gcd (fib m, fib n)"
  by (simp add: gcd_fib_add [symmetric, of _ "n-m"]) 

lemma gcd_fib_mod: "0 < m ==> gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)"
  apply (induct n rule: nat_less_induct)
  apply (simp add: mod_if gcd_fib_diff mod_geq)
  done

lemma fib_gcd: "fib (gcd (m, n)) = gcd (fib m, fib n)"  -- {* Law 6.111 *}
  apply (induct m n rule: gcd_induct)
  apply (simp_all add: gcd_non_0 gcd_commute gcd_fib_mod)
  done

theorem fib_mult_eq_setsum:
    "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  apply (induct n rule: fib.induct)
    apply (auto simp add: atMost_Suc fib.Suc_Suc)
  apply (simp add: add_mult_distrib add_mult_distrib2)
  done

end
