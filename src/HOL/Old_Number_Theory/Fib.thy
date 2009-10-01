(*  ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

header {* The Fibonacci function *}

theory Fib
imports Primes
begin

text {*
  Fibonacci numbers: proofs of laws taken from:
  R. L. Graham, D. E. Knuth, O. Patashnik.  Concrete Mathematics.
  (Addison-Wesley, 1989)

  \bigskip
*}

fun fib :: "nat \<Rightarrow> nat"
where
         "fib 0 = 0"
|        "fib (Suc 0) = 1"
| fib_2: "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {*
  \medskip The difficulty in these proofs is to ensure that the
  induction hypotheses are applied before the definition of @{term
  fib}.  Towards this end, the @{term fib} equations are not declared
  to the Simplifier and are applied very selectively at first.
*}

text{*We disable @{text fib.fib_2fib_2} for simplification ...*}
declare fib_2 [simp del]

text{*...then prove a version that has a more restrictive pattern.*}
lemma fib_Suc3: "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
  by (rule fib_2)

text {* \medskip Concrete Mathematics, page 280 *}

lemma fib_add: "fib (Suc (n + k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
proof (induct n rule: fib.induct)
  case 1 show ?case by simp
next
  case 2 show ?case  by (simp add: fib_2)
next
  case 3 thus ?case by (simp add: fib_2 add_mult_distrib2)
qed

lemma fib_Suc_neq_0: "fib (Suc n) \<noteq> 0"
  apply (induct n rule: fib.induct)
    apply (simp_all add: fib_2)
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
proof(induct n rule: fib.induct)
  case 1 thus ?case by (simp add: fib_2)
next
  case 2 thus ?case by (simp add: fib_2 mod_Suc)
next 
  case (3 x) 
  have "Suc 0 \<noteq> x mod 2 \<longrightarrow> x mod 2 = 0" by presburger
  with "3.hyps" show ?case by (simp add: fib.simps add_mult_distrib add_mult_distrib2)
qed

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

lemma gcd_fib_Suc_eq_1: "gcd (fib n) (fib (Suc n)) = Suc 0"
  apply (induct n rule: fib.induct)
    prefer 3
    apply (simp add: gcd_commute fib_Suc3)
   apply (simp_all add: fib_2)
  done

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
  apply (simp add: gcd_commute [of "fib m"])
  apply (case_tac m)
   apply simp 
  apply (simp add: fib_add)
  apply (simp add: add_commute gcd_non_0 [OF fib_Suc_gr_0])
  apply (simp add: gcd_non_0 [OF fib_Suc_gr_0, symmetric])
  apply (simp add: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  done

lemma gcd_fib_diff: "m \<le> n ==> gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add [symmetric, of _ "n-m"]) 

lemma gcd_fib_mod: "0 < m ==> gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: less_induct)
  case (less n)
  from less.prems have pos_m: "0 < m" .
  show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
  proof (cases "m < n")
    case True note m_n = True
    then have m_n': "m \<le> n" by auto
    with pos_m have pos_n: "0 < n" by auto
    with pos_m m_n have diff: "n - m < n" by auto
    have "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib ((n - m) mod m))"
    by (simp add: mod_if [of n]) (insert m_n, auto)
    also have "\<dots> = gcd (fib m) (fib (n - m))" by (simp add: less.hyps diff pos_m)
    also have "\<dots> = gcd (fib m) (fib n)" by (simp add: gcd_fib_diff m_n')
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
    by (cases "m = n") auto
  qed
qed

lemma fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"  -- {* Law 6.111 *}
  apply (induct m n rule: gcd_induct)
  apply (simp_all add: gcd_non_0 gcd_commute gcd_fib_mod)
  done

theorem fib_mult_eq_setsum:
    "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  apply (induct n rule: fib.induct)
    apply (auto simp add: atMost_Suc fib_2)
  apply (simp add: add_mult_distrib add_mult_distrib2)
  done

end
