(*  Title       : EvenOdd.thy
    ID:         $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1999  University of Edinburgh
*)

header{*Even and Odd Numbers: Compatibility file for Parity*}

theory EvenOdd = NthRoot:

subsection{*General Lemmas About Division*}

lemma Suc_times_mod_eq: "1<k ==> Suc (k * m) mod k = 1" 
apply (induct_tac "m")
apply (simp_all add: mod_Suc)
done

declare Suc_times_mod_eq [of "number_of w", standard, simp]

lemma [simp]: "n div k \<le> (Suc n) div k"
by (simp add: div_le_mono) 

lemma Suc_n_div_2_gt_zero [simp]: "(0::nat) < n ==> 0 < (n + 1) div 2"
by arith

lemma div_2_gt_zero [simp]: "(1::nat) < n ==> 0 < n div 2" 
by arith

lemma mod_mult_self3 [simp]: "(k*n + m) mod n = m mod (n::nat)"
by (simp add: mult_ac add_ac)

lemma mod_mult_self4 [simp]: "Suc (k*n + m) mod n = Suc m mod n"
proof -
  have "Suc (k * n + m) mod n = (k * n + Suc m) mod n" by simp
  also have "... = Suc m mod n" by (rule mod_mult_self3) 
  finally show ?thesis .
qed

lemma mod_Suc_eq_Suc_mod: "Suc m mod n = Suc (m mod n) mod n"
apply (subst mod_Suc [of m]) 
apply (subst mod_Suc [of "m mod n"], simp) 
done


subsection{*More Even/Odd Results*}
 
lemma even_mult_two_ex: "even(n) = (\<exists>m::nat. n = 2*m)"
by (simp add: even_nat_equiv_def2 numeral_2_eq_2)

lemma odd_Suc_mult_two_ex: "odd(n) = (\<exists>m. n = Suc (2*m))"
by (simp add: odd_nat_equiv_def2 numeral_2_eq_2)

lemma even_add [simp]: "even(m + n::nat) = (even m = even n)" 
by auto

lemma odd_add [simp]: "odd(m + n::nat) = (odd m \<noteq> odd n)"
by auto

lemma lemma_even_div2 [simp]: "even (n::nat) ==> (n + 1) div 2 = n div 2"
apply (simp add: numeral_2_eq_2) 
apply (subst div_Suc)  
apply (simp add: even_nat_mod_two_eq_zero) 
done

lemma lemma_not_even_div2 [simp]: "~even n ==> (n + 1) div 2 = Suc (n div 2)"
apply (simp add: numeral_2_eq_2) 
apply (subst div_Suc)  
apply (simp add: odd_nat_mod_two_eq_one) 
done

lemma even_num_iff: "0 < n ==> even n = (~ even(n - 1 :: nat))" 
by (case_tac "n", auto)

lemma even_even_mod_4_iff: "even (n::nat) = even (n mod 4)"
apply (induct n, simp)
apply (subst mod_Suc, simp) 
done

lemma lemma_odd_mod_4_div_2: "n mod 4 = (3::nat) ==> odd((n - 1) div 2)"
apply (rule_tac t = n and n1 = 4 in mod_div_equality [THEN subst])
apply (simp add: even_num_iff)
done

lemma lemma_even_mod_4_div_2: "n mod 4 = (1::nat) ==> even ((n - 1) div 2)"
by (rule_tac t = n and n1 = 4 in mod_div_equality [THEN subst], simp)

ML
{*
val even_nat_Suc = thm"Parity.even_nat_Suc";

val even_mult_two_ex = thm "even_mult_two_ex";
val odd_Suc_mult_two_ex = thm "odd_Suc_mult_two_ex";
val even_add = thm "even_add";
val odd_add = thm "odd_add";
val Suc_n_div_2_gt_zero = thm "Suc_n_div_2_gt_zero";
val div_2_gt_zero = thm "div_2_gt_zero";
val even_num_iff = thm "even_num_iff";
val nat_mod_div_trivial = thm "nat_mod_div_trivial";
val nat_mod_mod_trivial = thm "nat_mod_mod_trivial";
val mod_Suc_eq_Suc_mod = thm "mod_Suc_eq_Suc_mod";
val even_even_mod_4_iff = thm "even_even_mod_4_iff";
val lemma_odd_mod_4_div_2 = thm "lemma_odd_mod_4_div_2";
val lemma_even_mod_4_div_2 = thm "lemma_even_mod_4_div_2";
*}

end

