(*  Title       : EvenOdd.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1999  University of Edinburgh
    Description : Even and odd numbers defined 
*)

header{*Compatibility file from Parity*}

theory EvenOdd = NthRoot:

subsection{*General Lemmas About Division*}

lemma div_add_self_two_is_m: "(m + m) div 2 = (m::nat)"
by arith
declare div_add_self_two_is_m [simp]

lemma div_mult_self_Suc_Suc: "Suc(Suc(m*2)) div 2 = Suc m"
by arith
declare div_mult_self_Suc_Suc [simp]

lemma div_mult_self_Suc_Suc2: "Suc(Suc(2*m)) div 2 = Suc m"
by arith
declare div_mult_self_Suc_Suc2 [simp]

lemma div_add_self_Suc_Suc: "Suc(Suc(m + m)) div 2 = Suc m"
by arith
declare div_add_self_Suc_Suc [simp]

lemma mod_two_Suc_2m: "Suc (2 * m) mod 2 = 1" 
apply (induct_tac "m")
apply (auto simp add: mod_Suc)
done
declare mod_two_Suc_2m [simp]

lemma Suc_n_le_Suc_Suc_n_div_2: "Suc n div 2 \<le> Suc (Suc n) div 2"
by arith
declare Suc_n_le_Suc_Suc_n_div_2 [simp]

lemma Suc_n_div_2_gt_zero: "(0::nat) < n ==> 0 < (n + 1) div 2"
by arith
declare Suc_n_div_2_gt_zero [simp]

lemma le_Suc_n_div_2: "n div 2 \<le> (Suc n) div 2"
by arith
declare le_Suc_n_div_2 [simp]

lemma div_2_gt_zero: "(1::nat) < n ==> 0 < n div 2" 
by arith
declare div_2_gt_zero [simp]

lemma mod_mult_self3: "(k*n + m) mod n = m mod (n::nat)"
by (simp add: mult_ac add_ac)
declare mod_mult_self3 [simp]

lemma mod_mult_self4: "Suc (k*n + m) mod n = Suc m mod n"
proof -
  have "Suc (k * n + m) mod n = (k * n + Suc m) mod n" by simp
  also have "... = Suc m mod n" by (rule mod_mult_self3) 
  finally show ?thesis .
qed
declare mod_mult_self4 [simp]

lemma nat_mod_idem [simp]: "m mod n mod n = (m mod n :: nat)"
by (case_tac "n=0", auto)

lemma mod_Suc_eq_Suc_mod: "Suc m mod n = Suc (m mod n) mod n"
apply (subst mod_Suc [of m]) 
apply (subst mod_Suc [of "m mod n"], simp) 
done

lemma lemma_4n_add_2_div_2_eq: "((4 * n) + 2) div 2 = (2::nat) * n + 1"
by arith
declare lemma_4n_add_2_div_2_eq [simp]

lemma lemma_Suc_Suc_4n_div_2_eq: "(Suc(Suc(4 * n))) div 2 = (2::nat) * n + 1"
by arith
declare lemma_Suc_Suc_4n_div_2_eq [simp]

lemma lemma_Suc_Suc_4n_div_2_eq2: "(Suc(Suc(n * 4))) div 2 = (2::nat) * n + 1"
by arith
declare lemma_Suc_Suc_4n_div_2_eq2 [simp]


subsection{*More Even/Odd Results*}
 
lemma even_mult_two_ex: "even(n) = (EX m::nat. n = 2*m)"
by (simp add: even_nat_equiv_def2 numeral_2_eq_2)

lemma odd_Suc_mult_two_ex: "odd(n) = (EX m. n = Suc (2*m))"
by (simp add: odd_nat_equiv_def2 numeral_2_eq_2)

lemma even_add: "even(m + n::nat) = (even m = even n)"
by auto
declare even_add [iff]

lemma odd_add: "odd(m + n::nat) = (odd m ~= odd n)"
by auto
declare odd_add [iff]

lemma lemma_even_div2: "even (n::nat) ==> (n + 1) div 2 = n div 2"
apply (simp add: numeral_2_eq_2) 
apply (subst div_Suc)  
apply (simp add: even_nat_mod_two_eq_zero) 
done
declare lemma_even_div2 [simp]

lemma lemma_not_even_div2: "~even n ==> (n + 1) div 2 = Suc (n div 2)"
apply (simp add: numeral_2_eq_2) 
apply (subst div_Suc)  
apply (simp add: odd_nat_mod_two_eq_one) 
done
declare lemma_not_even_div2 [simp]

lemma even_num_iff: "0 < n ==> even n = (~ even(n - 1 :: nat))" 
by (case_tac "n", auto)

lemma even_even_mod_4_iff: "even (n::nat) = even (n mod 4)"
apply (induct n, simp)
apply (subst mod_Suc, simp) 
done

declare neg_one_odd_power [simp]
declare neg_one_even_power [simp]

lemma lemma_odd_mod_4_div_2: "n mod 4 = (3::nat) ==> odd((n - 1) div 2)"
apply (rule_tac t = n and n1 = 4 in mod_div_equality [THEN subst])
apply (simp add: even_num_iff)
done

lemma lemma_even_mod_4_div_2: "n mod 4 = (1::nat) ==> even ((n - 1) div 2)"
by (rule_tac t = n and n1 = 4 in mod_div_equality [THEN subst], simp)

ML
{*
val even_Suc = thm"Parity.even_nat_suc";

val even_mult_two_ex = thm "even_mult_two_ex";
val odd_Suc_mult_two_ex = thm "odd_Suc_mult_two_ex";
val div_add_self_two_is_m = thm "div_add_self_two_is_m";
val div_mult_self_Suc_Suc = thm "div_mult_self_Suc_Suc";
val div_mult_self_Suc_Suc2 = thm "div_mult_self_Suc_Suc2";
val div_add_self_Suc_Suc = thm "div_add_self_Suc_Suc";
val even_add = thm "even_add";
val odd_add = thm "odd_add";
val mod_two_Suc_2m = thm "mod_two_Suc_2m";
val Suc_n_le_Suc_Suc_n_div_2 = thm "Suc_n_le_Suc_Suc_n_div_2";
val Suc_n_div_2_gt_zero = thm "Suc_n_div_2_gt_zero";
val le_Suc_n_div_2 = thm "le_Suc_n_div_2";
val div_2_gt_zero = thm "div_2_gt_zero";
val lemma_even_div2 = thm "lemma_even_div2";
val lemma_not_even_div2 = thm "lemma_not_even_div2";
val even_num_iff = thm "even_num_iff";
val mod_mult_self3 = thm "mod_mult_self3";
val mod_mult_self4 = thm "mod_mult_self4";
val nat_mod_idem = thm "nat_mod_idem";
val mod_Suc_eq_Suc_mod = thm "mod_Suc_eq_Suc_mod";
val even_even_mod_4_iff = thm "even_even_mod_4_iff";
val lemma_4n_add_2_div_2_eq = thm "lemma_4n_add_2_div_2_eq";
val lemma_Suc_Suc_4n_div_2_eq = thm "lemma_Suc_Suc_4n_div_2_eq";
val lemma_Suc_Suc_4n_div_2_eq2 = thm "lemma_Suc_Suc_4n_div_2_eq2";
val lemma_odd_mod_4_div_2 = thm "lemma_odd_mod_4_div_2";
val lemma_even_mod_4_div_2 = thm "lemma_even_mod_4_div_2";
*}

end

