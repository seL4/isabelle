(*  Title:      HOL/Power.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

*)

header{*Exponentiation and Binomial Coefficients*}

theory Power = Divides:

subsection{*Powers for Arbitrary (Semi)Rings*}

axclass ringpower \<subseteq> semiring, power
  power_0 [simp]:   "a ^ 0       = 1"
  power_Suc: "a ^ (Suc n) = a * (a ^ n)"

lemma power_0_Suc [simp]: "(0::'a::ringpower) ^ (Suc n) = 0"
by (simp add: power_Suc)

text{*It looks plausible as a simprule, but its effect can be strange.*}
lemma power_0_left: "0^n = (if n=0 then 1 else (0::'a::ringpower))"
by (induct_tac "n", auto)

lemma power_one [simp]: "1^n = (1::'a::ringpower)"
apply (induct_tac "n")
apply (auto simp add: power_Suc)  
done

lemma power_one_right [simp]: "(a::'a::ringpower) ^ 1 = a"
by (simp add: power_Suc)

lemma power_add: "(a::'a::ringpower) ^ (m+n) = (a^m) * (a^n)"
apply (induct_tac "n")
apply (simp_all add: power_Suc mult_ac)
done

lemma power_mult: "(a::'a::ringpower) ^ (m*n) = (a^m) ^ n"
apply (induct_tac "n")
apply (simp_all add: power_Suc power_add)
done

lemma power_mult_distrib: "((a::'a::ringpower) * b) ^ n = (a^n) * (b^n)"
apply (induct_tac "n") 
apply (auto simp add: power_Suc mult_ac)
done

lemma zero_less_power:
     "0 < (a::'a::{ordered_semiring,ringpower}) ==> 0 < a^n"
apply (induct_tac "n")
apply (simp_all add: power_Suc zero_less_one mult_pos)
done

lemma zero_le_power:
     "0 \<le> (a::'a::{ordered_semiring,ringpower}) ==> 0 \<le> a^n"
apply (simp add: order_le_less)
apply (erule disjE) 
apply (simp_all add: zero_less_power zero_less_one power_0_left)
done

lemma one_le_power:
     "1 \<le> (a::'a::{ordered_semiring,ringpower}) ==> 1 \<le> a^n"
apply (induct_tac "n")
apply (simp_all add: power_Suc)
apply (rule order_trans [OF _ mult_mono [of 1 _ 1]]) 
apply (simp_all add: zero_le_one order_trans [OF zero_le_one]) 
done

lemma gt1_imp_ge0: "1 < a ==> 0 \<le> (a::'a::ordered_semiring)"
  by (simp add: order_trans [OF zero_le_one order_less_imp_le])

lemma power_gt1_lemma:
     assumes gt1: "1 < (a::'a::{ordered_semiring,ringpower})"
        shows     "1 < a * a^n"
proof -
  have "1*1 < a * a^n"
    proof (rule order_less_le_trans) 
      show "1*1 < a*1" by (simp add: gt1)
      show  "a*1 \<le> a * a^n"
   by (simp only: mult_mono gt1 gt1_imp_ge0 one_le_power order_less_imp_le 
                  zero_le_one order_refl)
    qed
  thus ?thesis by simp
qed

lemma power_gt1:
     "1 < (a::'a::{ordered_semiring,ringpower}) ==> 1 < a ^ (Suc n)"
by (simp add: power_gt1_lemma power_Suc)

lemma power_le_imp_le_exp:
     assumes gt1: "(1::'a::{ringpower,ordered_semiring}) < a"
       shows      "!!n. a^m \<le> a^n ==> m \<le> n"
proof (induct "m")
  case 0
    show ?case by simp
next
  case (Suc m)
    show ?case 
      proof (cases n)
        case 0
          from prems have "a * a^m \<le> 1" by (simp add: power_Suc)
          with gt1 show ?thesis
            by (force simp only: power_gt1_lemma 
                                 linorder_not_less [symmetric])
      next
        case (Suc n)
          from prems show ?thesis 
	    by (force dest: mult_left_le_imp_le
	          simp add: power_Suc order_less_trans [OF zero_less_one gt1]) 
      qed
qed

text{*Surely we can strengthen this? It holds for 0<a<1 too.*}
lemma power_inject_exp [simp]:
     "1 < (a::'a::{ordered_semiring,ringpower}) ==> (a^m = a^n) = (m=n)"
  by (force simp add: order_antisym power_le_imp_le_exp)  

text{*Can relax the first premise to @{term "0<a"} in the case of the
natural numbers.*}
lemma power_less_imp_less_exp:
     "[| (1::'a::{ringpower,ordered_semiring}) < a; a^m < a^n |] ==> m < n"
by (simp add: order_less_le [of m n] order_less_le [of "a^m" "a^n"] 
              power_le_imp_le_exp) 


lemma power_mono:
     "[|a \<le> b; (0::'a::{ringpower,ordered_semiring}) \<le> a|] ==> a^n \<le> b^n"
apply (induct_tac "n") 
apply (simp_all add: power_Suc)
apply (auto intro: mult_mono zero_le_power order_trans [of 0 a b])
done

lemma power_strict_mono [rule_format]:
     "[|a < b; (0::'a::{ringpower,ordered_semiring}) \<le> a|] 
      ==> 0 < n --> a^n < b^n" 
apply (induct_tac "n") 
apply (auto simp add: mult_strict_mono zero_le_power power_Suc
                      order_le_less_trans [of 0 a b])
done

lemma power_eq_0_iff [simp]:
     "(a^n = 0) = (a = (0::'a::{ordered_ring,ringpower}) & 0<n)"
apply (induct_tac "n")
apply (auto simp add: power_Suc zero_neq_one [THEN not_sym])
done

lemma field_power_eq_0_iff [simp]:
     "(a^n = 0) = (a = (0::'a::{field,ringpower}) & 0<n)"
apply (induct_tac "n")
apply (auto simp add: power_Suc field_mult_eq_0_iff zero_neq_one[THEN not_sym])
done

lemma field_power_not_zero: "a \<noteq> (0::'a::{field,ringpower}) ==> a^n \<noteq> 0"
by force

lemma nonzero_power_inverse:
  "a \<noteq> 0 ==> inverse ((a::'a::{field,ringpower}) ^ n) = (inverse a) ^ n"
apply (induct_tac "n")
apply (auto simp add: power_Suc nonzero_inverse_mult_distrib mult_commute)
done

text{*Perhaps these should be simprules.*}
lemma power_inverse:
  "inverse ((a::'a::{field,division_by_zero,ringpower}) ^ n) = (inverse a) ^ n"
apply (induct_tac "n")
apply (auto simp add: power_Suc inverse_mult_distrib)
done

lemma nonzero_power_divide: 
    "b \<noteq> 0 ==> (a/b) ^ n = ((a::'a::{field,ringpower}) ^ n) / (b ^ n)"
by (simp add: divide_inverse power_mult_distrib nonzero_power_inverse)

lemma power_divide: 
    "(a/b) ^ n = ((a::'a::{field,division_by_zero,ringpower}) ^ n / b ^ n)"
apply (case_tac "b=0", simp add: power_0_left)
apply (rule nonzero_power_divide) 
apply assumption 
done

lemma power_abs: "abs(a ^ n) = abs(a::'a::{ordered_ring,ringpower}) ^ n"
apply (induct_tac "n")
apply (auto simp add: power_Suc abs_mult)
done

lemma zero_less_power_abs_iff [simp]:
     "(0 < (abs a)^n) = (a \<noteq> (0::'a::{ordered_ring,ringpower}) | n=0)" 
proof (induct "n")
  case 0
    show ?case by (simp add: zero_less_one)
next
  case (Suc n)
    show ?case by (force simp add: prems power_Suc zero_less_mult_iff)
qed

lemma zero_le_power_abs [simp]:
     "(0::'a::{ordered_ring,ringpower}) \<le> (abs a)^n"
apply (induct_tac "n")
apply (auto simp add: zero_le_one zero_le_power)
done

lemma power_minus: "(-a) ^ n = (- 1)^n * (a::'a::{ring,ringpower}) ^ n"
proof -
  have "-a = (- 1) * a"  by (simp add: minus_mult_left [symmetric])
  thus ?thesis by (simp only: power_mult_distrib)
qed

text{*Lemma for @{text power_strict_decreasing}*}
lemma power_Suc_less:
     "[|(0::'a::{ordered_semiring,ringpower}) < a; a < 1|]
      ==> a * a^n < a^n"
apply (induct_tac n) 
apply (auto simp add: power_Suc mult_strict_left_mono) 
done

lemma power_strict_decreasing:
     "[|n < N; 0 < a; a < (1::'a::{ordered_semiring,ringpower})|]
      ==> a^N < a^n"
apply (erule rev_mp) 
apply (induct_tac "N")  
apply (auto simp add: power_Suc power_Suc_less less_Suc_eq) 
apply (rename_tac m)  
apply (subgoal_tac "a * a^m < 1 * a^n", simp)
apply (rule mult_strict_mono) 
apply (auto simp add: zero_le_power zero_less_one order_less_imp_le)
done

text{*Proof resembles that of @{text power_strict_decreasing}*}
lemma power_decreasing:
     "[|n \<le> N; 0 \<le> a; a \<le> (1::'a::{ordered_semiring,ringpower})|]
      ==> a^N \<le> a^n"
apply (erule rev_mp) 
apply (induct_tac "N") 
apply (auto simp add: power_Suc  le_Suc_eq) 
apply (rename_tac m)  
apply (subgoal_tac "a * a^m \<le> 1 * a^n", simp)
apply (rule mult_mono) 
apply (auto simp add: zero_le_power zero_le_one)
done

lemma power_Suc_less_one:
     "[| 0 < a; a < (1::'a::{ordered_semiring,ringpower}) |] ==> a ^ Suc n < 1"
apply (insert power_strict_decreasing [of 0 "Suc n" a], simp) 
done

text{*Proof again resembles that of @{text power_strict_decreasing}*}
lemma power_increasing:
     "[|n \<le> N; (1::'a::{ordered_semiring,ringpower}) \<le> a|] ==> a^n \<le> a^N"
apply (erule rev_mp) 
apply (induct_tac "N") 
apply (auto simp add: power_Suc le_Suc_eq) 
apply (rename_tac m)
apply (subgoal_tac "1 * a^n \<le> a * a^m", simp)
apply (rule mult_mono) 
apply (auto simp add: order_trans [OF zero_le_one] zero_le_power)
done

text{*Lemma for @{text power_strict_increasing}*}
lemma power_less_power_Suc:
     "(1::'a::{ordered_semiring,ringpower}) < a ==> a^n < a * a^n"
apply (induct_tac n) 
apply (auto simp add: power_Suc mult_strict_left_mono order_less_trans [OF zero_less_one]) 
done

lemma power_strict_increasing:
     "[|n < N; (1::'a::{ordered_semiring,ringpower}) < a|] ==> a^n < a^N"
apply (erule rev_mp) 
apply (induct_tac "N")  
apply (auto simp add: power_less_power_Suc power_Suc less_Suc_eq) 
apply (rename_tac m)
apply (subgoal_tac "1 * a^n < a * a^m", simp)
apply (rule mult_strict_mono)  
apply (auto simp add: order_less_trans [OF zero_less_one] zero_le_power
                 order_less_imp_le)
done

lemma power_le_imp_le_base:
  assumes le: "a ^ Suc n \<le> b ^ Suc n"
      and xnonneg: "(0::'a::{ordered_semiring,ringpower}) \<le> a"
      and ynonneg: "0 \<le> b"
  shows "a \<le> b"
 proof (rule ccontr)
   assume "~ a \<le> b"
   then have "b < a" by (simp only: linorder_not_le)
   then have "b ^ Suc n < a ^ Suc n"
     by (simp only: prems power_strict_mono) 
   from le and this show "False"
      by (simp add: linorder_not_less [symmetric])
 qed
  
lemma power_inject_base:
     "[| a ^ Suc n = b ^ Suc n; 0 \<le> a; 0 \<le> b |] 
      ==> a = (b::'a::{ordered_semiring,ringpower})"
by (blast intro: power_le_imp_le_base order_antisym order_eq_refl sym)


subsection{*Exponentiation for the Natural Numbers*}

primrec (power)
  "p ^ 0 = 1"
  "p ^ (Suc n) = (p::nat) * (p ^ n)"
  
instance nat :: ringpower
proof
  fix z n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed

lemma nat_one_le_power [simp]: "1 \<le> i ==> Suc 0 \<le> i^n"
by (insert one_le_power [of i n], simp)

lemma le_imp_power_dvd: "!!i::nat. m \<le> n ==> i^m dvd i^n"
apply (unfold dvd_def)
apply (erule not_less_iff_le [THEN iffD2, THEN add_diff_inverse, THEN subst])
apply (simp add: power_add)
done

text{*Valid for the naturals, but what if @{text"0<i<1"}?
Premises cannot be weakened: consider the case where @{term "i=0"},
@{term "m=1"} and @{term "n=0"}.*}
lemma nat_power_less_imp_less: "!!i::nat. [| 0 < i; i^m < i^n |] ==> m < n"
apply (rule ccontr)
apply (drule leI [THEN le_imp_power_dvd, THEN dvd_imp_le, THEN leD])
apply (erule zero_less_power, auto) 
done

lemma nat_zero_less_power_iff [simp]: "(0 < x^n) = (x \<noteq> (0::nat) | n=0)"
by (induct_tac "n", auto)

lemma power_le_dvd [rule_format]: "k^j dvd n --> i\<le>j --> k^i dvd (n::nat)"
apply (induct_tac "j")
apply (simp_all add: le_Suc_eq)
apply (blast dest!: dvd_mult_right)
done

lemma power_dvd_imp_le: "[|i^m dvd i^n;  (1::nat) < i|] ==> m \<le> n"
apply (rule power_le_imp_le_exp, assumption)
apply (erule dvd_imp_le, simp)
done


subsection{*Binomial Coefficients*}

text{*This development is based on the work of Andy Gordon and 
Florian Kammueller*}

consts
  binomial :: "[nat,nat] => nat"      (infixl "choose" 65)

primrec
  binomial_0:   "(0     choose k) = (if k = 0 then 1 else 0)"

  binomial_Suc: "(Suc n choose k) =
                 (if k = 0 then 1 else (n choose (k - 1)) + (n choose k))"

lemma binomial_n_0 [simp]: "(n choose 0) = 1"
by (case_tac "n", simp_all)

lemma binomial_0_Suc [simp]: "(0 choose Suc k) = 0"
by simp

lemma binomial_Suc_Suc [simp]:
     "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
by simp

lemma binomial_eq_0 [rule_format]: "\<forall>k. n < k --> (n choose k) = 0"
apply (induct_tac "n", auto)
apply (erule allE)
apply (erule mp, arith)
done

declare binomial_0 [simp del] binomial_Suc [simp del]

lemma binomial_n_n [simp]: "(n choose n) = 1"
apply (induct_tac "n")
apply (simp_all add: binomial_eq_0)
done

lemma binomial_Suc_n [simp]: "(Suc n choose n) = Suc n"
by (induct_tac "n", simp_all)

lemma binomial_1 [simp]: "(n choose Suc 0) = n"
by (induct_tac "n", simp_all)

lemma zero_less_binomial [rule_format]: "k \<le> n --> 0 < (n choose k)"
by (rule_tac m = n and n = k in diff_induct, simp_all)

lemma binomial_eq_0_iff: "(n choose k = 0) = (n<k)"
apply (safe intro!: binomial_eq_0)
apply (erule contrapos_pp)
apply (simp add: zero_less_binomial)
done

lemma zero_less_binomial_iff: "(0 < n choose k) = (k\<le>n)"
by (simp add: linorder_not_less [symmetric] binomial_eq_0_iff [symmetric])

(*Might be more useful if re-oriented*)
lemma Suc_times_binomial_eq [rule_format]:
     "\<forall>k. k \<le> n --> Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
apply (induct_tac "n")
apply (simp add: binomial_0, clarify)
apply (case_tac "k")
apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq 
                      binomial_eq_0)
done

text{*This is the well-known version, but it's harder to use because of the
  need to reason about division.*}
lemma binomial_Suc_Suc_eq_times:
     "k \<le> n ==> (Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
by (simp add: Suc_times_binomial_eq div_mult_self_is_m zero_less_Suc 
        del: mult_Suc mult_Suc_right)

text{*Another version, with -1 instead of Suc.*}
lemma times_binomial_minus1_eq:
     "[|k \<le> n;  0<k|] ==> (n choose k) * k = n * ((n - 1) choose (k - 1))"
apply (cut_tac n = "n - 1" and k = "k - 1" in Suc_times_binomial_eq)
apply (simp split add: nat_diff_split, auto)
done

text{*ML bindings for the general exponentiation theorems*}
ML
{*
val power_0 = thm"power_0";
val power_Suc = thm"power_Suc";
val power_0_Suc = thm"power_0_Suc";
val power_0_left = thm"power_0_left";
val power_one = thm"power_one";
val power_one_right = thm"power_one_right";
val power_add = thm"power_add";
val power_mult = thm"power_mult";
val power_mult_distrib = thm"power_mult_distrib";
val zero_less_power = thm"zero_less_power";
val zero_le_power = thm"zero_le_power";
val one_le_power = thm"one_le_power";
val gt1_imp_ge0 = thm"gt1_imp_ge0";
val power_gt1_lemma = thm"power_gt1_lemma";
val power_gt1 = thm"power_gt1";
val power_le_imp_le_exp = thm"power_le_imp_le_exp";
val power_inject_exp = thm"power_inject_exp";
val power_less_imp_less_exp = thm"power_less_imp_less_exp";
val power_mono = thm"power_mono";
val power_strict_mono = thm"power_strict_mono";
val power_eq_0_iff = thm"power_eq_0_iff";
val field_power_eq_0_iff = thm"field_power_eq_0_iff";
val field_power_not_zero = thm"field_power_not_zero";
val power_inverse = thm"power_inverse";
val nonzero_power_divide = thm"nonzero_power_divide";
val power_divide = thm"power_divide";
val power_abs = thm"power_abs";
val zero_less_power_abs_iff = thm"zero_less_power_abs_iff";
val zero_le_power_abs = thm "zero_le_power_abs";
val power_minus = thm"power_minus";
val power_Suc_less = thm"power_Suc_less";
val power_strict_decreasing = thm"power_strict_decreasing";
val power_decreasing = thm"power_decreasing";
val power_Suc_less_one = thm"power_Suc_less_one";
val power_increasing = thm"power_increasing";
val power_strict_increasing = thm"power_strict_increasing";
val power_le_imp_le_base = thm"power_le_imp_le_base";
val power_inject_base = thm"power_inject_base";
*}
 
text{*ML bindings for the remaining theorems*}
ML
{*
val nat_one_le_power = thm"nat_one_le_power";
val le_imp_power_dvd = thm"le_imp_power_dvd";
val nat_power_less_imp_less = thm"nat_power_less_imp_less";
val nat_zero_less_power_iff = thm"nat_zero_less_power_iff";
val power_le_dvd = thm"power_le_dvd";
val power_dvd_imp_le = thm"power_dvd_imp_le";
val binomial_n_0 = thm"binomial_n_0";
val binomial_0_Suc = thm"binomial_0_Suc";
val binomial_Suc_Suc = thm"binomial_Suc_Suc";
val binomial_eq_0 = thm"binomial_eq_0";
val binomial_n_n = thm"binomial_n_n";
val binomial_Suc_n = thm"binomial_Suc_n";
val binomial_1 = thm"binomial_1";
val zero_less_binomial = thm"zero_less_binomial";
val binomial_eq_0_iff = thm"binomial_eq_0_iff";
val zero_less_binomial_iff = thm"zero_less_binomial_iff";
val Suc_times_binomial_eq = thm"Suc_times_binomial_eq";
val binomial_Suc_Suc_eq_times = thm"binomial_Suc_Suc_eq_times";
val times_binomial_minus1_eq = thm"times_binomial_minus1_eq";
*}

end

