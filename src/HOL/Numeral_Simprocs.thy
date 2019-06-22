(* Author: Various *)

section \<open>Combination and Cancellation Simprocs for Numeral Expressions\<close>

theory Numeral_Simprocs
imports Divides
begin

ML_file \<open>~~/src/Provers/Arith/assoc_fold.ML\<close>
ML_file \<open>~~/src/Provers/Arith/cancel_numerals.ML\<close>
ML_file \<open>~~/src/Provers/Arith/combine_numerals.ML\<close>
ML_file \<open>~~/src/Provers/Arith/cancel_numeral_factor.ML\<close>
ML_file \<open>~~/src/Provers/Arith/extract_common_term.ML\<close>

lemmas semiring_norm =
  Let_def arith_simps diff_nat_numeral rel_simps
  if_False if_True
  add_0 add_Suc add_numeral_left
  add_neg_numeral_left mult_numeral_left
  numeral_One [symmetric] uminus_numeral_One [symmetric] Suc_eq_plus1
  eq_numeral_iff_iszero not_iszero_Numeral1

declare split_div [of _ _ "numeral k", arith_split] for k
declare split_mod [of _ _ "numeral k", arith_split] for k

text \<open>For \<open>combine_numerals\<close>\<close>

lemma left_add_mult_distrib: "i*u + (j*u + k) = (i+j)*u + (k::nat)"
by (simp add: add_mult_distrib)

text \<open>For \<open>cancel_numerals\<close>\<close>

lemma nat_diff_add_eq1:
     "j <= (i::nat) ==> ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)"
by (simp split: nat_diff_split add: add_mult_distrib)

lemma nat_diff_add_eq2:
     "i <= (j::nat) ==> ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))"
by (simp split: nat_diff_split add: add_mult_distrib)

lemma nat_eq_add_iff1:
     "j <= (i::nat) ==> (i*u + m = j*u + n) = ((i-j)*u + m = n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

lemma nat_eq_add_iff2:
     "i <= (j::nat) ==> (i*u + m = j*u + n) = (m = (j-i)*u + n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff1:
     "j <= (i::nat) ==> (i*u + m < j*u + n) = ((i-j)*u + m < n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff2:
     "i <= (j::nat) ==> (i*u + m < j*u + n) = (m < (j-i)*u + n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff1:
     "j <= (i::nat) ==> (i*u + m <= j*u + n) = ((i-j)*u + m <= n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff2:
     "i <= (j::nat) ==> (i*u + m <= j*u + n) = (m <= (j-i)*u + n)"
by (auto split: nat_diff_split simp add: add_mult_distrib)

text \<open>For \<open>cancel_numeral_factors\<close>\<close>

lemma nat_mult_le_cancel1: "(0::nat) < k ==> (k*m <= k*n) = (m<=n)"
by auto

lemma nat_mult_less_cancel1: "(0::nat) < k ==> (k*m < k*n) = (m<n)"
by auto

lemma nat_mult_eq_cancel1: "(0::nat) < k ==> (k*m = k*n) = (m=n)"
by auto

lemma nat_mult_div_cancel1: "(0::nat) < k ==> (k*m) div (k*n) = (m div n)"
by auto

lemma nat_mult_dvd_cancel_disj[simp]:
  "(k*m) dvd (k*n) = (k=0 \<or> m dvd (n::nat))"
by (auto simp: dvd_eq_mod_eq_0 mod_mult_mult1)

lemma nat_mult_dvd_cancel1: "0 < k \<Longrightarrow> (k*m) dvd (k*n::nat) = (m dvd n)"
by(auto)

text \<open>For \<open>cancel_factor\<close>\<close>

lemmas nat_mult_le_cancel_disj = mult_le_cancel1

lemmas nat_mult_less_cancel_disj = mult_less_cancel1

lemma nat_mult_eq_cancel_disj:
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> k = 0 \<or> m = n"
  by auto

lemma nat_mult_div_cancel_disj [simp]:
  fixes k m n :: nat
  shows "(k * m) div (k * n) = (if k = 0 then 0 else m div n)"
  by (fact div_mult_mult1_if)

lemma numeral_times_minus_swap:
  fixes x:: "'a::comm_ring_1" shows  "numeral w * -x = x * - numeral w"
  by (simp add: mult.commute)

ML_file \<open>Tools/numeral_simprocs.ML\<close>

simproc_setup semiring_assoc_fold
  ("(a::'a::comm_semiring_1_cancel) * b") =
  \<open>fn phi => Numeral_Simprocs.assoc_fold\<close>

(* TODO: see whether the type class can be generalized further *)
simproc_setup int_combine_numerals
  ("(i::'a::comm_ring_1) + j" | "(i::'a::comm_ring_1) - j") =
  \<open>fn phi => Numeral_Simprocs.combine_numerals\<close>

simproc_setup field_combine_numerals
  ("(i::'a::{field,ring_char_0}) + j"
  |"(i::'a::{field,ring_char_0}) - j") =
  \<open>fn phi => Numeral_Simprocs.field_combine_numerals\<close>

simproc_setup inteq_cancel_numerals
  ("(l::'a::comm_ring_1) + m = n"
  |"(l::'a::comm_ring_1) = m + n"
  |"(l::'a::comm_ring_1) - m = n"
  |"(l::'a::comm_ring_1) = m - n"
  |"(l::'a::comm_ring_1) * m = n"
  |"(l::'a::comm_ring_1) = m * n"
  |"- (l::'a::comm_ring_1) = m"
  |"(l::'a::comm_ring_1) = - m") =
  \<open>fn phi => Numeral_Simprocs.eq_cancel_numerals\<close>

simproc_setup intless_cancel_numerals
  ("(l::'a::linordered_idom) + m < n"
  |"(l::'a::linordered_idom) < m + n"
  |"(l::'a::linordered_idom) - m < n"
  |"(l::'a::linordered_idom) < m - n"
  |"(l::'a::linordered_idom) * m < n"
  |"(l::'a::linordered_idom) < m * n"
  |"- (l::'a::linordered_idom) < m"
  |"(l::'a::linordered_idom) < - m") =
  \<open>fn phi => Numeral_Simprocs.less_cancel_numerals\<close>

simproc_setup intle_cancel_numerals
  ("(l::'a::linordered_idom) + m \<le> n"
  |"(l::'a::linordered_idom) \<le> m + n"
  |"(l::'a::linordered_idom) - m \<le> n"
  |"(l::'a::linordered_idom) \<le> m - n"
  |"(l::'a::linordered_idom) * m \<le> n"
  |"(l::'a::linordered_idom) \<le> m * n"
  |"- (l::'a::linordered_idom) \<le> m"
  |"(l::'a::linordered_idom) \<le> - m") =
  \<open>fn phi => Numeral_Simprocs.le_cancel_numerals\<close>

simproc_setup ring_eq_cancel_numeral_factor
  ("(l::'a::{idom,ring_char_0}) * m = n"
  |"(l::'a::{idom,ring_char_0}) = m * n") =
  \<open>fn phi => Numeral_Simprocs.eq_cancel_numeral_factor\<close>

simproc_setup ring_less_cancel_numeral_factor
  ("(l::'a::linordered_idom) * m < n"
  |"(l::'a::linordered_idom) < m * n") =
  \<open>fn phi => Numeral_Simprocs.less_cancel_numeral_factor\<close>

simproc_setup ring_le_cancel_numeral_factor
  ("(l::'a::linordered_idom) * m <= n"
  |"(l::'a::linordered_idom) <= m * n") =
  \<open>fn phi => Numeral_Simprocs.le_cancel_numeral_factor\<close>

(* TODO: remove comm_ring_1 constraint if possible *)
simproc_setup int_div_cancel_numeral_factors
  ("((l::'a::{euclidean_semiring_cancel,comm_ring_1,ring_char_0}) * m) div n"
  |"(l::'a::{euclidean_semiring_cancel,comm_ring_1,ring_char_0}) div (m * n)") =
  \<open>fn phi => Numeral_Simprocs.div_cancel_numeral_factor\<close>

simproc_setup divide_cancel_numeral_factor
  ("((l::'a::{field,ring_char_0}) * m) / n"
  |"(l::'a::{field,ring_char_0}) / (m * n)"
  |"((numeral v)::'a::{field,ring_char_0}) / (numeral w)") =
  \<open>fn phi => Numeral_Simprocs.divide_cancel_numeral_factor\<close>

simproc_setup ring_eq_cancel_factor
  ("(l::'a::idom) * m = n" | "(l::'a::idom) = m * n") =
  \<open>fn phi => Numeral_Simprocs.eq_cancel_factor\<close>

simproc_setup linordered_ring_le_cancel_factor
  ("(l::'a::linordered_idom) * m <= n"
  |"(l::'a::linordered_idom) <= m * n") =
  \<open>fn phi => Numeral_Simprocs.le_cancel_factor\<close>

simproc_setup linordered_ring_less_cancel_factor
  ("(l::'a::linordered_idom) * m < n"
  |"(l::'a::linordered_idom) < m * n") =
  \<open>fn phi => Numeral_Simprocs.less_cancel_factor\<close>

simproc_setup int_div_cancel_factor
  ("((l::'a::euclidean_semiring_cancel) * m) div n"
  |"(l::'a::euclidean_semiring_cancel) div (m * n)") =
  \<open>fn phi => Numeral_Simprocs.div_cancel_factor\<close>

simproc_setup int_mod_cancel_factor
  ("((l::'a::euclidean_semiring_cancel) * m) mod n"
  |"(l::'a::euclidean_semiring_cancel) mod (m * n)") =
  \<open>fn phi => Numeral_Simprocs.mod_cancel_factor\<close>

simproc_setup dvd_cancel_factor
  ("((l::'a::idom) * m) dvd n"
  |"(l::'a::idom) dvd (m * n)") =
  \<open>fn phi => Numeral_Simprocs.dvd_cancel_factor\<close>

simproc_setup divide_cancel_factor
  ("((l::'a::field) * m) / n"
  |"(l::'a::field) / (m * n)") =
  \<open>fn phi => Numeral_Simprocs.divide_cancel_factor\<close>

ML_file \<open>Tools/nat_numeral_simprocs.ML\<close>

simproc_setup nat_combine_numerals
  ("(i::nat) + j" | "Suc (i + j)") =
  \<open>fn phi => Nat_Numeral_Simprocs.combine_numerals\<close>

simproc_setup nateq_cancel_numerals
  ("(l::nat) + m = n" | "(l::nat) = m + n" |
   "(l::nat) * m = n" | "(l::nat) = m * n" |
   "Suc m = n" | "m = Suc n") =
  \<open>fn phi => Nat_Numeral_Simprocs.eq_cancel_numerals\<close>

simproc_setup natless_cancel_numerals
  ("(l::nat) + m < n" | "(l::nat) < m + n" |
   "(l::nat) * m < n" | "(l::nat) < m * n" |
   "Suc m < n" | "m < Suc n") =
  \<open>fn phi => Nat_Numeral_Simprocs.less_cancel_numerals\<close>

simproc_setup natle_cancel_numerals
  ("(l::nat) + m \<le> n" | "(l::nat) \<le> m + n" |
   "(l::nat) * m \<le> n" | "(l::nat) \<le> m * n" |
   "Suc m \<le> n" | "m \<le> Suc n") =
  \<open>fn phi => Nat_Numeral_Simprocs.le_cancel_numerals\<close>

simproc_setup natdiff_cancel_numerals
  ("((l::nat) + m) - n" | "(l::nat) - (m + n)" |
   "(l::nat) * m - n" | "(l::nat) - m * n" |
   "Suc m - n" | "m - Suc n") =
  \<open>fn phi => Nat_Numeral_Simprocs.diff_cancel_numerals\<close>

simproc_setup nat_eq_cancel_numeral_factor
  ("(l::nat) * m = n" | "(l::nat) = m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.eq_cancel_numeral_factor\<close>

simproc_setup nat_less_cancel_numeral_factor
  ("(l::nat) * m < n" | "(l::nat) < m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.less_cancel_numeral_factor\<close>

simproc_setup nat_le_cancel_numeral_factor
  ("(l::nat) * m <= n" | "(l::nat) <= m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.le_cancel_numeral_factor\<close>

simproc_setup nat_div_cancel_numeral_factor
  ("((l::nat) * m) div n" | "(l::nat) div (m * n)") =
  \<open>fn phi => Nat_Numeral_Simprocs.div_cancel_numeral_factor\<close>

simproc_setup nat_dvd_cancel_numeral_factor
  ("((l::nat) * m) dvd n" | "(l::nat) dvd (m * n)") =
  \<open>fn phi => Nat_Numeral_Simprocs.dvd_cancel_numeral_factor\<close>

simproc_setup nat_eq_cancel_factor
  ("(l::nat) * m = n" | "(l::nat) = m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.eq_cancel_factor\<close>

simproc_setup nat_less_cancel_factor
  ("(l::nat) * m < n" | "(l::nat) < m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.less_cancel_factor\<close>

simproc_setup nat_le_cancel_factor
  ("(l::nat) * m <= n" | "(l::nat) <= m * n") =
  \<open>fn phi => Nat_Numeral_Simprocs.le_cancel_factor\<close>

simproc_setup nat_div_cancel_factor
  ("((l::nat) * m) div n" | "(l::nat) div (m * n)") =
  \<open>fn phi => Nat_Numeral_Simprocs.div_cancel_factor\<close>

simproc_setup nat_dvd_cancel_factor
  ("((l::nat) * m) dvd n" | "(l::nat) dvd (m * n)") =
  \<open>fn phi => Nat_Numeral_Simprocs.dvd_cancel_factor\<close>

declaration \<open>
  K (Lin_Arith.add_simprocs
      [\<^simproc>\<open>semiring_assoc_fold\<close>,
       \<^simproc>\<open>int_combine_numerals\<close>,
       \<^simproc>\<open>inteq_cancel_numerals\<close>,
       \<^simproc>\<open>intless_cancel_numerals\<close>,
       \<^simproc>\<open>intle_cancel_numerals\<close>,
       \<^simproc>\<open>field_combine_numerals\<close>,
       \<^simproc>\<open>nat_combine_numerals\<close>,
       \<^simproc>\<open>nateq_cancel_numerals\<close>,
       \<^simproc>\<open>natless_cancel_numerals\<close>,
       \<^simproc>\<open>natle_cancel_numerals\<close>,
       \<^simproc>\<open>natdiff_cancel_numerals\<close>,
       Numeral_Simprocs.field_divide_cancel_numeral_factor])
\<close>

end
