(* Author: Various *)

header {* Combination and Cancellation Simprocs for Numeral Expressions *}

theory Numeral_Simprocs
imports Divides
uses
  "~~/src/Provers/Arith/assoc_fold.ML"
  "~~/src/Provers/Arith/cancel_numerals.ML"
  "~~/src/Provers/Arith/combine_numerals.ML"
  "~~/src/Provers/Arith/cancel_numeral_factor.ML"
  "~~/src/Provers/Arith/extract_common_term.ML"
  ("Tools/numeral_simprocs.ML")
  ("Tools/nat_numeral_simprocs.ML")
begin

declare split_div [of _ _ "number_of k", standard, arith_split]
declare split_mod [of _ _ "number_of k", standard, arith_split]

text {* For @{text combine_numerals} *}

lemma left_add_mult_distrib: "i*u + (j*u + k) = (i+j)*u + (k::nat)"
by (simp add: add_mult_distrib)

text {* For @{text cancel_numerals} *}

lemma nat_diff_add_eq1:
     "j <= (i::nat) ==> ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_diff_add_eq2:
     "i <= (j::nat) ==> ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_eq_add_iff1:
     "j <= (i::nat) ==> (i*u + m = j*u + n) = ((i-j)*u + m = n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_eq_add_iff2:
     "i <= (j::nat) ==> (i*u + m = j*u + n) = (m = (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff1:
     "j <= (i::nat) ==> (i*u + m < j*u + n) = ((i-j)*u + m < n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff2:
     "i <= (j::nat) ==> (i*u + m < j*u + n) = (m < (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff1:
     "j <= (i::nat) ==> (i*u + m <= j*u + n) = ((i-j)*u + m <= n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff2:
     "i <= (j::nat) ==> (i*u + m <= j*u + n) = (m <= (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

text {* For @{text cancel_numeral_factors} *}

lemma nat_mult_le_cancel1: "(0::nat) < k ==> (k*m <= k*n) = (m<=n)"
by auto

lemma nat_mult_less_cancel1: "(0::nat) < k ==> (k*m < k*n) = (m<n)"
by auto

lemma nat_mult_eq_cancel1: "(0::nat) < k ==> (k*m = k*n) = (m=n)"
by auto

lemma nat_mult_div_cancel1: "(0::nat) < k ==> (k*m) div (k*n) = (m div n)"
by auto

lemma nat_mult_dvd_cancel_disj[simp]:
  "(k*m) dvd (k*n) = (k=0 | m dvd (n::nat))"
by(auto simp: dvd_eq_mod_eq_0 mod_mult_distrib2[symmetric])

lemma nat_mult_dvd_cancel1: "0 < k \<Longrightarrow> (k*m) dvd (k*n::nat) = (m dvd n)"
by(auto)

text {* For @{text cancel_factor} *}

lemma nat_mult_le_cancel_disj: "(k*m <= k*n) = ((0::nat) < k --> m<=n)"
by auto

lemma nat_mult_less_cancel_disj: "(k*m < k*n) = ((0::nat) < k & m<n)"
by auto

lemma nat_mult_eq_cancel_disj: "(k*m = k*n) = (k = (0::nat) | m=n)"
by auto

lemma nat_mult_div_cancel_disj[simp]:
     "(k*m) div (k*n) = (if k = (0::nat) then 0 else m div n)"
by (simp add: nat_mult_div_cancel1)


use "Tools/numeral_simprocs.ML"

use "Tools/nat_numeral_simprocs.ML"

declaration {* 
  K (Lin_Arith.add_simps (@{thms neg_simps} @ [@{thm Suc_nat_number_of}, @{thm int_nat_number_of}])
  #> Lin_Arith.add_simps (@{thms ring_distribs} @ [@{thm Let_number_of}, @{thm Let_0}, @{thm Let_1},
     @{thm nat_0}, @{thm nat_1},
     @{thm add_nat_number_of}, @{thm diff_nat_number_of}, @{thm mult_nat_number_of},
     @{thm eq_nat_number_of}, @{thm less_nat_number_of}, @{thm le_number_of_eq_not_less},
     @{thm le_Suc_number_of}, @{thm le_number_of_Suc},
     @{thm less_Suc_number_of}, @{thm less_number_of_Suc},
     @{thm Suc_eq_number_of}, @{thm eq_number_of_Suc},
     @{thm mult_Suc}, @{thm mult_Suc_right},
     @{thm add_Suc}, @{thm add_Suc_right},
     @{thm eq_number_of_0}, @{thm eq_0_number_of}, @{thm less_0_number_of},
     @{thm of_int_number_of_eq}, @{thm of_nat_number_of_eq}, @{thm nat_number_of},
     @{thm if_True}, @{thm if_False}])
  #> Lin_Arith.add_simprocs (Numeral_Simprocs.assoc_fold_simproc
      :: Numeral_Simprocs.combine_numerals
      :: Numeral_Simprocs.cancel_numerals)
  #> Lin_Arith.add_simprocs (Nat_Numeral_Simprocs.combine_numerals :: Nat_Numeral_Simprocs.cancel_numerals))
*}

end