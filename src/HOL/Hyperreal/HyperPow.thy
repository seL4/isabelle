(*  Title       : HyperPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Exponentials on the Hyperreals*}

theory HyperPow
imports HyperArith HyperNat
begin

(* consts hpowr :: "[hypreal,nat] => hypreal" *)

lemma hpowr_0 [simp]:   "r ^ 0       = (1::hypreal)"
by (rule power_0)

lemma hpowr_Suc [simp]: "r ^ (Suc n) = (r::hypreal) * (r ^ n)"
by (rule power_Suc)

consts
  "pow"  :: "[hypreal,hypnat] => hypreal"     (infixr "pow" 80)

defs

  (* hypernatural powers of hyperreals *)
  hyperpow_def [transfer_unfold]:
  "(R::hypreal) pow (N::hypnat) == ( *f2* op ^) R N"

lemma hrealpow_two: "(r::hypreal) ^ Suc (Suc 0) = r * r"
by simp

lemma hrealpow_two_le [simp]: "(0::hypreal) \<le> r ^ Suc (Suc 0)"
by (auto simp add: zero_le_mult_iff)

lemma hrealpow_two_le_add_order [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hrealpow_two_le_add_order2 [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hypreal_add_nonneg_eq_0_iff:
     "[| 0 \<le> x; 0 \<le> y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))"
by arith


text{*FIXME: DELETE THESE*}
lemma hypreal_three_squares_add_zero_iff:
     "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))"
apply (simp only: zero_le_square add_nonneg_nonneg hypreal_add_nonneg_eq_0_iff, auto)
done

lemma hrealpow_three_squares_add_zero_iff [simp]:
     "(x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = (0::hypreal)) = 
      (x = 0 & y = 0 & z = 0)"
by (simp only: hypreal_three_squares_add_zero_iff hrealpow_two)

(*FIXME: This and RealPow.abs_realpow_two should be replaced by an abstract
  result proved in Ring_and_Field*)
lemma hrabs_hrealpow_two [simp]:
     "abs(x ^ Suc (Suc 0)) = (x::hypreal) ^ Suc (Suc 0)"
by (simp add: abs_mult)

lemma two_hrealpow_ge_one [simp]: "(1::hypreal) \<le> 2 ^ n"
by (insert power_increasing [of 0 n "2::hypreal"], simp)

lemma two_hrealpow_gt [simp]: "hypreal_of_nat n < 2 ^ n"
apply (induct_tac "n")
apply (auto simp add: hypreal_of_nat_Suc left_distrib)
apply (cut_tac n = n in two_hrealpow_ge_one, arith)
done

lemma hrealpow:
    "star_n X ^ m = star_n (%n. (X n::real) ^ m)"
apply (induct_tac "m")
apply (auto simp add: star_n_one_num star_n_mult power_0)
done

lemma hrealpow_sum_square_expand:
     "(x + (y::hypreal)) ^ Suc (Suc 0) =
      x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0)))*x*y"
by (simp add: right_distrib left_distrib hypreal_of_nat_Suc)


subsection{*Literal Arithmetic Involving Powers and Type @{typ hypreal}*}

lemma power_hypreal_of_real_number_of:
     "(number_of v :: hypreal) ^ n = hypreal_of_real ((number_of v) ^ n)"
by simp
(* why is this a simp rule? - BH *)
declare power_hypreal_of_real_number_of [of _ "number_of w", standard, simp]

lemma hrealpow_HFinite: "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct_tac "n")
apply (auto intro: HFinite_mult)
done


subsection{*Powers with Hypernatural Exponents*}

lemma hyperpow: "star_n X pow star_n Y = star_n (%n. X n ^ Y n)"
by (simp add: hyperpow_def starfun2_star_n)

lemma hyperpow_zero [simp]: "!!n. (0::hypreal) pow (n + (1::hypnat)) = 0"
by (transfer, simp)

lemma hyperpow_not_zero: "!!r n. r \<noteq> (0::hypreal) ==> r pow n \<noteq> 0"
by (transfer, simp)

lemma hyperpow_inverse:
     "!!r n. r \<noteq> (0::hypreal) ==> inverse(r pow n) = (inverse r) pow n"
by (transfer, rule power_inverse)

lemma hyperpow_hrabs: "!!r n. abs r pow n = abs (r pow n)"
by (transfer, rule power_abs [symmetric])

lemma hyperpow_add: "!!r n m. r pow (n + m) = (r pow n) * (r pow m)"
by (transfer, rule power_add)

lemma hyperpow_one [simp]: "!!r. r pow (1::hypnat) = r"
by (transfer, simp)

lemma hyperpow_two:
     "!!r. r pow ((1::hypnat) + (1::hypnat)) = r * r"
by (transfer, simp)

lemma hyperpow_gt_zero: "!!r n. (0::hypreal) < r ==> 0 < r pow n"
by (transfer, rule zero_less_power)

lemma hyperpow_ge_zero: "!!r n. (0::hypreal) \<le> r ==> 0 \<le> r pow n"
by (transfer, rule zero_le_power)

lemma hyperpow_le:
  "!!x y n. [|(0::hypreal) < x; x \<le> y|] ==> x pow n \<le> y pow n"
by (transfer, rule power_mono [OF _ order_less_imp_le])

lemma hyperpow_eq_one [simp]: "!!n. 1 pow n = (1::hypreal)"
by (transfer, simp)

lemma hrabs_hyperpow_minus_one [simp]: "!!n. abs(-1 pow n) = (1::hypreal)"
by (transfer, simp)

lemma hyperpow_mult: "!!r s n. (r * s) pow n = (r pow n) * (s pow n)"
by (transfer, rule power_mult_distrib)

lemma hyperpow_two_le [simp]: "0 \<le> r pow (1 + 1)"
by (auto simp add: hyperpow_two zero_le_mult_iff)

lemma hrabs_hyperpow_two [simp]: "abs(x pow (1 + 1)) = x pow (1 + 1)"
by (simp add: abs_if hyperpow_two_le linorder_not_less)

lemma hyperpow_two_hrabs [simp]: "abs(x) pow (1 + 1)  = x pow (1 + 1)"
by (simp add: hyperpow_hrabs)

text{*The precondition could be weakened to @{term "0\<le>x"}*}
lemma hypreal_mult_less_mono:
     "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y"
 by (simp add: Ring_and_Field.mult_strict_mono order_less_imp_le)

lemma hyperpow_two_gt_one: "1 < r ==> 1 < r pow (1 + 1)"
apply (auto simp add: hyperpow_two)
apply (rule_tac y = "1*1" in order_le_less_trans)
apply (rule_tac [2] hypreal_mult_less_mono, auto)
done

lemma hyperpow_two_ge_one:
     "1 \<le> r ==> 1 \<le> r pow (1 + 1)"
by (auto dest!: order_le_imp_less_or_eq intro: hyperpow_two_gt_one order_less_imp_le)

lemma two_hyperpow_ge_one [simp]: "(1::hypreal) \<le> 2 pow n"
apply (rule_tac y = "1 pow n" in order_trans)
apply (rule_tac [2] hyperpow_le, auto)
done

lemma hyperpow_minus_one2 [simp]:
     "!!n. -1 pow ((1 + 1)*n) = (1::hypreal)"
by (transfer, simp)

lemma hyperpow_less_le:
     "!!r n N. [|(0::hypreal) \<le> r; r \<le> 1; n < N|] ==> r pow N \<le> r pow n"
by (transfer, rule power_decreasing [OF order_less_imp_le])

lemma hyperpow_SHNat_le:
     "[| 0 \<le> r;  r \<le> (1::hypreal);  N \<in> HNatInfinite |]
      ==> ALL n: Nats. r pow N \<le> r pow n"
by (auto intro!: hyperpow_less_le simp add: HNatInfinite_iff)

lemma hyperpow_realpow:
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)"
by (simp add: star_of_def hypnat_of_nat_eq hyperpow)

lemma hyperpow_SReal [simp]:
     "(hypreal_of_real r) pow (hypnat_of_nat n) \<in> Reals"
by (simp del: star_of_power add: hyperpow_realpow SReal_def)


lemma hyperpow_zero_HNatInfinite [simp]:
     "N \<in> HNatInfinite ==> (0::hypreal) pow N = 0"
by (drule HNatInfinite_is_Suc, auto)

lemma hyperpow_le_le:
     "[| (0::hypreal) \<le> r; r \<le> 1; n \<le> N |] ==> r pow N \<le> r pow n"
apply (drule order_le_less [of n, THEN iffD1])
apply (auto intro: hyperpow_less_le)
done

lemma hyperpow_Suc_le_self2:
     "[| (0::hypreal) \<le> r; r < 1 |] ==> r pow (n + (1::hypnat)) \<le> r"
apply (drule_tac n = " (1::hypnat) " in hyperpow_le_le)
apply auto
done

lemma lemma_Infinitesimal_hyperpow:
     "[| x \<in> Infinitesimal; 0 < N |] ==> abs (x pow N) \<le> abs x"
apply (unfold Infinitesimal_def)
apply (auto intro!: hyperpow_Suc_le_self2 
          simp add: hyperpow_hrabs [symmetric] hypnat_gt_zero_iff2 abs_ge_zero)
done

lemma Infinitesimal_hyperpow:
     "[| x \<in> Infinitesimal; 0 < N |] ==> x pow N \<in> Infinitesimal"
apply (rule hrabs_le_Infinitesimal)
apply (rule_tac [2] lemma_Infinitesimal_hyperpow, auto)
done

lemma hrealpow_hyperpow_Infinitesimal_iff:
     "(x ^ n \<in> Infinitesimal) = (x pow (hypnat_of_nat n) \<in> Infinitesimal)"
apply (cases x)
apply (simp add: hrealpow hyperpow hypnat_of_nat_eq)
done

lemma Infinitesimal_hrealpow:
     "[| x \<in> Infinitesimal; 0 < n |] ==> x ^ n \<in> Infinitesimal"
by (simp add: hrealpow_hyperpow_Infinitesimal_iff Infinitesimal_hyperpow)

ML
{*
val hrealpow_two = thm "hrealpow_two";
val hrealpow_two_le = thm "hrealpow_two_le";
val hrealpow_two_le_add_order = thm "hrealpow_two_le_add_order";
val hrealpow_two_le_add_order2 = thm "hrealpow_two_le_add_order2";
val hypreal_add_nonneg_eq_0_iff = thm "hypreal_add_nonneg_eq_0_iff";
val hypreal_three_squares_add_zero_iff = thm "hypreal_three_squares_add_zero_iff";
val hrealpow_three_squares_add_zero_iff = thm "hrealpow_three_squares_add_zero_iff";
val hrabs_hrealpow_two = thm "hrabs_hrealpow_two";
val two_hrealpow_ge_one = thm "two_hrealpow_ge_one";
val two_hrealpow_gt = thm "two_hrealpow_gt";
val hrealpow = thm "hrealpow";
val hrealpow_sum_square_expand = thm "hrealpow_sum_square_expand";
val power_hypreal_of_real_number_of = thm "power_hypreal_of_real_number_of";
val hrealpow_HFinite = thm "hrealpow_HFinite";
val hyperpow = thm "hyperpow";
val hyperpow_zero = thm "hyperpow_zero";
val hyperpow_not_zero = thm "hyperpow_not_zero";
val hyperpow_inverse = thm "hyperpow_inverse";
val hyperpow_hrabs = thm "hyperpow_hrabs";
val hyperpow_add = thm "hyperpow_add";
val hyperpow_one = thm "hyperpow_one";
val hyperpow_two = thm "hyperpow_two";
val hyperpow_gt_zero = thm "hyperpow_gt_zero";
val hyperpow_ge_zero = thm "hyperpow_ge_zero";
val hyperpow_le = thm "hyperpow_le";
val hyperpow_eq_one = thm "hyperpow_eq_one";
val hrabs_hyperpow_minus_one = thm "hrabs_hyperpow_minus_one";
val hyperpow_mult = thm "hyperpow_mult";
val hyperpow_two_le = thm "hyperpow_two_le";
val hrabs_hyperpow_two = thm "hrabs_hyperpow_two";
val hyperpow_two_hrabs = thm "hyperpow_two_hrabs";
val hyperpow_two_gt_one = thm "hyperpow_two_gt_one";
val hyperpow_two_ge_one = thm "hyperpow_two_ge_one";
val two_hyperpow_ge_one = thm "two_hyperpow_ge_one";
val hyperpow_minus_one2 = thm "hyperpow_minus_one2";
val hyperpow_less_le = thm "hyperpow_less_le";
val hyperpow_SHNat_le = thm "hyperpow_SHNat_le";
val hyperpow_realpow = thm "hyperpow_realpow";
val hyperpow_SReal = thm "hyperpow_SReal";
val hyperpow_zero_HNatInfinite = thm "hyperpow_zero_HNatInfinite";
val hyperpow_le_le = thm "hyperpow_le_le";
val hyperpow_Suc_le_self2 = thm "hyperpow_Suc_le_self2";
val lemma_Infinitesimal_hyperpow = thm "lemma_Infinitesimal_hyperpow";
val Infinitesimal_hyperpow = thm "Infinitesimal_hyperpow";
val hrealpow_hyperpow_Infinitesimal_iff = thm "hrealpow_hyperpow_Infinitesimal_iff";
val Infinitesimal_hrealpow = thm "Infinitesimal_hrealpow";
*}

end
