(*  Title       : HyperPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Powers theory for hyperreals
*)

header{*Exponentials on the Hyperreals*}

theory HyperPow = HyperArith + HyperNat + RealPow:

instance hypreal :: power ..

consts hpowr :: "[hypreal,nat] => hypreal"  
primrec
   hpowr_0:   "r ^ 0       = (1::hypreal)"
   hpowr_Suc: "r ^ (Suc n) = (r::hypreal) * (r ^ n)"


instance hypreal :: ringpower
proof
  fix z :: hypreal
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed


consts
  "pow"  :: "[hypreal,hypnat] => hypreal"     (infixr 80)

defs

  (* hypernatural powers of hyperreals *)
  hyperpow_def:
  "(R::hypreal) pow (N::hypnat) ==
      Abs_hypreal(\<Union>X \<in> Rep_hypreal(R). \<Union>Y \<in> Rep_hypnat(N).
                        hyprel``{%n::nat. (X n) ^ (Y n)})"

lemma hrealpow_two: "(r::hypreal) ^ Suc (Suc 0) = r * r"
apply (simp (no_asm))
done

lemma hrabs_hrealpow_minus_one [simp]: "abs(-1 ^ n) = (1::hypreal)"
by (simp add: power_abs)

lemma hrealpow_two_le: "(0::hypreal) \<le> r ^ Suc (Suc 0)"
by (auto simp add: zero_le_mult_iff)
declare hrealpow_two_le [simp]

lemma hrealpow_two_le_add_order:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0)"
apply (simp only: hrealpow_two_le hypreal_le_add_order)
done
declare hrealpow_two_le_add_order [simp]

lemma hrealpow_two_le_add_order2:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)"
apply (simp only: hrealpow_two_le hypreal_le_add_order)
done
declare hrealpow_two_le_add_order2 [simp]

lemma hypreal_add_nonneg_eq_0_iff:
     "[| 0 \<le> x; 0 \<le> y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))"
apply arith
done

text{*FIXME: DELETE THESE*}
lemma hypreal_three_squares_add_zero_iff:
     "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))"
apply (simp only: zero_le_square hypreal_le_add_order hypreal_add_nonneg_eq_0_iff, auto)
done

lemma hrealpow_three_squares_add_zero_iff [simp]:
     "(x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = (0::hypreal)) = 
      (x = 0 & y = 0 & z = 0)"
by (simp only: hypreal_three_squares_add_zero_iff hrealpow_two)


lemma hrabs_hrealpow_two [simp]:
     "abs(x ^ Suc (Suc 0)) = (x::hypreal) ^ Suc (Suc 0)"
by (simp add: abs_mult)

lemma two_hrealpow_ge_one [simp]: "(1::hypreal) \<le> 2 ^ n"
by (insert power_increasing [of 0 n "2::hypreal"], simp)

lemma two_hrealpow_gt: "hypreal_of_nat n < 2 ^ n"
apply (induct_tac "n")
apply (auto simp add: hypreal_of_nat_Suc left_distrib)
apply (cut_tac n = n in two_hrealpow_ge_one, arith)
done
declare two_hrealpow_gt [simp] 

lemma hrealpow_minus_one: "-1 ^ (2*n) = (1::hypreal)"
by (induct_tac "n", auto)

lemma double_lemma: "n+n = (2*n::nat)"
by auto

(*ugh: need to get rid fo the n+n*)
lemma hrealpow_minus_one2: "-1 ^ (n + n) = (1::hypreal)"
by (auto simp add: double_lemma hrealpow_minus_one)
declare hrealpow_minus_one2 [simp]

lemma hrealpow:
    "Abs_hypreal(hyprel``{%n. X n}) ^ m = Abs_hypreal(hyprel``{%n. (X n) ^ m})"
apply (induct_tac "m")
apply (auto simp add: hypreal_one_def hypreal_mult)
done

lemma hrealpow_sum_square_expand:
     "(x + (y::hypreal)) ^ Suc (Suc 0) =
      x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0)))*x*y"
by (simp add: right_distrib left_distrib hypreal_of_nat_Suc)


subsection{*Literal Arithmetic Involving Powers and Type @{typ hypreal}*}

lemma hypreal_of_real_power: "hypreal_of_real (x ^ n) = hypreal_of_real x ^ n"
apply (induct_tac "n")
apply (simp_all add: nat_mult_distrib)
done
declare hypreal_of_real_power [simp]

lemma power_hypreal_of_real_number_of:
     "(number_of v :: hypreal) ^ n = hypreal_of_real ((number_of v) ^ n)"
by (simp only: hypreal_number_of_def hypreal_of_real_power)

declare power_hypreal_of_real_number_of [of _ "number_of w", standard, simp]

lemma hrealpow_HFinite: "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct_tac "n")
apply (auto intro: HFinite_mult)
done


subsection{*Powers with Hypernatural Exponents*}

lemma hyperpow_congruent:
     "congruent hyprel
     (%X Y. hyprel``{%n. ((X::nat=>real) n ^ (Y::nat=>nat) n)})"
apply (unfold congruent_def)
apply (auto intro!: ext, fuf+)
done

lemma hyperpow:
  "Abs_hypreal(hyprel``{%n. X n}) pow Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypreal(hyprel``{%n. X n ^ Y n})"
apply (unfold hyperpow_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto intro!: lemma_hyprel_refl bexI 
           simp add: hyprel_in_hypreal [THEN Abs_hypreal_inverse] equiv_hyprel 
                     hyperpow_congruent, fuf)
done

lemma hyperpow_zero: "(0::hypreal) pow (n + (1::hypnat)) = 0"
apply (unfold hypnat_one_def)
apply (simp (no_asm) add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hyperpow hypnat_add)
done
declare hyperpow_zero [simp]

lemma hyperpow_not_zero [rule_format (no_asm)]:
     "r \<noteq> (0::hypreal) --> r pow n \<noteq> 0"
apply (simp (no_asm) add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hyperpow)
apply (drule FreeUltrafilterNat_Compl_mem, ultra)
done

lemma hyperpow_inverse:
     "r \<noteq> (0::hypreal) --> inverse(r pow n) = (inverse r) pow n"
apply (simp (no_asm) add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto dest!: FreeUltrafilterNat_Compl_mem simp add: hypreal_inverse hyperpow)
apply (rule FreeUltrafilterNat_subset)
apply (auto dest: realpow_not_zero intro: power_inverse)
done

lemma hyperpow_hrabs: "abs r pow n = abs (r pow n)"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hypreal_hrabs hyperpow power_abs [symmetric])
done

lemma hyperpow_add: "r pow (n + m) = (r pow n) * (r pow m)"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = m in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hyperpow hypnat_add hypreal_mult power_add)
done

lemma hyperpow_one: "r pow (1::hypnat) = r"
apply (unfold hypnat_one_def)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hyperpow)
done
declare hyperpow_one [simp]

lemma hyperpow_two:
     "r pow ((1::hypnat) + (1::hypnat)) = r * r"
apply (unfold hypnat_one_def)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hyperpow hypnat_add hypreal_mult)
done

lemma hyperpow_gt_zero: "(0::hypreal) < r ==> 0 < r pow n"
apply (simp add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto elim!: FreeUltrafilterNat_subset zero_less_power
                   simp add: hyperpow hypreal_less hypreal_le)
done

lemma hyperpow_ge_zero: "(0::hypreal) \<le> r ==> 0 \<le> r pow n"
apply (simp add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto elim!: FreeUltrafilterNat_subset zero_le_power 
            simp add: hyperpow hypreal_le)
done

lemma hyperpow_le: "[|(0::hypreal) < x; x \<le> y|] ==> x pow n \<le> y pow n"
apply (simp add: hypreal_zero_def)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: hyperpow hypreal_le hypreal_less)
apply (erule FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset], assumption)
apply (auto intro: power_mono)
done

lemma hyperpow_eq_one: "1 pow n = (1::hypreal)"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hypreal_one_def hyperpow)
done
declare hyperpow_eq_one [simp]

lemma hrabs_hyperpow_minus_one: "abs(-1 pow n) = (1::hypreal)"
apply (subgoal_tac "abs ((- (1::hypreal)) pow n) = (1::hypreal) ")
apply simp
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hypreal_one_def hyperpow hypreal_minus hypreal_hrabs)
done
declare hrabs_hyperpow_minus_one [simp]

lemma hyperpow_mult: "(r * s) pow n = (r pow n) * (s pow n)"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (rule_tac z = s in eq_Abs_hypreal)
apply (auto simp add: hyperpow hypreal_mult power_mult_distrib)
done

lemma hyperpow_two_le: "(0::hypreal) \<le> r pow ((1::hypnat) + (1::hypnat))"
by (auto simp add: hyperpow_two zero_le_mult_iff)
declare hyperpow_two_le [simp]

lemma hrabs_hyperpow_two [simp]: "abs(x pow (1 + 1)) = x pow (1 + 1)"
by (simp add: hrabs_def hyperpow_two_le)

lemma hyperpow_two_hrabs:
     "abs(x) pow (1 + 1)  = x pow (1 + 1)"
apply (simp add: hyperpow_hrabs)
done
declare hyperpow_two_hrabs [simp]

lemma hyperpow_two_gt_one:
     "(1::hypreal) < r ==> 1 < r pow (1 + 1)"
apply (auto simp add: hyperpow_two)
apply (rule_tac y = "1*1" in order_le_less_trans)
apply (rule_tac [2] hypreal_mult_less_mono, auto)
done

lemma hyperpow_two_ge_one:
     "(1::hypreal) \<le> r ==> 1 \<le> r pow (1 + 1)"
apply (auto dest!: order_le_imp_less_or_eq intro: hyperpow_two_gt_one order_less_imp_le)
done

lemma two_hyperpow_ge_one: "(1::hypreal) \<le> 2 pow n"
apply (rule_tac y = "1 pow n" in order_trans)
apply (rule_tac [2] hyperpow_le, auto)
done
declare two_hyperpow_ge_one [simp]

lemma hyperpow_minus_one2:
     "-1 pow ((1 + 1)*n) = (1::hypreal)"
apply (subgoal_tac " (- ((1::hypreal))) pow ((1 + 1)*n) = (1::hypreal) ")
apply simp
apply (simp only: hypreal_one_def)
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: double_lemma hyperpow hypnat_add hypreal_minus
                      left_distrib)
done
declare hyperpow_minus_one2 [simp]

lemma hyperpow_less_le:
     "[|(0::hypreal) \<le> r; r \<le> 1; n < N|] ==> r pow N \<le> r pow n"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (rule_tac z = N in eq_Abs_hypnat)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hyperpow hypreal_le hypreal_less hypnat_less 
            hypreal_zero_def hypreal_one_def)
apply (erule FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset])
apply (erule FreeUltrafilterNat_Int, assumption)
apply (auto intro: power_decreasing)
done

lemma hyperpow_SHNat_le:
     "[| 0 \<le> r;  r \<le> (1::hypreal);  N \<in> HNatInfinite |]
      ==> ALL n: Nats. r pow N \<le> r pow n"
by (auto intro!: hyperpow_less_le simp add: HNatInfinite_iff)

lemma hyperpow_realpow:
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)"
apply (unfold hypreal_of_real_def hypnat_of_nat_def)
apply (auto simp add: hyperpow)
done

lemma hyperpow_SReal: "(hypreal_of_real r) pow (hypnat_of_nat n) \<in> Reals"
apply (unfold SReal_def)
apply (simp (no_asm) del: hypreal_of_real_power add: hyperpow_realpow)
done
declare hyperpow_SReal [simp]

lemma hyperpow_zero_HNatInfinite: "N \<in> HNatInfinite ==> (0::hypreal) pow N = 0"
by (drule HNatInfinite_is_Suc, auto)
declare hyperpow_zero_HNatInfinite [simp]

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
apply (unfold hypnat_of_nat_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: hrealpow hyperpow)
done

lemma Infinitesimal_hrealpow:
     "[| x \<in> Infinitesimal; 0 < n |] ==> x ^ n \<in> Infinitesimal"
by (force intro!: Infinitesimal_hyperpow
          simp add: hrealpow_hyperpow_Infinitesimal_iff 
                    hypnat_of_nat_less_iff [symmetric] hypnat_of_nat_zero
          simp del: hypnat_of_nat_less_iff)

ML
{*
val hrealpow_two = thm "hrealpow_two";
val hrabs_hrealpow_minus_one = thm "hrabs_hrealpow_minus_one";
val hrealpow_two_le = thm "hrealpow_two_le";
val hrealpow_two_le_add_order = thm "hrealpow_two_le_add_order";
val hrealpow_two_le_add_order2 = thm "hrealpow_two_le_add_order2";
val hypreal_add_nonneg_eq_0_iff = thm "hypreal_add_nonneg_eq_0_iff";
val hypreal_three_squares_add_zero_iff = thm "hypreal_three_squares_add_zero_iff";
val hrealpow_three_squares_add_zero_iff = thm "hrealpow_three_squares_add_zero_iff";
val hrabs_hrealpow_two = thm "hrabs_hrealpow_two";
val two_hrealpow_ge_one = thm "two_hrealpow_ge_one";
val two_hrealpow_gt = thm "two_hrealpow_gt";
val hrealpow_minus_one = thm "hrealpow_minus_one";
val double_lemma = thm "double_lemma";
val hrealpow_minus_one2 = thm "hrealpow_minus_one2";
val hrealpow = thm "hrealpow";
val hrealpow_sum_square_expand = thm "hrealpow_sum_square_expand";
val hypreal_of_real_power = thm "hypreal_of_real_power";
val power_hypreal_of_real_number_of = thm "power_hypreal_of_real_number_of";
val hrealpow_HFinite = thm "hrealpow_HFinite";
val hyperpow_congruent = thm "hyperpow_congruent";
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
