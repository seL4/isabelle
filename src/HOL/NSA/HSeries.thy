(*  Title       : HSeries.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp    
*) 

header{*Finite Summation and Infinite Series for Hyperreals*}

theory HSeries
imports Series HSEQ
begin

definition
  sumhr :: "(hypnat * hypnat * (nat=>real)) => hypreal" where
  "sumhr = 
      (%(M,N,f). starfun2 (%m n. setsum f {m..<n}) M N)"

definition
  NSsums  :: "[nat=>real,real] => bool"     (infixr "NSsums" 80) where
  "f NSsums s = (%n. setsum f {0..<n}) ----NS> s"

definition
  NSsummable :: "(nat=>real) => bool" where
  "NSsummable f = (\<exists>s. f NSsums s)"

definition
  NSsuminf   :: "(nat=>real) => real" where
  "NSsuminf f = (THE s. f NSsums s)"

lemma sumhr_app: "sumhr(M,N,f) = ( *f2* (\<lambda>m n. setsum f {m..<n})) M N"
by (simp add: sumhr_def)

text{*Base case in definition of @{term sumr}*}
lemma sumhr_zero [simp]: "!!m. sumhr (m,0,f) = 0"
unfolding sumhr_app by transfer simp

text{*Recursive case in definition of @{term sumr}*}
lemma sumhr_if: 
     "!!m n. sumhr(m,n+1,f) = 
      (if n + 1 \<le> m then 0 else sumhr(m,n,f) + ( *f* f) n)"
unfolding sumhr_app by transfer simp

lemma sumhr_Suc_zero [simp]: "!!n. sumhr (n + 1, n, f) = 0"
unfolding sumhr_app by transfer simp

lemma sumhr_eq_bounds [simp]: "!!n. sumhr (n,n,f) = 0"
unfolding sumhr_app by transfer simp

lemma sumhr_Suc [simp]: "!!m. sumhr (m,m + 1,f) = ( *f* f) m"
unfolding sumhr_app by transfer simp

lemma sumhr_add_lbound_zero [simp]: "!!k m. sumhr(m+k,k,f) = 0"
unfolding sumhr_app by transfer simp

lemma sumhr_add:
  "!!m n. sumhr (m,n,f) + sumhr(m,n,g) = sumhr(m,n,%i. f i + g i)"
unfolding sumhr_app by transfer (rule setsum_addf [symmetric])

lemma sumhr_mult:
  "!!m n. hypreal_of_real r * sumhr(m,n,f) = sumhr(m,n,%n. r * f n)"
unfolding sumhr_app by transfer (rule setsum_right_distrib)

lemma sumhr_split_add:
  "!!n p. n < p ==> sumhr(0,n,f) + sumhr(n,p,f) = sumhr(0,p,f)"
unfolding sumhr_app by transfer (simp add: setsum_add_nat_ivl)

lemma sumhr_split_diff: "n<p ==> sumhr(0,p,f) - sumhr(0,n,f) = sumhr(n,p,f)"
by (drule_tac f = f in sumhr_split_add [symmetric], simp)

lemma sumhr_hrabs: "!!m n. abs(sumhr(m,n,f)) \<le> sumhr(m,n,%i. abs(f i))"
unfolding sumhr_app by transfer (rule setsum_abs)

text{* other general version also needed *}
lemma sumhr_fun_hypnat_eq:
   "(\<forall>r. m \<le> r & r < n --> f r = g r) -->  
      sumhr(hypnat_of_nat m, hypnat_of_nat n, f) =  
      sumhr(hypnat_of_nat m, hypnat_of_nat n, g)"
unfolding sumhr_app by transfer simp

lemma sumhr_const:
     "!!n. sumhr(0, n, %i. r) = hypreal_of_hypnat n * hypreal_of_real r"
unfolding sumhr_app by transfer (simp add: real_of_nat_def)

lemma sumhr_less_bounds_zero [simp]: "!!m n. n < m ==> sumhr(m,n,f) = 0"
unfolding sumhr_app by transfer simp

lemma sumhr_minus: "!!m n. sumhr(m, n, %i. - f i) = - sumhr(m, n, f)"
unfolding sumhr_app by transfer (rule setsum_negf)

lemma sumhr_shift_bounds:
  "!!m n. sumhr(m+hypnat_of_nat k,n+hypnat_of_nat k,f) =
          sumhr(m,n,%i. f(i + k))"
unfolding sumhr_app by transfer (rule setsum_shift_bounds_nat_ivl)


subsection{*Nonstandard Sums*}

text{*Infinite sums are obtained by summing to some infinite hypernatural
 (such as @{term whn})*}
lemma sumhr_hypreal_of_hypnat_omega: 
      "sumhr(0,whn,%i. 1) = hypreal_of_hypnat whn"
by (simp add: sumhr_const)

lemma sumhr_hypreal_omega_minus_one: "sumhr(0, whn, %i. 1) = omega - 1"
apply (simp add: sumhr_const)
(* FIXME: need lemma: hypreal_of_hypnat whn = omega - 1 *)
(* maybe define omega = hypreal_of_hypnat whn + 1 *)
apply (unfold star_class_defs omega_def hypnat_omega_def
              of_hypnat_def star_of_def)
apply (simp add: starfun_star_n starfun2_star_n real_of_nat_def)
done

lemma sumhr_minus_one_realpow_zero [simp]: 
     "!!N. sumhr(0, N + N, %i. (-1) ^ (i+1)) = 0"
unfolding sumhr_app
by transfer (simp del: power_Suc add: mult_2 [symmetric])

lemma sumhr_interval_const:
     "(\<forall>n. m \<le> Suc n --> f n = r) & m \<le> na  
      ==> sumhr(hypnat_of_nat m,hypnat_of_nat na,f) =  
          (hypreal_of_nat (na - m) * hypreal_of_real r)"
unfolding sumhr_app by transfer simp

lemma starfunNat_sumr: "!!N. ( *f* (%n. setsum f {0..<n})) N = sumhr(0,N,f)"
unfolding sumhr_app by transfer (rule refl)

lemma sumhr_hrabs_approx [simp]: "sumhr(0, M, f) @= sumhr(0, N, f)  
      ==> abs (sumhr(M, N, f)) @= 0"
apply (cut_tac x = M and y = N in linorder_less_linear)
apply (auto simp add: approx_refl)
apply (drule approx_sym [THEN approx_minus_iff [THEN iffD1]])
apply (auto dest: approx_hrabs 
            simp add: sumhr_split_diff diff_minus [symmetric])
done

(*----------------------------------------------------------------
      infinite sums: Standard and NS theorems
 ----------------------------------------------------------------*)
lemma sums_NSsums_iff: "(f sums l) = (f NSsums l)"
by (simp add: sums_def NSsums_def LIMSEQ_NSLIMSEQ_iff)

lemma summable_NSsummable_iff: "(summable f) = (NSsummable f)"
by (simp add: summable_def NSsummable_def sums_NSsums_iff)

lemma suminf_NSsuminf_iff: "(suminf f) = (NSsuminf f)"
by (simp add: suminf_def NSsuminf_def sums_NSsums_iff)

lemma NSsums_NSsummable: "f NSsums l ==> NSsummable f"
by (simp add: NSsums_def NSsummable_def, blast)

lemma NSsummable_NSsums: "NSsummable f ==> f NSsums (NSsuminf f)"
apply (simp add: NSsummable_def NSsuminf_def NSsums_def)
apply (blast intro: theI NSLIMSEQ_unique)
done

lemma NSsums_unique: "f NSsums s ==> (s = NSsuminf f)"
by (simp add: suminf_NSsuminf_iff [symmetric] sums_NSsums_iff sums_unique)

lemma NSseries_zero:
  "\<forall>m. n \<le> Suc m --> f(m) = 0 ==> f NSsums (setsum f {0..<n})"
by (simp add: sums_NSsums_iff [symmetric] series_zero)

lemma NSsummable_NSCauchy:
     "NSsummable f =  
      (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. abs (sumhr(M,N,f)) @= 0)"
apply (auto simp add: summable_NSsummable_iff [symmetric] 
       summable_convergent_sumr_iff convergent_NSconvergent_iff 
       NSCauchy_NSconvergent_iff [symmetric] NSCauchy_def starfunNat_sumr)
apply (cut_tac x = M and y = N in linorder_less_linear)
apply (auto simp add: approx_refl)
apply (rule approx_minus_iff [THEN iffD2, THEN approx_sym])
apply (rule_tac [2] approx_minus_iff [THEN iffD2])
apply (auto dest: approx_hrabs_zero_cancel 
            simp add: sumhr_split_diff diff_minus [symmetric])
done


text{*Terms of a convergent series tend to zero*}
lemma NSsummable_NSLIMSEQ_zero: "NSsummable f ==> f ----NS> 0"
apply (auto simp add: NSLIMSEQ_def NSsummable_NSCauchy)
apply (drule bspec, auto)
apply (drule_tac x = "N + 1 " in bspec)
apply (auto intro: HNatInfinite_add_one approx_hrabs_zero_cancel)
done

text{*Nonstandard comparison test*}
lemma NSsummable_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; NSsummable g |] ==> NSsummable f"
apply (fold summable_NSsummable_iff)
apply (rule summable_comparison_test, simp, assumption)
done

lemma NSsummable_rabs_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; NSsummable g |]
      ==> NSsummable (%k. abs (f k))"
apply (rule NSsummable_comparison_test)
apply (auto)
done

end
