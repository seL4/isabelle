(*  Title       : HSeries.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp    
*) 

header{*Finite Summation and Infinite Series for Hyperreals*}

theory HSeries = Series:

constdefs 
  sumhr :: "(hypnat * hypnat * (nat=>real)) => hypreal"
   "sumhr p == 
      (%(M,N,f). Abs_hypreal(\<Union>X \<in> Rep_hypnat(M). \<Union>Y \<in> Rep_hypnat(N).  
                             hyprel ``{%n::nat. sumr (X n) (Y n) f})) p"

  NSsums  :: "[nat=>real,real] => bool"     (infixr "NSsums" 80)
   "f NSsums s  == (%n. sumr 0 n f) ----NS> s"

  NSsummable :: "(nat=>real) => bool"
   "NSsummable f == (\<exists>s. f NSsums s)"

  NSsuminf   :: "(nat=>real) => real"
   "NSsuminf f == (@s. f NSsums s)"


lemma sumhr: 
     "sumhr(Abs_hypnat(hypnatrel``{%n. M n}),  
            Abs_hypnat(hypnatrel``{%n. N n}), f) =  
      Abs_hypreal(hyprel `` {%n. sumr (M n) (N n) f})"
apply (simp add: sumhr_def)
apply (rule arg_cong [where f = Abs_hypreal]) 
apply (auto, ultra)
done

text{*Base case in definition of @{term sumr}*}
lemma sumhr_zero [simp]: "sumhr (m,0,f) = 0"
apply (cases m)
apply (simp add: hypnat_zero_def sumhr symmetric hypreal_zero_def)
done

text{*Recursive case in definition of @{term sumr}*}
lemma sumhr_if: 
     "sumhr(m,n+1,f) = 
      (if n + 1 \<le> m then 0 else sumhr(m,n,f) + ( *fNat* f) n)"
apply (cases m, cases n)
apply (auto simp add: hypnat_one_def sumhr hypnat_add hypnat_le starfunNat
           hypreal_add hypreal_zero_def,   ultra+)
done

lemma sumhr_Suc_zero [simp]: "sumhr (n + 1, n, f) = 0"
apply (cases n)
apply (simp add: hypnat_one_def sumhr hypnat_add hypreal_zero_def)
done

lemma sumhr_eq_bounds [simp]: "sumhr (n,n,f) = 0"
apply (cases n)
apply (simp add: sumhr hypreal_zero_def)
done

lemma sumhr_Suc [simp]: "sumhr (m,m + 1,f) = ( *fNat* f) m"
apply (cases m)
apply (simp add: sumhr hypnat_one_def  hypnat_add starfunNat)
done

lemma sumhr_add_lbound_zero [simp]: "sumhr(m+k,k,f) = 0"
apply (cases m, cases k)
apply (simp add: sumhr hypnat_add hypreal_zero_def)
done

lemma sumhr_add: "sumhr (m,n,f) + sumhr(m,n,g) = sumhr(m,n,%i. f i + g i)"
apply (cases m, cases n)
apply (simp add: sumhr hypreal_add sumr_add)
done

lemma sumhr_mult: "hypreal_of_real r * sumhr(m,n,f) = sumhr(m,n,%n. r * f n)"
apply (cases m, cases n)
apply (simp add: sumhr hypreal_of_real_def hypreal_mult sumr_mult)
done

lemma sumhr_split_add: "n < p ==> sumhr(0,n,f) + sumhr(n,p,f) = sumhr(0,p,f)"
apply (cases n, cases p)
apply (auto elim!: FreeUltrafilterNat_subset simp 
            add: hypnat_zero_def sumhr hypreal_add hypnat_less sumr_split_add)
done

lemma sumhr_split_diff: "n<p ==> sumhr(0,p,f) - sumhr(0,n,f) = sumhr(n,p,f)"
by (drule_tac f1 = f in sumhr_split_add [symmetric], simp)

lemma sumhr_hrabs: "abs(sumhr(m,n,f)) \<le> sumhr(m,n,%i. abs(f i))"
apply (cases n, cases m)
apply (simp add: sumhr hypreal_le hypreal_hrabs sumr_rabs)
done

text{* other general version also needed *}
lemma sumhr_fun_hypnat_eq:
   "(\<forall>r. m \<le> r & r < n --> f r = g r) -->  
      sumhr(hypnat_of_nat m, hypnat_of_nat n, f) =  
      sumhr(hypnat_of_nat m, hypnat_of_nat n, g)"
apply (safe, drule sumr_fun_eq)
apply (simp add: sumhr hypnat_of_nat_eq)
done

lemma sumhr_const: "sumhr(0,n,%i. r) = hypreal_of_hypnat n*hypreal_of_real r"
apply (cases n)
apply (simp add: sumhr hypnat_zero_def hypreal_of_real_def hypreal_of_hypnat hypreal_mult)
done

lemma sumhr_add_mult_const: 
     "sumhr(0,n,f) + -(hypreal_of_hypnat n*hypreal_of_real r) =  
      sumhr(0,n,%i. f i + -r)"
apply (cases n)
apply (simp add: sumhr hypnat_zero_def hypreal_of_real_def hypreal_of_hypnat 
                 hypreal_mult hypreal_add hypreal_minus sumr_add [symmetric])
done

lemma sumhr_less_bounds_zero [simp]: "n < m ==> sumhr(m,n,f) = 0"
apply (cases m, cases n)
apply (auto elim: FreeUltrafilterNat_subset 
            simp add: sumhr hypnat_less hypreal_zero_def)
done

lemma sumhr_minus: "sumhr(m, n, %i. - f i) = - sumhr(m, n, f)"
apply (cases m, cases n)
apply (simp add: sumhr hypreal_minus sumr_minus)
done

lemma sumhr_shift_bounds:
     "sumhr(m+hypnat_of_nat k,n+hypnat_of_nat k,f) = sumhr(m,n,%i. f(i + k))"
apply (cases m, cases n)
apply (simp add: sumhr hypnat_add sumr_shift_bounds hypnat_of_nat_eq)
done


subsection{*Nonstandard Sums*}

text{*Infinite sums are obtained by summing to some infinite hypernatural
 (such as @{term whn})*}
lemma sumhr_hypreal_of_hypnat_omega: 
      "sumhr(0,whn,%i. 1) = hypreal_of_hypnat whn"
by (simp add: hypnat_omega_def hypnat_zero_def sumhr hypreal_of_hypnat)

lemma sumhr_hypreal_omega_minus_one: "sumhr(0, whn, %i. 1) = omega - 1"
by (simp add: hypnat_omega_def hypnat_zero_def omega_def hypreal_one_def
              sumhr hypreal_diff real_of_nat_Suc)

lemma sumhr_minus_one_realpow_zero [simp]: 
     "sumhr(0, whn + whn, %i. (-1) ^ (i+1)) = 0"
by (simp del: realpow_Suc 
         add: sumhr hypnat_add nat_mult_2 [symmetric] hypreal_zero_def 
              hypnat_zero_def hypnat_omega_def)

lemma sumhr_interval_const:
     "(\<forall>n. m \<le> Suc n --> f n = r) & m \<le> na  
      ==> sumhr(hypnat_of_nat m,hypnat_of_nat na,f) =  
          (hypreal_of_nat (na - m) * hypreal_of_real r)"
by (auto dest!: sumr_interval_const 
         simp add: hypreal_of_real_def sumhr hypreal_of_nat_eq 
                   hypnat_of_nat_eq hypreal_of_real_def hypreal_mult)

lemma starfunNat_sumr: "( *fNat* (%n. sumr 0 n f)) N = sumhr(0,N,f)"
apply (cases N)
apply (simp add: hypnat_zero_def starfunNat sumhr)
done

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
apply (simp add: NSsummable_def NSsuminf_def)
apply (blast intro: someI2)
done

lemma NSsums_unique: "f NSsums s ==> (s = NSsuminf f)"
by (simp add: suminf_NSsuminf_iff [symmetric] sums_NSsums_iff sums_unique)

lemma NSseries_zero: "\<forall>m. n \<le> Suc m --> f(m) = 0 ==> f NSsums (sumr 0 n f)"
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

text{* Easy to prove stsandard case now *}
lemma summable_LIMSEQ_zero: "summable f ==> f ----> 0"
by (simp add: summable_NSsummable_iff LIMSEQ_NSLIMSEQ_iff NSsummable_NSLIMSEQ_zero)

text{*Nonstandard comparison test*}
lemma NSsummable_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; NSsummable g |] ==> NSsummable f"
by (auto intro: summable_comparison_test 
         simp add: summable_NSsummable_iff [symmetric])

lemma NSsummable_rabs_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; NSsummable g |]
      ==> NSsummable (%k. abs (f k))"
apply (rule NSsummable_comparison_test)
apply (auto simp add: abs_idempotent)
done

ML
{*
val sumhr = thm "sumhr";
val sumhr_zero = thm "sumhr_zero";
val sumhr_if = thm "sumhr_if";
val sumhr_Suc_zero = thm "sumhr_Suc_zero";
val sumhr_eq_bounds = thm "sumhr_eq_bounds";
val sumhr_Suc = thm "sumhr_Suc";
val sumhr_add_lbound_zero = thm "sumhr_add_lbound_zero";
val sumhr_add = thm "sumhr_add";
val sumhr_mult = thm "sumhr_mult";
val sumhr_split_add = thm "sumhr_split_add";
val sumhr_split_diff = thm "sumhr_split_diff";
val sumhr_hrabs = thm "sumhr_hrabs";
val sumhr_fun_hypnat_eq = thm "sumhr_fun_hypnat_eq";
val sumhr_const = thm "sumhr_const";
val sumhr_add_mult_const = thm "sumhr_add_mult_const";
val sumhr_less_bounds_zero = thm "sumhr_less_bounds_zero";
val sumhr_minus = thm "sumhr_minus";
val sumhr_shift_bounds = thm "sumhr_shift_bounds";
val sumhr_hypreal_of_hypnat_omega = thm "sumhr_hypreal_of_hypnat_omega";
val sumhr_hypreal_omega_minus_one = thm "sumhr_hypreal_omega_minus_one";
val sumhr_minus_one_realpow_zero = thm "sumhr_minus_one_realpow_zero";
val sumhr_interval_const = thm "sumhr_interval_const";
val starfunNat_sumr = thm "starfunNat_sumr";
val sumhr_hrabs_approx = thm "sumhr_hrabs_approx";
val sums_NSsums_iff = thm "sums_NSsums_iff";
val summable_NSsummable_iff = thm "summable_NSsummable_iff";
val suminf_NSsuminf_iff = thm "suminf_NSsuminf_iff";
val NSsums_NSsummable = thm "NSsums_NSsummable";
val NSsummable_NSsums = thm "NSsummable_NSsums";
val NSsums_unique = thm "NSsums_unique";
val NSseries_zero = thm "NSseries_zero";
val NSsummable_NSCauchy = thm "NSsummable_NSCauchy";
val NSsummable_NSLIMSEQ_zero = thm "NSsummable_NSLIMSEQ_zero";
val summable_LIMSEQ_zero = thm "summable_LIMSEQ_zero";
val NSsummable_comparison_test = thm "NSsummable_comparison_test";
val NSsummable_rabs_comparison_test = thm "NSsummable_rabs_comparison_test";
*}

end
