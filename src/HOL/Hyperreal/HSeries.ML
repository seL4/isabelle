(*  Title       : HSeries.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Finite summation and infinite series
                  for hyperreals
*) 

Goalw [sumhr_def]
     "sumhr(M,N,f) =  \
\       Abs_hypreal(UN X:Rep_hypnat(M). UN Y: Rep_hypnat(N). \
\         hyprel ``{%n::nat. sumr (X n) (Y n) f})";
by (Auto_tac);
qed "sumhr_iff";

Goalw [sumhr_def]
     "sumhr(Abs_hypnat(hypnatrel``{%n. M n}), \
\           Abs_hypnat(hypnatrel``{%n. N n}), f) = \
\     Abs_hypreal(hyprel `` {%n. sumr (M n) (N n) f})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "sumhr";

(*------------------------------------------------------- 
  lcp's suggestion: exploit pattern matching 
  facilities and use as definition instead (to do)
 -------------------------------------------------------*)
Goalw [sumhr_def]
      "sumhr p = (%(M,N,f). Abs_hypreal(UN X:Rep_hypnat(M). \
\                     UN Y: Rep_hypnat(N). \
\           hyprel ``{%n::nat. sumr (X n) (Y n) f})) p";
by (res_inst_tac [("p","p")] PairE 1);
by (res_inst_tac [("p","y")] PairE 1);
by (Auto_tac);
qed "sumhr_iff2";

(* Theorem corresponding to base case in def of sumr *)
Goalw [hypnat_zero_def]
     "sumhr (m,0,f) = 0";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (auto_tac (claset(), 
              simpset() addsimps [sumhr, symmetric hypreal_zero_def]));
qed "sumhr_zero";
Addsimps [sumhr_zero];

(* Theorem corresponding to recursive case in def of sumr *)
Goalw [hypnat_one_def]
     "sumhr(m,n+(1::hypnat),f) = (if n + (1::hypnat) <= m then 0 \
\                         else sumhr(m,n,f) + ( *fNat* f) n)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
     simpset() addsimps [sumhr, hypnat_add,hypnat_le,starfunNat,hypreal_add, 
                         hypreal_zero_def]));
by (ALLGOALS(Ultra_tac));
qed "sumhr_if";

Goalw [hypnat_one_def] "sumhr (n + (1::hypnat), n, f) = 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypnat_add, hypreal_zero_def]));
qed "sumhr_Suc_zero";
Addsimps [sumhr_Suc_zero];

Goal "sumhr (n,n,f) = 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [sumhr, hypreal_zero_def]));
qed "sumhr_eq_bounds";
Addsimps [sumhr_eq_bounds];

Goalw [hypnat_one_def] 
     "sumhr (m,m + (1::hypnat),f) = ( *fNat* f) m";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypnat_add,starfunNat]));
qed "sumhr_Suc";
Addsimps [sumhr_Suc];

Goal "sumhr(m+k,k,f) = 0";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","k")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypnat_add, hypreal_zero_def]));
qed "sumhr_add_lbound_zero";
Addsimps [sumhr_add_lbound_zero];

Goal "sumhr (m,n,f) + sumhr(m,n,g) = sumhr(m,n,%i. f i + g i)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypreal_add,sumr_add]));
qed "sumhr_add";

Goalw [hypreal_of_real_def]
      "hypreal_of_real r * sumhr(m,n,f) = sumhr(m,n,%n. r * f n)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypreal_mult,sumr_mult]));
qed "sumhr_mult";

Goalw [hypnat_zero_def]
     "n < p ==> sumhr (0,n,f) + sumhr (n,p,f) = sumhr (0,p,f)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","p")] eq_Abs_hypnat 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset],
       simpset() addsimps [sumhr,hypreal_add,hypnat_less, sumr_split_add]));
qed "sumhr_split_add";

(*FIXME delete*)
Goal "n < p ==> sumhr (0, p, f) + - sumhr (0, n, f) = sumhr (n,p,f)";
by (dres_inst_tac [("f1","f")] (sumhr_split_add RS sym) 1);
by (Asm_simp_tac 1);
qed "sumhr_split_add_minus";

Goal "n < p ==> sumhr (0, p, f) - sumhr (0, n, f) = sumhr (n,p,f)";
by (dres_inst_tac [("f1","f")] (sumhr_split_add RS sym) 1);
by (Asm_simp_tac 1);
qed "sumhr_split_diff";

Goal "abs(sumhr(m,n,f)) <= sumhr(m,n,%i. abs(f i))";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypreal_le,hypreal_hrabs,sumr_rabs]));
qed "sumhr_hrabs";

(* other general version also needed *)
Goalw [hypnat_of_nat_def]
     "(ALL r. m <= r & r < n --> f r = g r) --> \
\     sumhr(hypnat_of_nat m, hypnat_of_nat n, f) = \
\     sumhr(hypnat_of_nat m, hypnat_of_nat n, g)";
by (Step_tac 1 THEN dtac sumr_fun_eq 1);
by (auto_tac (claset(), simpset() addsimps [sumhr]));
qed "sumhr_fun_hypnat_eq";

Goalw [hypnat_zero_def,hypreal_of_real_def]
      "sumhr(0,n,%i. r) = hypreal_of_hypnat n*hypreal_of_real r";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac
    (simpset() addsimps [sumhr, hypreal_of_hypnat,hypreal_mult]) 1);
qed "sumhr_const";

Goalw [hypnat_zero_def,hypreal_of_real_def]
     "sumhr(0,n,f) + -(hypreal_of_hypnat n*hypreal_of_real r) = \
\     sumhr(0,n,%i. f i + -r)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [sumhr,
		    hypreal_of_hypnat,hypreal_mult,hypreal_add,
		    hypreal_minus,sumr_add RS sym]) 1);
qed "sumhr_add_mult_const";

Goal "n < m ==> sumhr (m,n,f) = 0";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset() addEs [FreeUltrafilterNat_subset],
              simpset() addsimps [sumhr,hypnat_less, hypreal_zero_def]));
qed "sumhr_less_bounds_zero";
Addsimps [sumhr_less_bounds_zero];

Goal "sumhr(m, n, %i. - f i) = - sumhr(m, n, f)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [sumhr, hypreal_minus,sumr_minus]));
qed "sumhr_minus";

Goalw [hypnat_of_nat_def]
     "sumhr(m+hypnat_of_nat k,n+hypnat_of_nat k,f) = sumhr(m,n,%i. f(i + k))";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypnat_add,sumr_shift_bounds]));
qed "sumhr_shift_bounds";

(*------------------------------------------------------------------
      Theorems about NS sums - infinite sums are obtained
      by summing to some infinite hypernatural (such as whn)
 -----------------------------------------------------------------*)
Goalw [hypnat_omega_def,hypnat_zero_def] 
      "sumhr(0,whn,%i. 1) = hypreal_of_hypnat whn";
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypreal_of_hypnat]));
qed "sumhr_hypreal_of_hypnat_omega";

Goalw [hypnat_omega_def,hypnat_zero_def,omega_def]  
     "sumhr(0, whn, %i. 1) = omega - 1";
by (simp_tac (HOL_ss addsimps
             [hypreal_numeral_1_eq_1, hypreal_one_def]) 1); 
by (auto_tac (claset(),
              simpset() addsimps [sumhr, hypreal_diff, real_of_nat_Suc]));
qed "sumhr_hypreal_omega_minus_one";

Goalw [hypnat_zero_def, hypnat_omega_def]
     "sumhr(0, whn + whn, %i. (-1) ^ (i+1)) = 0";
by (simp_tac (simpset() delsimps [realpow_Suc]
               addsimps [sumhr,hypnat_add,double_lemma, hypreal_zero_def]) 1);
qed "sumhr_minus_one_realpow_zero";
Addsimps [sumhr_minus_one_realpow_zero];

Goalw [hypnat_of_nat_def,hypreal_of_real_def]
     "(ALL n. m <= Suc n --> f n = r) & m <= na \
\          ==> sumhr(hypnat_of_nat m,hypnat_of_nat na,f) = \
\          (hypreal_of_nat (na - m) * hypreal_of_real r)";
by (auto_tac (claset() addSDs [sumr_interval_const],
              simpset() addsimps [sumhr,hypreal_of_nat_def,
                                  hypreal_of_real_def, hypreal_mult]));
qed "sumhr_interval_const";

Goalw [hypnat_zero_def]
     "( *fNat* (%n. sumr 0 n f)) N = sumhr(0,N,f)";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [starfunNat,sumhr]) 1);
qed "starfunNat_sumr";

Goal "sumhr (0, M, f) @= sumhr (0, N, f) \
\     ==> abs (sumhr (M, N, f)) @= 0";
by (cut_inst_tac [("x","M"),("y","N")] hypnat_linear 1);
by (auto_tac (claset(), simpset() addsimps [approx_refl]));
by (dtac (approx_sym RS (approx_minus_iff RS iffD1)) 1);
by (auto_tac (claset() addDs [approx_hrabs],
              simpset() addsimps [sumhr_split_add_minus]));
qed "sumhr_hrabs_approx";
Addsimps [sumhr_hrabs_approx];

(*----------------------------------------------------------------
      infinite sums: Standard and NS theorems
 ----------------------------------------------------------------*)
Goalw [sums_def,NSsums_def] "(f sums l) = (f NSsums l)";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]) 1);
qed "sums_NSsums_iff";

Goalw [summable_def,NSsummable_def] 
      "(summable f) = (NSsummable f)";
by (simp_tac (simpset() addsimps [sums_NSsums_iff]) 1);
qed "summable_NSsummable_iff";

Goalw [suminf_def,NSsuminf_def] 
      "(suminf f) = (NSsuminf f)";
by (simp_tac (simpset() addsimps [sums_NSsums_iff]) 1);
qed "suminf_NSsuminf_iff";

Goalw [NSsums_def,NSsummable_def] 
      "f NSsums l ==> NSsummable f";
by (Blast_tac 1);
qed "NSsums_NSsummable";

Goalw [NSsummable_def,NSsuminf_def]
     "NSsummable f ==> f NSsums (NSsuminf f)";
by (blast_tac (claset() addIs [someI2]) 1);
qed "NSsummable_NSsums";

Goal "f NSsums s ==> (s = NSsuminf f)";
by (asm_full_simp_tac 
    (simpset() addsimps [suminf_NSsuminf_iff RS sym,sums_NSsums_iff,
                         sums_unique]) 1);
qed "NSsums_unique";

Goal "ALL m. n <= Suc m --> f(m) = 0 ==> f NSsums (sumr 0 n f)";
by (asm_simp_tac (simpset() addsimps [sums_NSsums_iff RS sym, series_zero]) 1);
qed "NSseries_zero";

Goal "NSsummable f = \
\     (ALL M: HNatInfinite. ALL N: HNatInfinite. abs (sumhr(M,N,f)) @= 0)";
by (auto_tac (claset(),
              simpset() addsimps [summable_NSsummable_iff RS sym,
                 summable_convergent_sumr_iff, convergent_NSconvergent_iff,
                 NSCauchy_NSconvergent_iff RS sym, NSCauchy_def,
                 starfunNat_sumr]));
by (cut_inst_tac [("x","M"),("y","N")] hypnat_linear 1);
by (auto_tac (claset(), simpset() addsimps [approx_refl]));
by (rtac ((approx_minus_iff RS iffD2) RS approx_sym) 1);
by (rtac (approx_minus_iff RS iffD2) 2);
by (auto_tac (claset() addDs [approx_hrabs_zero_cancel],
              simpset() addsimps [sumhr_split_add_minus]));
qed "NSsummable_NSCauchy";

(*-------------------------------------------------------------------
         Terms of a convergent series tend to zero
 -------------------------------------------------------------------*)
Goalw [NSLIMSEQ_def] "NSsummable f ==> f ----NS> 0";
by (auto_tac (claset(), simpset() addsimps [NSsummable_NSCauchy]));
by (dtac bspec 1 THEN Auto_tac);
by (dres_inst_tac [("x","N + (1::hypnat)")] bspec 1);
by (auto_tac (claset() addIs [HNatInfinite_add_one, approx_hrabs_zero_cancel],
              simpset()));
qed "NSsummable_NSLIMSEQ_zero";

(* Easy to prove stsandard case now *)
Goal "summable f ==> f ----> 0";
by (auto_tac (claset(),
        simpset() addsimps [summable_NSsummable_iff,
                            LIMSEQ_NSLIMSEQ_iff, NSsummable_NSLIMSEQ_zero]));
qed "summable_LIMSEQ_zero";

(*-------------------------------------------------------------------
                  NS Comparison test
 -------------------------------------------------------------------*)

Goal "[| EX N. ALL n. N <= n --> abs(f n) <= g n; \
\        NSsummable g \
\     |] ==> NSsummable f";
by (auto_tac (claset() addIs [summable_comparison_test],
              simpset() addsimps [summable_NSsummable_iff RS sym]));
qed "NSsummable_comparison_test";

Goal "[| EX N. ALL n. N <= n --> abs(f n) <= g n; \
\        NSsummable g \
\     |] ==> NSsummable (%k. abs (f k))";
by (rtac NSsummable_comparison_test 1);
by (auto_tac (claset(), simpset() addsimps [abs_idempotent]));
qed "NSsummable_rabs_comparison_test";
