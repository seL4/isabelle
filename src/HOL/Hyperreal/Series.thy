(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
*) 

header{*Finite Summation and Infinite Series*}

theory Series = SEQ + Lim:

consts sumr :: "[nat,nat,(nat=>real)] => real"
primrec
   sumr_0:   "sumr m 0 f = 0"
   sumr_Suc: "sumr m (Suc n) f = (if n < m then 0 else sumr m n f + f(n))"

constdefs
   sums  :: "[nat=>real,real] => bool"     (infixr "sums" 80)
   "f sums s  == (%n. sumr 0 n f) ----> s"

   summable :: "(nat=>real) => bool"
   "summable f == (\<exists>s. f sums s)"

   suminf   :: "(nat=>real) => real"
   "suminf f == (@s. f sums s)"


lemma sumr_Suc_zero [simp]: "sumr (Suc n) n f = 0"
by (induct_tac "n", auto)

lemma sumr_eq_bounds [simp]: "sumr m m f = 0"
by (induct_tac "m", auto)

lemma sumr_Suc_eq [simp]: "sumr m (Suc m) f = f(m)"
by auto

lemma sumr_add_lbound_zero [simp]: "sumr (m+k) k f = 0"
by (induct_tac "k", auto)

lemma sumr_add: "sumr m n f + sumr m n g = sumr m n (%n. f n + g n)"
apply (induct_tac "n")
apply (simp_all add: add_ac)
done

lemma sumr_mult: "r * sumr m n f = sumr m n (%n. r * f n)"
apply (induct_tac "n")
apply (simp_all add: right_distrib)
done

lemma sumr_split_add [rule_format]:
     "n < p --> sumr 0 n f + sumr n p f = sumr 0 p f"
apply (induct_tac "p", auto)
apply (rename_tac k) 
apply (subgoal_tac "n=k", auto) 
done

lemma sumr_split_add_minus: "n < p ==> sumr 0 p f + - sumr 0 n f = sumr n p f"
apply (drule_tac f1 = f in sumr_split_add [symmetric])
apply (simp add: add_ac)
done

lemma sumr_split_add2 [rule_format]:
     "0 < n --> n < p --> sumr (Suc 0) n f + sumr n p f = sumr (Suc 0) p f"
apply (induct_tac "p", auto) 
apply (rename_tac k) 
apply (subgoal_tac "n=k", auto)
done

lemma sumr_split_add3:
     "[| 0<n; n \<le> p |] ==> sumr (Suc 0) n f + sumr n p f = sumr (Suc 0) p f"
apply (drule le_imp_less_or_eq, auto)
apply (blast intro: sumr_split_add2)
done

lemma sumr_rabs: "abs(sumr m n f) \<le> sumr m n (%i. abs(f i))"
apply (induct_tac "n")
apply (auto intro: abs_triangle_ineq [THEN order_trans] add_right_mono)
done

lemma sumr_fun_eq [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < n --> f r = g r) --> sumr m n f = sumr m n g"
by (induct_tac "n", auto)

lemma sumr_const [simp]: "sumr 0 n (%i. r) = real n * r"
apply (induct_tac "n")
apply (simp_all add: left_distrib real_of_nat_zero real_of_nat_Suc)
done

lemma sumr_add_mult_const:
     "sumr 0 n f + -(real n * r) = sumr 0 n (%i. f i + -r)"
by (simp only: sumr_add [symmetric] minus_mult_right, simp)

lemma sumr_diff_mult_const: "sumr 0 n f - (real n*r) = sumr 0 n (%i. f i - r)"
by (simp add: real_diff_def sumr_add_mult_const)

lemma sumr_less_bounds_zero [rule_format, simp]: "n < m --> sumr m n f = 0"
apply (induct_tac "n")
apply (auto dest: less_imp_le)
done

lemma sumr_minus: "sumr m n (%i. - f i) = - sumr m n f"
apply (induct_tac "n")
apply (case_tac [2] "Suc n \<le> m", simp_all)
done

lemma sumr_shift_bounds: "sumr (m+k) (n+k) f = sumr m n (%i. f(i + k))"
by (induct_tac "n", auto)

lemma sumr_minus_one_realpow_zero [simp]: "sumr 0 (2*n) (%i. (-1) ^ Suc i) = 0"
by (induct_tac "n", auto)

lemma Suc_diff_n: "m < Suc n ==> Suc n - m = Suc (n - m)"
by (drule less_imp_Suc_add, auto)

lemma sumr_interval_const [rule_format (no_asm)]:
     "(\<forall>n. m \<le> Suc n --> f n = r) --> m \<le> k --> sumr m k f = (real(k-m) * r)"
apply (induct_tac "k", auto) 
apply (drule_tac x = n in spec)
apply (auto dest!: le_imp_less_or_eq)
apply (simp (no_asm_simp) add: left_distrib Suc_diff_n real_of_nat_Suc)
done

lemma sumr_interval_const2 [rule_format (no_asm)]:
     "(\<forall>n. m \<le> n --> f n = r) --> m \<le> k  
      --> sumr m k f = (real (k - m) * r)"
apply (induct_tac "k", auto) 
apply (drule_tac x = n in spec)
apply (auto dest!: le_imp_less_or_eq)
apply (simp (no_asm_simp) add: Suc_diff_n left_distrib real_of_nat_Suc)
done

lemma sumr_le [rule_format (no_asm)]:
     "(\<forall>n. m \<le> n --> 0 \<le> f n) --> m < k --> sumr 0 m f \<le> sumr 0 k f"
apply (induct_tac "k")
apply (auto simp add: less_Suc_eq_le)
apply (drule_tac [!] x = n in spec, safe)
apply (drule le_imp_less_or_eq, safe)
apply (drule_tac [2] a = "sumr 0 m f" in add_mono)
apply (drule_tac a = "sumr 0 m f" in order_refl [THEN add_mono], auto)
done

lemma sumr_le2 [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < n --> f r \<le> g r) --> sumr m n f \<le> sumr m n g"
apply (induct_tac "n")
apply (auto intro: add_mono simp add: le_def)
done

lemma sumr_ge_zero [rule_format (no_asm)]: "(\<forall>n. 0 \<le> f n) --> 0 \<le> sumr m n f"
apply (induct_tac "n", auto)
apply (drule_tac x = n in spec, arith)
done

lemma sumr_ge_zero2 [rule_format (no_asm)]:
     "(\<forall>n. m \<le> n --> 0 \<le> f n) --> 0 \<le> sumr m n f"
apply (induct_tac "n", auto)
apply (drule_tac x = n in spec, arith)
done

lemma sumr_rabs_ge_zero [iff]: "0 \<le> sumr m n (%n. abs (f n))"
by (induct_tac "n", auto, arith)

lemma rabs_sumr_rabs_cancel [simp]:
     "abs (sumr m n (%n. abs (f n))) = (sumr m n (%n. abs (f n)))"
apply (induct_tac "n")
apply (auto, arith)
done

lemma sumr_zero [rule_format]:
     "\<forall>n. N \<le> n --> f n = 0 ==> N \<le> m --> sumr m n f = 0"
by (induct_tac "n", auto)

lemma Suc_le_imp_diff_ge2:
     "[|\<forall>n. N \<le> n --> f (Suc n) = 0; Suc N \<le> m|] ==> sumr m n f = 0"
apply (rule sumr_zero) 
apply (case_tac "n", auto)
done

lemma sumr_one_lb_realpow_zero [simp]: "sumr (Suc 0) n (%n. f(n) * 0 ^ n) = 0"
apply (induct_tac "n")
apply (case_tac [2] "n", auto)
done

lemma sumr_diff: "sumr m n f - sumr m n g = sumr m n (%n. f n - g n)"
by (simp add: diff_minus sumr_add [symmetric] sumr_minus)

lemma sumr_subst [rule_format (no_asm)]:
     "(\<forall>p. m \<le> p & p < m+n --> (f p = g p)) --> sumr m n f = sumr m n g"
by (induct_tac "n", auto)

lemma sumr_bound [rule_format (no_asm)]:
     "(\<forall>p. m \<le> p & p < m + n --> (f(p) \<le> K))  
      --> (sumr m (m + n) f \<le> (real n * K))"
apply (induct_tac "n")
apply (auto intro: add_mono simp add: left_distrib real_of_nat_Suc)
done

lemma sumr_bound2 [rule_format (no_asm)]:
     "(\<forall>p. 0 \<le> p & p < n --> (f(p) \<le> K))  
      --> (sumr 0 n f \<le> (real n * K))"
apply (induct_tac "n")
apply (auto intro: add_mono simp add: left_distrib real_of_nat_Suc)
done

lemma sumr_group [simp]:
     "sumr 0 n (%m. sumr (m * k) (m*k + k) f) = sumr 0 (n * k) f"
apply (subgoal_tac "k = 0 | 0 < k", auto)
apply (induct_tac "n")
apply (simp_all add: sumr_split_add add_commute)
done

subsection{* Infinite Sums, by the Properties of Limits*}

(*----------------------
   suminf is the sum   
 ---------------------*)
lemma sums_summable: "f sums l ==> summable f"
by (simp add: sums_def summable_def, blast)

lemma summable_sums: "summable f ==> f sums (suminf f)"
apply (simp add: summable_def suminf_def)
apply (blast intro: someI2)
done

lemma summable_sumr_LIMSEQ_suminf: 
     "summable f ==> (%n. sumr 0 n f) ----> (suminf f)"
apply (simp add: summable_def suminf_def sums_def)
apply (blast intro: someI2)
done

(*-------------------
    sum is unique                    
 ------------------*)
lemma sums_unique: "f sums s ==> (s = suminf f)"
apply (frule sums_summable [THEN summable_sums])
apply (auto intro!: LIMSEQ_unique simp add: sums_def)
done

(*
Goalw [sums_def,LIMSEQ_def] 
     "(\<forall>m. n \<le> Suc m --> f(m) = 0) ==> f sums (sumr 0 n f)"
by safe
by (res_inst_tac [("x","n")] exI 1);
by (safe THEN ftac le_imp_less_or_eq 1)
by safe
by (dres_inst_tac [("f","f")] sumr_split_add_minus 1);
by (ALLGOALS (Asm_simp_tac));
by (dtac (conjI RS sumr_interval_const) 1);
by Auto_tac
qed "series_zero";
next one was called series_zero2
**********************)

lemma series_zero: 
     "(\<forall>m. n \<le> m --> f(m) = 0) ==> f sums (sumr 0 n f)"
apply (simp add: sums_def LIMSEQ_def, safe)
apply (rule_tac x = n in exI)
apply (safe, frule le_imp_less_or_eq, safe)
apply (drule_tac f = f in sumr_split_add_minus, simp_all)
apply (drule sumr_interval_const2, auto)
done

lemma sums_mult: "x sums x0 ==> (%n. c * x(n)) sums (c * x0)"
by (auto simp add: sums_def sumr_mult [symmetric]
         intro!: LIMSEQ_mult intro: LIMSEQ_const)

lemma sums_divide: "x sums x' ==> (%n. x(n)/c) sums (x'/c)"
by (simp add: real_divide_def sums_mult mult_commute [of _ "inverse c"])

lemma sums_diff: "[| x sums x0; y sums y0 |] ==> (%n. x n - y n) sums (x0-y0)"
by (auto simp add: sums_def sumr_diff [symmetric] intro: LIMSEQ_diff)

lemma suminf_mult: "summable f ==> suminf f * c = suminf(%n. f n * c)"
by (auto intro!: sums_unique sums_mult summable_sums simp add: mult_commute)

lemma suminf_mult2: "summable f ==> c * suminf f  = suminf(%n. c * f n)"
by (auto intro!: sums_unique sums_mult summable_sums)

lemma suminf_diff:
     "[| summable f; summable g |]   
      ==> suminf f - suminf g  = suminf(%n. f n - g n)"
by (auto intro!: sums_diff sums_unique summable_sums)

lemma sums_minus: "x sums x0 ==> (%n. - x n) sums - x0"
by (auto simp add: sums_def intro!: LIMSEQ_minus simp add: sumr_minus)

lemma sums_group:
     "[|summable f; 0 < k |] ==> (%n. sumr (n*k) (n*k + k) f) sums (suminf f)"
apply (drule summable_sums)
apply (auto simp add: sums_def LIMSEQ_def)
apply (drule_tac x = r in spec, safe)
apply (rule_tac x = no in exI, safe)
apply (drule_tac x = "n*k" in spec)
apply (auto dest!: not_leE)
apply (drule_tac j = no in less_le_trans, auto)
done

lemma sumr_pos_lt_pair_lemma:
     "[|\<forall>d. - f (n + (d + d)) < f (Suc (n + (d + d)))|]
      ==> sumr 0 (n + Suc (Suc 0)) f \<le> sumr 0 (Suc (Suc 0) * Suc no + n) f"
apply (induct_tac "no", simp)
apply (rule_tac y = "sumr 0 (Suc (Suc 0) * (Suc na) +n) f" in order_trans)
apply assumption
apply (drule_tac x = "Suc na" in spec)
apply (simp add: add_ac) 
done


lemma sumr_pos_lt_pair:
     "[|summable f; \<forall>d. 0 < (f(n + (Suc(Suc 0) * d))) + f(n + ((Suc(Suc 0) * d) + 1))|]  
      ==> sumr 0 n f < suminf f"
apply (drule summable_sums)
apply (auto simp add: sums_def LIMSEQ_def)
apply (drule_tac x = "f (n) + f (n + 1) " in spec)
apply auto
apply (rule_tac [2] ccontr, drule_tac [2] linorder_not_less [THEN iffD1])
apply (frule_tac [2] no=no in sumr_pos_lt_pair_lemma) 
apply (drule_tac x = 0 in spec, simp)
apply (rotate_tac 1, drule_tac x = "Suc (Suc 0) * (Suc no) + n" in spec)
apply (safe, simp)
apply (subgoal_tac "suminf f + (f (n) + f (n + 1)) \<le> sumr 0 (Suc (Suc 0) * (Suc no) + n) f")
apply (rule_tac [2] y = "sumr 0 (n+ Suc (Suc 0)) f" in order_trans)
prefer 3 apply assumption
apply (rule_tac [2] y = "sumr 0 n f + (f (n) + f (n + 1))" in order_trans)
apply simp_all 
apply (subgoal_tac "suminf f \<le> sumr 0 (Suc (Suc 0) * (Suc no) + n) f")
apply (rule_tac [2] y = "suminf f + (f (n) + f (n + 1))" in order_trans)
prefer 3 apply simp 
apply (drule_tac [2] x = 0 in spec)
 prefer 2 apply simp 
apply (subgoal_tac "0 \<le> sumr 0 (Suc (Suc 0) * Suc no + n) f + - suminf f")
apply (simp add: abs_if) 
apply (auto simp add: linorder_not_less [symmetric])
done



(*-----------------------------------------------------------------
   Summable series of positive terms has limit >= any partial sum 
 ----------------------------------------------------------------*)
lemma series_pos_le: 
     "[| summable f; \<forall>m. n \<le> m --> 0 \<le> f(m) |] ==> sumr 0 n f \<le> suminf f"
apply (drule summable_sums)
apply (simp add: sums_def)
apply (cut_tac k = "sumr 0 n f" in LIMSEQ_const)
apply (erule LIMSEQ_le, blast) 
apply (rule_tac x = n in exI, clarify) 
apply (drule le_imp_less_or_eq)
apply (auto intro: sumr_le)
done

lemma series_pos_less:
     "[| summable f; \<forall>m. n \<le> m --> 0 < f(m) |] ==> sumr 0 n f < suminf f"
apply (rule_tac y = "sumr 0 (Suc n) f" in order_less_le_trans)
apply (rule_tac [2] series_pos_le, auto)
apply (drule_tac x = m in spec, auto)
done

(*-------------------------------------------------------------------
                    sum of geometric progression                 
 -------------------------------------------------------------------*)

lemma sumr_geometric: "x ~= 1 ==> sumr 0 n (%n. x ^ n) = (x ^ n - 1) / (x - 1)"
apply (induct_tac "n", auto)
apply (rule_tac c1 = "x - 1" in real_mult_right_cancel [THEN iffD1])
apply (auto simp add: real_mult_assoc left_distrib)
apply (simp add: right_distrib real_diff_def real_mult_commute)
done

lemma geometric_sums: "abs(x) < 1 ==> (%n. x ^ n) sums (1/(1 - x))"
apply (case_tac "x = 1")
apply (auto dest!: LIMSEQ_rabs_realpow_zero2 simp add: sumr_geometric sums_def real_diff_def add_divide_distrib)
apply (subgoal_tac "1 / (1 + -x) = 0/ (x - 1) + - 1/ (x - 1) ")
apply (erule ssubst)
apply (rule LIMSEQ_add, rule LIMSEQ_divide)
apply (auto intro: LIMSEQ_const simp add: real_diff_def minus_divide_right LIMSEQ_rabs_realpow_zero2)
done

(*-------------------------------------------------------------------
    Cauchy-type criterion for convergence of series (c.f. Harrison)
 -------------------------------------------------------------------*)
lemma summable_convergent_sumr_iff: "summable f = convergent (%n. sumr 0 n f)"
by (simp add: summable_def sums_def convergent_def)

lemma summable_Cauchy:
     "summable f =  
      (\<forall>e. 0 < e --> (\<exists>N. \<forall>m n. N \<le> m --> abs(sumr m n f) < e))"
apply (auto simp add: summable_convergent_sumr_iff Cauchy_convergent_iff [symmetric] Cauchy_def)
apply (drule_tac [!] spec, auto) 
apply (rule_tac x = M in exI)
apply (rule_tac [2] x = N in exI, auto)
apply (cut_tac [!] m = m and n = n in less_linear, auto)
apply (frule le_less_trans [THEN less_imp_le], assumption)
apply (drule_tac x = n in spec)
apply (drule_tac x = m in spec)
apply (auto intro: abs_minus_add_cancel [THEN subst]
            simp add: sumr_split_add_minus abs_minus_add_cancel)
done

(*-------------------------------------------------------------------
     Terms of a convergent series tend to zero
     > Goalw [LIMSEQ_def] "summable f ==> f ----> 0"
     Proved easily in HSeries after proving nonstandard case.
 -------------------------------------------------------------------*)
(*-------------------------------------------------------------------
                    Comparison test
 -------------------------------------------------------------------*)
lemma summable_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; summable g |] ==> summable f"
apply (auto simp add: summable_Cauchy)
apply (drule spec, auto)
apply (rule_tac x = "N + Na" in exI, auto)
apply (rotate_tac 2)
apply (drule_tac x = m in spec)
apply (auto, rotate_tac 2, drule_tac x = n in spec)
apply (rule_tac y = "sumr m n (%k. abs (f k))" in order_le_less_trans)
apply (rule sumr_rabs)
apply (rule_tac y = "sumr m n g" in order_le_less_trans)
apply (auto intro: sumr_le2 simp add: abs_interval_iff)
done

lemma summable_rabs_comparison_test:
     "[| \<exists>N. \<forall>n. N \<le> n --> abs(f n) \<le> g n; summable g |] 
      ==> summable (%k. abs (f k))"
apply (rule summable_comparison_test)
apply (auto simp add: abs_idempotent)
done

(*------------------------------------------------------------------*)
(*       Limit comparison property for series (c.f. jrh)            *)
(*------------------------------------------------------------------*)
lemma summable_le:
     "[|\<forall>n. f n \<le> g n; summable f; summable g |] ==> suminf f \<le> suminf g"
apply (drule summable_sums)+
apply (auto intro!: LIMSEQ_le simp add: sums_def)
apply (rule exI)
apply (auto intro!: sumr_le2)
done

lemma summable_le2:
     "[|\<forall>n. abs(f n) \<le> g n; summable g |]  
      ==> summable f & suminf f \<le> suminf g"
apply (auto intro: summable_comparison_test intro!: summable_le)
apply (simp add: abs_le_interval_iff)
done

(*-------------------------------------------------------------------
         Absolute convergence imples normal convergence
 -------------------------------------------------------------------*)
lemma summable_rabs_cancel: "summable (%n. abs (f n)) ==> summable f"
apply (auto simp add: sumr_rabs summable_Cauchy)
apply (drule spec, auto)
apply (rule_tac x = N in exI, auto)
apply (drule spec, auto)
apply (rule_tac y = "sumr m n (%n. abs (f n))" in order_le_less_trans)
apply (auto intro: sumr_rabs)
done

(*-------------------------------------------------------------------
         Absolute convergence of series
 -------------------------------------------------------------------*)
lemma summable_rabs:
     "summable (%n. abs (f n)) ==> abs(suminf f) \<le> suminf (%n. abs(f n))"
by (auto intro: LIMSEQ_le LIMSEQ_imp_rabs summable_rabs_cancel summable_sumr_LIMSEQ_suminf sumr_rabs)


subsection{* The Ratio Test*}

lemma rabs_ratiotest_lemma: "[| c \<le> 0; abs x \<le> c * abs y |] ==> x = (0::real)"
apply (drule order_le_imp_less_or_eq, auto)
apply (subgoal_tac "0 \<le> c * abs y")
apply (simp add: zero_le_mult_iff, arith)
done

lemma le_Suc_ex: "(k::nat) \<le> l ==> (\<exists>n. l = k + n)"
apply (drule le_imp_less_or_eq)
apply (auto dest: less_imp_Suc_add)
done

lemma le_Suc_ex_iff: "((k::nat) \<le> l) = (\<exists>n. l = k + n)"
by (auto simp add: le_Suc_ex)

(*All this trouble just to get 0<c *)
lemma ratio_test_lemma2:
     "[| \<forall>n. N \<le> n --> abs(f(Suc n)) \<le> c*abs(f n) |]  
      ==> 0 < c | summable f"
apply (simp (no_asm) add: linorder_not_le [symmetric])
apply (simp add: summable_Cauchy)
apply (safe, subgoal_tac "\<forall>n. N \<le> n --> f (Suc n) = 0")
prefer 2 apply (blast intro: rabs_ratiotest_lemma)
apply (rule_tac x = "Suc N" in exI, clarify)
apply (drule_tac n=n in Suc_le_imp_diff_ge2, auto) 
done

lemma ratio_test:
     "[| c < 1; \<forall>n. N \<le> n --> abs(f(Suc n)) \<le> c*abs(f n) |]  
      ==> summable f"
apply (frule ratio_test_lemma2, auto)
apply (rule_tac g = "%n. (abs (f N) / (c ^ N))*c ^ n" in summable_comparison_test)
apply (rule_tac x = N in exI, safe)
apply (drule le_Suc_ex_iff [THEN iffD1])
apply (auto simp add: power_add realpow_not_zero)
apply (induct_tac "na", auto)
apply (rule_tac y = "c*abs (f (N + n))" in order_trans)
apply (auto intro: mult_right_mono simp add: summable_def)
apply (simp add: mult_ac)
apply (rule_tac x = "abs (f N) * (1/ (1 - c)) / (c ^ N) " in exI)
apply (rule sums_divide)
apply (rule sums_mult)
apply (auto intro!: sums_mult geometric_sums simp add: real_abs_def)
done


(*--------------------------------------------------------------------------*)
(* Differentiation of finite sum                                            *)
(*--------------------------------------------------------------------------*)

lemma DERIV_sumr [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x))  
      --> DERIV (%x. sumr m n (%n. f n x)) x :> sumr m n (%r. f' r x)"
apply (induct_tac "n")
apply (auto intro: DERIV_add)
done

ML
{*
val sumr_0 = thm"sumr_0";
val sumr_Suc = thm"sumr_Suc";
val sums_def = thm"sums_def";
val summable_def = thm"summable_def";
val suminf_def = thm"suminf_def";

val sumr_Suc_zero = thm "sumr_Suc_zero";
val sumr_eq_bounds = thm "sumr_eq_bounds";
val sumr_Suc_eq = thm "sumr_Suc_eq";
val sumr_add_lbound_zero = thm "sumr_add_lbound_zero";
val sumr_add = thm "sumr_add";
val sumr_mult = thm "sumr_mult";
val sumr_split_add = thm "sumr_split_add";
val sumr_split_add_minus = thm "sumr_split_add_minus";
val sumr_split_add2 = thm "sumr_split_add2";
val sumr_split_add3 = thm "sumr_split_add3";
val sumr_rabs = thm "sumr_rabs";
val sumr_fun_eq = thm "sumr_fun_eq";
val sumr_const = thm "sumr_const";
val sumr_add_mult_const = thm "sumr_add_mult_const";
val sumr_diff_mult_const = thm "sumr_diff_mult_const";
val sumr_less_bounds_zero = thm "sumr_less_bounds_zero";
val sumr_minus = thm "sumr_minus";
val sumr_shift_bounds = thm "sumr_shift_bounds";
val sumr_minus_one_realpow_zero = thm "sumr_minus_one_realpow_zero";
val Suc_diff_n = thm "Suc_diff_n";
val sumr_interval_const = thm "sumr_interval_const";
val sumr_interval_const2 = thm "sumr_interval_const2";
val sumr_le = thm "sumr_le";
val sumr_le2 = thm "sumr_le2";
val sumr_ge_zero = thm "sumr_ge_zero";
val sumr_ge_zero2 = thm "sumr_ge_zero2";
val sumr_rabs_ge_zero = thm "sumr_rabs_ge_zero";
val rabs_sumr_rabs_cancel = thm "rabs_sumr_rabs_cancel";
val sumr_zero = thm "sumr_zero";
val Suc_le_imp_diff_ge2 = thm "Suc_le_imp_diff_ge2";
val sumr_one_lb_realpow_zero = thm "sumr_one_lb_realpow_zero";
val sumr_diff = thm "sumr_diff";
val sumr_subst = thm "sumr_subst";
val sumr_bound = thm "sumr_bound";
val sumr_bound2 = thm "sumr_bound2";
val sumr_group = thm "sumr_group";
val sums_summable = thm "sums_summable";
val summable_sums = thm "summable_sums";
val summable_sumr_LIMSEQ_suminf = thm "summable_sumr_LIMSEQ_suminf";
val sums_unique = thm "sums_unique";
val series_zero = thm "series_zero";
val sums_mult = thm "sums_mult";
val sums_divide = thm "sums_divide";
val sums_diff = thm "sums_diff";
val suminf_mult = thm "suminf_mult";
val suminf_mult2 = thm "suminf_mult2";
val suminf_diff = thm "suminf_diff";
val sums_minus = thm "sums_minus";
val sums_group = thm "sums_group";
val sumr_pos_lt_pair_lemma = thm "sumr_pos_lt_pair_lemma";
val sumr_pos_lt_pair = thm "sumr_pos_lt_pair";
val series_pos_le = thm "series_pos_le";
val series_pos_less = thm "series_pos_less";
val sumr_geometric = thm "sumr_geometric";
val geometric_sums = thm "geometric_sums";
val summable_convergent_sumr_iff = thm "summable_convergent_sumr_iff";
val summable_Cauchy = thm "summable_Cauchy";
val summable_comparison_test = thm "summable_comparison_test";
val summable_rabs_comparison_test = thm "summable_rabs_comparison_test";
val summable_le = thm "summable_le";
val summable_le2 = thm "summable_le2";
val summable_rabs_cancel = thm "summable_rabs_cancel";
val summable_rabs = thm "summable_rabs";
val rabs_ratiotest_lemma = thm "rabs_ratiotest_lemma";
val le_Suc_ex = thm "le_Suc_ex";
val le_Suc_ex_iff = thm "le_Suc_ex_iff";
val ratio_test_lemma2 = thm "ratio_test_lemma2";
val ratio_test = thm "ratio_test";
val DERIV_sumr = thm "DERIV_sumr";
*}

end
