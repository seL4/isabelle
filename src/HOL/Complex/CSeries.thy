(*  Title       : CSeries.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2002  University of Edinburgh
*)

header{*Finite Summation and Infinite Series for Complex Numbers*}

theory CSeries = CStar:

consts sumc :: "[nat,nat,(nat=>complex)] => complex"
primrec
   sumc_0:   "sumc m 0 f = 0"
   sumc_Suc: "sumc m (Suc n) f = (if n < m then 0 else sumc m n f + f(n))"

(*  
constdefs

   needs convergence of complex sequences  

  csums  :: [nat=>complex,complex] => bool     (infixr 80)
   "f sums s  == (%n. sumr 0 n f) ----C> s"
  
   csummable :: (nat=>complex) => bool
   "csummable f == (EX s. f csums s)"

   csuminf   :: (nat=>complex) => complex
   "csuminf f == (@s. f csums s)"
*)

lemma sumc_Suc_zero [simp]: "sumc (Suc n) n f = 0"
by (induct_tac "n", auto)

lemma sumc_eq_bounds [simp]: "sumc m m f = 0"
by (induct_tac "m", auto)

lemma sumc_Suc_eq [simp]: "sumc m (Suc m) f = f(m)"
by auto

lemma sumc_add_lbound_zero [simp]: "sumc (m+k) k f = 0"
by (induct_tac "k", auto)

lemma sumc_add: "sumc m n f + sumc m n g = sumc m n (%n. f n + g n)"
apply (induct_tac "n")
apply (auto simp add: add_ac)
done

lemma sumc_mult: "r * sumc m n f = sumc m n (%n. r * f n)"
apply (induct_tac "n", auto)
apply (auto simp add: right_distrib)
done

lemma sumc_split_add [rule_format]:
     "n < p --> sumc 0 n f + sumc n p f = sumc 0 p f"
apply (induct_tac "p") 
apply (auto dest!: leI dest: le_anti_sym)
done

lemma sumc_split_add_minus:
     "n < p ==> sumc 0 p f + - sumc 0 n f = sumc n p f"
apply (drule_tac f1 = f in sumc_split_add [symmetric])
apply (simp add: add_ac)
done

lemma sumc_cmod: "cmod(sumc m n f) \<le> sumr m n (%i. cmod(f i))"
apply (induct_tac "n")
apply (auto intro: complex_mod_triangle_ineq [THEN order_trans])
done

lemma sumc_fun_eq [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < n --> f r = g r) --> sumc m n f = sumc m n g"
by (induct_tac "n", auto)

lemma sumc_const [simp]: "sumc 0 n (%i. r) = complex_of_real (real n) * r"
apply (induct_tac "n")
apply (auto simp add: left_distrib complex_of_real_add [symmetric] real_of_nat_Suc)
done

lemma sumc_add_mult_const:
     "sumc 0 n f + -(complex_of_real(real n) * r) = sumc 0 n (%i. f i + -r)"
by (simp add: sumc_add [symmetric])

lemma sumc_diff_mult_const: 
     "sumc 0 n f - (complex_of_real(real n)*r) = sumc 0 n (%i. f i - r)"
by (simp add: diff_minus sumc_add_mult_const)

lemma sumc_less_bounds_zero [rule_format]: "n < m --> sumc m n f = 0"
by (induct_tac "n", auto)

lemma sumc_minus: "sumc m n (%i. - f i) = - sumc m n f"
by (induct_tac "n", auto)

lemma sumc_shift_bounds: "sumc (m+k) (n+k) f = sumc m n (%i. f(i + k))"
by (induct_tac "n", auto)

lemma sumc_minus_one_complexpow_zero [simp]:
     "sumc 0 (2*n) (%i. (-1) ^ Suc i) = 0"
by (induct_tac "n", auto)

lemma sumc_interval_const [rule_format (no_asm)]:
     "(\<forall>n. m \<le> Suc n --> f n = r) & m \<le> na  
                 --> sumc m na f = (complex_of_real(real (na - m)) * r)"
apply (induct_tac "na")
apply (auto simp add: Suc_diff_le real_of_nat_Suc complex_of_real_add [symmetric] left_distrib)
done

lemma sumc_interval_const2 [rule_format (no_asm)]:
     "(\<forall>n. m \<le> n --> f n = r) & m \<le> na  
      --> sumc m na f = (complex_of_real(real (na - m)) * r)"
apply (induct_tac "na")
apply (auto simp add: left_distrib Suc_diff_le real_of_nat_Suc complex_of_real_add [symmetric])
done

(*** 
Goal "(\<forall>n. m \<le> n --> 0 \<le> cmod(f n)) & m < k --> cmod(sumc 0 m f) \<le> cmod(sumc 0 k f)"
by (induct_tac "k" 1)
by (Step_tac 1)
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [less_Suc_eq_le])));
by (ALLGOALS(dres_inst_tac [("x","n")] spec));
by (Step_tac 1)
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1)
by (dtac add_mono 2)
by (dres_inst_tac [("i","sumr 0 m f")] (order_refl RS add_mono) 1);
by Auto_tac
qed_spec_mp "sumc_le";

Goal "!!f g. (\<forall>r. m \<le> r & r < n --> f r \<le> g r) \
\                --> sumc m n f \<le> sumc m n g";
by (induct_tac "n" 1)
by (auto_tac (claset() addIs [add_mono],
    simpset() addsimps [le_def]));
qed_spec_mp "sumc_le2";

Goal "(\<forall>n. 0 \<le> f n) --> 0 \<le> sumc m n f";
by (induct_tac "n" 1)
by Auto_tac
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1)
qed_spec_mp "sumc_ge_zero";

Goal "(\<forall>n. m \<le> n --> 0 \<le> f n) --> 0 \<le> sumc m n f";
by (induct_tac "n" 1)
by Auto_tac
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1)
qed_spec_mp "sumc_ge_zero2";
***)

lemma sumr_cmod_ge_zero [iff]: "0 \<le> sumr m n (%n. cmod (f n))"
apply (induct_tac "n", auto)
apply (rule_tac j = 0 in real_le_trans, auto)
done

lemma rabs_sumc_cmod_cancel [simp]:
     "abs (sumr m n (%n. cmod (f n))) = (sumr m n (%n. cmod (f n)))"
by (simp add: abs_if linorder_not_less)

lemma sumc_zero:
     "\<forall>n. N \<le> n --> f n = 0  
      ==> \<forall>m n. N \<le> m --> sumc m n f = 0"
apply safe
apply (induct_tac "n", auto)
done

lemma fun_zero_sumc_zero:
     "\<forall>n. N \<le> n --> f (Suc n) = 0  
      ==> \<forall>m n. Suc N \<le> m --> sumc m n f = 0"
apply (rule sumc_zero, safe)
apply (drule_tac x = "n - 1" in spec, auto, arith)
done

lemma sumc_one_lb_complexpow_zero [simp]: "sumc 1 n (%n. f(n) * 0 ^ n) = 0"
apply (induct_tac "n")
apply (case_tac [2] "n", auto)
done

lemma sumc_diff: "sumc m n f - sumc m n g = sumc m n (%n. f n - g n)"
by (simp add: diff_minus sumc_add [symmetric] sumc_minus)

lemma sumc_subst [rule_format (no_asm)]:
     "(\<forall>p. (m \<le> p & p < m + n --> (f p = g p))) --> sumc m n f = sumc m n g"
by (induct_tac "n", auto)

lemma sumc_group [simp]:
     "sumc 0 n (%m. sumc (m * k) (m*k + k) f) = sumc 0 (n * k) f"
apply (subgoal_tac "k = 0 | 0 < k", auto)
apply (induct_tac "n")
apply (auto simp add: sumc_split_add add_commute)
done

ML
{*
val sumc_Suc_zero = thm "sumc_Suc_zero";
val sumc_eq_bounds = thm "sumc_eq_bounds";
val sumc_Suc_eq = thm "sumc_Suc_eq";
val sumc_add_lbound_zero = thm "sumc_add_lbound_zero";
val sumc_add = thm "sumc_add";
val sumc_mult = thm "sumc_mult";
val sumc_split_add = thm "sumc_split_add";
val sumc_split_add_minus = thm "sumc_split_add_minus";
val sumc_cmod = thm "sumc_cmod";
val sumc_fun_eq = thm "sumc_fun_eq";
val sumc_const = thm "sumc_const";
val sumc_add_mult_const = thm "sumc_add_mult_const";
val sumc_diff_mult_const = thm "sumc_diff_mult_const";
val sumc_less_bounds_zero = thm "sumc_less_bounds_zero";
val sumc_minus = thm "sumc_minus";
val sumc_shift_bounds = thm "sumc_shift_bounds";
val sumc_minus_one_complexpow_zero = thm "sumc_minus_one_complexpow_zero";
val sumc_interval_const = thm "sumc_interval_const";
val sumc_interval_const2 = thm "sumc_interval_const2";
val sumr_cmod_ge_zero = thm "sumr_cmod_ge_zero";
val rabs_sumc_cmod_cancel = thm "rabs_sumc_cmod_cancel";
val sumc_zero = thm "sumc_zero";
val fun_zero_sumc_zero = thm "fun_zero_sumc_zero";
val sumc_one_lb_complexpow_zero = thm "sumc_one_lb_complexpow_zero";
val sumc_diff = thm "sumc_diff";
val sumc_subst = thm "sumc_subst";
val sumc_group = thm "sumc_group";
*}

end

