(*  Title       : Transcendental.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998,1999 University of Cambridge
                  1999,2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Power Series, Transcendental Functions etc.*}

theory Transcendental
import NthRoot Fact HSeries EvenOdd Lim
begin

constdefs
    root :: "[nat,real] => real"
    "root n x == (@u. ((0::real) < x --> 0 < u) & (u ^ n = x))"

    sqrt :: "real => real"
    "sqrt x == root 2 x"

    exp :: "real => real"
    "exp x == suminf(%n. inverse(real (fact n)) * (x ^ n))"

    sin :: "real => real"
    "sin x == suminf(%n. (if even(n) then 0 else
             ((- 1) ^ ((n - Suc 0) div 2))/(real (fact n))) * x ^ n)"
 
    diffs :: "(nat => real) => nat => real"
    "diffs c == (%n. real (Suc n) * c(Suc n))"

    cos :: "real => real"
    "cos x == suminf(%n. (if even(n) then ((- 1) ^ (n div 2))/(real (fact n)) 
                          else 0) * x ^ n)"
  
    ln :: "real => real"
    "ln x == (@u. exp u = x)"

    pi :: "real"
    "pi == 2 * (@x. 0 \<le> (x::real) & x \<le> 2 & cos x = 0)"

    tan :: "real => real"
    "tan x == (sin x)/(cos x)"

    arcsin :: "real => real"
    "arcsin y == (@x. -(pi/2) \<le> x & x \<le> pi/2 & sin x = y)"

    arcos :: "real => real"
    "arcos y == (@x. 0 \<le> x & x \<le> pi & cos x = y)"
     
    arctan :: "real => real"
    "arctan y == (@x. -(pi/2) < x & x < pi/2 & tan x = y)"


lemma real_root_zero [simp]: "root (Suc n) 0 = 0"
apply (unfold root_def)
apply (safe intro!: some_equality power_0_Suc elim!: realpow_zero_zero)
done

lemma real_root_pow_pos: 
     "0 < x ==> (root(Suc n) x) ^ (Suc n) = x"
apply (unfold root_def)
apply (drule_tac n = n in realpow_pos_nth2)
apply (auto intro: someI2)
done

lemma real_root_pow_pos2: "0 \<le> x ==> (root(Suc n) x) ^ (Suc n) = x"
by (auto dest!: real_le_imp_less_or_eq dest: real_root_pow_pos)

lemma real_root_pos: 
     "0 < x ==> root(Suc n) (x ^ (Suc n)) = x"
apply (unfold root_def)
apply (rule some_equality)
apply (frule_tac [2] n = n in zero_less_power)
apply (auto simp add: zero_less_mult_iff)
apply (rule_tac x = u and y = x in linorder_cases)
apply (drule_tac n1 = n and x = u in zero_less_Suc [THEN [3] realpow_less])
apply (drule_tac [4] n1 = n and x = x in zero_less_Suc [THEN [3] realpow_less])
apply (auto simp add: order_less_irrefl)
done

lemma real_root_pos2: "0 \<le> x ==> root(Suc n) (x ^ (Suc n)) = x"
by (auto dest!: real_le_imp_less_or_eq real_root_pos)

lemma real_root_pos_pos: 
     "0 < x ==> 0 \<le> root(Suc n) x"
apply (unfold root_def)
apply (drule_tac n = n in realpow_pos_nth2)
apply (safe, rule someI2)
apply (auto intro!: order_less_imp_le dest: zero_less_power simp add: zero_less_mult_iff)
done

lemma real_root_pos_pos_le: "0 \<le> x ==> 0 \<le> root(Suc n) x"
by (auto dest!: real_le_imp_less_or_eq dest: real_root_pos_pos)

lemma real_root_one [simp]: "root (Suc n) 1 = 1"
apply (unfold root_def)
apply (rule some_equality, auto)
apply (rule ccontr)
apply (rule_tac x = u and y = 1 in linorder_cases)
apply (drule_tac n = n in realpow_Suc_less_one)
apply (drule_tac [4] n = n in power_gt1_lemma)
apply (auto simp add: order_less_irrefl)
done


subsection{*Square Root*}

(*lcp: needed now because 2 is a binary numeral!*)
lemma root_2_eq [simp]: "root 2 = root (Suc (Suc 0))"
apply (simp (no_asm) del: nat_numeral_0_eq_0 nat_numeral_1_eq_1 add: nat_numeral_0_eq_0 [symmetric])
done

lemma real_sqrt_zero [simp]: "sqrt 0 = 0"
by (unfold sqrt_def, auto)

lemma real_sqrt_one [simp]: "sqrt 1 = 1"
by (unfold sqrt_def, auto)

lemma real_sqrt_pow2_iff [simp]: "((sqrt x)\<twosuperior> = x) = (0 \<le> x)"
apply (unfold sqrt_def)
apply (rule iffI) 
 apply (cut_tac r = "root 2 x" in realpow_two_le)
 apply (simp add: numeral_2_eq_2)
apply (subst numeral_2_eq_2)
apply (erule real_root_pow_pos2)
done

lemma [simp]: "(sqrt(u2\<twosuperior> + v2\<twosuperior>))\<twosuperior> = u2\<twosuperior> + v2\<twosuperior>"
by (rule realpow_two_le_add_order [THEN real_sqrt_pow2_iff [THEN iffD2]])

lemma real_sqrt_pow2 [simp]: "0 \<le> x ==> (sqrt x)\<twosuperior> = x"
by (simp add: real_sqrt_pow2_iff)

lemma real_sqrt_abs_abs [simp]: "sqrt\<bar>x\<bar> ^ 2 = \<bar>x\<bar>"
by (rule real_sqrt_pow2_iff [THEN iffD2], arith)

lemma real_pow_sqrt_eq_sqrt_pow: 
      "0 \<le> x ==> (sqrt x)\<twosuperior> = sqrt(x\<twosuperior>)"
apply (unfold sqrt_def)
apply (subst numeral_2_eq_2)
apply (auto intro: real_root_pow_pos2 [THEN ssubst] real_root_pos2 [THEN ssubst] simp del: realpow_Suc)
done

lemma real_pow_sqrt_eq_sqrt_abs_pow2:
     "0 \<le> x ==> (sqrt x)\<twosuperior> = sqrt(\<bar>x\<bar> ^ 2)" 
by (simp add: real_pow_sqrt_eq_sqrt_pow [symmetric])

lemma real_sqrt_pow_abs: "0 \<le> x ==> (sqrt x)\<twosuperior> = \<bar>x\<bar>"
apply (rule real_sqrt_abs_abs [THEN subst])
apply (rule_tac x1 = x in real_pow_sqrt_eq_sqrt_abs_pow2 [THEN ssubst])
apply (rule_tac [2] real_pow_sqrt_eq_sqrt_pow [symmetric])
apply (assumption, arith)
done

lemma not_real_square_gt_zero [simp]: "(~ (0::real) < x*x) = (x = 0)"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (simp add: zero_less_mult_iff)
done

lemma real_mult_self_eq_zero_iff [simp]: "(r * r = 0) = (r = (0::real))"
by auto

lemma real_sqrt_gt_zero: "0 < x ==> 0 < sqrt(x)"
apply (unfold sqrt_def root_def)
apply (subst numeral_2_eq_2)
apply (drule realpow_pos_nth2 [where n=1], safe)
apply (rule someI2, auto)
done

lemma real_sqrt_ge_zero: "0 \<le> x ==> 0 \<le> sqrt(x)"
by (auto intro: real_sqrt_gt_zero simp add: order_le_less)


(*we need to prove something like this:
lemma "[|r ^ n = a; 0<n; 0 < a \<longrightarrow> 0 < r|] ==> root n a = r"
apply (case_tac n, simp) 
apply (unfold root_def) 
apply (rule someI2 [of _ r], safe)
apply (auto simp del: realpow_Suc dest: power_inject_base)
*)

lemma sqrt_eqI: "[|r\<twosuperior> = a; 0 \<le> r|] ==> sqrt a = r"
apply (unfold sqrt_def root_def) 
apply (rule someI2 [of _ r], auto) 
apply (auto simp add: numeral_2_eq_2 simp del: realpow_Suc 
            dest: power_inject_base) 
done

lemma real_sqrt_mult_distrib: 
     "[| 0 \<le> x; 0 \<le> y |] ==> sqrt(x*y) = sqrt(x) * sqrt(y)"
apply (rule sqrt_eqI)
apply (simp add: power_mult_distrib)  
apply (simp add: zero_le_mult_iff real_sqrt_ge_zero) 
done

lemma real_sqrt_mult_distrib2: "[|0\<le>x; 0\<le>y |] ==> sqrt(x*y) =  sqrt(x) * sqrt(y)"
by (auto intro: real_sqrt_mult_distrib simp add: order_le_less)

lemma real_sqrt_sum_squares_ge_zero [simp]: "0 \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (auto intro!: real_sqrt_ge_zero)

lemma real_sqrt_sum_squares_mult_ge_zero [simp]: "0 \<le> sqrt ((x\<twosuperior> + y\<twosuperior>)*(xa\<twosuperior> + ya\<twosuperior>))"
by (auto intro!: real_sqrt_ge_zero simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_mult_squared_eq [simp]:
     "sqrt ((x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)) ^ 2 = (x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)"
by (auto simp add: real_sqrt_pow2_iff zero_le_mult_iff simp del: realpow_Suc)

lemma real_sqrt_abs [simp]: "sqrt(x\<twosuperior>) = \<bar>x\<bar>"
apply (rule abs_realpow_two [THEN subst])
apply (rule real_sqrt_abs_abs [THEN subst])
apply (subst real_pow_sqrt_eq_sqrt_pow)
apply (auto simp add: numeral_2_eq_2 abs_mult)
done

lemma real_sqrt_abs2 [simp]: "sqrt(x*x) = \<bar>x\<bar>"
apply (rule realpow_two [THEN subst])
apply (subst numeral_2_eq_2 [symmetric])
apply (rule real_sqrt_abs)
done

lemma real_sqrt_pow2_gt_zero: "0 < x ==> 0 < (sqrt x)\<twosuperior>"
by simp

lemma real_sqrt_not_eq_zero: "0 < x ==> sqrt x \<noteq> 0"
apply (frule real_sqrt_pow2_gt_zero)
apply (auto simp add: numeral_2_eq_2 order_less_irrefl)
done

lemma real_inv_sqrt_pow2: "0 < x ==> inverse (sqrt(x)) ^ 2 = inverse x"
by (cut_tac n1 = 2 and a1 = "sqrt x" in power_inverse [symmetric], auto)

lemma real_sqrt_eq_zero_cancel: "[| 0 \<le> x; sqrt(x) = 0|] ==> x = 0"
apply (drule real_le_imp_less_or_eq)
apply (auto dest: real_sqrt_not_eq_zero)
done

lemma real_sqrt_eq_zero_cancel_iff [simp]: "0 \<le> x ==> ((sqrt x = 0) = (x = 0))"
by (auto simp add: real_sqrt_eq_zero_cancel)

lemma real_sqrt_sum_squares_ge1 [simp]: "x \<le> sqrt(x\<twosuperior> + y\<twosuperior>)"
apply (subgoal_tac "x \<le> 0 | 0 \<le> x", safe)
apply (rule real_le_trans)
apply (auto simp del: realpow_Suc)
apply (rule_tac n = 1 in realpow_increasing)
apply (auto simp add: numeral_2_eq_2 [symmetric] simp del: realpow_Suc)
done

lemma real_sqrt_sum_squares_ge2 [simp]: "y \<le> sqrt(z\<twosuperior> + y\<twosuperior>)"
apply (simp (no_asm) add: real_add_commute del: realpow_Suc)
done

lemma real_sqrt_ge_one: "1 \<le> x ==> 1 \<le> sqrt x"
apply (rule_tac n = 1 in realpow_increasing)
apply (auto simp add: numeral_2_eq_2 [symmetric] real_sqrt_ge_zero simp 
            del: realpow_Suc)
done


subsection{*Exponential Function*}

lemma summable_exp: "summable (%n. inverse (real (fact n)) * x ^ n)"
apply (cut_tac 'a = real in zero_less_one [THEN dense], safe)
apply (cut_tac x = r in reals_Archimedean3, auto)
apply (drule_tac x = "\<bar>x\<bar>" in spec, safe)
apply (rule_tac N = n and c = r in ratio_test)
apply (auto simp add: abs_mult mult_assoc [symmetric] simp del: fact_Suc)
apply (rule mult_right_mono)
apply (rule_tac b1 = "\<bar>x\<bar>" in mult_commute [THEN ssubst])
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (auto simp add: abs_mult inverse_mult_distrib)
apply (auto simp add: mult_assoc [symmetric] abs_eqI2 positive_imp_inverse_positive)
apply (rule order_less_imp_le)
apply (rule_tac z1 = "real (Suc na) " in real_mult_less_iff1 [THEN iffD1])
apply (auto simp add: real_not_refl2 [THEN not_sym] mult_assoc abs_inverse)
apply (erule order_less_trans)
apply (auto simp add: mult_less_cancel_left mult_ac)
done


lemma summable_sin: 
     "summable (%n.  
           (if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                x ^ n)"
apply (unfold real_divide_def)
apply (rule_tac g = " (%n. inverse (real (fact n)) * \<bar>x\<bar> ^ n) " in summable_comparison_test)
apply (rule_tac [2] summable_exp)
apply (rule_tac x = 0 in exI)
apply (auto simp add: power_abs [symmetric] abs_mult zero_le_mult_iff)
done

lemma summable_cos: 
      "summable (%n.  
           (if even n then  
           (- 1) ^ (n div 2)/(real (fact n)) else 0) * x ^ n)"
apply (unfold real_divide_def)
apply (rule_tac g = " (%n. inverse (real (fact n)) * \<bar>x\<bar> ^ n) " in summable_comparison_test)
apply (rule_tac [2] summable_exp)
apply (rule_tac x = 0 in exI)
apply (auto simp add: power_abs [symmetric] abs_mult zero_le_mult_iff)
done

lemma lemma_STAR_sin [simp]: "(if even n then 0  
       else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * 0 ^ n = 0"
apply (induct_tac "n", auto)
done

lemma lemma_STAR_cos [simp]: "0 < n -->  
      (- 1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0"
apply (induct_tac "n", auto)
done

lemma lemma_STAR_cos1 [simp]: "0 < n -->  
      (-1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0"
apply (induct_tac "n", auto)
done

lemma lemma_STAR_cos2 [simp]: "sumr 1 n (%n. if even n  
                    then (- 1) ^ (n div 2)/(real (fact n)) *  
                          0 ^ n  
                    else 0) = 0"
apply (induct_tac "n")
apply (case_tac [2] "n", auto)
done

lemma exp_converges: "(%n. inverse (real (fact n)) * x ^ n) sums exp(x)"
apply (unfold exp_def)
apply (rule summable_exp [THEN summable_sums])
done

lemma sin_converges: 
      "(%n. (if even n then 0  
            else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                 x ^ n) sums sin(x)"
apply (unfold sin_def)
apply (rule summable_sin [THEN summable_sums])
done

lemma cos_converges: 
      "(%n. (if even n then  
           (- 1) ^ (n div 2)/(real (fact n))  
           else 0) * x ^ n) sums cos(x)"
apply (unfold cos_def)
apply (rule summable_cos [THEN summable_sums])
done

lemma lemma_realpow_diff [rule_format (no_asm)]: "p \<le> n --> y ^ (Suc n - p) = ((y::real) ^ (n - p)) * y"
apply (induct_tac "n", auto)
apply (subgoal_tac "p = Suc n")
apply (simp (no_asm_simp), auto)
apply (drule sym)
apply (simp add: Suc_diff_le mult_commute realpow_Suc [symmetric] 
       del: realpow_Suc)
done


subsection{*Properties of Power Series*}

lemma lemma_realpow_diff_sumr:
     "sumr 0 (Suc n) (%p. (x ^ p) * y ^ ((Suc n) - p)) =  
      y * sumr 0 (Suc n) (%p. (x ^ p) * (y ^ (n - p)))"
apply (auto simp add: sumr_mult simp del: sumr_Suc)
apply (rule sumr_subst)
apply (intro strip)
apply (subst lemma_realpow_diff)
apply (auto simp add: mult_ac)
done

lemma lemma_realpow_diff_sumr2: "x ^ (Suc n) - y ^ (Suc n) =  
      (x - y) * sumr 0 (Suc n) (%p. (x ^ p) * (y ^(n - p)))"
apply (induct_tac "n", simp)
apply (auto simp del: sumr_Suc)
apply (subst sumr_Suc)
apply (drule sym)
apply (auto simp add: lemma_realpow_diff_sumr right_distrib real_diff_def mult_ac simp del: sumr_Suc)
done

lemma lemma_realpow_rev_sumr: "sumr 0 (Suc n) (%p. (x ^ p) * (y ^ (n - p))) =  
      sumr 0 (Suc n) (%p. (x ^ (n - p)) * (y ^ p))"
apply (case_tac "x = y")
apply (auto simp add: mult_commute power_add [symmetric] simp del: sumr_Suc)
apply (rule_tac c1 = "x - y" in real_mult_left_cancel [THEN iffD1])
apply (rule_tac [2] minus_minus [THEN subst], simp)
apply (subst minus_mult_left)
apply (simp add: lemma_realpow_diff_sumr2 [symmetric] del: sumr_Suc)
done

text{*Power series has a `circle` of convergence, i.e. if it sums for @{term
x}, then it sums absolutely for @{term z} with @{term "\<bar>z\<bar> < \<bar>x\<bar>"}.*}

lemma powser_insidea:
     "[| summable (%n. f(n) * (x ^ n)); \<bar>z\<bar> < \<bar>x\<bar> |]  
      ==> summable (%n. \<bar>f(n)\<bar> * (z ^ n))"
apply (drule summable_LIMSEQ_zero)
apply (drule convergentI)
apply (simp add: Cauchy_convergent_iff [symmetric])
apply (drule Cauchy_Bseq)
apply (simp add: Bseq_def, safe)
apply (rule_tac g = "%n. K * \<bar>z ^ n\<bar> * inverse (\<bar>x ^ n\<bar>)" in summable_comparison_test)
apply (rule_tac x = 0 in exI, safe)
apply (subgoal_tac "0 < \<bar>x ^ n\<bar> ")
apply (rule_tac c="\<bar>x ^ n\<bar>" in mult_right_le_imp_le) 
apply (auto simp add: mult_assoc power_abs)
 prefer 2
 apply (drule_tac x = 0 in spec, force)
apply (auto simp add: abs_mult power_abs mult_ac)
apply (rule_tac a2 = "z ^ n" 
       in abs_ge_zero [THEN real_le_imp_less_or_eq, THEN disjE])
apply (auto intro!: mult_right_mono simp add: mult_assoc [symmetric] power_abs summable_def power_0_left)
apply (rule_tac x = "K * inverse (1 - (\<bar>z\<bar> * inverse (\<bar>x\<bar>))) " in exI)
apply (auto intro!: sums_mult simp add: mult_assoc)
apply (subgoal_tac "\<bar>z ^ n\<bar> * inverse (\<bar>x\<bar> ^ n) = (\<bar>z\<bar> * inverse (\<bar>x\<bar>)) ^ n")
apply (auto simp add: power_abs [symmetric])
apply (subgoal_tac "x \<noteq> 0")
apply (subgoal_tac [3] "x \<noteq> 0")
apply (auto simp del: abs_inverse abs_mult simp add: abs_inverse [symmetric] realpow_not_zero abs_mult [symmetric] power_inverse power_mult_distrib [symmetric])
apply (auto intro!: geometric_sums simp add: power_abs inverse_eq_divide)
apply (rule_tac c="\<bar>x\<bar>" in mult_right_less_imp_less) 
apply (auto simp add: abs_mult [symmetric] mult_assoc)
done

lemma powser_inside: "[| summable (%n. f(n) * (x ^ n)); \<bar>z\<bar> < \<bar>x\<bar> |]  
      ==> summable (%n. f(n) * (z ^ n))"
apply (drule_tac z = "\<bar>z\<bar>" in powser_insidea)
apply (auto intro: summable_rabs_cancel simp add: power_abs [symmetric])
done


subsection{*Differentiation of Power Series*}

text{*Lemma about distributing negation over it*}
lemma diffs_minus: "diffs (%n. - c n) = (%n. - diffs c n)"
by (simp add: diffs_def)

text{*Show that we can shift the terms down one*}
lemma lemma_diffs:
     "sumr 0 n (%n. (diffs c)(n) * (x ^ n)) =  
      sumr 0 n (%n. real n * c(n) * (x ^ (n - Suc 0))) +  
      (real n * c(n) * x ^ (n - Suc 0))"
apply (induct_tac "n")
apply (auto simp add: mult_assoc add_assoc [symmetric] diffs_def)
done

lemma lemma_diffs2: "sumr 0 n (%n. real n * c(n) * (x ^ (n - Suc 0))) =  
      sumr 0 n (%n. (diffs c)(n) * (x ^ n)) -  
      (real n * c(n) * x ^ (n - Suc 0))"
by (auto simp add: lemma_diffs)


lemma diffs_equiv: "summable (%n. (diffs c)(n) * (x ^ n)) ==>  
      (%n. real n * c(n) * (x ^ (n - Suc 0))) sums  
         (suminf(%n. (diffs c)(n) * (x ^ n)))"
apply (subgoal_tac " (%n. real n * c (n) * (x ^ (n - Suc 0))) ----> 0")
apply (rule_tac [2] LIMSEQ_imp_Suc)
apply (drule summable_sums) 
apply (auto simp add: sums_def)
apply (drule_tac X="(\<lambda>n. \<Sum>n = 0..<n. diffs c n * x ^ n)" in LIMSEQ_diff)
apply (auto simp add: lemma_diffs2 [symmetric] diffs_def [symmetric])
apply (simp add: diffs_def summable_LIMSEQ_zero)
done


subsection{*Term-by-Term Differentiability of Power Series*}

lemma lemma_termdiff1:
     "sumr 0 m (%p. (((z + h) ^ (m - p)) * (z ^ p)) - (z ^ m)) =  
        sumr 0 m (%p. (z ^ p) *  
        (((z + h) ^ (m - p)) - (z ^ (m - p))))"
apply (rule sumr_subst)
apply (auto simp add: right_distrib real_diff_def power_add [symmetric] mult_ac)
done

lemma less_add_one: "m < n ==> (\<exists>d. n = m + d + Suc 0)"
by (simp add: less_iff_Suc_add)

lemma sumdiff: "a + b - (c + d) = a - c + b - (d::real)"
by arith


lemma lemma_termdiff2: " h \<noteq> 0 ==>  
        (((z + h) ^ n) - (z ^ n)) * inverse h -  
            real n * (z ^ (n - Suc 0)) =  
         h * sumr 0 (n - Suc 0) (%p. (z ^ p) *  
               sumr 0 ((n - Suc 0) - p)  
                 (%q. ((z + h) ^ q) * (z ^ (((n - 2) - p) - q))))"
apply (rule real_mult_left_cancel [THEN iffD1], simp (no_asm_simp))
apply (simp add: right_diff_distrib mult_ac)
apply (simp add: mult_assoc [symmetric])
apply (case_tac "n")
apply (auto simp add: lemma_realpow_diff_sumr2 
                      right_diff_distrib [symmetric] mult_assoc
            simp del: realpow_Suc sumr_Suc)
apply (auto simp add: lemma_realpow_rev_sumr simp del: sumr_Suc)
apply (auto simp add: real_of_nat_Suc sumr_diff_mult_const left_distrib 
                sumdiff lemma_termdiff1 sumr_mult)
apply (auto intro!: sumr_subst simp add: real_diff_def real_add_assoc)
apply (simp add: diff_minus [symmetric] less_iff_Suc_add) 
apply (auto simp add: sumr_mult lemma_realpow_diff_sumr2 mult_ac simp
                 del: sumr_Suc realpow_Suc)
done

lemma lemma_termdiff3: "[| h \<noteq> 0; \<bar>z\<bar> \<le> K; \<bar>z + h\<bar> \<le> K |]  
      ==> abs (((z + h) ^ n - z ^ n) * inverse h - real n * z ^ (n - Suc 0))  
          \<le> real n * real (n - Suc 0) * K ^ (n - 2) * \<bar>h\<bar>"
apply (subst lemma_termdiff2, assumption)
apply (simp add: abs_mult mult_commute) 
apply (simp add: mult_commute [of _ "K ^ (n - 2)"]) 
apply (rule sumr_rabs [THEN real_le_trans])
apply (simp add: mult_assoc [symmetric])
apply (simp add: mult_commute [of _ "real (n - Suc 0)"])
apply (auto intro!: sumr_bound2 simp add: abs_mult)
apply (case_tac "n", auto)
apply (drule less_add_one)
(*CLAIM_SIMP " (a * b * c = a * (c * (b::real))" mult_ac]*)
apply clarify 
apply (subgoal_tac "K ^ p * K ^ d * real (Suc (Suc (p + d))) =
                    K ^ p * (real (Suc (Suc (p + d))) * K ^ d)") 
apply (simp (no_asm_simp) add: power_add del: sumr_Suc)
apply (auto intro!: mult_mono simp del: sumr_Suc)
apply (auto intro!: power_mono simp add: power_abs simp del: sumr_Suc)
apply (rule_tac j = "real (Suc d) * (K ^ d) " in real_le_trans)
apply (subgoal_tac [2] "0 \<le> K")
apply (drule_tac [2] n = d in zero_le_power)
apply (auto simp del: sumr_Suc)
apply (rule sumr_rabs [THEN real_le_trans])
apply (rule sumr_bound2, auto dest!: less_add_one intro!: mult_mono simp add: abs_mult power_add)
apply (auto intro!: power_mono zero_le_power simp add: power_abs, arith+)
done

lemma lemma_termdiff4: 
  "[| 0 < k;  
      (\<forall>h. 0 < \<bar>h\<bar> & \<bar>h\<bar> < k --> \<bar>f h\<bar> \<le> K * \<bar>h\<bar>) |]  
   ==> f -- 0 --> 0"
apply (unfold LIM_def, auto)
apply (subgoal_tac "0 \<le> K")
apply (drule_tac [2] x = "k/2" in spec)
apply (frule_tac [2] real_less_half_sum)
apply (drule_tac [2] real_gt_half_sum)
apply (auto simp add: abs_eqI2)
apply (rule_tac [2] c = "k/2" in mult_right_le_imp_le)
apply (auto intro: abs_ge_zero [THEN real_le_trans])
apply (drule real_le_imp_less_or_eq, auto)
apply (subgoal_tac "0 < (r * inverse K) * inverse 2")
apply (rule_tac [2] real_mult_order)+
apply (drule_tac ?d1.0 = "r * inverse K * inverse 2" and ?d2.0 = k in real_lbound_gt_zero)
apply (auto simp add: positive_imp_inverse_positive zero_less_mult_iff)
apply (rule_tac [2] y="\<bar>f (k / 2)\<bar> * 2" in order_trans, auto)
apply (rule_tac x = e in exI, auto)
apply (rule_tac y = "K * \<bar>x\<bar>" in order_le_less_trans)
apply (rule_tac [2] y = "K * e" in order_less_trans)
apply (rule_tac [3] c = "inverse K" in mult_right_less_imp_less, force)
apply (simp add: mult_less_cancel_left)
apply (auto simp add: mult_ac)
done

lemma lemma_termdiff5: "[| 0 < k;  
            summable f;  
            \<forall>h. 0 < \<bar>h\<bar> & \<bar>h\<bar> < k -->  
                    (\<forall>n. abs(g(h) (n::nat)) \<le> (f(n) * \<bar>h\<bar>)) |]  
         ==> (%h. suminf(g h)) -- 0 --> 0"
apply (drule summable_sums)
apply (subgoal_tac "\<forall>h. 0 < \<bar>h\<bar> & \<bar>h\<bar> < k --> \<bar>suminf (g h)\<bar> \<le> suminf f * \<bar>h\<bar>")
apply (auto intro!: lemma_termdiff4 simp add: sums_summable [THEN suminf_mult, symmetric])
apply (subgoal_tac "summable (%n. f n * \<bar>h\<bar>) ")
 prefer 2
 apply (simp add: summable_def) 
 apply (rule_tac x = "suminf f * \<bar>h\<bar>" in exI)
 apply (drule_tac c = "\<bar>h\<bar>" in sums_mult)
 apply (simp add: mult_ac) 
apply (subgoal_tac "summable (%n. abs (g (h::real) (n::nat))) ")
 apply (rule_tac [2] g = "%n. f n * \<bar>h\<bar>" in summable_comparison_test)
  apply (rule_tac [2] x = 0 in exI, auto)
apply (rule_tac j = "suminf (%n. \<bar>g h n\<bar>)" in real_le_trans)
apply (auto intro: summable_rabs summable_le simp add: sums_summable [THEN suminf_mult])
done



text{* FIXME: Long proofs*}

lemma termdiffs_aux:
     "[|summable (\<lambda>n. diffs (diffs c) n * K ^ n); \<bar>x\<bar> < \<bar>K\<bar> |]
    ==> (\<lambda>h. suminf
             (\<lambda>n. c n *
                  (((x + h) ^ n - x ^ n) * inverse h -
                   real n * x ^ (n - Suc 0))))
       -- 0 --> 0"
apply (drule dense, safe)
apply (frule real_less_sum_gt_zero)
apply (drule_tac
         f = "%n. \<bar>c n\<bar> * real n * real (n - Suc 0) * (r ^ (n - 2))" 
     and g = "%h n. c (n) * ((( ((x + h) ^ n) - (x ^ n)) * inverse h) 
                             - (real n * (x ^ (n - Suc 0))))" 
       in lemma_termdiff5)
apply (auto simp add: add_commute)
apply (subgoal_tac "summable (%n. \<bar>diffs (diffs c) n\<bar> * (r ^ n))")
apply (rule_tac [2] x = K in powser_insidea, auto)
apply (subgoal_tac [2] "\<bar>r\<bar> = r", auto)
apply (rule_tac [2] y1 = "\<bar>x\<bar>" in order_trans [THEN abs_eqI1], auto)
apply (simp add: diffs_def mult_assoc [symmetric])
apply (subgoal_tac
        "\<forall>n. real (Suc n) * real (Suc (Suc n)) * \<bar>c (Suc (Suc n))\<bar> * (r ^ n) 
              = diffs (diffs (%n. \<bar>c n\<bar>)) n * (r ^ n) ") 
apply auto
apply (drule diffs_equiv)
apply (drule sums_summable)
apply (simp_all add: diffs_def) 
apply (simp add: diffs_def mult_ac)
apply (subgoal_tac " (%n. real n * (real (Suc n) * (\<bar>c (Suc n)\<bar> * (r ^ (n - Suc 0))))) = (%n. diffs (%m. real (m - Suc 0) * \<bar>c m\<bar> * inverse r) n * (r ^ n))")
apply auto
  prefer 2
  apply (rule ext)
  apply (simp add: diffs_def) 
  apply (case_tac "n", auto)
txt{*23*}
   apply (drule abs_ge_zero [THEN order_le_less_trans])
   apply (simp add: mult_ac) 
  apply (drule abs_ge_zero [THEN order_le_less_trans])
  apply (simp add: mult_ac) 
 apply (drule diffs_equiv)
 apply (drule sums_summable)
apply (subgoal_tac
          "summable
            (\<lambda>n. real n * (real (n - Suc 0) * \<bar>c n\<bar> * inverse r) *
                 r ^ (n - Suc 0)) =
           summable
            (\<lambda>n. real n * (\<bar>c n\<bar> * (real (n - Suc 0) * r ^ (n - 2))))")
apply simp 
apply (rule_tac f = summable in arg_cong, rule ext)
txt{*33*}
apply (case_tac "n", auto)
apply (case_tac "nat", auto)
apply (drule abs_ge_zero [THEN order_le_less_trans], auto) 
apply (drule abs_ge_zero [THEN order_le_less_trans])
apply (simp add: mult_assoc)
apply (rule mult_left_mono)
apply (rule add_commute [THEN subst])
apply (simp (no_asm) add: mult_assoc [symmetric])
apply (rule lemma_termdiff3)
apply (auto intro: abs_triangle_ineq [THEN order_trans], arith)
done


lemma termdiffs: 
    "[| summable(%n. c(n) * (K ^ n));  
        summable(%n. (diffs c)(n) * (K ^ n));  
        summable(%n. (diffs(diffs c))(n) * (K ^ n));  
        \<bar>x\<bar> < \<bar>K\<bar> |]  
     ==> DERIV (%x. suminf (%n. c(n) * (x ^ n)))  x :>  
             suminf (%n. (diffs c)(n) * (x ^ n))"
apply (unfold deriv_def)
apply (rule_tac g = "%h. suminf (%n. ((c (n) * ( (x + h) ^ n)) - (c (n) * (x ^ n))) * inverse h) " in LIM_trans)
apply (simp add: LIM_def, safe)
apply (rule_tac x = "\<bar>K\<bar> - \<bar>x\<bar>" in exI)
apply (auto simp add: less_diff_eq)
apply (drule abs_triangle_ineq [THEN order_le_less_trans])
apply (rule_tac y = 0 in order_le_less_trans, auto)
apply (subgoal_tac " (%n. (c n) * (x ^ n)) sums (suminf (%n. (c n) * (x ^ n))) & (%n. (c n) * ((x + xa) ^ n)) sums (suminf (%n. (c n) * ( (x + xa) ^ n))) ")
apply (auto intro!: summable_sums)
apply (rule_tac [2] powser_inside, rule_tac [4] powser_inside)
apply (auto simp add: add_commute)
apply (drule_tac x="(\<lambda>n. c n * (xa + x) ^ n)" in sums_diff, assumption) 
apply (drule_tac x = " (%n. c n * (xa + x) ^ n - c n * x ^ n) " and c = "inverse xa" in sums_mult)
apply (rule sums_unique)
apply (simp add: diff_def divide_inverse add_ac mult_ac)
apply (rule LIM_zero_cancel)
apply (rule_tac g = "%h. suminf (%n. c (n) * ((( ((x + h) ^ n) - (x ^ n)) * inverse h) - (real n * (x ^ (n - Suc 0))))) " in LIM_trans)
 prefer 2 apply (blast intro: termdiffs_aux) 
apply (simp add: LIM_def, safe)
apply (rule_tac x = "\<bar>K\<bar> - \<bar>x\<bar>" in exI)
apply (auto simp add: less_diff_eq)
apply (drule abs_triangle_ineq [THEN order_le_less_trans])
apply (rule_tac y = 0 in order_le_less_trans, auto)
apply (subgoal_tac "summable (%n. (diffs c) (n) * (x ^ n))")
apply (rule_tac [2] powser_inside, auto)
apply (drule_tac c = c and x = x in diffs_equiv)
apply (frule sums_unique, auto)
apply (subgoal_tac " (%n. (c n) * (x ^ n)) sums (suminf (%n. (c n) * (x ^ n))) & (%n. (c n) * ((x + xa) ^ n)) sums (suminf (%n. (c n) * ( (x + xa) ^ n))) ")
apply safe
apply (auto intro!: summable_sums)
apply (rule_tac [2] powser_inside, rule_tac [4] powser_inside)
apply (auto simp add: add_commute)
apply (frule_tac x = " (%n. c n * (xa + x) ^ n) " and y = " (%n. c n * x ^ n) " in sums_diff, assumption)
apply (simp add: suminf_diff [OF sums_summable sums_summable] 
               right_diff_distrib [symmetric])
apply (frule_tac x = " (%n. c n * ((xa + x) ^ n - x ^ n))" and c = "inverse xa" in sums_mult)
apply (simp add: sums_summable [THEN suminf_mult2])
apply (frule_tac x = " (%n. inverse xa * (c n * ((xa + x) ^ n - x ^ n))) " and y = " (%n. real n * c n * x ^ (n - Suc 0))" in sums_diff)
apply assumption
apply (simp add: suminf_diff [OF sums_summable sums_summable] add_ac mult_ac)
apply (rule_tac f = suminf in arg_cong)
apply (rule ext)
apply (simp add: diff_def right_distrib add_ac mult_ac)
done


subsection{*Formal Derivatives of Exp, Sin, and Cos Series*} 

lemma exp_fdiffs: 
      "diffs (%n. inverse(real (fact n))) = (%n. inverse(real (fact n)))"
apply (unfold diffs_def)
apply (rule ext)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (subst inverse_mult_distrib)
apply (auto simp add: mult_assoc [symmetric])
done

lemma sin_fdiffs: 
      "diffs(%n. if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n)))  
       = (%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n))  
              else 0)"
apply (unfold diffs_def real_divide_def)
apply (rule ext)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (subst even_nat_Suc)
apply (subst inverse_mult_distrib, auto)
done

lemma sin_fdiffs2: 
       "diffs(%n. if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) n  
       = (if even n then  
                 (- 1) ^ (n div 2)/(real (fact n))  
              else 0)"
apply (unfold diffs_def real_divide_def)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (subst even_nat_Suc)
apply (subst inverse_mult_distrib, auto)
done

lemma cos_fdiffs: 
      "diffs(%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n)) else 0)  
       = (%n. - (if even n then 0  
           else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n))))"
apply (unfold diffs_def real_divide_def)
apply (rule ext)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (auto simp add: mult_assoc odd_Suc_mult_two_ex)
done


lemma cos_fdiffs2: 
      "diffs(%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n)) else 0) n 
       = - (if even n then 0  
           else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n)))"
apply (unfold diffs_def real_divide_def)
apply (subst fact_Suc)
apply (subst real_of_nat_mult) 
apply (auto simp add: mult_assoc odd_Suc_mult_two_ex)
done

text{*Now at last we can get the derivatives of exp, sin and cos*}

lemma lemma_sin_minus:
     "- sin x =
         suminf(%n. - ((if even n then 0 
                  else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * x ^ n))"
by (auto intro!: sums_unique sums_minus sin_converges)

lemma lemma_exp_ext: "exp = (%x. suminf (%n. inverse (real (fact n)) * x ^ n))"
by (auto intro!: ext simp add: exp_def)

lemma DERIV_exp [simp]: "DERIV exp x :> exp(x)"
apply (unfold exp_def)
apply (subst lemma_exp_ext)
apply (subgoal_tac "DERIV (%u. suminf (%n. inverse (real (fact n)) * u ^ n)) x :> suminf (%n. diffs (%n. inverse (real (fact n))) n * x ^ n) ")
apply (rule_tac [2] K = "1 + \<bar>x\<bar> " in termdiffs)
apply (auto intro: exp_converges [THEN sums_summable] simp add: exp_fdiffs, arith)
done

lemma lemma_sin_ext:
     "sin = (%x. suminf(%n. 
                   (if even n then 0  
                       else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                   x ^ n))"
by (auto intro!: ext simp add: sin_def)

lemma lemma_cos_ext:
     "cos = (%x. suminf(%n. 
                   (if even n then (- 1) ^ (n div 2)/(real (fact n)) else 0) *
                   x ^ n))"
by (auto intro!: ext simp add: cos_def)

lemma DERIV_sin [simp]: "DERIV sin x :> cos(x)"
apply (unfold cos_def)
apply (subst lemma_sin_ext)
apply (auto simp add: sin_fdiffs2 [symmetric])
apply (rule_tac K = "1 + \<bar>x\<bar> " in termdiffs)
apply (auto intro: sin_converges cos_converges sums_summable intro!: sums_minus [THEN sums_summable] simp add: cos_fdiffs sin_fdiffs, arith)
done

lemma DERIV_cos [simp]: "DERIV cos x :> -sin(x)"
apply (subst lemma_cos_ext)
apply (auto simp add: lemma_sin_minus cos_fdiffs2 [symmetric] minus_mult_left)
apply (rule_tac K = "1 + \<bar>x\<bar> " in termdiffs)
apply (auto intro: sin_converges cos_converges sums_summable intro!: sums_minus [THEN sums_summable] simp add: cos_fdiffs sin_fdiffs diffs_minus, arith)
done


subsection{*Properties of the Exponential Function*}

lemma exp_zero [simp]: "exp 0 = 1"
proof -
  have "(\<Sum>n = 0..<1. inverse (real (fact n)) * 0 ^ n) =
        suminf (\<lambda>n. inverse (real (fact n)) * 0 ^ n)"
    by (rule series_zero [rule_format, THEN sums_unique],
        case_tac "m", auto)
  thus ?thesis by (simp add:  exp_def) 
qed

lemma exp_ge_add_one_self [simp]: "0 \<le> x ==> (1 + x) \<le> exp(x)"
apply (drule real_le_imp_less_or_eq, auto)
apply (unfold exp_def)
apply (rule real_le_trans)
apply (rule_tac [2] n = 2 and f = " (%n. inverse (real (fact n)) * x ^ n) " in series_pos_le)
apply (auto intro: summable_exp simp add: numeral_2_eq_2 zero_le_power zero_le_mult_iff)
done

lemma exp_gt_one [simp]: "0 < x ==> 1 < exp x"
apply (rule order_less_le_trans)
apply (rule_tac [2] exp_ge_add_one_self, auto)
done

lemma DERIV_exp_add_const: "DERIV (%x. exp (x + y)) x :> exp(x + y)"
proof -
  have "DERIV (exp \<circ> (\<lambda>x. x + y)) x :> exp (x + y) * (1+0)"
    by (fast intro: DERIV_chain DERIV_add DERIV_exp DERIV_Id DERIV_const) 
  thus ?thesis by (simp add: o_def)
qed

lemma DERIV_exp_minus [simp]: "DERIV (%x. exp (-x)) x :> - exp(-x)"
proof -
  have "DERIV (exp \<circ> uminus) x :> exp (- x) * - 1"
    by (fast intro: DERIV_chain DERIV_minus DERIV_exp DERIV_Id) 
  thus ?thesis by (simp add: o_def)
qed

lemma DERIV_exp_exp_zero [simp]: "DERIV (%x. exp (x + y) * exp (- x)) x :> 0"
proof -
  have "DERIV (\<lambda>x. exp (x + y) * exp (- x)) x
       :> exp (x + y) * exp (- x) + - exp (- x) * exp (x + y)"
    by (fast intro: DERIV_exp_add_const DERIV_exp_minus DERIV_mult) 
  thus ?thesis by simp
qed

lemma exp_add_mult_minus [simp]: "exp(x + y)*exp(-x) = exp(y)"
proof -
  have "\<forall>x. DERIV (%x. exp (x + y) * exp (- x)) x :> 0" by simp
  hence "exp (x + y) * exp (- x) = exp (0 + y) * exp (- 0)" 
    by (rule DERIV_isconst_all) 
  thus ?thesis by simp
qed

lemma exp_mult_minus [simp]: "exp x * exp(-x) = 1"
proof -
  have "exp (x + 0) * exp (- x) = exp 0" by (rule exp_add_mult_minus) 
  thus ?thesis by simp
qed

lemma exp_mult_minus2 [simp]: "exp(-x)*exp(x) = 1"
by (simp add: mult_commute)


lemma exp_minus: "exp(-x) = inverse(exp(x))"
by (auto intro: inverse_unique [symmetric])

lemma exp_add: "exp(x + y) = exp(x) * exp(y)"
proof -
  have "exp x * exp y = exp x * (exp (x + y) * exp (- x))" by simp
  thus ?thesis by (simp (no_asm_simp) add: mult_ac)
qed

text{*Proof: because every exponential can be seen as a square.*}
lemma exp_ge_zero [simp]: "0 \<le> exp x"
apply (rule_tac t = x in real_sum_of_halves [THEN subst])
apply (subst exp_add, auto)
done

lemma exp_not_eq_zero [simp]: "exp x \<noteq> 0"
apply (cut_tac x = x in exp_mult_minus2)
apply (auto simp del: exp_mult_minus2)
done

lemma exp_gt_zero [simp]: "0 < exp x"
by (simp add: order_less_le)

lemma inv_exp_gt_zero [simp]: "0 < inverse(exp x)"
by (auto intro: positive_imp_inverse_positive)

lemma abs_exp_cancel [simp]: "\<bar>exp x\<bar> = exp x"
by (auto simp add: abs_eqI2)

lemma exp_real_of_nat_mult: "exp(real n * x) = exp(x) ^ n"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc right_distrib exp_add mult_commute)
done

lemma exp_diff: "exp(x - y) = exp(x)/(exp y)"
apply (unfold real_diff_def real_divide_def)
apply (simp (no_asm) add: exp_add exp_minus)
done


lemma exp_less_mono:
  assumes xy: "x < y" shows "exp x < exp y"
proof -
  have "1 < exp (y + - x)"
    by (rule real_less_sum_gt_zero [THEN exp_gt_one])
  hence "exp x * inverse (exp x) < exp y * inverse (exp x)"
    by (auto simp add: exp_add exp_minus)
  thus ?thesis
    by (simp add: divide_inverse [symmetric] pos_less_divide_eq)
qed

lemma exp_less_cancel: "exp x < exp y ==> x < y"
apply (rule ccontr) 
apply (simp add: linorder_not_less order_le_less) 
apply (auto dest: exp_less_mono)
done

lemma exp_less_cancel_iff [iff]: "(exp(x) < exp(y)) = (x < y)"
by (auto intro: exp_less_mono exp_less_cancel)

lemma exp_le_cancel_iff [iff]: "(exp(x) \<le> exp(y)) = (x \<le> y)"
by (auto simp add: linorder_not_less [symmetric])

lemma exp_inj_iff [iff]: "(exp x = exp y) = (x = y)"
by (simp add: order_eq_iff)

lemma lemma_exp_total: "1 \<le> y ==> \<exists>x. 0 \<le> x & x \<le> y - 1 & exp(x) = y"
apply (rule IVT)
apply (auto intro: DERIV_exp [THEN DERIV_isCont] simp add: le_diff_eq)
apply (subgoal_tac "1 + (y - 1) \<le> exp (y - 1)") 
apply simp 
apply (rule exp_ge_add_one_self, simp)
done

lemma exp_total: "0 < y ==> \<exists>x. exp x = y"
apply (rule_tac x = 1 and y = y in linorder_cases)
apply (drule order_less_imp_le [THEN lemma_exp_total])
apply (rule_tac [2] x = 0 in exI)
apply (frule_tac [3] real_inverse_gt_one)
apply (drule_tac [4] order_less_imp_le [THEN lemma_exp_total], auto)
apply (rule_tac x = "-x" in exI)
apply (simp add: exp_minus)
done


subsection{*Properties of the Logarithmic Function*}

lemma ln_exp[simp]: "ln(exp x) = x"
by (simp add: ln_def)

lemma exp_ln_iff[simp]: "(exp(ln x) = x) = (0 < x)"
apply (auto dest: exp_total)
apply (erule subst, simp) 
done

lemma ln_mult: "[| 0 < x; 0 < y |] ==> ln(x * y) = ln(x) + ln(y)"
apply (rule exp_inj_iff [THEN iffD1])
apply (frule real_mult_order)
apply (auto simp add: exp_add exp_ln_iff [symmetric] simp del: exp_inj_iff exp_ln_iff)
done

lemma ln_inj_iff[simp]: "[| 0 < x; 0 < y |] ==> (ln x = ln y) = (x = y)"
apply (simp only: exp_ln_iff [symmetric])
apply (erule subst)+
apply simp 
done

lemma ln_one[simp]: "ln 1 = 0"
by (rule exp_inj_iff [THEN iffD1], auto)

lemma ln_inverse: "0 < x ==> ln(inverse x) = - ln x"
apply (rule_tac a1 = "ln x" in add_left_cancel [THEN iffD1])
apply (auto simp add: positive_imp_inverse_positive ln_mult [symmetric])
done

lemma ln_div: 
    "[|0 < x; 0 < y|] ==> ln(x/y) = ln x - ln y"
apply (unfold real_divide_def)
apply (auto simp add: positive_imp_inverse_positive ln_mult ln_inverse)
done

lemma ln_less_cancel_iff[simp]: "[| 0 < x; 0 < y|] ==> (ln x < ln y) = (x < y)"
apply (simp only: exp_ln_iff [symmetric])
apply (erule subst)+
apply simp 
done

lemma ln_le_cancel_iff[simp]: "[| 0 < x; 0 < y|] ==> (ln x \<le> ln y) = (x \<le> y)"
by (auto simp add: linorder_not_less [symmetric])

lemma ln_realpow: "0 < x ==> ln(x ^ n) = real n * ln(x)"
by (auto dest!: exp_total simp add: exp_real_of_nat_mult [symmetric])

lemma ln_add_one_self_le_self [simp]: "0 \<le> x ==> ln(1 + x) \<le> x"
apply (rule ln_exp [THEN subst])
apply (rule ln_le_cancel_iff [THEN iffD2], auto)
done

lemma ln_less_self [simp]: "0 < x ==> ln x < x"
apply (rule order_less_le_trans)
apply (rule_tac [2] ln_add_one_self_le_self)
apply (rule ln_less_cancel_iff [THEN iffD2], auto)
done

lemma ln_ge_zero:
  assumes x: "1 \<le> x" shows "0 \<le> ln x"
proof -
  have "0 < x" using x by arith
  hence "exp 0 \<le> exp (ln x)"
    by (simp add: x exp_ln_iff [symmetric] del: exp_ln_iff)
  thus ?thesis by (simp only: exp_le_cancel_iff)
qed

lemma ln_ge_zero_imp_ge_one:
  assumes ln: "0 \<le> ln x" 
      and x:  "0 < x"
  shows "1 \<le> x"
proof -
  from ln have "ln 1 \<le> ln x" by simp
  thus ?thesis by (simp add: x del: ln_one) 
qed

lemma ln_ge_zero_iff [simp]: "0 < x ==> (0 \<le> ln x) = (1 \<le> x)"
by (blast intro: ln_ge_zero ln_ge_zero_imp_ge_one)

lemma ln_gt_zero:
  assumes x: "1 < x" shows "0 < ln x"
proof -
  have "0 < x" using x by arith
  hence "exp 0 < exp (ln x)"
    by (simp add: x exp_ln_iff [symmetric] del: exp_ln_iff)
  thus ?thesis  by (simp only: exp_less_cancel_iff)
qed

lemma ln_gt_zero_imp_gt_one:
  assumes ln: "0 < ln x" 
      and x:  "0 < x"
  shows "1 < x"
proof -
  from ln have "ln 1 < ln x" by simp
  thus ?thesis by (simp add: x del: ln_one) 
qed

lemma ln_gt_zero_iff [simp]: "0 < x ==> (0 < ln x) = (1 < x)"
by (blast intro: ln_gt_zero ln_gt_zero_imp_gt_one)

lemma ln_not_eq_zero [simp]: "[| 0 < x; x \<noteq> 1 |] ==> ln x \<noteq> 0"
apply safe
apply (drule exp_inj_iff [THEN iffD2])
apply (drule exp_ln_iff [THEN iffD2], auto)
done

lemma ln_less_zero: "[| 0 < x; x < 1 |] ==> ln x < 0"
apply (rule exp_less_cancel_iff [THEN iffD1])
apply (auto simp add: exp_ln_iff [symmetric] simp del: exp_ln_iff)
done

lemma exp_ln_eq: "exp u = x ==> ln x = u"
by auto


subsection{*Basic Properties of the Trigonometric Functions*}

lemma sin_zero [simp]: "sin 0 = 0"
by (auto intro!: sums_unique [symmetric] LIMSEQ_const 
         simp add: sin_def sums_def simp del: power_0_left)

lemma lemma_series_zero2: "(\<forall>m. n \<le> m --> f m = 0) --> f sums sumr 0 n f"
by (auto intro: series_zero)

lemma cos_zero [simp]: "cos 0 = 1"
apply (unfold cos_def)
apply (rule sums_unique [symmetric])
apply (cut_tac n = 1 and f = " (%n. (if even n then (- 1) ^ (n div 2) / (real (fact n)) else 0) * 0 ^ n) " in lemma_series_zero2)
apply auto
done

lemma DERIV_sin_sin_mult [simp]:
     "DERIV (%x. sin(x)*sin(x)) x :> cos(x) * sin(x) + cos(x) * sin(x)"
by (rule DERIV_mult, auto)

lemma DERIV_sin_sin_mult2 [simp]:
     "DERIV (%x. sin(x)*sin(x)) x :> 2 * cos(x) * sin(x)"
apply (cut_tac x = x in DERIV_sin_sin_mult)
apply (auto simp add: mult_assoc)
done

lemma DERIV_sin_realpow2 [simp]:
     "DERIV (%x. (sin x)\<twosuperior>) x :> cos(x) * sin(x) + cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2 real_mult_assoc [symmetric])

lemma DERIV_sin_realpow2a [simp]:
     "DERIV (%x. (sin x)\<twosuperior>) x :> 2 * cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2)

lemma DERIV_cos_cos_mult [simp]:
     "DERIV (%x. cos(x)*cos(x)) x :> -sin(x) * cos(x) + -sin(x) * cos(x)"
by (rule DERIV_mult, auto)

lemma DERIV_cos_cos_mult2 [simp]:
     "DERIV (%x. cos(x)*cos(x)) x :> -2 * cos(x) * sin(x)"
apply (cut_tac x = x in DERIV_cos_cos_mult)
apply (auto simp add: mult_ac)
done

lemma DERIV_cos_realpow2 [simp]:
     "DERIV (%x. (cos x)\<twosuperior>) x :> -sin(x) * cos(x) + -sin(x) * cos(x)"
by (auto simp add: numeral_2_eq_2 real_mult_assoc [symmetric])

lemma DERIV_cos_realpow2a [simp]:
     "DERIV (%x. (cos x)\<twosuperior>) x :> -2 * cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2)

lemma lemma_DERIV_subst: "[| DERIV f x :> D; D = E |] ==> DERIV f x :> E"
by auto

lemma DERIV_cos_realpow2b: "DERIV (%x. (cos x)\<twosuperior>) x :> -(2 * cos(x) * sin(x))"
apply (rule lemma_DERIV_subst)
apply (rule DERIV_cos_realpow2a, auto)
done

(* most useful *)
lemma DERIV_cos_cos_mult3 [simp]: "DERIV (%x. cos(x)*cos(x)) x :> -(2 * cos(x) * sin(x))"
apply (rule lemma_DERIV_subst)
apply (rule DERIV_cos_cos_mult2, auto)
done

lemma DERIV_sin_circle_all: 
     "\<forall>x. DERIV (%x. (sin x)\<twosuperior> + (cos x)\<twosuperior>) x :>  
             (2*cos(x)*sin(x) - 2*cos(x)*sin(x))"
apply (unfold real_diff_def, safe)
apply (rule DERIV_add)
apply (auto simp add: numeral_2_eq_2)
done

lemma DERIV_sin_circle_all_zero [simp]: "\<forall>x. DERIV (%x. (sin x)\<twosuperior> + (cos x)\<twosuperior>) x :> 0"
by (cut_tac DERIV_sin_circle_all, auto)

lemma sin_cos_squared_add [simp]: "((sin x)\<twosuperior>) + ((cos x)\<twosuperior>) = 1"
apply (cut_tac x = x and y = 0 in DERIV_sin_circle_all_zero [THEN DERIV_isconst_all])
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_cos_squared_add2 [simp]: "((cos x)\<twosuperior>) + ((sin x)\<twosuperior>) = 1"
apply (subst real_add_commute)
apply (simp (no_asm) del: realpow_Suc)
done

lemma sin_cos_squared_add3 [simp]: "cos x * cos x + sin x * sin x = 1"
apply (cut_tac x = x in sin_cos_squared_add2)
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_squared_eq: "(sin x)\<twosuperior> = 1 - (cos x)\<twosuperior>"
apply (rule_tac a1 = "(cos x)\<twosuperior> " in add_right_cancel [THEN iffD1])
apply (simp del: realpow_Suc)
done

lemma cos_squared_eq: "(cos x)\<twosuperior> = 1 - (sin x)\<twosuperior>"
apply (rule_tac a1 = "(sin x)\<twosuperior>" in add_right_cancel [THEN iffD1])
apply (simp del: realpow_Suc)
done

lemma real_gt_one_ge_zero_add_less: "[| 1 < x; 0 \<le> y |] ==> 1 < x + (y::real)"
by arith

lemma abs_sin_le_one [simp]: "\<bar>sin x\<bar> \<le> 1"
apply (auto simp add: linorder_not_less [symmetric])
apply (drule_tac n = "Suc 0" in power_gt1)
apply (auto simp del: realpow_Suc)
apply (drule_tac r1 = "cos x" in realpow_two_le [THEN [2] real_gt_one_ge_zero_add_less])
apply (simp add: numeral_2_eq_2 [symmetric] del: realpow_Suc)
done

lemma sin_ge_minus_one [simp]: "-1 \<le> sin x"
apply (insert abs_sin_le_one [of x]) 
apply (simp add: abs_le_interval_iff del: abs_sin_le_one) 
done

lemma sin_le_one [simp]: "sin x \<le> 1"
apply (insert abs_sin_le_one [of x]) 
apply (simp add: abs_le_interval_iff del: abs_sin_le_one) 
done

lemma abs_cos_le_one [simp]: "\<bar>cos x\<bar> \<le> 1"
apply (auto simp add: linorder_not_less [symmetric])
apply (drule_tac n = "Suc 0" in power_gt1)
apply (auto simp del: realpow_Suc)
apply (drule_tac r1 = "sin x" in realpow_two_le [THEN [2] real_gt_one_ge_zero_add_less])
apply (simp add: numeral_2_eq_2 [symmetric] del: realpow_Suc)
done

lemma cos_ge_minus_one [simp]: "-1 \<le> cos x"
apply (insert abs_cos_le_one [of x]) 
apply (simp add: abs_le_interval_iff del: abs_cos_le_one) 
done

lemma cos_le_one [simp]: "cos x \<le> 1"
apply (insert abs_cos_le_one [of x]) 
apply (simp add: abs_le_interval_iff del: abs_cos_le_one)
done

lemma DERIV_fun_pow: "DERIV g x :> m ==>  
      DERIV (%x. (g x) ^ n) x :> real n * (g x) ^ (n - 1) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = " (%x. x ^ n) " in DERIV_chain2)
apply (rule DERIV_pow, auto)
done

lemma DERIV_fun_exp: "DERIV g x :> m ==> DERIV (%x. exp(g x)) x :> exp(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = exp in DERIV_chain2)
apply (rule DERIV_exp, auto)
done

lemma DERIV_fun_sin: "DERIV g x :> m ==> DERIV (%x. sin(g x)) x :> cos(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = sin in DERIV_chain2)
apply (rule DERIV_sin, auto)
done

lemma DERIV_fun_cos: "DERIV g x :> m ==> DERIV (%x. cos(g x)) x :> -sin(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = cos in DERIV_chain2)
apply (rule DERIV_cos, auto)
done

lemmas DERIV_intros = DERIV_Id DERIV_const DERIV_cos DERIV_cmult 
                    DERIV_sin  DERIV_exp  DERIV_inverse DERIV_pow 
                    DERIV_add  DERIV_diff  DERIV_mult  DERIV_minus 
                    DERIV_inverse_fun DERIV_quotient DERIV_fun_pow 
                    DERIV_fun_exp DERIV_fun_sin DERIV_fun_cos 
                    DERIV_Id DERIV_const DERIV_cos

(* lemma *)
lemma lemma_DERIV_sin_cos_add: "\<forall>x.  
         DERIV (%x. (sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +  
               (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2) x :> 0"
apply (safe, rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
  --{*replaces the old @{text DERIV_tac}*}
apply (auto simp add: real_diff_def left_distrib right_distrib mult_ac add_ac)
done

lemma sin_cos_add [simp]:
     "(sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +  
      (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2 = 0"
apply (cut_tac y = 0 and x = x and y7 = y 
       in lemma_DERIV_sin_cos_add [THEN DERIV_isconst_all])
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_add: "sin (x + y) = sin x * cos y + cos x * sin y"
apply (cut_tac x = x and y = y in sin_cos_add)
apply (auto dest!: real_sum_squares_cancel_a 
            simp add: numeral_2_eq_2 real_add_eq_0_iff simp del: sin_cos_add)
done

lemma cos_add: "cos (x + y) = cos x * cos y - sin x * sin y"
apply (cut_tac x = x and y = y in sin_cos_add)
apply (auto dest!: real_sum_squares_cancel_a
            simp add: numeral_2_eq_2 real_add_eq_0_iff simp del: sin_cos_add)
done

lemma lemma_DERIV_sin_cos_minus:
    "\<forall>x. DERIV (%x. (sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2) x :> 0"
apply (safe, rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
apply (auto simp add: real_diff_def left_distrib right_distrib mult_ac add_ac)
done

lemma sin_cos_minus [simp]: 
    "(sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2 = 0"
apply (cut_tac y = 0 and x = x 
       in lemma_DERIV_sin_cos_minus [THEN DERIV_isconst_all])
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_minus [simp]: "sin (-x) = -sin(x)"
apply (cut_tac x = x in sin_cos_minus)
apply (auto dest!: real_sum_squares_cancel_a 
       simp add: numeral_2_eq_2 real_add_eq_0_iff simp del: sin_cos_minus)
done

lemma cos_minus [simp]: "cos (-x) = cos(x)"
apply (cut_tac x = x in sin_cos_minus)
apply (auto dest!: real_sum_squares_cancel_a 
                   simp add: numeral_2_eq_2 simp del: sin_cos_minus)
done

lemma sin_diff: "sin (x - y) = sin x * cos y - cos x * sin y"
apply (unfold real_diff_def)
apply (simp (no_asm) add: sin_add)
done

lemma sin_diff2: "sin (x - y) = cos y * sin x - sin y * cos x"
by (simp add: sin_diff mult_commute)

lemma cos_diff: "cos (x - y) = cos x * cos y + sin x * sin y"
apply (unfold real_diff_def)
apply (simp (no_asm) add: cos_add)
done

lemma cos_diff2: "cos (x - y) = cos y * cos x + sin y * sin x"
by (simp add: cos_diff mult_commute)

lemma sin_double [simp]: "sin(2 * x) = 2* sin x * cos x"
by (cut_tac x = x and y = x in sin_add, auto)


lemma cos_double: "cos(2* x) = ((cos x)\<twosuperior>) - ((sin x)\<twosuperior>)"
apply (cut_tac x = x and y = x in cos_add)
apply (auto simp add: numeral_2_eq_2)
done


subsection{*The Constant Pi*}

text{*Show that there's a least positive @{term x} with @{term "cos(x) = 0"}; 
   hence define pi.*}

lemma sin_paired:
     "(%n. (- 1) ^ n /(real (fact (2 * n + 1))) * x ^ (2 * n + 1)) 
      sums  sin x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
            (if even k then 0
             else (- 1) ^ ((k - Suc 0) div 2) / real (fact k)) *
            x ^ k) 
	sums
	suminf (\<lambda>n. (if even n then 0
		     else (- 1) ^ ((n - Suc 0) div 2) / real (fact n)) *
	            x ^ n)" 
    by (rule sin_converges [THEN sums_summable, THEN sums_group], simp) 
  thus ?thesis by (simp add: mult_ac sin_def)
qed

lemma sin_gt_zero: "[|0 < x; x < 2 |] ==> 0 < sin x"
apply (subgoal_tac 
       "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
              (- 1) ^ k / real (fact (2 * k + 1)) * x ^ (2 * k + 1)) 
     sums suminf (\<lambda>n. (- 1) ^ n / real (fact (2 * n + 1)) * x ^ (2 * n + 1))")
 prefer 2
 apply (rule sin_paired [THEN sums_summable, THEN sums_group], simp) 
apply (rotate_tac 2)
apply (drule sin_paired [THEN sums_unique, THEN ssubst])
apply (auto simp del: fact_Suc realpow_Suc)
apply (frule sums_unique)
apply (auto simp del: fact_Suc realpow_Suc)
apply (rule_tac n1 = 0 in series_pos_less [THEN [2] order_le_less_trans])
apply (auto simp del: fact_Suc realpow_Suc)
apply (erule sums_summable)
apply (case_tac "m=0")
apply (simp (no_asm_simp))
apply (subgoal_tac "6 * (x * (x * x) / real (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) < 6 * x")
apply (simp only: mult_less_cancel_left, simp)
apply (simp (no_asm_simp) add: numeral_2_eq_2 [symmetric] mult_assoc [symmetric])
apply (subgoal_tac "x*x < 2*3", simp) 
apply (rule mult_strict_mono)
apply (auto simp add: real_0_less_add_iff real_of_nat_Suc simp del: fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (simp (no_asm) add: divide_inverse inverse_mult_distrib del: fact_Suc)
apply (auto simp add: mult_assoc [symmetric] simp del: fact_Suc)
apply (rule_tac c="real (Suc (Suc (4*m)))" in mult_less_imp_less_right) 
apply (auto simp add: mult_assoc simp del: fact_Suc)
apply (rule_tac c="real (Suc (Suc (Suc (4*m))))" in mult_less_imp_less_right) 
apply (auto simp add: mult_assoc mult_less_cancel_left simp del: fact_Suc)
apply (subgoal_tac "x * (x * x ^ (4*m)) = (x ^ (4*m)) * (x * x)") 
apply (erule ssubst)+
apply (auto simp del: fact_Suc)
apply (subgoal_tac "0 < x ^ (4 * m) ")
 prefer 2 apply (simp only: zero_less_power) 
apply (simp (no_asm_simp) add: mult_less_cancel_left)
apply (rule mult_strict_mono)
apply (simp_all (no_asm_simp))
done

lemma sin_gt_zero1: "[|0 < x; x < 2 |] ==> 0 < sin x"
by (auto intro: sin_gt_zero)

lemma cos_double_less_one: "[| 0 < x; x < 2 |] ==> cos (2 * x) < 1"
apply (cut_tac x = x in sin_gt_zero1)
apply (auto simp add: cos_squared_eq cos_double)
done

lemma cos_paired:
     "(%n. (- 1) ^ n /(real (fact (2 * n))) * x ^ (2 * n)) sums cos x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
            (if even k then (- 1) ^ (k div 2) / real (fact k) else 0) *
            x ^ k) 
        sums
	suminf
	 (\<lambda>n. (if even n then (- 1) ^ (n div 2) / real (fact n) else 0) *
	      x ^ n)" 
    by (rule cos_converges [THEN sums_summable, THEN sums_group], simp) 
  thus ?thesis by (simp add: mult_ac cos_def)
qed

declare zero_less_power [simp]

lemma fact_lemma: "real (n::nat) * 4 = real (4 * n)"
by simp

lemma cos_two_less_zero: "cos (2) < 0"
apply (cut_tac x = 2 in cos_paired)
apply (drule sums_minus)
apply (rule neg_less_iff_less [THEN iffD1]) 
apply (frule sums_unique, auto)
apply (rule_tac y = "sumr 0 (Suc (Suc (Suc 0))) (%n. - ((- 1) ^ n / (real (fact (2 * n))) * 2 ^ (2 * n))) " in order_less_trans)
apply (simp (no_asm) add: fact_num_eq_if realpow_num_eq_if del: fact_Suc realpow_Suc)
apply (simp (no_asm) add: mult_assoc del: sumr_Suc)
apply (rule sumr_pos_lt_pair)
apply (erule sums_summable, safe)
apply (simp (no_asm) add: divide_inverse real_0_less_add_iff mult_assoc [symmetric] 
            del: fact_Suc)
apply (rule real_mult_inverse_cancel2)
apply (rule real_of_nat_fact_gt_zero)+
apply (simp (no_asm) add: mult_assoc [symmetric] del: fact_Suc)
apply (subst fact_lemma) 
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (erule ssubst, subst real_of_nat_mult)
apply (rule real_mult_less_mono, force)
prefer 2 apply force
apply (rule_tac [2] real_of_nat_fact_gt_zero)
apply (rule real_of_nat_less_iff [THEN iffD2])
apply (rule fact_less_mono, auto)
done
declare cos_two_less_zero [simp]
declare cos_two_less_zero [THEN real_not_refl2, simp]
declare cos_two_less_zero [THEN order_less_imp_le, simp]

lemma cos_is_zero: "EX! x. 0 \<le> x & x \<le> 2 & cos x = 0"
apply (subgoal_tac "\<exists>x. 0 \<le> x & x \<le> 2 & cos x = 0")
apply (rule_tac [2] IVT2)
apply (auto intro: DERIV_isCont DERIV_cos)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (rule ccontr)
apply (subgoal_tac " (\<forall>x. cos differentiable x) & (\<forall>x. isCont cos x) ")
apply (auto intro: DERIV_cos DERIV_isCont simp add: differentiable_def)
apply (drule_tac f = cos in Rolle)
apply (drule_tac [5] f = cos in Rolle)
apply (auto dest!: DERIV_cos [THEN DERIV_unique] simp add: differentiable_def)
apply (drule_tac y1 = xa in order_le_less_trans [THEN sin_gt_zero])
apply (assumption, rule_tac y=y in order_less_le_trans, simp_all) 
apply (drule_tac y1 = y in order_le_less_trans [THEN sin_gt_zero], assumption, simp_all) 
done
    
lemma pi_half: "pi/2 = (@x. 0 \<le> x & x \<le> 2 & cos x = 0)"
by (simp add: pi_def)

lemma cos_pi_half [simp]: "cos (pi / 2) = 0"
apply (rule cos_is_zero [THEN ex1E])
apply (auto intro!: someI2 simp add: pi_half)
done

lemma pi_half_gt_zero: "0 < pi / 2"
apply (rule cos_is_zero [THEN ex1E])
apply (auto simp add: pi_half)
apply (rule someI2, blast, safe)
apply (drule_tac y = xa in real_le_imp_less_or_eq)
apply (safe, simp)
done
declare pi_half_gt_zero [simp]
declare pi_half_gt_zero [THEN real_not_refl2, THEN not_sym, simp]
declare pi_half_gt_zero [THEN order_less_imp_le, simp]

lemma pi_half_less_two: "pi / 2 < 2"
apply (rule cos_is_zero [THEN ex1E])
apply (auto simp add: pi_half)
apply (rule someI2, blast, safe)
apply (drule_tac x = xa in order_le_imp_less_or_eq)
apply (safe, simp)
done
declare pi_half_less_two [simp]
declare pi_half_less_two [THEN real_not_refl2, simp]
declare pi_half_less_two [THEN order_less_imp_le, simp]

lemma pi_gt_zero [simp]: "0 < pi"
apply (rule_tac c="inverse 2" in mult_less_imp_less_right) 
apply (cut_tac pi_half_gt_zero, simp_all)
done

lemma pi_neq_zero [simp]: "pi \<noteq> 0"
by (rule pi_gt_zero [THEN real_not_refl2, THEN not_sym])

lemma pi_not_less_zero [simp]: "~ (pi < 0)"
apply (insert pi_gt_zero)
apply (blast elim: order_less_asym) 
done

lemma pi_ge_zero [simp]: "0 \<le> pi"
by (auto intro: order_less_imp_le)

lemma minus_pi_half_less_zero [simp]: "-(pi/2) < 0"
by auto

lemma sin_pi_half [simp]: "sin(pi/2) = 1"
apply (cut_tac x = "pi/2" in sin_cos_squared_add2)
apply (cut_tac sin_gt_zero [OF pi_half_gt_zero pi_half_less_two])
apply (auto simp add: numeral_2_eq_2)
done

lemma cos_pi [simp]: "cos pi = -1"
by (cut_tac x = "pi/2" and y = "pi/2" in cos_add, simp)

lemma sin_pi [simp]: "sin pi = 0"
by (cut_tac x = "pi/2" and y = "pi/2" in sin_add, simp)

lemma sin_cos_eq: "sin x = cos (pi/2 - x)"
apply (unfold real_diff_def)
apply (simp (no_asm) add: cos_add)
done

lemma minus_sin_cos_eq: "-sin x = cos (x + pi/2)"
apply (simp (no_asm) add: cos_add)
done
declare minus_sin_cos_eq [symmetric, simp]

lemma cos_sin_eq: "cos x = sin (pi/2 - x)"
apply (unfold real_diff_def)
apply (simp (no_asm) add: sin_add)
done
declare sin_cos_eq [symmetric, simp] cos_sin_eq [symmetric, simp]

lemma sin_periodic_pi [simp]: "sin (x + pi) = - sin x"
apply (simp (no_asm) add: sin_add)
done

lemma sin_periodic_pi2 [simp]: "sin (pi + x) = - sin x"
apply (simp (no_asm) add: sin_add)
done

lemma cos_periodic_pi [simp]: "cos (x + pi) = - cos x"
apply (simp (no_asm) add: cos_add)
done

lemma sin_periodic [simp]: "sin (x + 2*pi) = sin x"
by (simp add: sin_add cos_double)

lemma cos_periodic [simp]: "cos (x + 2*pi) = cos x"
by (simp add: cos_add cos_double)

lemma cos_npi [simp]: "cos (real n * pi) = -1 ^ n"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc left_distrib)
done

lemma sin_npi [simp]: "sin (real (n::nat) * pi) = 0"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc left_distrib)
done

lemma sin_npi2 [simp]: "sin (pi * real (n::nat)) = 0"
apply (cut_tac n = n in sin_npi)
apply (auto simp add: mult_commute simp del: sin_npi)
done

lemma cos_two_pi [simp]: "cos (2 * pi) = 1"
by (simp add: cos_double)

lemma sin_two_pi [simp]: "sin (2 * pi) = 0"
apply (simp (no_asm))
done

lemma sin_gt_zero2: "[| 0 < x; x < pi/2 |] ==> 0 < sin x"
apply (rule sin_gt_zero, assumption)
apply (rule order_less_trans, assumption)
apply (rule pi_half_less_two)
done

lemma sin_less_zero: 
  assumes lb: "- pi/2 < x" and "x < 0" shows "sin x < 0"
proof -
  have "0 < sin (- x)" using prems by (simp only: sin_gt_zero2) 
  thus ?thesis by simp
qed

lemma pi_less_4: "pi < 4"
by (cut_tac pi_half_less_two, auto)

lemma cos_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < cos x"
apply (cut_tac pi_less_4)
apply (cut_tac f = cos and a = 0 and b = x and y = 0 in IVT2_objl, safe, simp_all)
apply (force intro: DERIV_isCont DERIV_cos)
apply (cut_tac cos_is_zero, safe)
apply (rename_tac y z)
apply (drule_tac x = y in spec)
apply (drule_tac x = "pi/2" in spec, simp) 
done

lemma cos_gt_zero_pi: "[| -(pi/2) < x; x < pi/2 |] ==> 0 < cos x"
apply (rule_tac x = x and y = 0 in linorder_cases)
apply (rule cos_minus [THEN subst])
apply (rule cos_gt_zero)
apply (auto intro: cos_gt_zero)
done
 
lemma cos_ge_zero: "[| -(pi/2) \<le> x; x \<le> pi/2 |] ==> 0 \<le> cos x"
apply (auto simp add: order_le_less cos_gt_zero_pi)
apply (subgoal_tac "x = pi/2", auto) 
done

lemma sin_gt_zero_pi: "[| 0 < x; x < pi  |] ==> 0 < sin x"
apply (subst sin_cos_eq)
apply (rotate_tac 1)
apply (drule real_sum_of_halves [THEN ssubst])
apply (auto intro!: cos_gt_zero_pi simp del: sin_cos_eq [symmetric])
done

lemma sin_ge_zero: "[| 0 \<le> x; x \<le> pi |] ==> 0 \<le> sin x"
by (auto simp add: order_le_less sin_gt_zero_pi)

lemma cos_total: "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. 0 \<le> x & x \<le> pi & (cos x = y)"
apply (subgoal_tac "\<exists>x. 0 \<le> x & x \<le> pi & cos x = y")
apply (rule_tac [2] IVT2)
apply (auto intro: order_less_imp_le DERIV_isCont DERIV_cos)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (rule ccontr, auto)
apply (drule_tac f = cos in Rolle)
apply (drule_tac [5] f = cos in Rolle)
apply (auto intro: order_less_imp_le DERIV_isCont DERIV_cos
            dest!: DERIV_cos [THEN DERIV_unique] 
            simp add: differentiable_def)
apply (auto dest: sin_gt_zero_pi [OF order_le_less_trans order_less_le_trans])
done

lemma sin_total:
     "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. -(pi/2) \<le> x & x \<le> pi/2 & (sin x = y)"
apply (rule ccontr)
apply (subgoal_tac "\<forall>x. (- (pi/2) \<le> x & x \<le> pi/2 & (sin x = y)) = (0 \<le> (x + pi/2) & (x + pi/2) \<le> pi & (cos (x + pi/2) = -y))")
apply (erule swap)
apply (simp del: minus_sin_cos_eq [symmetric])
apply (cut_tac y="-y" in cos_total, simp) apply simp 
apply (erule ex1E)
apply (rule_tac a = "x - (pi/2) " in ex1I)
apply (simp (no_asm) add: real_add_assoc)
apply (rotate_tac 3)
apply (drule_tac x = "xa + pi/2" in spec, safe, simp_all) 
done

lemma reals_Archimedean4:
     "[| 0 < y; 0 \<le> x |] ==> \<exists>n. real n * y \<le> x & x < real (Suc n) * y"
apply (auto dest!: reals_Archimedean3)
apply (drule_tac x = x in spec, clarify) 
apply (subgoal_tac "x < real(LEAST m::nat. x < real m * y) * y")
 prefer 2 apply (erule LeastI) 
apply (case_tac "LEAST m::nat. x < real m * y", simp) 
apply (subgoal_tac "~ x < real nat * y")
 prefer 2 apply (rule not_less_Least, simp, force)  
done

(* Pre Isabelle99-2 proof was simpler- numerals arithmetic 
   now causes some unwanted re-arrangements of literals!   *)
lemma cos_zero_lemma: "[| 0 \<le> x; cos x = 0 |] ==>  
      \<exists>n::nat. ~even n & x = real n * (pi/2)"
apply (drule pi_gt_zero [THEN reals_Archimedean4], safe)
apply (subgoal_tac "0 \<le> x - real n * pi & 
                    (x - real n * pi) \<le> pi & (cos (x - real n * pi) = 0) ")
apply (auto simp add: compare_rls) 
  prefer 3 apply (simp add: cos_diff) 
 prefer 2 apply (simp add: real_of_nat_Suc left_distrib) 
apply (simp add: cos_diff)
apply (subgoal_tac "EX! x. 0 \<le> x & x \<le> pi & cos x = 0")
apply (rule_tac [2] cos_total, safe)
apply (drule_tac x = "x - real n * pi" in spec)
apply (drule_tac x = "pi/2" in spec)
apply (simp add: cos_diff)
apply (rule_tac x = "Suc (2 * n) " in exI)
apply (simp add: real_of_nat_Suc left_distrib, auto)
done

lemma sin_zero_lemma: "[| 0 \<le> x; sin x = 0 |] ==>  
      \<exists>n::nat. even n & x = real n * (pi/2)"
apply (subgoal_tac "\<exists>n::nat. ~ even n & x + pi/2 = real n * (pi/2) ")
 apply (clarify, rule_tac x = "n - 1" in exI)
 apply (force simp add: odd_Suc_mult_two_ex real_of_nat_Suc left_distrib)
apply (rule cos_zero_lemma)
apply (simp_all add: add_increasing)  
done


lemma cos_zero_iff: "(cos x = 0) =  
      ((\<exists>n::nat. ~even n & (x = real n * (pi/2))) |    
       (\<exists>n::nat. ~even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule cos_zero_lemma, assumption+)
apply (cut_tac x="-x" in cos_zero_lemma, simp, simp) 
apply (force simp add: minus_equation_iff [of x]) 
apply (auto simp only: odd_Suc_mult_two_ex real_of_nat_Suc left_distrib) 
apply (auto simp add: cos_add)
done

(* ditto: but to a lesser extent *)
lemma sin_zero_iff: "(sin x = 0) =  
      ((\<exists>n::nat. even n & (x = real n * (pi/2))) |    
       (\<exists>n::nat. even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule sin_zero_lemma, assumption+)
apply (cut_tac x="-x" in sin_zero_lemma, simp, simp, safe)
apply (force simp add: minus_equation_iff [of x]) 
apply (auto simp add: even_mult_two_ex)
done


subsection{*Tangent*}

lemma tan_zero [simp]: "tan 0 = 0"
by (simp add: tan_def)

lemma tan_pi [simp]: "tan pi = 0"
by (simp add: tan_def)

lemma tan_npi [simp]: "tan (real (n::nat) * pi) = 0"
by (simp add: tan_def)

lemma tan_minus [simp]: "tan (-x) = - tan x"
by (simp add: tan_def minus_mult_left)

lemma tan_periodic [simp]: "tan (x + 2*pi) = tan x"
by (simp add: tan_def)

lemma lemma_tan_add1: 
      "[| cos x \<noteq> 0; cos y \<noteq> 0 |]  
        ==> 1 - tan(x)*tan(y) = cos (x + y)/(cos x * cos y)"
apply (unfold tan_def real_divide_def)
apply (auto simp del: inverse_mult_distrib simp add: inverse_mult_distrib [symmetric] mult_ac)
apply (rule_tac c1 = "cos x * cos y" in real_mult_right_cancel [THEN subst])
apply (auto simp del: inverse_mult_distrib simp add: mult_assoc left_diff_distrib cos_add)
done

lemma add_tan_eq: 
      "[| cos x \<noteq> 0; cos y \<noteq> 0 |]  
       ==> tan x + tan y = sin(x + y)/(cos x * cos y)"
apply (unfold tan_def)
apply (rule_tac c1 = "cos x * cos y" in real_mult_right_cancel [THEN subst])
apply (auto simp add: mult_assoc left_distrib)
apply (simp (no_asm) add: sin_add)
done

lemma tan_add: "[| cos x \<noteq> 0; cos y \<noteq> 0; cos (x + y) \<noteq> 0 |]  
      ==> tan(x + y) = (tan(x) + tan(y))/(1 - tan(x) * tan(y))"
apply (simp (no_asm_simp) add: add_tan_eq lemma_tan_add1)
apply (simp add: tan_def)
done

lemma tan_double: "[| cos x \<noteq> 0; cos (2 * x) \<noteq> 0 |]  
      ==> tan (2 * x) = (2 * tan x)/(1 - (tan(x) ^ 2))"
apply (insert tan_add [of x x]) 
apply (simp add: mult_2 [symmetric])  
apply (auto simp add: numeral_2_eq_2)
done

lemma tan_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < tan x"
apply (unfold tan_def real_divide_def)
apply (auto intro!: sin_gt_zero2 cos_gt_zero_pi intro!: real_mult_order positive_imp_inverse_positive)
done

lemma tan_less_zero: 
  assumes lb: "- pi/2 < x" and "x < 0" shows "tan x < 0"
proof -
  have "0 < tan (- x)" using prems by (simp only: tan_gt_zero) 
  thus ?thesis by simp
qed

lemma lemma_DERIV_tan:
     "cos x \<noteq> 0 ==> DERIV (%x. sin(x)/cos(x)) x :> inverse((cos x)\<twosuperior>)"
apply (rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
apply (auto simp add: divide_inverse numeral_2_eq_2)
done

lemma DERIV_tan [simp]: "cos x \<noteq> 0 ==> DERIV tan x :> inverse((cos x)\<twosuperior>)"
by (auto dest: lemma_DERIV_tan simp add: tan_def [symmetric])

lemma LIM_cos_div_sin [simp]: "(%x. cos(x)/sin(x)) -- pi/2 --> 0"
apply (unfold real_divide_def)
apply (subgoal_tac "(\<lambda>x. cos x * inverse (sin x)) -- pi * inverse 2 --> 0*1")
apply simp 
apply (rule LIM_mult2)
apply (rule_tac [2] inverse_1 [THEN subst])
apply (rule_tac [2] LIM_inverse)
apply (simp_all add: divide_inverse [symmetric]) 
apply (simp_all only: isCont_def [symmetric] cos_pi_half [symmetric] sin_pi_half [symmetric]) 
apply (blast intro!: DERIV_isCont DERIV_sin DERIV_cos)+
done

lemma lemma_tan_total: "0 < y ==> \<exists>x. 0 < x & x < pi/2 & y < tan x"
apply (cut_tac LIM_cos_div_sin)
apply (simp only: LIM_def)
apply (drule_tac x = "inverse y" in spec, safe, force)
apply (drule_tac ?d1.0 = s in pi_half_gt_zero [THEN [2] real_lbound_gt_zero], safe)
apply (rule_tac x = " (pi/2) - e" in exI)
apply (simp (no_asm_simp))
apply (drule_tac x = " (pi/2) - e" in spec)
apply (auto simp add: abs_eqI2 tan_def)
apply (rule inverse_less_iff_less [THEN iffD1])
apply (auto simp add: divide_inverse)
apply (rule real_mult_order)
apply (subgoal_tac [3] "0 < sin e")
apply (subgoal_tac [3] "0 < cos e")
apply (auto intro: cos_gt_zero sin_gt_zero2 simp add: inverse_mult_distrib abs_mult)
apply (drule_tac a = "cos e" in positive_imp_inverse_positive)
apply (drule_tac x = "inverse (cos e) " in abs_eqI2)
apply (auto dest!: abs_eqI2 simp add: mult_ac)
done

lemma tan_total_pos: "0 \<le> y ==> \<exists>x. 0 \<le> x & x < pi/2 & tan x = y"
apply (frule real_le_imp_less_or_eq, safe)
 prefer 2 apply force
apply (drule lemma_tan_total, safe)
apply (cut_tac f = tan and a = 0 and b = x and y = y in IVT_objl)
apply (auto intro!: DERIV_tan [THEN DERIV_isCont])
apply (drule_tac y = xa in order_le_imp_less_or_eq)
apply (auto dest: cos_gt_zero)
done

lemma lemma_tan_total1: "\<exists>x. -(pi/2) < x & x < (pi/2) & tan x = y"
apply (cut_tac linorder_linear [of 0 y], safe)
apply (drule tan_total_pos)
apply (cut_tac [2] y="-y" in tan_total_pos, safe)
apply (rule_tac [3] x = "-x" in exI)
apply (auto intro!: exI)
done

lemma tan_total: "EX! x. -(pi/2) < x & x < (pi/2) & tan x = y"
apply (cut_tac y = y in lemma_tan_total1, auto)
apply (cut_tac x = xa and y = y in linorder_less_linear, auto)
apply (subgoal_tac [2] "\<exists>z. y < z & z < xa & DERIV tan z :> 0")
apply (subgoal_tac "\<exists>z. xa < z & z < y & DERIV tan z :> 0")
apply (rule_tac [4] Rolle)
apply (rule_tac [2] Rolle)
apply (auto intro!: DERIV_tan DERIV_isCont exI 
            simp add: differentiable_def)
txt{*Now, simulate TRYALL*}
apply (rule_tac [!] DERIV_tan asm_rl)
apply (auto dest!: DERIV_unique [OF _ DERIV_tan]
	    simp add: cos_gt_zero_pi [THEN real_not_refl2, THEN not_sym]) 
done

lemma arcsin_pi: "[| -1 \<le> y; y \<le> 1 |]  
      ==> -(pi/2) \<le> arcsin y & arcsin y \<le> pi & sin(arcsin y) = y"
apply (drule sin_total, assumption)
apply (erule ex1E)
apply (unfold arcsin_def)
apply (rule someI2, blast) 
apply (force intro: order_trans) 
done

lemma arcsin: "[| -1 \<le> y; y \<le> 1 |]  
      ==> -(pi/2) \<le> arcsin y &  
           arcsin y \<le> pi/2 & sin(arcsin y) = y"
apply (unfold arcsin_def)
apply (drule sin_total, assumption)
apply (fast intro: someI2)
done

lemma sin_arcsin [simp]: "[| -1 \<le> y; y \<le> 1 |] ==> sin(arcsin y) = y"
by (blast dest: arcsin)
      
lemma arcsin_bounded:
     "[| -1 \<le> y; y \<le> 1 |] ==> -(pi/2) \<le> arcsin y & arcsin y \<le> pi/2"
by (blast dest: arcsin)

lemma arcsin_lbound: "[| -1 \<le> y; y \<le> 1 |] ==> -(pi/2) \<le> arcsin y"
by (blast dest: arcsin)

lemma arcsin_ubound: "[| -1 \<le> y; y \<le> 1 |] ==> arcsin y \<le> pi/2"
by (blast dest: arcsin)

lemma arcsin_lt_bounded:
     "[| -1 < y; y < 1 |] ==> -(pi/2) < arcsin y & arcsin y < pi/2"
apply (frule order_less_imp_le)
apply (frule_tac y = y in order_less_imp_le)
apply (frule arcsin_bounded)
apply (safe, simp)
apply (drule_tac y = "arcsin y" in order_le_imp_less_or_eq)
apply (drule_tac [2] y = "pi/2" in order_le_imp_less_or_eq, safe)
apply (drule_tac [!] f = sin in arg_cong, auto)
done

lemma arcsin_sin: "[|-(pi/2) \<le> x; x \<le> pi/2 |] ==> arcsin(sin x) = x"
apply (unfold arcsin_def)
apply (rule some1_equality)
apply (rule sin_total, auto)
done

lemma arcos: "[| -1 \<le> y; y \<le> 1 |]  
      ==> 0 \<le> arcos y & arcos y \<le> pi & cos(arcos y) = y"
apply (unfold arcos_def)
apply (drule cos_total, assumption)
apply (fast intro: someI2)
done

lemma cos_arcos [simp]: "[| -1 \<le> y; y \<le> 1 |] ==> cos(arcos y) = y"
by (blast dest: arcos)
      
lemma arcos_bounded: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arcos y & arcos y \<le> pi"
by (blast dest: arcos)

lemma arcos_lbound: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arcos y"
by (blast dest: arcos)

lemma arcos_ubound: "[| -1 \<le> y; y \<le> 1 |] ==> arcos y \<le> pi"
by (blast dest: arcos)

lemma arcos_lt_bounded: "[| -1 < y; y < 1 |]  
      ==> 0 < arcos y & arcos y < pi"
apply (frule order_less_imp_le)
apply (frule_tac y = y in order_less_imp_le)
apply (frule arcos_bounded, auto)
apply (drule_tac y = "arcos y" in order_le_imp_less_or_eq)
apply (drule_tac [2] y = pi in order_le_imp_less_or_eq, auto)
apply (drule_tac [!] f = cos in arg_cong, auto)
done

lemma arcos_cos: "[|0 \<le> x; x \<le> pi |] ==> arcos(cos x) = x"
apply (unfold arcos_def)
apply (auto intro!: some1_equality cos_total)
done

lemma arcos_cos2: "[|x \<le> 0; -pi \<le> x |] ==> arcos(cos x) = -x"
apply (unfold arcos_def)
apply (auto intro!: some1_equality cos_total)
done

lemma arctan [simp]:
     "- (pi/2) < arctan y  & arctan y < pi/2 & tan (arctan y) = y"
apply (cut_tac y = y in tan_total)
apply (unfold arctan_def)
apply (fast intro: someI2)
done

lemma tan_arctan: "tan(arctan y) = y"
by auto

lemma arctan_bounded: "- (pi/2) < arctan y  & arctan y < pi/2"
by (auto simp only: arctan)

lemma arctan_lbound: "- (pi/2) < arctan y"
by auto

lemma arctan_ubound: "arctan y < pi/2"
by (auto simp only: arctan)

lemma arctan_tan: 
      "[|-(pi/2) < x; x < pi/2 |] ==> arctan(tan x) = x"
apply (unfold arctan_def)
apply (rule some1_equality)
apply (rule tan_total, auto)
done

lemma arctan_zero_zero [simp]: "arctan 0 = 0"
by (insert arctan_tan [of 0], simp)

lemma cos_arctan_not_zero [simp]: "cos(arctan x) \<noteq> 0"
apply (auto simp add: cos_zero_iff)
apply (case_tac "n")
apply (case_tac [3] "n")
apply (cut_tac [2] y = x in arctan_ubound)
apply (cut_tac [4] y = x in arctan_lbound) 
apply (auto simp add: real_of_nat_Suc left_distrib mult_less_0_iff)
done

lemma tan_sec: "cos x \<noteq> 0 ==> 1 + tan(x) ^ 2 = inverse(cos x) ^ 2"
apply (rule power_inverse [THEN subst])
apply (rule_tac c1 = "(cos x)\<twosuperior>" in real_mult_right_cancel [THEN iffD1])
apply (auto dest: realpow_not_zero 
        simp add: power_mult_distrib left_distrib realpow_divide tan_def 
                  mult_assoc power_inverse [symmetric] 
        simp del: realpow_Suc)
done

text{*NEEDED??*}
lemma [simp]: "sin (xa + 1 / 2 * real (Suc m) * pi) =  
      cos (xa + 1 / 2 * real  (m) * pi)"
apply (simp only: cos_add sin_add real_of_nat_Suc left_distrib right_distrib, auto)
done

text{*NEEDED??*}
lemma [simp]: "sin (xa + real (Suc m) * pi / 2) =  
      cos (xa + real (m) * pi / 2)"
apply (simp only: cos_add sin_add divide_inverse real_of_nat_Suc left_distrib right_distrib, auto)
done

lemma DERIV_sin_add [simp]: "DERIV (%x. sin (x + k)) xa :> cos (xa + k)"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = sin and g = "%x. x + k" in DERIV_chain2)
apply (best intro!: DERIV_intros intro: DERIV_chain2)+
apply (simp (no_asm))
done

(* which further simplifies to (- 1 ^ m) !! *)
lemma sin_cos_npi [simp]: "sin ((real m + 1/2) * pi) = cos (real m * pi)"
by (auto simp add: right_distrib sin_add left_distrib mult_ac)

lemma sin_cos_npi2 [simp]: "sin (real (Suc (2 * n)) * pi / 2) = (-1) ^ n"
apply (cut_tac m = n in sin_cos_npi)
apply (simp only: real_of_nat_Suc left_distrib divide_inverse, auto)
done

lemma cos_2npi [simp]: "cos (2 * real (n::nat) * pi) = 1"
by (simp add: cos_double mult_assoc power_add [symmetric] numeral_2_eq_2)

lemma cos_3over2_pi [simp]: "cos (3 / 2 * pi) = 0"
apply (subgoal_tac "3/2 = (1+1 / 2::real)")
apply (simp only: left_distrib) 
apply (auto simp add: cos_add mult_ac)
done

lemma sin_2npi [simp]: "sin (2 * real (n::nat) * pi) = 0"
by (auto simp add: mult_assoc)

lemma sin_3over2_pi [simp]: "sin (3 / 2 * pi) = - 1"
apply (subgoal_tac "3/2 = (1+1 / 2::real)")
apply (simp only: left_distrib) 
apply (auto simp add: sin_add mult_ac)
done

(*NEEDED??*)
lemma [simp]: "cos(x + 1 / 2 * real(Suc m) * pi) = -sin (x + 1 / 2 * real m * pi)"
apply (simp only: cos_add sin_add real_of_nat_Suc right_distrib left_distrib minus_mult_right, auto)
done

(*NEEDED??*)
lemma [simp]: "cos (x + real(Suc m) * pi / 2) = -sin (x + real m * pi / 2)"
apply (simp only: cos_add sin_add divide_inverse real_of_nat_Suc left_distrib right_distrib, auto)
done

lemma cos_pi_eq_zero [simp]: "cos (pi * real (Suc (2 * m)) / 2) = 0"
by (simp only: cos_add sin_add divide_inverse real_of_nat_Suc left_distrib right_distrib, auto)

lemma DERIV_cos_add [simp]: "DERIV (%x. cos (x + k)) xa :> - sin (xa + k)"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = cos and g = "%x. x + k" in DERIV_chain2)
apply (best intro!: DERIV_intros intro: DERIV_chain2)+
apply (simp (no_asm))
done

lemma isCont_cos [simp]: "isCont cos x"
by (rule DERIV_cos [THEN DERIV_isCont])

lemma isCont_sin [simp]: "isCont sin x"
by (rule DERIV_sin [THEN DERIV_isCont])

lemma isCont_exp [simp]: "isCont exp x"
by (rule DERIV_exp [THEN DERIV_isCont])

lemma sin_zero_abs_cos_one: "sin x = 0 ==> \<bar>cos x\<bar> = 1"
by (auto simp add: sin_zero_iff even_mult_two_ex)

lemma exp_eq_one_iff [simp]: "(exp x = 1) = (x = 0)"
apply auto
apply (drule_tac f = ln in arg_cong, auto)
done

lemma cos_one_sin_zero: "cos x = 1 ==> sin x = 0"
by (cut_tac x = x in sin_cos_squared_add3, auto)


lemma real_root_less_mono: "[| 0 \<le> x; x < y |] ==> root(Suc n) x < root(Suc n) y"
apply (frule order_le_less_trans, assumption)
apply (frule_tac n1 = n in real_root_pow_pos2 [THEN ssubst])
apply (rotate_tac 1, assumption)
apply (frule_tac n1 = n in real_root_pow_pos [THEN ssubst])
apply (rotate_tac 3, assumption)
apply (drule_tac y = "root (Suc n) y ^ Suc n" in order_less_imp_le)
apply (frule_tac n = n in real_root_pos_pos_le)
apply (frule_tac n = n in real_root_pos_pos)
apply (drule_tac x = "root (Suc n) x" and y = "root (Suc n) y" in realpow_increasing)
apply (assumption, assumption)
apply (drule_tac x = "root (Suc n) x" in order_le_imp_less_or_eq)
apply auto
apply (drule_tac f = "%x. x ^ (Suc n) " in arg_cong)
apply (auto simp add: real_root_pow_pos2 simp del: realpow_Suc)
done

lemma real_root_le_mono: "[| 0 \<le> x; x \<le> y |] ==> root(Suc n) x \<le> root(Suc n) y"
apply (drule_tac y = y in order_le_imp_less_or_eq)
apply (auto dest: real_root_less_mono intro: order_less_imp_le)
done

lemma real_root_less_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x < root(Suc n) y) = (x < y)"
apply (auto intro: real_root_less_mono)
apply (rule ccontr, drule linorder_not_less [THEN iffD1])
apply (drule_tac x = y and n = n in real_root_le_mono, auto)
done

lemma real_root_le_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x \<le> root(Suc n) y) = (x \<le> y)"
apply (auto intro: real_root_le_mono)
apply (simp (no_asm) add: linorder_not_less [symmetric])
apply auto
apply (drule_tac x = y and n = n in real_root_less_mono, auto)
done

lemma real_root_eq_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x = root(Suc n) y) = (x = y)"
apply (auto intro!: order_antisym)
apply (rule_tac n1 = n in real_root_le_iff [THEN iffD1])
apply (rule_tac [4] n1 = n in real_root_le_iff [THEN iffD1], auto)
done

lemma real_root_pos_unique: "[| 0 \<le> x; 0 \<le> y; y ^ (Suc n) = x |] ==> root (Suc n) x = y"
by (auto dest: real_root_pos2 simp del: realpow_Suc)

lemma real_root_mult: "[| 0 \<le> x; 0 \<le> y |] 
      ==> root(Suc n) (x * y) = root(Suc n) x * root(Suc n) y"
apply (rule real_root_pos_unique)
apply (auto intro!: real_root_pos_pos_le simp add: power_mult_distrib zero_le_mult_iff real_root_pow_pos2 simp del: realpow_Suc)
done

lemma real_root_inverse: "0 \<le> x ==> (root(Suc n) (inverse x) = inverse(root(Suc n) x))"
apply (rule real_root_pos_unique)
apply (auto intro: real_root_pos_pos_le simp add: power_inverse [symmetric] real_root_pow_pos2 simp del: realpow_Suc)
done

lemma real_root_divide: 
     "[| 0 \<le> x; 0 \<le> y |]  
      ==> (root(Suc n) (x / y) = root(Suc n) x / root(Suc n) y)"
apply (unfold real_divide_def)
apply (auto simp add: real_root_mult real_root_inverse)
done

lemma real_sqrt_less_mono: "[| 0 \<le> x; x < y |] ==> sqrt(x) < sqrt(y)"
apply (unfold sqrt_def)
apply (auto intro: real_root_less_mono)
done

lemma real_sqrt_le_mono: "[| 0 \<le> x; x \<le> y |] ==> sqrt(x) \<le> sqrt(y)"
apply (unfold sqrt_def)
apply (auto intro: real_root_le_mono)
done

lemma real_sqrt_less_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) < sqrt(y)) = (x < y)"
by (unfold sqrt_def, auto)

lemma real_sqrt_le_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) \<le> sqrt(y)) = (x \<le> y)"
by (unfold sqrt_def, auto)

lemma real_sqrt_eq_iff [simp]: "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) = sqrt(y)) = (x = y)"
by (unfold sqrt_def, auto)

lemma real_sqrt_sos_less_one_iff [simp]: "(sqrt(x\<twosuperior> + y\<twosuperior>) < 1) = (x\<twosuperior> + y\<twosuperior> < 1)"
apply (rule real_sqrt_one [THEN subst], safe)
apply (rule_tac [2] real_sqrt_less_mono)
apply (drule real_sqrt_less_iff [THEN [2] rev_iffD1], auto)
done

lemma real_sqrt_sos_eq_one_iff [simp]: "(sqrt(x\<twosuperior> + y\<twosuperior>) = 1) = (x\<twosuperior> + y\<twosuperior> = 1)"
apply (rule real_sqrt_one [THEN subst], safe)
apply (drule real_sqrt_eq_iff [THEN [2] rev_iffD1], auto)
done

lemma real_divide_square_eq [simp]: "(((r::real) * a) / (r * r)) = a / r"
apply (unfold real_divide_def)
apply (case_tac "r=0")
apply (auto simp add: inverse_mult_distrib mult_ac)
done


subsection{*Theorems About Sqrt, Transcendental Functions for Complex*}

lemma lemma_real_divide_sqrt: 
    "0 < x ==> 0 \<le> x/(sqrt (x * x + y * y))"
apply (unfold real_divide_def)
apply (rule real_mult_order [THEN order_less_imp_le], assumption)
apply (subgoal_tac "0 < inverse (sqrt (x\<twosuperior> + y\<twosuperior>))") 
 apply (simp add: numeral_2_eq_2)
apply (simp add: real_sqrt_sum_squares_ge1 [THEN [2] order_less_le_trans]) 
done

lemma lemma_real_divide_sqrt_ge_minus_one:
     "0 < x ==> -1 \<le> x/(sqrt (x * x + y * y))"
apply (rule real_le_trans)
apply (rule_tac [2] lemma_real_divide_sqrt, auto)
done

lemma real_sqrt_sum_squares_gt_zero1: "x < 0 ==> 0 < sqrt (x * x + y * y)"
apply (rule real_sqrt_gt_zero)
apply (subgoal_tac "0 < x*x & 0 \<le> y*y", arith) 
apply (auto simp add: zero_less_mult_iff)
done

lemma real_sqrt_sum_squares_gt_zero2: "0 < x ==> 0 < sqrt (x * x + y * y)"
apply (rule real_sqrt_gt_zero)
apply (subgoal_tac "0 < x*x & 0 \<le> y*y", arith) 
apply (auto simp add: zero_less_mult_iff)
done

lemma real_sqrt_sum_squares_gt_zero3: "x \<noteq> 0 ==> 0 < sqrt(x\<twosuperior> + y\<twosuperior>)"
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (auto intro: real_sqrt_sum_squares_gt_zero2 real_sqrt_sum_squares_gt_zero1 simp add: numeral_2_eq_2)
done

lemma real_sqrt_sum_squares_gt_zero3a: "y \<noteq> 0 ==> 0 < sqrt(x\<twosuperior> + y\<twosuperior>)"
apply (drule_tac y = x in real_sqrt_sum_squares_gt_zero3)
apply (auto simp add: real_add_commute)
done

lemma real_sqrt_sum_squares_eq_cancel [simp]: "sqrt(x\<twosuperior> + y\<twosuperior>) = x ==> y = 0"
by (drule_tac f = "%x. x\<twosuperior>" in arg_cong, auto)

lemma real_sqrt_sum_squares_eq_cancel2 [simp]: "sqrt(x\<twosuperior> + y\<twosuperior>) = y ==> x = 0"
apply (rule_tac x = y in real_sqrt_sum_squares_eq_cancel)
apply (simp add: real_add_commute)
done

lemma lemma_real_divide_sqrt_le_one: "x < 0 ==> x/(sqrt (x * x + y * y)) \<le> 1"
by (insert lemma_real_divide_sqrt_ge_minus_one [of "-x" y], simp)

lemma lemma_real_divide_sqrt_ge_minus_one2:
     "x < 0 ==> -1 \<le> x/(sqrt (x * x + y * y))"
apply (case_tac "y = 0", auto)
apply (frule abs_minus_eqI2)
apply (auto simp add: inverse_minus_eq)
apply (rule order_less_imp_le)
apply (rule_tac z1 = "sqrt (x * x + y * y) " in real_mult_less_iff1 [THEN iffD1])
apply (frule_tac [2] y2 = y in
       real_sqrt_sum_squares_gt_zero1 [THEN real_not_refl2, THEN not_sym])
apply (auto intro: real_sqrt_sum_squares_gt_zero1 simp add: mult_ac)
apply (cut_tac x = "-x" and y = y in real_sqrt_sum_squares_ge1)
apply (drule order_le_less [THEN iffD1], safe) 
apply (simp add: numeral_2_eq_2)
apply (drule sym [THEN real_sqrt_sum_squares_eq_cancel], simp)
done

lemma lemma_real_divide_sqrt_le_one2: "0 < x ==> x/(sqrt (x * x + y * y)) \<le> 1"
by (cut_tac x = "-x" and y = y in lemma_real_divide_sqrt_ge_minus_one2, auto)


lemma cos_x_y_ge_minus_one: "-1 \<le> x / sqrt (x * x + y * y)"
apply (cut_tac x = x and y = 0 in linorder_less_linear, safe)
apply (rule lemma_real_divide_sqrt_ge_minus_one2)
apply (rule_tac [3] lemma_real_divide_sqrt_ge_minus_one, auto)
done

lemma cos_x_y_ge_minus_one1a [simp]: "-1 \<le> y / sqrt (x * x + y * y)"
apply (cut_tac x = y and y = x in cos_x_y_ge_minus_one)
apply (simp add: real_add_commute)
done

lemma cos_x_y_le_one [simp]: "x / sqrt (x * x + y * y) \<le> 1"
apply (cut_tac x = x and y = 0 in linorder_less_linear, safe)
apply (rule lemma_real_divide_sqrt_le_one)
apply (rule_tac [3] lemma_real_divide_sqrt_le_one2, auto)
done

lemma cos_x_y_le_one2 [simp]: "y / sqrt (x * x + y * y) \<le> 1"
apply (cut_tac x = y and y = x in cos_x_y_le_one)
apply (simp add: real_add_commute)
done

declare cos_arcos [OF cos_x_y_ge_minus_one cos_x_y_le_one, simp] 
declare arcos_bounded [OF cos_x_y_ge_minus_one cos_x_y_le_one, simp] 

declare cos_arcos [OF cos_x_y_ge_minus_one1a cos_x_y_le_one2, simp] 
declare arcos_bounded [OF cos_x_y_ge_minus_one1a cos_x_y_le_one2, simp] 

lemma cos_abs_x_y_ge_minus_one [simp]:
     "-1 \<le> \<bar>x\<bar> / sqrt (x * x + y * y)"
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (auto simp add: abs_minus_eqI2 abs_eqI2)
apply (drule lemma_real_divide_sqrt_ge_minus_one, force)
done

lemma cos_abs_x_y_le_one [simp]: "\<bar>x\<bar> / sqrt (x * x + y * y) \<le> 1"
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (auto simp add: abs_minus_eqI2 abs_eqI2)
apply (drule lemma_real_divide_sqrt_ge_minus_one2, force)
done

declare cos_arcos [OF cos_abs_x_y_ge_minus_one cos_abs_x_y_le_one, simp] 
declare arcos_bounded [OF cos_abs_x_y_ge_minus_one cos_abs_x_y_le_one, simp] 

lemma minus_pi_less_zero: "-pi < 0"
apply (simp (no_asm))
done
declare minus_pi_less_zero [simp]
declare minus_pi_less_zero [THEN order_less_imp_le, simp]

lemma arcos_ge_minus_pi: "[| -1 \<le> y; y \<le> 1 |] ==> -pi \<le> arcos y"
apply (rule real_le_trans)
apply (rule_tac [2] arcos_lbound, auto)
done

declare arcos_ge_minus_pi [OF cos_x_y_ge_minus_one cos_x_y_le_one, simp] 

(* How tedious! *)
lemma lemma_divide_rearrange:
     "[| x + (y::real) \<noteq> 0; 1 - z = x/(x + y) |] ==> z = y/(x + y)"
apply (rule_tac c1 = "x + y" in real_mult_right_cancel [THEN iffD1])
apply (frule_tac [2] c1 = "x + y" in real_mult_right_cancel [THEN iffD2])
prefer 2 apply assumption
apply (rotate_tac [2] 2)
apply (drule_tac [2] mult_assoc [THEN subst])
apply (rotate_tac [2] 2)
apply (frule_tac [2] left_inverse [THEN subst])
prefer 2 apply assumption
apply (erule_tac [2] V = " (1 - z) * (x + y) = x / (x + y) * (x + y) " in thin_rl)
apply (erule_tac [2] V = "1 - z = x / (x + y) " in thin_rl)
apply (auto simp add: mult_assoc)
apply (auto simp add: right_distrib left_diff_distrib)
done

lemma lemma_cos_sin_eq:
     "[| 0 < x * x + y * y;  
         1 - (sin xa)\<twosuperior> = (x / sqrt (x * x + y * y)) ^ 2 |] 
      ==> (sin xa)\<twosuperior> = (y / sqrt (x * x + y * y)) ^ 2"
by (auto intro: lemma_divide_rearrange
         simp add: realpow_divide power2_eq_square [symmetric])


lemma lemma_sin_cos_eq:
     "[| 0 < x * x + y * y;  
         1 - (cos xa)\<twosuperior> = (y / sqrt (x * x + y * y)) ^ 2 |]
      ==> (cos xa)\<twosuperior> = (x / sqrt (x * x + y * y)) ^ 2"
apply (auto simp add: realpow_divide power2_eq_square [symmetric])
apply (subst add_commute)
apply (rule lemma_divide_rearrange, simp add: real_add_eq_0_iff)
apply (simp add: add_commute)
done

lemma sin_x_y_disj:
     "[| x \<noteq> 0;  
         cos xa = x / sqrt (x * x + y * y)  
      |] ==>  sin xa = y / sqrt (x * x + y * y) |  
              sin xa = - y / sqrt (x * x + y * y)"
apply (drule_tac f = "%x. x\<twosuperior>" in arg_cong)
apply (frule_tac y = y in real_sum_square_gt_zero)
apply (simp add: cos_squared_eq)
apply (subgoal_tac "(sin xa)\<twosuperior> = (y / sqrt (x * x + y * y)) ^ 2")
apply (rule_tac [2] lemma_cos_sin_eq)
apply (auto simp add: realpow_two_disj numeral_2_eq_2 simp del: realpow_Suc)
done

lemma lemma_cos_not_eq_zero: "x \<noteq> 0 ==> x / sqrt (x * x + y * y) \<noteq> 0"
apply (unfold real_divide_def)
apply (frule_tac y3 = y in real_sqrt_sum_squares_gt_zero3 [THEN real_not_refl2, THEN not_sym, THEN nonzero_imp_inverse_nonzero])
apply (auto simp add: power2_eq_square)
done

lemma cos_x_y_disj: "[| x \<noteq> 0;  
         sin xa = y / sqrt (x * x + y * y)  
      |] ==>  cos xa = x / sqrt (x * x + y * y) |  
              cos xa = - x / sqrt (x * x + y * y)"
apply (drule_tac f = "%x. x\<twosuperior>" in arg_cong)
apply (frule_tac y = y in real_sum_square_gt_zero)
apply (simp add: sin_squared_eq del: realpow_Suc)
apply (subgoal_tac "(cos xa)\<twosuperior> = (x / sqrt (x * x + y * y)) ^ 2")
apply (rule_tac [2] lemma_sin_cos_eq)
apply (auto simp add: realpow_two_disj numeral_2_eq_2 simp del: realpow_Suc)
done

lemma real_sqrt_divide_less_zero: "0 < y ==> - y / sqrt (x * x + y * y) < 0"
apply (case_tac "x = 0")
apply (auto simp add: abs_eqI2)
apply (drule_tac y = y in real_sqrt_sum_squares_gt_zero3)
apply (auto simp add: zero_less_mult_iff divide_inverse power2_eq_square)
done

lemma polar_ex1: "[| x \<noteq> 0; 0 < y |] ==> \<exists>r a. x = r * cos a & y = r * sin a"
apply (rule_tac x = "sqrt (x\<twosuperior> + y\<twosuperior>) " in exI)
apply (rule_tac x = "arcos (x / sqrt (x * x + y * y))" in exI)
apply auto
apply (drule_tac y2 = y in real_sqrt_sum_squares_gt_zero3 [THEN real_not_refl2, THEN not_sym])
apply (auto simp add: power2_eq_square)
apply (unfold arcos_def)
apply (cut_tac x1 = x and y1 = y 
       in cos_total [OF cos_x_y_ge_minus_one cos_x_y_le_one])
apply (rule someI2_ex, blast)
apply (erule_tac V = "EX! xa. 0 \<le> xa & xa \<le> pi & cos xa = x / sqrt (x * x + y * y) " in thin_rl)
apply (frule sin_x_y_disj, blast)
apply (drule_tac y2 = y in real_sqrt_sum_squares_gt_zero3 [THEN real_not_refl2, THEN not_sym])
apply (auto simp add: power2_eq_square)
apply (drule sin_ge_zero, assumption)
apply (drule_tac x = x in real_sqrt_divide_less_zero, auto)
done

lemma real_sum_squares_cancel2a: "x * x = -(y * y) ==> y = (0::real)"
by (auto intro: real_sum_squares_cancel iff: real_add_eq_0_iff)

lemma polar_ex2: "[| x \<noteq> 0; y < 0 |] ==> \<exists>r a. x = r * cos a & y = r * sin a"
apply (cut_tac x = 0 and y = x in linorder_less_linear, auto)
apply (rule_tac x = "sqrt (x\<twosuperior> + y\<twosuperior>) " in exI)
apply (rule_tac x = "arcsin (y / sqrt (x * x + y * y))" in exI)
apply (auto dest: real_sum_squares_cancel2a 
            simp add: power2_eq_square real_0_le_add_iff real_add_eq_0_iff)
apply (unfold arcsin_def)
apply (cut_tac x1 = x and y1 = y 
       in sin_total [OF cos_x_y_ge_minus_one1a cos_x_y_le_one2])
apply (rule someI2_ex, blast)
apply (erule_tac V = "EX! xa. - (pi/2) \<le> xa & xa \<le> pi/2 & sin xa = y / sqrt (x * x + y * y) " in thin_rl)
apply (cut_tac x=x and y=y in cos_x_y_disj, simp, blast)
apply (auto simp add: real_0_le_add_iff real_add_eq_0_iff)
apply (drule cos_ge_zero, force)
apply (drule_tac x = y in real_sqrt_divide_less_zero)
apply (auto simp add: add_commute)
apply (insert polar_ex1 [of x "-y"], simp, clarify) 
apply (rule_tac x = r in exI)
apply (rule_tac x = "-a" in exI, simp) 
done

lemma polar_Ex: "\<exists>r a. x = r * cos a & y = r * sin a"
apply (case_tac "x = 0", auto)
apply (rule_tac x = y in exI)
apply (rule_tac x = "pi/2" in exI, auto)
apply (cut_tac x = 0 and y = y in linorder_less_linear, auto)
apply (rule_tac [2] x = x in exI)
apply (rule_tac [2] x = 0 in exI, auto)
apply (blast intro: polar_ex1 polar_ex2)+
done

lemma real_sqrt_ge_abs1 [simp]: "\<bar>x\<bar> \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
apply (rule_tac n = 1 in realpow_increasing)
apply (auto simp add: numeral_2_eq_2 [symmetric])
done

lemma real_sqrt_ge_abs2 [simp]: "\<bar>y\<bar> \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
apply (rule real_add_commute [THEN subst])
apply (rule real_sqrt_ge_abs1)
done
declare real_sqrt_ge_abs1 [simp] real_sqrt_ge_abs2 [simp]

lemma real_sqrt_two_gt_zero [simp]: "0 < sqrt 2"
by (auto intro: real_sqrt_gt_zero)

lemma real_sqrt_two_ge_zero [simp]: "0 \<le> sqrt 2"
by (auto intro: real_sqrt_ge_zero)

lemma real_sqrt_two_gt_one [simp]: "1 < sqrt 2"
apply (rule order_less_le_trans [of _ "7/5"], simp) 
apply (rule_tac n = 1 in realpow_increasing)
  prefer 3 apply (simp add: numeral_2_eq_2 [symmetric] del: realpow_Suc)
apply (simp_all add: numeral_2_eq_2)
done

lemma lemma_real_divide_sqrt_less: "0 < u ==> u / sqrt 2 < u"
apply (rule_tac z1 = "inverse u" in real_mult_less_iff1 [THEN iffD1], auto)
apply (rule_tac z1 = "sqrt 2" in real_mult_less_iff1 [THEN iffD1], auto)
done

lemma four_x_squared: 
  fixes x::real
  shows "4 * x\<twosuperior> = (2 * x)\<twosuperior>"
by (simp add: power2_eq_square)


text{*Needed for the infinitely close relation over the nonstandard
    complex numbers*}
lemma lemma_sqrt_hcomplex_capprox:
     "[| 0 < u; x < u/2; y < u/2; 0 \<le> x; 0 \<le> y |] ==> sqrt (x\<twosuperior> + y\<twosuperior>) < u"
apply (rule_tac y = "u/sqrt 2" in order_le_less_trans)
apply (erule_tac [2] lemma_real_divide_sqrt_less)
apply (rule_tac n = 1 in realpow_increasing)
apply (auto simp add: real_0_le_divide_iff realpow_divide numeral_2_eq_2 [symmetric] 
        simp del: realpow_Suc)
apply (rule_tac t = "u\<twosuperior>" in real_sum_of_halves [THEN subst])
apply (rule add_mono)
apply (auto simp add: four_x_squared simp del: realpow_Suc intro: power_mono)
done

declare real_sqrt_sum_squares_ge_zero [THEN abs_eqI1, simp]


subsection{*A Few Theorems Involving Ln, Derivatives, etc.*}

lemma lemma_DERIV_ln:
     "DERIV ln z :> l ==> DERIV (%x. exp (ln x)) z :> exp (ln z) * l"
by (erule DERIV_fun_exp)

lemma STAR_exp_ln: "0 < z ==> ( *f* (%x. exp (ln x))) z = z"
apply (rule_tac z = z in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_zero_def hypreal_less)
done

lemma hypreal_add_Infinitesimal_gt_zero: "[|e : Infinitesimal; 0 < x |] ==> 0 < hypreal_of_real x + e"
apply (rule_tac c1 = "-e" in add_less_cancel_right [THEN iffD1])
apply (auto intro: Infinitesimal_less_SReal)
done

lemma NSDERIV_exp_ln_one: "0 < z ==> NSDERIV (%x. exp (ln x)) z :> 1"
apply (unfold nsderiv_def NSLIM_def, auto)
apply (rule ccontr)
apply (subgoal_tac "0 < hypreal_of_real z + h")
apply (drule STAR_exp_ln)
apply (rule_tac [2] hypreal_add_Infinitesimal_gt_zero)
apply (subgoal_tac "h/h = 1")
apply (auto simp add: exp_ln_iff [symmetric] simp del: exp_ln_iff)
done

lemma DERIV_exp_ln_one: "0 < z ==> DERIV (%x. exp (ln x)) z :> 1"
by (auto intro: NSDERIV_exp_ln_one simp add: NSDERIV_DERIV_iff [symmetric])

lemma lemma_DERIV_ln2: "[| 0 < z; DERIV ln z :> l |] ==>  exp (ln z) * l = 1"
apply (rule DERIV_unique)
apply (rule lemma_DERIV_ln)
apply (rule_tac [2] DERIV_exp_ln_one, auto)
done

lemma lemma_DERIV_ln3: "[| 0 < z; DERIV ln z :> l |] ==>  l = 1/(exp (ln z))"
apply (rule_tac c1 = "exp (ln z) " in real_mult_left_cancel [THEN iffD1])
apply (auto intro: lemma_DERIV_ln2)
done

lemma lemma_DERIV_ln4: "[| 0 < z; DERIV ln z :> l |] ==>  l = 1/z"
apply (rule_tac t = z in exp_ln_iff [THEN iffD2, THEN subst])
apply (auto intro: lemma_DERIV_ln3)
done

(* need to rename second isCont_inverse *)

lemma isCont_inv_fun: "[| 0 < d; \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
      ==> isCont g (f x)"
apply (simp (no_asm) add: isCont_iff LIM_def)
apply safe
apply (drule_tac ?d1.0 = r in real_lbound_gt_zero)
apply (assumption, safe)
apply (subgoal_tac "\<forall>z. \<bar>z - x\<bar> \<le> e --> (g (f z) = z) ")
prefer 2 apply force
apply (subgoal_tac "\<forall>z. \<bar>z - x\<bar> \<le> e --> isCont f z")
prefer 2 apply force
apply (drule_tac d = e in isCont_inj_range)
prefer 2 apply (assumption, assumption, safe)
apply (rule_tac x = ea in exI, auto)
apply (drule_tac x = "f (x) + xa" and P = "%y. \<bar>y - f x\<bar> \<le> ea \<longrightarrow> (\<exists>z. \<bar>z - x\<bar> \<le> e \<and> f z = y)" in spec)
apply auto
apply (drule sym, auto, arith)
done

lemma isCont_inv_fun_inv:
     "[| 0 < d;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
       ==> \<exists>e. 0 < e &  
             (\<forall>y. 0 < \<bar>y - f(x)\<bar> & \<bar>y - f(x)\<bar> < e --> f(g(y)) = y)"
apply (drule isCont_inj_range)
prefer 2 apply (assumption, assumption, auto)
apply (rule_tac x = e in exI, auto)
apply (rotate_tac 2)
apply (drule_tac x = y in spec, auto)
done


text{*Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110*}
lemma LIM_fun_gt_zero: "[| f -- c --> l; 0 < l |]  
         ==> \<exists>r. 0 < r & (\<forall>x. x \<noteq> c & \<bar>c - x\<bar> < r --> 0 < f x)"
apply (auto simp add: LIM_def)
apply (drule_tac x = "l/2" in spec, safe, force)
apply (rule_tac x = s in exI)
apply (auto simp only: abs_interval_iff)
done

lemma LIM_fun_less_zero: "[| f -- c --> l; l < 0 |]  
         ==> \<exists>r. 0 < r & (\<forall>x. x \<noteq> c & \<bar>c - x\<bar> < r --> f x < 0)"
apply (auto simp add: LIM_def)
apply (drule_tac x = "-l/2" in spec, safe, force)
apply (rule_tac x = s in exI)
apply (auto simp only: abs_interval_iff)
done


lemma LIM_fun_not_zero:
     "[| f -- c --> l; l \<noteq> 0 |] 
      ==> \<exists>r. 0 < r & (\<forall>x. x \<noteq> c & \<bar>c - x\<bar> < r --> f x \<noteq> 0)"
apply (cut_tac x = l and y = 0 in linorder_less_linear, auto)
apply (drule LIM_fun_less_zero)
apply (drule_tac [3] LIM_fun_gt_zero, auto)
apply (rule_tac [!] x = r in exI, auto)
done

ML
{*
val inverse_unique = thm "inverse_unique";
val real_root_zero = thm "real_root_zero";
val real_root_pow_pos = thm "real_root_pow_pos";
val real_root_pow_pos2 = thm "real_root_pow_pos2";
val real_root_pos = thm "real_root_pos";
val real_root_pos2 = thm "real_root_pos2";
val real_root_pos_pos = thm "real_root_pos_pos";
val real_root_pos_pos_le = thm "real_root_pos_pos_le";
val real_root_one = thm "real_root_one";
val root_2_eq = thm "root_2_eq";
val real_sqrt_zero = thm "real_sqrt_zero";
val real_sqrt_one = thm "real_sqrt_one";
val real_sqrt_pow2_iff = thm "real_sqrt_pow2_iff";
val real_sqrt_pow2 = thm "real_sqrt_pow2";
val real_sqrt_abs_abs = thm "real_sqrt_abs_abs";
val real_pow_sqrt_eq_sqrt_pow = thm "real_pow_sqrt_eq_sqrt_pow";
val real_pow_sqrt_eq_sqrt_abs_pow2 = thm "real_pow_sqrt_eq_sqrt_abs_pow2";
val real_sqrt_pow_abs = thm "real_sqrt_pow_abs";
val not_real_square_gt_zero = thm "not_real_square_gt_zero";
val real_mult_self_eq_zero_iff = thm "real_mult_self_eq_zero_iff";
val real_sqrt_gt_zero = thm "real_sqrt_gt_zero";
val real_sqrt_ge_zero = thm "real_sqrt_ge_zero";
val sqrt_eqI = thm "sqrt_eqI";
val real_sqrt_mult_distrib = thm "real_sqrt_mult_distrib";
val real_sqrt_mult_distrib2 = thm "real_sqrt_mult_distrib2";
val real_sqrt_sum_squares_ge_zero = thm "real_sqrt_sum_squares_ge_zero";
val real_sqrt_sum_squares_mult_ge_zero = thm "real_sqrt_sum_squares_mult_ge_zero";
val real_sqrt_sum_squares_mult_squared_eq = thm "real_sqrt_sum_squares_mult_squared_eq";
val real_sqrt_abs = thm "real_sqrt_abs";
val real_sqrt_abs2 = thm "real_sqrt_abs2";
val real_sqrt_pow2_gt_zero = thm "real_sqrt_pow2_gt_zero";
val real_sqrt_not_eq_zero = thm "real_sqrt_not_eq_zero";
val real_inv_sqrt_pow2 = thm "real_inv_sqrt_pow2";
val real_sqrt_eq_zero_cancel = thm "real_sqrt_eq_zero_cancel";
val real_sqrt_eq_zero_cancel_iff = thm "real_sqrt_eq_zero_cancel_iff";
val real_sqrt_sum_squares_ge1 = thm "real_sqrt_sum_squares_ge1";
val real_sqrt_sum_squares_ge2 = thm "real_sqrt_sum_squares_ge2";
val real_sqrt_ge_one = thm "real_sqrt_ge_one";
val summable_exp = thm "summable_exp";
val summable_sin = thm "summable_sin";
val summable_cos = thm "summable_cos";
val exp_converges = thm "exp_converges";
val sin_converges = thm "sin_converges";
val cos_converges = thm "cos_converges";
val powser_insidea = thm "powser_insidea";
val powser_inside = thm "powser_inside";
val diffs_minus = thm "diffs_minus";
val diffs_equiv = thm "diffs_equiv";
val less_add_one = thm "less_add_one";
val termdiffs_aux = thm "termdiffs_aux";
val termdiffs = thm "termdiffs";
val exp_fdiffs = thm "exp_fdiffs";
val sin_fdiffs = thm "sin_fdiffs";
val sin_fdiffs2 = thm "sin_fdiffs2";
val cos_fdiffs = thm "cos_fdiffs";
val cos_fdiffs2 = thm "cos_fdiffs2";
val DERIV_exp = thm "DERIV_exp";
val DERIV_sin = thm "DERIV_sin";
val DERIV_cos = thm "DERIV_cos";
val exp_zero = thm "exp_zero";
val exp_ge_add_one_self = thm "exp_ge_add_one_self";
val exp_gt_one = thm "exp_gt_one";
val DERIV_exp_add_const = thm "DERIV_exp_add_const";
val DERIV_exp_minus = thm "DERIV_exp_minus";
val DERIV_exp_exp_zero = thm "DERIV_exp_exp_zero";
val exp_add_mult_minus = thm "exp_add_mult_minus";
val exp_mult_minus = thm "exp_mult_minus";
val exp_mult_minus2 = thm "exp_mult_minus2";
val exp_minus = thm "exp_minus";
val exp_add = thm "exp_add";
val exp_ge_zero = thm "exp_ge_zero";
val exp_not_eq_zero = thm "exp_not_eq_zero";
val exp_gt_zero = thm "exp_gt_zero";
val inv_exp_gt_zero = thm "inv_exp_gt_zero";
val abs_exp_cancel = thm "abs_exp_cancel";
val exp_real_of_nat_mult = thm "exp_real_of_nat_mult";
val exp_diff = thm "exp_diff";
val exp_less_mono = thm "exp_less_mono";
val exp_less_cancel = thm "exp_less_cancel";
val exp_less_cancel_iff = thm "exp_less_cancel_iff";
val exp_le_cancel_iff = thm "exp_le_cancel_iff";
val exp_inj_iff = thm "exp_inj_iff";
val exp_total = thm "exp_total";
val ln_exp = thm "ln_exp";
val exp_ln_iff = thm "exp_ln_iff";
val ln_mult = thm "ln_mult";
val ln_inj_iff = thm "ln_inj_iff";
val ln_one = thm "ln_one";
val ln_inverse = thm "ln_inverse";
val ln_div = thm "ln_div";
val ln_less_cancel_iff = thm "ln_less_cancel_iff";
val ln_le_cancel_iff = thm "ln_le_cancel_iff";
val ln_realpow = thm "ln_realpow";
val ln_add_one_self_le_self = thm "ln_add_one_self_le_self";
val ln_less_self = thm "ln_less_self";
val ln_ge_zero = thm "ln_ge_zero";
val ln_gt_zero = thm "ln_gt_zero";
val ln_not_eq_zero = thm "ln_not_eq_zero";
val ln_less_zero = thm "ln_less_zero";
val exp_ln_eq = thm "exp_ln_eq";
val sin_zero = thm "sin_zero";
val cos_zero = thm "cos_zero";
val DERIV_sin_sin_mult = thm "DERIV_sin_sin_mult";
val DERIV_sin_sin_mult2 = thm "DERIV_sin_sin_mult2";
val DERIV_sin_realpow2 = thm "DERIV_sin_realpow2";
val DERIV_sin_realpow2a = thm "DERIV_sin_realpow2a";
val DERIV_cos_cos_mult = thm "DERIV_cos_cos_mult";
val DERIV_cos_cos_mult2 = thm "DERIV_cos_cos_mult2";
val DERIV_cos_realpow2 = thm "DERIV_cos_realpow2";
val DERIV_cos_realpow2a = thm "DERIV_cos_realpow2a";
val DERIV_cos_realpow2b = thm "DERIV_cos_realpow2b";
val DERIV_cos_cos_mult3 = thm "DERIV_cos_cos_mult3";
val DERIV_sin_circle_all = thm "DERIV_sin_circle_all";
val DERIV_sin_circle_all_zero = thm "DERIV_sin_circle_all_zero";
val sin_cos_squared_add = thm "sin_cos_squared_add";
val sin_cos_squared_add2 = thm "sin_cos_squared_add2";
val sin_cos_squared_add3 = thm "sin_cos_squared_add3";
val sin_squared_eq = thm "sin_squared_eq";
val cos_squared_eq = thm "cos_squared_eq";
val real_gt_one_ge_zero_add_less = thm "real_gt_one_ge_zero_add_less";
val abs_sin_le_one = thm "abs_sin_le_one";
val sin_ge_minus_one = thm "sin_ge_minus_one";
val sin_le_one = thm "sin_le_one";
val abs_cos_le_one = thm "abs_cos_le_one";
val cos_ge_minus_one = thm "cos_ge_minus_one";
val cos_le_one = thm "cos_le_one";
val DERIV_fun_pow = thm "DERIV_fun_pow";
val DERIV_fun_exp = thm "DERIV_fun_exp";
val DERIV_fun_sin = thm "DERIV_fun_sin";
val DERIV_fun_cos = thm "DERIV_fun_cos";
val DERIV_intros = thms "DERIV_intros";
val sin_cos_add = thm "sin_cos_add";
val sin_add = thm "sin_add";
val cos_add = thm "cos_add";
val sin_cos_minus = thm "sin_cos_minus";
val sin_minus = thm "sin_minus";
val cos_minus = thm "cos_minus";
val sin_diff = thm "sin_diff";
val sin_diff2 = thm "sin_diff2";
val cos_diff = thm "cos_diff";
val cos_diff2 = thm "cos_diff2";
val sin_double = thm "sin_double";
val cos_double = thm "cos_double";
val sin_paired = thm "sin_paired";
val sin_gt_zero = thm "sin_gt_zero";
val sin_gt_zero1 = thm "sin_gt_zero1";
val cos_double_less_one = thm "cos_double_less_one";
val cos_paired = thm "cos_paired";
val cos_two_less_zero = thm "cos_two_less_zero";
val cos_is_zero = thm "cos_is_zero";
val pi_half = thm "pi_half";
val cos_pi_half = thm "cos_pi_half";
val pi_half_gt_zero = thm "pi_half_gt_zero";
val pi_half_less_two = thm "pi_half_less_two";
val pi_gt_zero = thm "pi_gt_zero";
val pi_neq_zero = thm "pi_neq_zero";
val pi_not_less_zero = thm "pi_not_less_zero";
val pi_ge_zero = thm "pi_ge_zero";
val minus_pi_half_less_zero = thm "minus_pi_half_less_zero";
val sin_pi_half = thm "sin_pi_half";
val cos_pi = thm "cos_pi";
val sin_pi = thm "sin_pi";
val sin_cos_eq = thm "sin_cos_eq";
val minus_sin_cos_eq = thm "minus_sin_cos_eq";
val cos_sin_eq = thm "cos_sin_eq";
val sin_periodic_pi = thm "sin_periodic_pi";
val sin_periodic_pi2 = thm "sin_periodic_pi2";
val cos_periodic_pi = thm "cos_periodic_pi";
val sin_periodic = thm "sin_periodic";
val cos_periodic = thm "cos_periodic";
val cos_npi = thm "cos_npi";
val sin_npi = thm "sin_npi";
val sin_npi2 = thm "sin_npi2";
val cos_two_pi = thm "cos_two_pi";
val sin_two_pi = thm "sin_two_pi";
val sin_gt_zero2 = thm "sin_gt_zero2";
val sin_less_zero = thm "sin_less_zero";
val pi_less_4 = thm "pi_less_4";
val cos_gt_zero = thm "cos_gt_zero";
val cos_gt_zero_pi = thm "cos_gt_zero_pi";
val cos_ge_zero = thm "cos_ge_zero";
val sin_gt_zero_pi = thm "sin_gt_zero_pi";
val sin_ge_zero = thm "sin_ge_zero";
val cos_total = thm "cos_total";
val sin_total = thm "sin_total";
val reals_Archimedean4 = thm "reals_Archimedean4";
val cos_zero_lemma = thm "cos_zero_lemma";
val sin_zero_lemma = thm "sin_zero_lemma";
val cos_zero_iff = thm "cos_zero_iff";
val sin_zero_iff = thm "sin_zero_iff";
val tan_zero = thm "tan_zero";
val tan_pi = thm "tan_pi";
val tan_npi = thm "tan_npi";
val tan_minus = thm "tan_minus";
val tan_periodic = thm "tan_periodic";
val add_tan_eq = thm "add_tan_eq";
val tan_add = thm "tan_add";
val tan_double = thm "tan_double";
val tan_gt_zero = thm "tan_gt_zero";
val tan_less_zero = thm "tan_less_zero";
val DERIV_tan = thm "DERIV_tan";
val LIM_cos_div_sin = thm "LIM_cos_div_sin";
val tan_total_pos = thm "tan_total_pos";
val tan_total = thm "tan_total";
val arcsin_pi = thm "arcsin_pi";
val arcsin = thm "arcsin";
val sin_arcsin = thm "sin_arcsin";
val arcsin_bounded = thm "arcsin_bounded";
val arcsin_lbound = thm "arcsin_lbound";
val arcsin_ubound = thm "arcsin_ubound";
val arcsin_lt_bounded = thm "arcsin_lt_bounded";
val arcsin_sin = thm "arcsin_sin";
val arcos = thm "arcos";
val cos_arcos = thm "cos_arcos";
val arcos_bounded = thm "arcos_bounded";
val arcos_lbound = thm "arcos_lbound";
val arcos_ubound = thm "arcos_ubound";
val arcos_lt_bounded = thm "arcos_lt_bounded";
val arcos_cos = thm "arcos_cos";
val arcos_cos2 = thm "arcos_cos2";
val arctan = thm "arctan";
val tan_arctan = thm "tan_arctan";
val arctan_bounded = thm "arctan_bounded";
val arctan_lbound = thm "arctan_lbound";
val arctan_ubound = thm "arctan_ubound";
val arctan_tan = thm "arctan_tan";
val arctan_zero_zero = thm "arctan_zero_zero";
val cos_arctan_not_zero = thm "cos_arctan_not_zero";
val tan_sec = thm "tan_sec";
val DERIV_sin_add = thm "DERIV_sin_add";
val sin_cos_npi = thm "sin_cos_npi";
val sin_cos_npi2 = thm "sin_cos_npi2";
val cos_2npi = thm "cos_2npi";
val cos_3over2_pi = thm "cos_3over2_pi";
val sin_2npi = thm "sin_2npi";
val sin_3over2_pi = thm "sin_3over2_pi";
val cos_pi_eq_zero = thm "cos_pi_eq_zero";
val DERIV_cos_add = thm "DERIV_cos_add";
val isCont_cos = thm "isCont_cos";
val isCont_sin = thm "isCont_sin";
val isCont_exp = thm "isCont_exp";
val sin_zero_abs_cos_one = thm "sin_zero_abs_cos_one";
val exp_eq_one_iff = thm "exp_eq_one_iff";
val cos_one_sin_zero = thm "cos_one_sin_zero";
val real_root_less_mono = thm "real_root_less_mono";
val real_root_le_mono = thm "real_root_le_mono";
val real_root_less_iff = thm "real_root_less_iff";
val real_root_le_iff = thm "real_root_le_iff";
val real_root_eq_iff = thm "real_root_eq_iff";
val real_root_pos_unique = thm "real_root_pos_unique";
val real_root_mult = thm "real_root_mult";
val real_root_inverse = thm "real_root_inverse";
val real_root_divide = thm "real_root_divide";
val real_sqrt_less_mono = thm "real_sqrt_less_mono";
val real_sqrt_le_mono = thm "real_sqrt_le_mono";
val real_sqrt_less_iff = thm "real_sqrt_less_iff";
val real_sqrt_le_iff = thm "real_sqrt_le_iff";
val real_sqrt_eq_iff = thm "real_sqrt_eq_iff";
val real_sqrt_sos_less_one_iff = thm "real_sqrt_sos_less_one_iff";
val real_sqrt_sos_eq_one_iff = thm "real_sqrt_sos_eq_one_iff";
val real_divide_square_eq = thm "real_divide_square_eq";
val real_sqrt_sum_squares_gt_zero1 = thm "real_sqrt_sum_squares_gt_zero1";
val real_sqrt_sum_squares_gt_zero2 = thm "real_sqrt_sum_squares_gt_zero2";
val real_sqrt_sum_squares_gt_zero3 = thm "real_sqrt_sum_squares_gt_zero3";
val real_sqrt_sum_squares_gt_zero3a = thm "real_sqrt_sum_squares_gt_zero3a";
val real_sqrt_sum_squares_eq_cancel = thm "real_sqrt_sum_squares_eq_cancel";
val real_sqrt_sum_squares_eq_cancel2 = thm "real_sqrt_sum_squares_eq_cancel2";
val cos_x_y_ge_minus_one = thm "cos_x_y_ge_minus_one";
val cos_x_y_ge_minus_one1a = thm "cos_x_y_ge_minus_one1a";
val cos_x_y_le_one = thm "cos_x_y_le_one";
val cos_x_y_le_one2 = thm "cos_x_y_le_one2";
val cos_abs_x_y_ge_minus_one = thm "cos_abs_x_y_ge_minus_one";
val cos_abs_x_y_le_one = thm "cos_abs_x_y_le_one";
val minus_pi_less_zero = thm "minus_pi_less_zero";
val arcos_ge_minus_pi = thm "arcos_ge_minus_pi";
val sin_x_y_disj = thm "sin_x_y_disj";
val cos_x_y_disj = thm "cos_x_y_disj";
val real_sqrt_divide_less_zero = thm "real_sqrt_divide_less_zero";
val polar_ex1 = thm "polar_ex1";
val polar_ex2 = thm "polar_ex2";
val polar_Ex = thm "polar_Ex";
val real_sqrt_ge_abs1 = thm "real_sqrt_ge_abs1";
val real_sqrt_ge_abs2 = thm "real_sqrt_ge_abs2";
val real_sqrt_two_gt_zero = thm "real_sqrt_two_gt_zero";
val real_sqrt_two_ge_zero = thm "real_sqrt_two_ge_zero";
val real_sqrt_two_gt_one = thm "real_sqrt_two_gt_one";
val STAR_exp_ln = thm "STAR_exp_ln";
val hypreal_add_Infinitesimal_gt_zero = thm "hypreal_add_Infinitesimal_gt_zero";
val NSDERIV_exp_ln_one = thm "NSDERIV_exp_ln_one";
val DERIV_exp_ln_one = thm "DERIV_exp_ln_one";
val isCont_inv_fun = thm "isCont_inv_fun";
val isCont_inv_fun_inv = thm "isCont_inv_fun_inv";
val LIM_fun_gt_zero = thm "LIM_fun_gt_zero";
val LIM_fun_less_zero = thm "LIM_fun_less_zero";
val LIM_fun_not_zero = thm "LIM_fun_not_zero";
*}
  
end 
