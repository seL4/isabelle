(*  Title       : Log.thy
    Author      : Jacques D. Fleuriot
                  Additional contributions by Jeremy Avigad
    Copyright   : 2000,2001 University of Edinburgh
*)

header{*Logarithms: Standard Version*}

theory Log
imports Transcendental
begin

definition
  powr  :: "[real,real] => real"     (infixr "powr" 80) where
    --{*exponentation with real exponent*}
  "x powr a = exp(a * ln x)"

definition
  log :: "[real,real] => real" where
    --{*logarithm of @{term x} to base @{term a}*}
  "log a x = ln x / ln a"



lemma powr_one_eq_one [simp]: "1 powr a = 1"
by (simp add: powr_def)

lemma powr_zero_eq_one [simp]: "x powr 0 = 1"
by (simp add: powr_def)

lemma powr_one_gt_zero_iff [simp]: "(x powr 1 = x) = (0 < x)"
by (simp add: powr_def)
declare powr_one_gt_zero_iff [THEN iffD2, simp]

lemma powr_mult: 
      "[| 0 < x; 0 < y |] ==> (x * y) powr a = (x powr a) * (y powr a)"
by (simp add: powr_def exp_add [symmetric] ln_mult right_distrib)

lemma powr_gt_zero [simp]: "0 < x powr a"
by (simp add: powr_def)

lemma powr_ge_pzero [simp]: "0 <= x powr y"
by (rule order_less_imp_le, rule powr_gt_zero)

lemma powr_not_zero [simp]: "x powr a \<noteq> 0"
by (simp add: powr_def)

lemma powr_divide:
     "[| 0 < x; 0 < y |] ==> (x / y) powr a = (x powr a)/(y powr a)"
apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
done

lemma powr_divide2: "x powr a / x powr b = x powr (a - b)"
  apply (simp add: powr_def)
  apply (subst exp_diff [THEN sym])
  apply (simp add: left_diff_distrib)
done

lemma powr_add: "x powr (a + b) = (x powr a) * (x powr b)"
by (simp add: powr_def exp_add [symmetric] left_distrib)

lemma powr_powr: "(x powr a) powr b = x powr (a * b)"
by (simp add: powr_def)

lemma powr_powr_swap: "(x powr a) powr b = (x powr b) powr a"
by (simp add: powr_powr mult_commute)

lemma powr_minus: "x powr (-a) = inverse (x powr a)"
by (simp add: powr_def exp_minus [symmetric])

lemma powr_minus_divide: "x powr (-a) = 1/(x powr a)"
by (simp add: divide_inverse powr_minus)

lemma powr_less_mono: "[| a < b; 1 < x |] ==> x powr a < x powr b"
by (simp add: powr_def)

lemma powr_less_cancel: "[| x powr a < x powr b; 1 < x |] ==> a < b"
by (simp add: powr_def)

lemma powr_less_cancel_iff [simp]: "1 < x ==> (x powr a < x powr b) = (a < b)"
by (blast intro: powr_less_cancel powr_less_mono)

lemma powr_le_cancel_iff [simp]: "1 < x ==> (x powr a \<le> x powr b) = (a \<le> b)"
by (simp add: linorder_not_less [symmetric])

lemma log_ln: "ln x = log (exp(1)) x"
by (simp add: log_def)

lemma DERIV_log: "x > 0 ==> DERIV (%y. log b y) x :> 1 / (ln b * x)"
  apply (subst log_def)
  apply (subgoal_tac "(%y. ln y / ln b) = (%y. (1 / ln b) * ln y)")
  apply (erule ssubst)
  apply (subgoal_tac "1 / (ln b * x) = (1 / ln b) * (1 / x)")
  apply (erule ssubst)
  apply (rule DERIV_cmult)
  apply (erule DERIV_ln_divide)
  apply auto
done

lemma powr_log_cancel [simp]:
     "[| 0 < a; a \<noteq> 1; 0 < x |] ==> a powr (log a x) = x"
by (simp add: powr_def log_def)

lemma log_powr_cancel [simp]: "[| 0 < a; a \<noteq> 1 |] ==> log a (a powr y) = y"
by (simp add: log_def powr_def)

lemma log_mult: 
     "[| 0 < a; a \<noteq> 1; 0 < x; 0 < y |]  
      ==> log a (x * y) = log a x + log a y"
by (simp add: log_def ln_mult divide_inverse left_distrib)

lemma log_eq_div_ln_mult_log: 
     "[| 0 < a; a \<noteq> 1; 0 < b; b \<noteq> 1; 0 < x |]  
      ==> log a x = (ln b/ln a) * log b x"
by (simp add: log_def divide_inverse)

text{*Base 10 logarithms*}
lemma log_base_10_eq1: "0 < x ==> log 10 x = (ln (exp 1) / ln 10) * ln x"
by (simp add: log_def)

lemma log_base_10_eq2: "0 < x ==> log 10 x = (log 10 (exp 1)) * ln x"
by (simp add: log_def)

lemma log_one [simp]: "log a 1 = 0"
by (simp add: log_def)

lemma log_eq_one [simp]: "[| 0 < a; a \<noteq> 1 |] ==> log a a = 1"
by (simp add: log_def)

lemma log_inverse:
     "[| 0 < a; a \<noteq> 1; 0 < x |] ==> log a (inverse x) = - log a x"
apply (rule_tac a1 = "log a x" in add_left_cancel [THEN iffD1])
apply (simp add: log_mult [symmetric])
done

lemma log_divide:
     "[|0 < a; a \<noteq> 1; 0 < x; 0 < y|] ==> log a (x/y) = log a x - log a y"
by (simp add: log_mult divide_inverse log_inverse)

lemma log_less_cancel_iff [simp]:
     "[| 1 < a; 0 < x; 0 < y |] ==> (log a x < log a y) = (x < y)"
apply safe
apply (rule_tac [2] powr_less_cancel)
apply (drule_tac a = "log a x" in powr_less_mono, auto)
done

lemma log_inj: assumes "1 < b" shows "inj_on (log b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y assume pos: "0 < x" "0 < y" and *: "log b x = log b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x < y" hence "log b x < log b y"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  next
    assume "y < x" hence "log b y < log b x"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  qed simp
qed

lemma log_le_cancel_iff [simp]:
     "[| 1 < a; 0 < x; 0 < y |] ==> (log a x \<le> log a y) = (x \<le> y)"
by (simp add: linorder_not_less [symmetric])


lemma powr_realpow: "0 < x ==> x powr (real n) = x^n"
  apply (induct n, simp)
  apply (subgoal_tac "real(Suc n) = real n + 1")
  apply (erule ssubst)
  apply (subst powr_add, simp, simp)
done

lemma powr_realpow2: "0 <= x ==> 0 < n ==> x^n = (if (x = 0) then 0
  else x powr (real n))"
  apply (case_tac "x = 0", simp, simp)
  apply (rule powr_realpow [THEN sym], simp)
done

lemma ln_powr: "0 < x ==> 0 < y ==> ln(x powr y) = y * ln x"
by (unfold powr_def, simp)

lemma log_powr: "0 < x ==> 0 \<le> y ==> log b (x powr y) = y * log b x"
  apply (case_tac "y = 0")
  apply force
  apply (auto simp add: log_def ln_powr field_simps)
done

lemma log_nat_power: "0 < x ==> log b (x^n) = real n * log b x"
  apply (subst powr_realpow [symmetric])
  apply (auto simp add: log_powr)
done

lemma ln_bound: "1 <= x ==> ln x <= x"
  apply (subgoal_tac "ln(1 + (x - 1)) <= x - 1")
  apply simp
  apply (rule ln_add_one_self_le_self, simp)
done

lemma powr_mono: "a <= b ==> 1 <= x ==> x powr a <= x powr b"
  apply (case_tac "x = 1", simp)
  apply (case_tac "a = b", simp)
  apply (rule order_less_imp_le)
  apply (rule powr_less_mono, auto)
done

lemma ge_one_powr_ge_zero: "1 <= x ==> 0 <= a ==> 1 <= x powr a"
  apply (subst powr_zero_eq_one [THEN sym])
  apply (rule powr_mono, assumption+)
done

lemma powr_less_mono2: "0 < a ==> 0 < x ==> x < y ==> x powr a <
    y powr a"
  apply (unfold powr_def)
  apply (rule exp_less_mono)
  apply (rule mult_strict_left_mono)
  apply (subst ln_less_cancel_iff, assumption)
  apply (rule order_less_trans)
  prefer 2
  apply assumption+
done

lemma powr_less_mono2_neg: "a < 0 ==> 0 < x ==> x < y ==> y powr a <
    x powr a"
  apply (unfold powr_def)
  apply (rule exp_less_mono)
  apply (rule mult_strict_left_mono_neg)
  apply (subst ln_less_cancel_iff)
  apply assumption
  apply (rule order_less_trans)
  prefer 2
  apply assumption+
done

lemma powr_mono2: "0 <= a ==> 0 < x ==> x <= y ==> x powr a <= y powr a"
  apply (case_tac "a = 0", simp)
  apply (case_tac "x = y", simp)
  apply (rule order_less_imp_le)
  apply (rule powr_less_mono2, auto)
done

lemma ln_powr_bound: "1 <= x ==> 0 < a ==> ln x <= (x powr a) / a"
  apply (rule mult_imp_le_div_pos)
  apply (assumption)
  apply (subst mult_commute)
  apply (subst ln_powr [THEN sym])
  apply auto
  apply (rule ln_bound)
  apply (erule ge_one_powr_ge_zero)
  apply (erule order_less_imp_le)
done

lemma ln_powr_bound2:
  assumes "1 < x" and "0 < a"
  shows "(ln x) powr a <= (a powr a) * x"
proof -
  from assms have "ln x <= (x powr (1 / a)) / (1 / a)"
    apply (intro ln_powr_bound)
    apply (erule order_less_imp_le)
    apply (rule divide_pos_pos)
    apply simp_all
    done
  also have "... = a * (x powr (1 / a))"
    by simp
  finally have "(ln x) powr a <= (a * (x powr (1 / a))) powr a"
    apply (intro powr_mono2)
    apply (rule order_less_imp_le, rule assms)
    apply (rule ln_gt_zero)
    apply (rule assms)
    apply assumption
    done
  also have "... = (a powr a) * ((x powr (1 / a)) powr a)"
    apply (rule powr_mult)
    apply (rule assms)
    apply (rule powr_gt_zero)
    done
  also have "(x powr (1 / a)) powr a = x powr ((1 / a) * a)"
    by (rule powr_powr)
  also have "... = x"
    apply simp
    apply (subgoal_tac "a ~= 0")
    using assms apply auto
    done
  finally show ?thesis .
qed

lemma tendsto_powr [tendsto_intros]:
  "\<lbrakk>(f ---> a) F; (g ---> b) F; 0 < a\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x powr g x) ---> a powr b) F"
  unfolding powr_def by (intro tendsto_intros)

(* FIXME: generalize by replacing d by with g x and g ---> d? *)
lemma tendsto_zero_powrI:
  assumes "eventually (\<lambda>x. 0 < f x ) F" and "(f ---> 0) F"
  assumes "0 < d"
  shows "((\<lambda>x. f x powr d) ---> 0) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  def Z \<equiv> "e powr (1 / d)"
  with `0 < e` have "0 < Z" by simp
  with assms have "eventually (\<lambda>x. 0 < f x \<and> dist (f x) 0 < Z) F"
    by (intro eventually_conj tendstoD)
  moreover
  from assms have "\<And>x. 0 < x \<and> dist x 0 < Z \<Longrightarrow> x powr d < Z powr d"
    by (intro powr_less_mono2) (auto simp: dist_real_def)
  with assms `0 < e` have "\<And>x. 0 < x \<and> dist x 0 < Z \<Longrightarrow> dist (x powr d) 0 < e"
    unfolding dist_real_def Z_def by (auto simp: powr_powr)
  ultimately
  show "eventually (\<lambda>x. dist (f x powr d) 0 < e) F" by (rule eventually_elim1)
qed

lemma tendsto_neg_powr:
  assumes "s < 0" and "real_tendsto_inf f F"
  shows "((\<lambda>x. f x powr s) ---> 0) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  def Z \<equiv> "e powr (1 / s)"
  from assms have "eventually (\<lambda>x. Z < f x) F" by (simp add: real_tendsto_inf_def)
  moreover
  from assms have "\<And>x. Z < x \<Longrightarrow> x powr s < Z powr s"
    by (auto simp: Z_def intro!: powr_less_mono2_neg)
  with assms `0 < e` have "\<And>x. Z < x \<Longrightarrow> dist (x powr s) 0 < e"
    by (simp add: powr_powr Z_def dist_real_def)
  ultimately
  show "eventually (\<lambda>x. dist (f x powr s) 0 < e) F" by (rule eventually_elim1)
qed

end
