(*  Title       : Log.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
*)

header{*Logarithms: Standard Version*}

theory Log = Transcendental:

constdefs

  powr  :: "[real,real] => real"     (infixr "powr" 80)
    --{*exponentation with real exponent*}
    "x powr a == exp(a * ln x)"

  log :: "[real,real] => real"
    --{*logarithm of @[term x} to base @[term a}*}
    "log a x == ln x / ln a"



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

lemma powr_not_zero [simp]: "x powr a \<noteq> 0"
by (simp add: powr_def)

lemma powr_divide:
     "[| 0 < x; 0 < y |] ==> (x / y) powr a = (x powr a)/(y powr a)"
apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
done

lemma powr_add: "x powr (a + b) = (x powr a) * (x powr b)"
by (simp add: powr_def exp_add [symmetric] left_distrib)

lemma powr_powr: "(x powr a) powr b = x powr (a * b)"
by (simp add: powr_def)

lemma powr_powr_swap: "(x powr a) powr b = (x powr b) powr a"
by (simp add: powr_powr real_mult_commute)

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

lemma log_le_cancel_iff [simp]:
     "[| 1 < a; 0 < x; 0 < y |] ==> (log a x \<le> log a y) = (x \<le> y)"
by (simp add: linorder_not_less [symmetric])



ML
{*
val powr_one_eq_one = thm "powr_one_eq_one";
val powr_zero_eq_one = thm "powr_zero_eq_one";
val powr_one_gt_zero_iff = thm "powr_one_gt_zero_iff";
val powr_mult = thm "powr_mult";
val powr_gt_zero = thm "powr_gt_zero";
val powr_not_zero = thm "powr_not_zero";
val powr_divide = thm "powr_divide";
val powr_add = thm "powr_add";
val powr_powr = thm "powr_powr";
val powr_powr_swap = thm "powr_powr_swap";
val powr_minus = thm "powr_minus";
val powr_minus_divide = thm "powr_minus_divide";
val powr_less_mono = thm "powr_less_mono";
val powr_less_cancel = thm "powr_less_cancel";
val powr_less_cancel_iff = thm "powr_less_cancel_iff";
val powr_le_cancel_iff = thm "powr_le_cancel_iff";
val log_ln = thm "log_ln";
val powr_log_cancel = thm "powr_log_cancel";
val log_powr_cancel = thm "log_powr_cancel";
val log_mult = thm "log_mult";
val log_eq_div_ln_mult_log = thm "log_eq_div_ln_mult_log";
val log_base_10_eq1 = thm "log_base_10_eq1";
val log_base_10_eq2 = thm "log_base_10_eq2";
val log_one = thm "log_one";
val log_eq_one = thm "log_eq_one";
val log_inverse = thm "log_inverse";
val log_divide = thm "log_divide";
val log_less_cancel_iff = thm "log_less_cancel_iff";
val log_le_cancel_iff = thm "log_le_cancel_iff";
*}

end
