(*  Title:      HOL/Real/HahnBanach/Aux.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Auxiliary theorems *};

theory Aux = Real + Zorn:;

lemmas [intro!!] = chainD; 
lemmas chainE2 = chainD2 [elimify];
lemmas [intro!!] = isLub_isUb;

theorem real_linear_split:
 "[| x < a ==> Q; x = a ==> Q; a < (x::real) ==> Q |] ==> Q";
  by (rule real_linear [of x a, elimify], elim disjE, force+);

theorem linorder_linear_split: 
"[| x < a ==> Q; x = a ==> Q; a < (x::'a::linorder) ==> Q |] ==> Q";
  by (rule linorder_less_linear [of x a, elimify], elim disjE, force+);

lemma le_max1: "x <= max x (y::'a::linorder)";
  by (simp add: le_max_iff_disj[of x x y]);

lemma le_max2: "y <= max x (y::'a::linorder)"; 
  by (simp add: le_max_iff_disj[of y x y]);

lemma lt_imp_not_eq: "x < (y::'a::order) ==> x ~= y"; 
  by (rule order_less_le[RS iffD1, RS conjunct2]);

lemma Int_singletonD: "[| A Int B = {v}; x:A; x:B |] ==> x = v";
  by (fast elim: equalityE);

lemma real_add_minus_eq: "x - y = 0r ==> x = y";
proof -;
  assume "x - y = 0r";
  have "x + - y = 0r"; by (simp!);
  hence "x = - (- y)"; by (rule real_add_minus_eq_minus);
  also; have "... = y"; by simp;
  finally; show "?thesis"; .;
qed;

lemma rabs_minus_one: "rabs (- 1r) = 1r"; 
proof -; 
  have "-1r < 0r"; 
    by (rule real_minus_zero_less_iff[RS iffD1], simp, 
        rule real_zero_less_one);
  hence "rabs (- 1r) = - (- 1r)"; 
    by (rule rabs_minus_eqI2);
  also; have "... = 1r"; by simp; 
  finally; show ?thesis; .;
qed;

lemma real_mult_le_le_mono2: 
  "[| 0r <= z; x <= y |] ==> x * z <= y * z";
proof -;
  assume "0r <= z" "x <= y";
  hence "x < y | x = y"; by (force simp add: order_le_less);
  thus ?thesis;
  proof (elim disjE); 
    assume "x < y"; show ?thesis; by (rule real_mult_le_less_mono1);
  next; 
    assume "x = y"; thus ?thesis;; by simp;
  qed;
qed;

lemma real_mult_less_le_anti: 
  "[| z < 0r; x <= y |] ==> z * y <= z * x";
proof -;
  assume "z < 0r" "x <= y";
  hence "0r < - z"; by simp;
  hence "0r <= - z"; by (rule real_less_imp_le);
  hence "(- z) * x <= (- z) * y"; 
    by (rule real_mult_le_le_mono1);
  hence  "- (z * x) <= - (z * y)"; 
    by (simp only: real_minus_mult_eq1);
  thus ?thesis; by simp;
qed;

lemma real_mult_less_le_mono: 
  "[| 0r < z; x <= y |] ==> z * x <= z * y";
proof -; 
  assume "0r < z" "x <= y";
  have "0r <= z"; by (rule real_less_imp_le);
  thus ?thesis; by (rule real_mult_le_le_mono1); 
qed;

lemma real_mult_diff_distrib: 
  "a * (- x - (y::real)) = - a * x - a * y";
proof -;
  have "- x - y = - x + - y"; by simp;
  also; have "a * ... = a * - x + a * - y"; 
    by (simp only: real_add_mult_distrib2);
  also; have "... = - a * x - a * y"; 
    by (simp add: real_minus_mult_eq2 [RS sym] real_minus_mult_eq1);
  finally; show ?thesis; .;
qed;

lemma real_mult_diff_distrib2: "a * (x - (y::real)) = a * x - a * y";
proof -; 
  have "x - y = x + - y"; by simp;
  also; have "a * ... = a * x + a * - y"; 
    by (simp only: real_add_mult_distrib2);
  also; have "... = a * x - a * y";   
    by (simp add: real_minus_mult_eq2 [RS sym] real_minus_mult_eq1);
  finally; show ?thesis; .;
qed;

lemma le_noteq_imp_less: 
  "[| x <= (r::'a::order); x ~= r |] ==> x < r";
proof -;
  assume "x <= (r::'a::order)" and ne:"x ~= r";
  then; have "x < r | x = r"; by (simp add: order_le_less);
  with ne; show ?thesis; by simp;
qed;

lemma real_minus_le: "- (x::real) <= y ==> - y <= x";
  by simp;

lemma real_diff_ineq_swap: 
  "(d::real) - b <= c + a ==> - a - b <= c - d";
  by simp;

lemma set_less_imp_diff_not_empty: "H < E ==> EX x0:E. x0 ~: H";
 by (force simp add: psubset_eq);

end;