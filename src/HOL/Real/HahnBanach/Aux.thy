(*  Title:      HOL/Real/HahnBanach/Aux.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory Aux = Real + Zorn:;

lemmas [intro!!] = chainD; 
lemmas chainE2 = chainD2 [elimify];
lemmas [intro!!] = isLub_isUb;


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
  have "x + - y = x - y"; by simp;
  also; have "... = 0r"; .;
  finally; have "x + - y = 0r"; .;
  hence "x = - (- y)"; by (rule real_add_minus_eq_minus);
  also; have "... = y"; by simp;
  finally; show "x = y"; .;
qed;

lemma rabs_minus_one: "rabs (- 1r) = 1r"; 
proof -; 
  have "rabs (- 1r) = - (- 1r)"; 
  proof (rule rabs_minus_eqI2);
    show "-1r < 0r";
      by (rule real_minus_zero_less_iff[RS iffD1], simp, rule real_zero_less_one);
  qed;
  also; have "... = 1r"; by simp; 
  finally; show ?thesis; by simp;
qed;

lemma real_mult_le_le_mono2: "[| 0r <= z; x <= y |] ==> x * z <= y * z";
proof -;
  assume gz: "0r <= z" and ineq: "x <= y";
  hence "x < y | x = y"; by (force simp add: order_le_less);
  thus ?thesis;
  proof (elim disjE); 
    assume "x < y"; show ?thesis; by (rule real_mult_le_less_mono1);
  next; 
    assume "x = y"; 
    hence "x * z <= y * z"; by simp;
    thus ?thesis; by fast;
  qed;
qed;

lemma real_mult_less_le_anti: "[| z < 0r; x <= y |] ==> z * y <= z * x";
proof -;
  assume lz: "z < 0r" and ineq: "x <= y";
  hence "0r < - z"; by simp;
  hence "0r <= - z"; by (rule real_less_imp_le);
  with ineq; have "(- z) * x <= (- z) * y"; by (simp add: real_mult_le_le_mono1);
  hence  "- (z * x) <= - (z * y)"; by (simp add: real_minus_mult_eq1 [RS sym]);
  thus ?thesis; by simp;
qed;

lemma real_mult_less_le_mono: "[| 0r < z; x <= y |] ==> z * x <= z * y";
proof -; 
  assume gt: "0r < z" and ineq: "x <= y";
  from gt; have "0r <= z"; by (rule real_less_imp_le);
  thus ?thesis; by (rule real_mult_le_le_mono1); 
qed;

lemma real_mult_diff_distrib: "a * (- x - (y::real)) = - a * x - a * y";
proof -;
  have "- x - (y::real) = - x + - y"; by simp;
  also; have "a * ... = a * - x + a * - y"; by (simp add: real_add_mult_distrib2);
  also; have "... = - a * x - a * y"; 
    by (simp add: real_minus_mult_eq2 [RS sym] real_minus_mult_eq1 [RS sym]);
  finally; show ?thesis; .;
qed;

lemma real_mult_diff_distrib2: "a * (x - (y::real)) = a * x - a * y";
proof -; 
  have "x - (y::real) = x + - y"; by simp;
  also; have "a * ... = a * x + a * - y"; by (simp add: real_add_mult_distrib2);
  also; have "... = a * x - a * y";   
    by (simp add: real_minus_mult_eq2 [RS sym] real_minus_mult_eq1 [RS sym]);
  finally; show ?thesis; .;
qed;

lemma le_noteq_imp_less: "[|x <= (r::'a::order); x ~= r |] ==> x < r";
proof -;
  assume "x <= (r::'a::order)" and ne:"x ~= r";
  then; have "x < r | x = r"; by (simp add: order_le_less);
  with ne; show ?thesis; by simp;
qed;

lemma minus_le: "- (x::real) <= y ==> - y <= x";
proof -; 
  assume "- x <= y";
  hence "- x < y | - x = y"; by (rule order_le_less [RS iffD1]);
  thus "-y <= x";
  proof;
     assume "- x < y"; show ?thesis; 
     proof -; 
       have "- y < - (- x)"; by (rule real_less_swap_iff [RS iffD1]); 
       hence "- y < x"; by simp;
       thus ?thesis; by (rule real_less_imp_le);
    qed;
  next; 
     assume "- x = y"; thus ?thesis; by force;
  qed;
qed;

lemma rabs_interval_iff_1: "(rabs (x::real) <= r) = (-r <= x & x <= r)";
proof (rule case_split [of "rabs x = r"]);
  assume  a: "rabs x = r";
  show ?thesis; 
  proof;
    assume "rabs x <= r";
    show "- r <= x & x <= r";
    proof;
      have "- x <= rabs x"; by (rule rabs_ge_minus_self);
      with a; have "- x <= r"; by simp;
      thus "- r <= x"; by (simp add : minus_le [of "x" "r"]);
      have "x <= rabs x"; by (rule rabs_ge_self); 
      with a; show "x <= r"; by simp; 
    qed;
  next; 
    assume "- r <= x & x <= r";
    with a; show "rabs x <= r"; by fast;
  qed;
next;   
  assume "rabs x ~= r";
  show ?thesis; 
  proof;
    assume "rabs x <= r"; 
    have "rabs x < r"; by (rule conjI [RS real_less_le [RS iffD2]]);
    hence "- r < x & x < r"; by (rule rabs_interval_iff [RS iffD1]);
    thus "- r <= x & x <= r";
    proof(elim conjE, intro conjI); 
      assume "- r < x";
      show "- r <= x"; by (rule real_less_imp_le); 
      assume "x < r";
      show "x <= r"; by (rule real_less_imp_le); 
    qed;
  next;
    assume "- r <= x & x <= r";
    thus "rabs x <= r";
    proof; 
      assume a: "- r <= x" and "x <= r";
      show ?thesis; 
      proof (rule rabs_disj [RS disjE, of x]);
        assume "rabs x = x";
        thus ?thesis; by simp; 
      next; 
        assume "rabs x = - x";
        with a minus_le [of r x]; show ?thesis; by simp;
      qed;
    qed;
  qed;
qed;


lemma real_diff_ineq_swap: "(d::real) - b <= c + a ==> - a - b <= c - d";
proof -;
  assume "d - b <= c + (a::real)";
  have "- a - b = d - b + (- d - a)"; by (simp!);
  also; have "... <= c + a + (- d - a)"; by (rule real_add_le_mono1);
  also; have "... = c - d"; by (simp!);
  finally; show "- a - b <= c - d"; .;
qed;


lemma set_less_imp_diff_not_empty: "H < E ==> EX x0:E. x0 ~: H";
 by (force simp add: psubset_eq);


end;
