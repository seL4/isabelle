(*  Title:      HOL/GroupTheory/Exponent
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

(*** prime theorems ***)

val prime_def = thm "prime_def";

Goalw [prime_def] "p\\<in>prime ==> 1' < p";
by (force_tac (claset(), simpset() addsimps []) 1); 
qed "prime_imp_one_less";

Goal "(p\\<in>prime) = (1'<p & (\\<forall>a b. p dvd a*b --> (p dvd a) | (p dvd b)))";
by (auto_tac (claset(), simpset() addsimps [prime_imp_one_less]));  
by (blast_tac (claset() addSDs [thm "prime_dvd_mult"]) 1);
by (auto_tac (claset(), simpset() addsimps [prime_def]));  
by (etac dvdE 1); 
by (case_tac "k=0" 1);
by (Asm_full_simp_tac 1); 
by (dres_inst_tac [("x","m")] spec 1); 
by (dres_inst_tac [("x","k")] spec 1);
by (asm_full_simp_tac
    (simpset() addsimps [dvd_mult_cancel1, dvd_mult_cancel2]) 1);  
by Auto_tac; 
qed "prime_iff";

Goal "p\\<in>prime ==> 0 < p^a";
by (rtac zero_less_power 1);
by (force_tac (claset(), simpset() addsimps [prime_iff]) 1);
qed "zero_less_prime_power";


(*First some things about HOL and sets *)
val [p1] = goal (the_context()) "(P x y) ==> ( (x, y)\\<in>{(a,b). P a b})";
by (rtac CollectI 1);
by (rewrite_goals_tac [split RS eq_reflection]);
by (rtac p1 1);
qed "CollectI_prod";

val [p1] = goal (the_context()) "( (x, y)\\<in>{(a,b). P a b}) ==> (P x y)";
by (res_inst_tac [("c1","P")] (split RS subst) 1);
by (res_inst_tac [("a","(x,y)")] CollectD 1);
by (rtac p1 1);
qed "CollectD_prod";

val [p1] = goal (the_context()) "(P x y z v) ==> ( (x, y, z, v)\\<in>{(a,b,c,d). P a b c d})";
by (rtac CollectI_prod 1);
by (rewrite_goals_tac [split RS eq_reflection]);
by (rtac p1 1);
qed "CollectI_prod4";

Goal "( (x, y, z, v)\\<in>{(a,b,c,d). P a b c d}) ==> (P x y z v)";
by Auto_tac; 
qed "CollectD_prod4";



val [p1] = goal (the_context()) "x\\<in>{y. P(y) & Q(y)} ==> P(x)";
by (res_inst_tac [("Q","Q x"),("P", "P x")] conjE 1);
by (assume_tac 2);
by (res_inst_tac [("a", "x")] CollectD 1);
by (rtac p1 1);
qed "subset_lemma1";

val [p1,p2] = goal (the_context()) "[|P == Q; P|] ==> Q";
by (fold_goals_tac [p1]);
by (rtac p2 1);
qed "apply_def";

Goal "S \\<noteq> {} ==> \\<exists>x. x\\<in>S";
by Auto_tac;  
qed "NotEmpty_ExEl";

Goal "\\<exists>x. x: S ==> S \\<noteq> {}";
by Auto_tac;  
qed "ExEl_NotEmpty";


(* The following lemmas are needed for existsM1inM *)

Goal "[| {} \\<notin> A; M\\<in>A |] ==> M \\<noteq> {}";
by Auto_tac;  
qed "MnotEqempty";

val [p1] = goal (the_context()) "\\<exists>g \\<in> A. x = P(g) ==> \\<exists>g \\<in> A. P(g) = x";
by (rtac bexE 1);
by (rtac p1 1);
by (rtac bexI 1);
by (rtac sym 1);
by (assume_tac 1);
by (assume_tac 1);
qed "bex_sym";

Goalw [equiv_def,quotient_def,sym_def,trans_def]
     "[| equiv A r; C\\<in>A // r |] ==> \\<forall>x \\<in> C. \\<forall>y \\<in> C. (x,y)\\<in>r";
by (Blast_tac 1); 
qed "ElemClassEquiv";

Goalw [equiv_def,quotient_def,sym_def,trans_def]
     "[|equiv A r; M\\<in>A // r; M1\\<in>M; (M1, M2)\\<in>r |] ==> M2\\<in>M";
by (Blast_tac 1); 
qed "EquivElemClass";

Goal "[| 0 < c; a <= b |] ==> a <= b * (c::nat)";
by (res_inst_tac [("P","%x. x <= b * c")] subst 1);
by (rtac mult_1_right 1);
by (rtac mult_le_mono 1);
by Auto_tac; 
qed "le_extend_mult";


Goal "0 < card(S) ==> S \\<noteq> {}";
by (force_tac (claset(), simpset() addsimps [card_empty]) 1); 
qed "card_nonempty";

Goal "[| x \\<notin> F; \
\        \\<forall>c1\\<in>insert x F. \\<forall>c2 \\<in> insert x F. c1 \\<noteq> c2 --> c1 \\<inter> c2 = {}|]\
\     ==> x \\<inter> \\<Union> F = {}";
by Auto_tac;  
qed "insert_partition";

(* main cardinality theorem *)
Goal "finite C ==> \
\       finite (\\<Union> C) --> \
\       (\\<forall>c\\<in>C. card c = k) -->  \
\       (\\<forall>c1 \\<in> C. \\<forall>c2 \\<in> C. c1 \\<noteq> c2 --> c1 \\<inter> c2 = {}) --> \
\       k * card(C) = card (\\<Union> C)";
by (etac finite_induct 1);
by (Asm_full_simp_tac 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [card_insert_disjoint, card_Un_disjoint, 
            insert_partition, inst "B" "\\<Union>(insert x F)" finite_subset]) 1);
qed_spec_mp "card_partition";

Goal "[| finite S; S \\<noteq> {} |] ==> 0 < card(S)";
by (swap_res_tac [card_0_eq RS iffD1] 1);
by Auto_tac;  
qed "zero_less_card_empty";


Goal "[| p*k dvd m*n;  p\\<in>prime |] \
\     ==> (\\<exists>x. k dvd x*n & m = p*x) | (\\<exists>y. k dvd m*y & n = p*y)";
by (asm_full_simp_tac (simpset() addsimps [prime_iff]) 1);
by (ftac dvd_mult_left 1);
by (subgoal_tac "p dvd m | p dvd n" 1);
by (Blast_tac 2);
by (etac disjE 1);
by (rtac disjI1 1); 
by (rtac disjI2 2);
by (eres_inst_tac [("n","m")] dvdE 1);
by (eres_inst_tac [("n","n")] dvdE 2);
by Auto_tac;
by (res_inst_tac [("k","p")] dvd_mult_cancel 2); 
by (res_inst_tac [("k","p")] dvd_mult_cancel 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps mult_ac))); 
qed "prime_dvd_cases";


Goal "p\\<in>prime \
\     ==> \\<forall>m n. p^c dvd m*n --> \
\         (\\<forall>a b. a+b = Suc c --> p^a dvd m | p^b dvd n)";
by (induct_tac "c" 1);
 by (Clarify_tac 1);
 by (case_tac "a" 1); 
  by (Asm_full_simp_tac 1); 
 by (Asm_full_simp_tac 1);
(*inductive step*)
by (Asm_full_simp_tac 1);  
by (Clarify_tac 1); 
by (etac (prime_dvd_cases RS disjE) 1); 
by (assume_tac 1); 
by Auto_tac;  
(*case 1: p dvd m*)
 by (case_tac "a" 1);
  by (Asm_full_simp_tac 1); 
 by (Clarify_tac 1); 
 by (dtac spec 1 THEN dtac spec 1 THEN  mp_tac 1);
 by (dres_inst_tac [("x","nat")] spec 1);
 by (dres_inst_tac [("x","b")] spec 1); 
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addIs [dvd_refl, mult_dvd_mono]) 1);
(*case 2: p dvd n*)
by (case_tac "b" 1);
 by (Asm_full_simp_tac 1); 
by (Clarify_tac 1); 
by (dtac spec 1 THEN dtac spec 1 THEN  mp_tac 1);
by (dres_inst_tac [("x","a")] spec 1); 
by (dres_inst_tac [("x","nat")] spec 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [dvd_refl, mult_dvd_mono]) 1);
qed_spec_mp "prime_power_dvd_cases";

(*needed in this form in Sylow.ML*)
Goal "[| p \\<in> prime; ~ (p ^ (Suc r) dvd n);  p^(a+r) dvd n*k |] \
\     ==> p ^ a dvd k";
by (dres_inst_tac [("a","Suc r"), ("b","a")] prime_power_dvd_cases 1);
by (assume_tac 1);  
by Auto_tac;  
qed "div_combine";

(*Lemma for power_dvd_bound*)
Goal "1' < p ==> Suc n <= p^n";
by (induct_tac "n" 1);
by (Asm_simp_tac 1); 
by (Asm_full_simp_tac 1); 
by (subgoal_tac "2*n + #2 <= p * p^n" 1);
by (Asm_full_simp_tac 1); 
by (subgoal_tac "#2 * p^n <= p * p^n" 1);
(*?arith_tac should handle all of this!*)
by (rtac order_trans 1); 
by (assume_tac 2); 
by (dres_inst_tac [("k","#2")] mult_le_mono2 1); 
by (Asm_full_simp_tac 1); 
by (rtac mult_le_mono1 1); 
by (Asm_full_simp_tac 1); 
qed "Suc_le_power";

(*An upper bound for the n such that p^n dvd a: needed for GREATEST to exist*)
Goal "[|p^n dvd a;  1' < p;  0 < a|] ==> n < a";
by (dtac dvd_imp_le 1); 
by (dres_inst_tac [("n","n")] Suc_le_power 2); 
by Auto_tac;  
qed "power_dvd_bound";


(*** exponent theorems ***)

Goal "[|p^k dvd n;  p\\<in>prime;  0<n|] ==> k <= exponent p n";
by (asm_full_simp_tac (simpset() addsimps [exponent_def]) 1); 
by (etac (thm "Greatest_le") 1);
by (blast_tac (claset() addDs [prime_imp_one_less, power_dvd_bound]) 1);  
qed_spec_mp "exponent_ge";

Goal "0<s ==> (p ^ exponent p s) dvd s";
by (simp_tac (simpset() addsimps [exponent_def]) 1); 
by (Clarify_tac 1); 
by (res_inst_tac [("k","0")] (thm "GreatestI") 1);
by (blast_tac (claset() addDs [prime_imp_one_less, power_dvd_bound]) 2);  
by (Asm_full_simp_tac 1); 
qed "power_exponent_dvd";

Goal "[|(p * p ^ exponent p s) dvd s;  p\\<in>prime |] ==> s=0";
by (subgoal_tac "p ^ Suc(exponent p s) dvd s" 1);
by (Asm_full_simp_tac 2);
by (rtac ccontr 1); 
by (dtac exponent_ge 1); 
by Auto_tac;  
qed "power_Suc_exponent_Not_dvd";

Goal "p\\<in>prime ==> exponent p (p^a) = a";
by (asm_simp_tac (simpset() addsimps [exponent_def]) 1);
by (rtac (thm "Greatest_equality") 1); 
by (Asm_full_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [prime_imp_one_less, power_dvd_imp_le]) 1); 
qed "exponent_power_eq";
Addsimps [exponent_power_eq];

Goal "!r::nat. (p^r dvd a) = (p^r dvd b) ==> exponent p a = exponent p b";
by (asm_simp_tac (simpset() addsimps [exponent_def]) 1); 
qed "exponent_equalityI";

Goal "p \\<notin> prime ==> exponent p s = 0";
by (asm_simp_tac (simpset() addsimps [exponent_def]) 1); 
qed "exponent_eq_0";
Addsimps [exponent_eq_0];


(* exponent_mult_add, easy inclusion.  Could weaken p\\<in>prime to 1'<p *)
Goal "[| 0 < a; 0 < b |]  \
\     ==> (exponent p a) + (exponent p b) <= exponent p (a * b)";
by (case_tac "p \\<in> prime" 1);
by (rtac exponent_ge 1);
by (auto_tac (claset(), simpset() addsimps [power_add]));   
by (blast_tac (claset() addIs [prime_imp_one_less, power_exponent_dvd, 
                               mult_dvd_mono]) 1); 
qed "exponent_mult_add1";

(* exponent_mult_add, opposite inclusion *)
Goal "[| 0 < a; 0 < b |] \
\     ==> exponent p (a * b) <= (exponent p a) + (exponent p b)";
by (case_tac "p\\<in>prime" 1);
by (rtac leI 1); 
by (Clarify_tac 1); 
by (cut_inst_tac [("p","p"),("s","a*b")] power_exponent_dvd 1);
by Auto_tac;  
by (subgoal_tac "p ^ (Suc (exponent p a + exponent p b)) dvd a * b" 1);
by (rtac (le_imp_power_dvd RS dvd_trans) 2);
  by (assume_tac 3);
 by (Asm_full_simp_tac 2);
by (forw_inst_tac [("a","Suc (exponent p a)"), ("b","Suc (exponent p b)")] 
    prime_power_dvd_cases 1);
 by (assume_tac 1 THEN Force_tac 1);
by (Asm_full_simp_tac 1); 
by (blast_tac (claset() addDs [power_Suc_exponent_Not_dvd]) 1); 
qed "exponent_mult_add2";

Goal "[| 0 < a; 0 < b |] \
\     ==> exponent p (a * b) = (exponent p a) + (exponent p b)";
by (blast_tac (claset() addIs [exponent_mult_add1, exponent_mult_add2, 
                               order_antisym]) 1); 
qed "exponent_mult_add";


Goal "~ (p dvd n) ==> exponent p n = 0";
by (case_tac "exponent p n" 1);
by (Asm_full_simp_tac 1); 
by (case_tac "n" 1);
by (Asm_full_simp_tac 1);
by (cut_inst_tac [("s","n"),("p","p")] power_exponent_dvd 1);
by (auto_tac (claset() addDs [dvd_mult_left], simpset()));  
qed "not_divides_exponent_0";

Goal "exponent p 1' = 0";
by (case_tac "p \\<in> prime" 1);
by (auto_tac (claset(), 
              simpset() addsimps [prime_iff, not_divides_exponent_0]));
qed "exponent_1_eq_0";
Addsimps [exponent_1_eq_0];


(*** Lemmas for the main combinatorial argument ***)

Goal "[| 0 < (m::nat); 0<k; k < p^a; (p^r) dvd (p^a)* m - k |] ==> r <= a";
by (rtac notnotD 1);
by (rtac notI 1);
by (dtac (leI RSN (2, contrapos_nn) RS notnotD) 1);
by (assume_tac 1);
by (dres_inst_tac [("m","a")] less_imp_le 1);
by (dtac le_imp_power_dvd 1);
by (dres_inst_tac [("n","p ^ r")] dvd_trans 1);
by (assume_tac 1);
by (forw_inst_tac [("m","k")] less_imp_le 1);
by (dres_inst_tac [("c","m")] le_extend_mult 1);
by (assume_tac 1);
by (dres_inst_tac [("k","p ^ a"),("m","(p ^ a) * m")] dvd_diffD1 1);
by (assume_tac 2);
by (rtac (dvd_refl RS dvd_mult2) 1);
by (dres_inst_tac [("n","k")] dvd_imp_le 1);
by Auto_tac;
qed "p_fac_forw_lemma";

Goal "[| 0 < (m::nat); 0<k; k < p^a; (p^r) dvd (p^a)* m - k |] \
\     ==> (p^r) dvd (p^a) - k";
by (forw_inst_tac [("k1","k"),("i","p")]
     (p_fac_forw_lemma RS le_imp_power_dvd) 1);
by Auto_tac;
by (subgoal_tac "p^r dvd p^a*m" 1);
 by (blast_tac (claset() addIs [dvd_mult2]) 2);
by (dtac dvd_diffD1 1);
  by (assume_tac 1);
 by (blast_tac (claset() addIs [dvd_diff]) 2);
by (dtac less_imp_Suc_add 1);
by Auto_tac;
qed "p_fac_forw";


Goal "[| 0 < (k::nat); k < p^a; 0 < p; (p^r) dvd (p^a) - k |] ==> r <= a";
by (res_inst_tac [("m","1'")] p_fac_forw_lemma 1);
by Auto_tac;
qed "r_le_a_forw";

Goal "[| 0<m; 0<k; 0 < (p::nat);  k < p^a;  (p^r) dvd p^a - k |] \
\     ==> (p^r) dvd (p^a)*m - k";
by (forw_inst_tac [("k1","k"),("i","p")] (r_le_a_forw RS le_imp_power_dvd) 1);
by Auto_tac;
by (subgoal_tac "p^r dvd p^a*m" 1);
 by (blast_tac (claset() addIs [dvd_mult2]) 2);
by (dtac dvd_diffD1 1);
  by (assume_tac 1);
 by (blast_tac (claset() addIs [dvd_diff]) 2);
by (dtac less_imp_Suc_add 1);
by Auto_tac;
qed "p_fac_backw";

Goal "[| 0<m; 0<k; 0 < (p::nat);  k < p^a |] \
\     ==> exponent p (p^a * m - k) = exponent p (p^a - k)";
by (blast_tac (claset() addIs [exponent_equalityI, p_fac_forw, 
                               p_fac_backw]) 1);
qed "exponent_p_a_m_k_equation";

(*Suc rules that we have to delete from the simpset*)
val bad_Sucs = [binomial_Suc_Suc, mult_Suc, mult_Suc_right];

(*The bound K is needed; otherwise it's too weak to be used.*)
Goal "[| \\<forall>i. Suc i < K --> exponent p (Suc i) = exponent p (Suc(j+i))|] \
\     ==> k<K --> exponent p ((j+k) choose k) = 0";
by (case_tac "p \\<in> prime" 1);
by (Asm_simp_tac 2);
by (induct_tac "k" 1);
by (Simp_tac 1);
(*induction step*)
by (subgoal_tac "0 < (Suc(j+n) choose Suc n)" 1);
 by (simp_tac (simpset() addsimps [zero_less_binomial_iff]) 2);
by (Clarify_tac 1);
by (subgoal_tac
     "exponent p ((Suc(j+n) choose Suc n) * Suc n) = exponent p (Suc n)" 1);
(*First, use the assumed equation.  We simplify the LHS to
  exponent p (Suc (j + n) choose Suc n) + exponent p (Suc n);
  the common terms cancel, proving the conclusion.*)
 by (asm_full_simp_tac (simpset() delsimps bad_Sucs
				  addsimps [exponent_mult_add]) 1);
(*Establishing the equation requires first applying Suc_times_binomial_eq...*)
by (asm_full_simp_tac (simpset() delsimps bad_Sucs
				 addsimps [Suc_times_binomial_eq RS sym]) 1);
(*...then exponent_mult_add and the quantified premise.*)
by (asm_full_simp_tac (simpset() delsimps bad_Sucs
          	 addsimps [zero_less_binomial_iff, exponent_mult_add]) 1);
qed_spec_mp "p_not_div_choose_lemma";

(*The lemma above, with two changes of variables*)
Goal "[| k<K;  k<=n;  \
\      \\<forall>j. 0<j & j<K --> exponent p (n - k + (K - j)) = exponent p (K - j)|] \
\     ==> exponent p (n choose k) = 0";
by (cut_inst_tac [("j","n-k"),("k","k"),("p","p")] p_not_div_choose_lemma 1);
by (assume_tac 2);
by (Asm_full_simp_tac 2);
by (Clarify_tac 1); 
by (dres_inst_tac [("x","K - Suc i")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [Suc_diff_le]) 1);
qed "p_not_div_choose";


Goal "0 < m ==> exponent p ((p^a * m - 1') choose (p^a - 1')) = 0";
by (case_tac "p \\<in> prime" 1);
by (Asm_simp_tac 2);
by (forw_inst_tac [("a","a")] zero_less_prime_power 1);
by (res_inst_tac [("K","p^a")] p_not_div_choose 1);
   by (Asm_full_simp_tac 1);
  by (Asm_full_simp_tac 1);
 by (case_tac "m" 1);
  by (case_tac "p^a" 2);
   by Auto_tac;
(*now the hard case, simplified to
    exponent p (Suc (p ^ a * m + i - p ^ a)) = exponent p (Suc i) *)
by (subgoal_tac "0<p" 1);
 by (force_tac (claset() addSDs [prime_imp_one_less], simpset()) 2);
by (stac exponent_p_a_m_k_equation 1);
by Auto_tac;
qed "const_p_fac_right";

Goal "0 < m ==> exponent p (((p^a) * m) choose p^a) = exponent p m";
by (case_tac "p \\<in> prime" 1);
by (Asm_simp_tac 2);
by (forw_inst_tac [("a","a")] zero_less_prime_power 1);
by (subgoal_tac "0 < p^a * m & p^a <= p^a * m" 1);
by (Asm_full_simp_tac 2);
(*A similar trick to the one used in p_not_div_choose_lemma:
  insert an equation; use exponent_mult_add on the LHS; on the RHS, first
  transform the binomial coefficient, then use exponent_mult_add.*)
by (subgoal_tac
    "exponent p ((((p^a) * m) choose p^a) * p^a) = a + exponent p m" 1);
by (asm_full_simp_tac (simpset() delsimps bad_Sucs
	 addsimps [zero_less_binomial_iff, exponent_mult_add, prime_iff]) 1);
(*one subgoal left!*)
by (stac times_binomial_minus1_eq 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (stac exponent_mult_add 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [zero_less_binomial_iff]) 1);
by (arith_tac 1);
by (asm_simp_tac (simpset() delsimps bad_Sucs
                         addsimps [exponent_mult_add, const_p_fac_right]) 1);
qed "const_p_fac";  
