(*  Title:	Chinese.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

The Chinese Remainder Theorem for an arbitrary finite number of equations. 
(The one-equation case is included in 'IntPrimes')

Uses functions for indexing. Maybe 'funprod' and 'funsum'
should be based on general 'fold' on indices?
*)


(*** extra nat theorems ***)

Goal "[| k <= i; i <= k |] ==> i = (k::nat)";
by (rtac diffs0_imp_equal 1);
by (ALLGOALS (stac diff_is_0_eq)); 
by Auto_tac;
qed "le_le_imp_eq";

Goal "m~=n --> m<=n --> m<(n::nat)";
by (induct_tac "n" 1);
by Auto_tac;
by (subgoal_tac "m = Suc n" 1);
by (rtac le_le_imp_eq 2);
by Auto_tac;
qed_spec_mp "neq_le_imp_less";


(*** funprod and funsum ***)

Goal "(ALL i. i <= n --> #0 < mf i) --> #0 < funprod mf 0 n";
by (induct_tac "n" 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 1);
qed_spec_mp "funprod_pos";

Goal "(ALL i. k<=i & i<=(k+l) --> zgcd (mf i, mf m) = #1) --> \
\     zgcd (funprod mf k l, mf m) = #1";
by (induct_tac "l" 1);
by (ALLGOALS Simp_tac);
by (REPEAT (rtac impI 1));
by (stac zgcd_zmult_cancel 1);
by Auto_tac;
qed_spec_mp "funprod_zgcd";

Goal "k<=i --> i<=(k+l) --> (mf i) dvd (funprod mf k l)";     
by (induct_tac "l" 1);
by Auto_tac;
by (rtac zdvd_zmult2 2);
by (rtac zdvd_zmult 3);
by (subgoal_tac "i=k" 1);
by (subgoal_tac "i=Suc (k + n)" 3);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "funprod_zdvd";

Goal "(funsum f k l) mod m = (funsum (%i. (f i) mod m) k l) mod m";
by (induct_tac "l" 1);
by Auto_tac;
by (rtac trans 1);
by (rtac zmod_zadd1_eq 1);
by (Asm_simp_tac 1);
by (rtac (zmod_zadd_right_eq RS sym) 1);
qed "funsum_mod";

Goal "(ALL i. k<=i & i<=(k+l) --> (f i) = #0) --> (funsum f k l) = #0";
by (induct_tac "l" 1);
by Auto_tac;
qed_spec_mp "funsum_zero";

Goal "k<=j --> j<=(k+l) --> \
\     (ALL i. k<=i & i<=(k+l) & i~=j --> (f i) = #0) --> \
\     (funsum f k l) = (f j)";
by (induct_tac "l" 1);
by (ALLGOALS Simp_tac); 
by (ALLGOALS (REPEAT o (rtac impI)));
by (case_tac "Suc (k+n) = j" 2);
by (subgoal_tac "funsum f k n = #0" 2);
by (rtac funsum_zero 3);
by (subgoal_tac "f (Suc (k+n)) = #0" 4);
by (subgoal_tac "k=j" 1);
by (Clarify_tac 4);
by (subgoal_tac "j<=k+n" 5);
by (subgoal_tac "j<Suc (k+n)" 6);
by (rtac neq_le_imp_less 7);
by (ALLGOALS Asm_simp_tac); 
by Auto_tac;
qed_spec_mp "funsum_oneelem";


(*** Chinese: Uniqueness ***)

Goalw [m_cond_def,km_cond_def,lincong_sol_def]
      "[| m_cond n mf; km_cond n kf mf; \
\         lincong_sol n kf bf mf x; lincong_sol n kf bf mf y |] \
\     ==>  [x=y] (mod mf n)";
by (rtac iffD1 1);
by (res_inst_tac [("k","kf n")] zcong_cancel2 1);
by (res_inst_tac [("b","bf n")] zcong_trans 3);
by (stac zcong_sym 4);
by (rtac zless_imp_zle 1);
by (ALLGOALS Asm_simp_tac);
val lemma = result();

Goal "m_cond n mf --> km_cond n kf mf --> \
\     lincong_sol n kf bf mf x --> lincong_sol n kf bf mf y --> \
\     [x=y] (mod funprod mf 0 n)";
by (induct_tac "n" 1);
by (ALLGOALS Simp_tac);
by (blast_tac (claset() addIs [lemma]) 1);
by (REPEAT (rtac impI 1));
by (rtac zcong_zgcd_zmult_zmod 1);
by (blast_tac (claset() addIs [lemma]) 1);
by (stac zgcd_commute 2);
by (rtac funprod_zgcd 2);
by (auto_tac (claset(), 
              simpset() addsimps [m_cond_def,km_cond_def,lincong_sol_def]));  
qed_spec_mp "zcong_funprod";


(* Chinese: Existence *)

Goal "[| 0<n; i<n |] ==> Suc (i+(n-Suc(i))) = n";
by (arith_tac 1);
val suclemma = result();

Goal "[| 0<n; i<=n; m_cond n mf; km_cond n kf mf |] \
\     ==> EX! x. #0<=x & x<(mf i) & \
\                [(kf i)*(mhf mf n i)*x = bf i] (mod mf i)";
by (rtac zcong_lineq_unique 1);
by (stac zgcd_zmult_cancel 2);
by (rewrite_goals_tac [m_cond_def,km_cond_def,mhf_def]);
by (ALLGOALS Asm_simp_tac);
by Auto_tac;  
by (stac zgcd_zmult_cancel 3);
by (Asm_simp_tac 3);
by (ALLGOALS (rtac funprod_zgcd));
by Safe_tac;
by (ALLGOALS Asm_full_simp_tac);
by (subgoal_tac "i<=n" 1);
by (res_inst_tac [("j","n-1")] le_trans 2);
by (subgoal_tac "i~=n" 1);
by (subgoal_tac "ia<=n" 5);
by (res_inst_tac [("j","i-1")] le_trans 6);
by (res_inst_tac [("j","n-1")] le_trans 7);
by (subgoal_tac "ia~=i" 5);
by (subgoal_tac "ia<=n" 10);
by (stac (suclemma RS sym) 11);
by (assume_tac 13);
by (rtac neq_le_imp_less 12);
by (rtac diff_le_mono 8);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [le_pred_eq])));
qed "unique_xi_sol";

Goalw [mhf_def] "[| 0<n; i<=n; j<=n; j~=i |] ==> (mf j) dvd (mhf mf n i)";
by (case_tac "i=0" 1);
by (case_tac "i=n" 2);
by (ALLGOALS Asm_simp_tac);
by (case_tac "j<i" 3);
by (rtac zdvd_zmult2 3);
by (rtac zdvd_zmult 4);
by (ALLGOALS (rtac funprod_zdvd));
by Auto_tac;
by (stac suclemma 4);
by (stac le_pred_eq 2);
by (stac le_pred_eq 1);
by (rtac neq_le_imp_less 2);
by (rtac neq_le_imp_less 8);
by (rtac pred_less_imp_le 6);
by (rtac neq_le_imp_less 6);
by Auto_tac;
val lemma = result();

Goalw [x_sol_def] "[| 0<n; i<=n |] \
\     ==> (x_sol n kf bf mf) mod (mf i) = \
\         (xilin_sol i n kf bf mf)*(mhf mf n i) mod (mf i)";
by (stac funsum_mod 1);
by (stac funsum_oneelem 1);
by Auto_tac;
by (stac (zdvd_iff_zmod_eq_0 RS sym) 1);
by (rtac zdvd_zmult 1);
by (rtac lemma 1);
by Auto_tac;
qed "x_sol_lin";


(* Chinese *)

Goal "[| 0<n; m_cond n mf; km_cond n kf mf |] \
\     ==> (EX! x. #0 <= x & x < (funprod mf 0 n) & \
\                 (lincong_sol n kf bf mf x))";
by Safe_tac;
by (res_inst_tac [("m","funprod mf 0 n")] zcong_zless_imp_eq 2);
by (rtac zcong_funprod 6);
by Auto_tac;
by (res_inst_tac [("x","(x_sol n kf bf mf) mod (funprod mf 0 n)")] exI 1);
by (rewtac lincong_sol_def);
by Safe_tac;
by (stac zcong_zmod 3);
by (stac zmod_zmult_distrib 3);
by (stac zmod_zdvd_zmod 3);
by (stac x_sol_lin 5);
by (stac (zmod_zmult_distrib RS sym) 7);
by (stac (zcong_zmod RS sym) 7);
by (subgoal_tac "#0<=(xilin_sol i n kf bf mf) & \
\                (xilin_sol i n kf bf mf)<(mf i) & \
\                [(kf i)*(mhf mf n i)*(xilin_sol i n kf bf mf) = bf i] \
\                  (mod mf i)" 7);
by (asm_full_simp_tac (simpset() addsimps zmult_ac) 7);
by (rewtac xilin_sol_def);
by (Asm_simp_tac 7);
by (rtac (ex1_implies_ex RS ex_someI) 7);
by (rtac unique_xi_sol 7);
by (rtac funprod_zdvd 4);
by (rewtac m_cond_def);
by (rtac (funprod_pos RS pos_mod_sign) 1);
by (rtac (funprod_pos RS pos_mod_bound) 2);
by Auto_tac;
qed "chinese_remainder";
