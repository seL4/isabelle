(*  Title:      HOL/ex/Factorization.thy
    ID:         $Id$
    Author:     Thomas Marthedal Rasmussen
    Copyright   2000  University of Cambridge

Fundamental Theorem of Arithmetic (unique factorization into primes)
*)


(* --- Arithmetic --- *)

Goal "[| m ~= m*k; m ~= 1 |] ==> 1<m";
by (case_tac "m" 1);
by Auto_tac;
qed "one_less_m";

Goal "[| m ~= m*k; 1<m*k |] ==> 1<k";
by (case_tac "k" 1);
by Auto_tac;
qed "one_less_k";

Goal "[| 0<k; k*n=k*m |] ==> n=m";
by Auto_tac;
qed "mult_left_cancel";

Goal "[| 0<m; m*n = m |] ==> n=1";
by (case_tac "n" 1);
by Auto_tac;
qed "mn_eq_m_one";

Goal "[| 0<n; 0<k |] ==> 1<m --> m*n = k --> n<k";
by (induct_tac "m" 1);
by Auto_tac;
qed_spec_mp "prod_mn_less_k";


(* --- Prime List & Product --- *)

Goal "prod (xs @ ys) = prod xs * prod ys"; 
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mult_assoc])));
qed "prod_append";

Goal "prod (x#xs) = prod (y#ys) ==> x*prod xs = y*prod ys";
by Auto_tac;
qed "prod_xy_prod";

Goalw [primel_def] "primel (xs @ ys) = (primel xs & primel ys)";
by Auto_tac;
qed "primel_append";

Goalw [primel_def] "n:prime ==> primel [n] & prod [n] = n";
by Auto_tac;
qed "prime_primel";

Goalw [prime_def,dvd_def] "p:prime ==> ~(p dvd 1)";
by Auto_tac;
by (case_tac "k" 1);
by Auto_tac;
qed "prime_nd_one";

Goalw [dvd_def] "[| prod (x#xs) = prod ys |] ==> x dvd (prod ys)";
by (rtac exI 1);
by (rtac sym 1);
by (Asm_full_simp_tac 1);
qed "hd_dvd_prod";

Goalw [primel_def] "primel (x#xs) ==> primel xs";
by Auto_tac;
qed "primel_tl";

Goalw [primel_def] "(primel (x#xs)) = (x:prime & primel xs)"; 
by Auto_tac;
qed "primel_hd_tl";

Goalw [prime_def] "[| p:prime; q:prime; p dvd q |] ==> p=q";
by Auto_tac;
qed "primes_eq";

Goalw [primel_def,prime_def] "[| primel xs; prod xs = 1 |] ==> xs = []";
by (case_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "primel_one_empty";

Goalw [prime_def] "p:prime ==> 1<p";
by Auto_tac;
qed "prime_g_one";

Goalw [prime_def] "p:prime ==> 0<p";
by Auto_tac;
qed "prime_g_zero";

Goalw [primel_def,prime_def] "primel xs --> xs ~= [] --> 1 < prod xs";
by (induct_tac "xs" 1);
by (auto_tac (claset() addEs [one_less_mult], simpset()));
qed_spec_mp "primel_nempty_g_one";

Goalw [primel_def,prime_def] "primel xs --> 0 < prod xs"; 
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "primel_prod_gz";


(* --- Sorting --- *)

Goal "nondec xs --> nondec (oinsert x xs)";
by (induct_tac "xs" 1);
by (case_tac "list" 2);
by (ALLGOALS(asm_full_simp_tac (simpset()delcongs[thm"list.weak_case_cong"])));
qed_spec_mp "nondec_oinsert";

Goal "nondec (sort xs)";
by (induct_tac "xs" 1);
by (ALLGOALS (Asm_full_simp_tac));
by (etac nondec_oinsert 1);
qed "nondec_sort";

Goal "[| x<=y; l=y#ys |]  ==> x#l = oinsert x l";
by (ALLGOALS Asm_full_simp_tac);
qed "x_less_y_oinsert";

Goal "nondec xs --> xs = sort xs";
by (induct_tac "xs" 1);
by Safe_tac;
by (ALLGOALS Asm_full_simp_tac);
by (case_tac "list" 1);
by (ALLGOALS Asm_full_simp_tac);
by (case_tac "list" 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("y","aa"),("ys","lista")] x_less_y_oinsert 1); 
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nondec_sort_eq";

Goal "oinsert x (oinsert y l) = oinsert y (oinsert x l)";
by (induct_tac "l" 1);
by Auto_tac;
qed "oinsert_x_y";


(* --- Permutation --- *)

Goalw [primel_def] "xs <~~> ys ==> primel xs --> primel ys";
by (etac perm.induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "perm_primel";

Goal "xs <~~> ys ==> prod xs = prod ys";
by (etac perm.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps mult_ac)));
qed_spec_mp "perm_prod";

Goal "xs <~~> ys ==> oinsert a xs <~~> oinsert a ys"; 
by (etac perm.induct 1);
by Auto_tac;
qed "perm_subst_oinsert";

Goal "x#xs <~~> oinsert x xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "perm_oinsert";

Goal "xs <~~> sort xs";
by (induct_tac "xs" 1);
by (auto_tac (claset() addIs [perm_oinsert] 
	               addEs [perm_subst_oinsert],
              simpset()));
qed "perm_sort";

Goal "xs <~~> ys ==> sort xs = sort ys";
by (etac perm.induct 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [oinsert_x_y])));
qed "perm_sort_eq";


(* --- Existence --- *)

Goal "primel xs ==> EX ys. primel ys & nondec ys & prod ys = prod xs";
by (blast_tac (claset() addIs [nondec_sort, perm_prod,perm_primel,perm_sort,
			       perm_sym]) 1);
qed "ex_nondec_lemma";

Goalw [prime_def,dvd_def]
     "1<n & n~:prime --> (EX m k.1<m & 1<k & m<n & k<n & n=m*k)";
by (auto_tac (claset() addIs [n_less_m_mult_n, n_less_n_mult_m,
			      one_less_m, one_less_k], 
	      simpset()));
qed_spec_mp "not_prime_ex_mk";

Goal "[| primel xs; primel ys |] \
\     ==> EX l. primel l & prod l = prod xs * prod ys";
by (rtac exI 1);
by Safe_tac;
by (rtac prod_append 2);
by (asm_simp_tac (simpset() addsimps [primel_append]) 1);
qed "split_primel";

Goal "1<n --> (EX l. primel l & prod l = n)"; 
by (res_inst_tac [("n","n")] less_induct 1);
by (rtac impI 1);
by (case_tac "n:prime" 1);
by (rtac exI 1);
by (etac prime_primel 1);
by (cut_inst_tac [("n","n")] not_prime_ex_mk 1);
by (auto_tac (claset() addSIs [split_primel], simpset()));
qed_spec_mp "factor_exists";

Goal "1<n ==> (EX l. primel l & nondec l & prod l = n)"; 
by (etac (factor_exists RS exE) 1);
by (blast_tac (claset() addSIs [ex_nondec_lemma]) 1);
qed "nondec_factor_exists";


(* --- Uniqueness --- *)

Goal "p:prime ==> p dvd (prod xs) --> (EX m. m:set xs & p dvd m)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
by (etac prime_nd_one 1);
by (rtac impI 1);
by (dtac prime_dvd_mult 1);
by Auto_tac;
qed_spec_mp "prime_dvd_mult_list";

Goal "[| primel (x#xs); primel ys; prod (x#xs) = prod ys |] \
\     ==> EX m. m :set ys & x dvd m";
by (rtac prime_dvd_mult_list 1);
by (etac hd_dvd_prod 2);
by (asm_full_simp_tac (simpset() addsimps [primel_hd_tl]) 1);
qed "hd_xs_dvd_prod";

Goal "[| primel (x#xs); primel ys; m:set ys; x dvd m |] ==> x=m";
by (rtac primes_eq 1);
by (auto_tac (claset(), simpset() addsimps [primel_def,primel_hd_tl]));
qed "prime_dvd_eq";

Goal "[| primel (x#xs); primel ys; prod (x#xs) = prod ys |] ==> x:set ys";
by (ftac hd_xs_dvd_prod 1);
by Auto_tac;
by (dtac prime_dvd_eq 1);
by Auto_tac;
qed "hd_xs_eq_prod";

Goal "[| primel (x#xs); primel ys; prod (x#xs) = prod ys |] \
\     ==> EX l. ys <~~> (x#l)";
by (rtac exI 1);
by (rtac perm_remove 1);
by (etac hd_xs_eq_prod 1);
by (ALLGOALS assume_tac);
qed "perm_primel_ex";

Goal "[| primel (x#xs); primel ys; prod (x#xs) = prod ys |] \
\     ==> prod xs < prod ys";
by (auto_tac (claset() addIs [prod_mn_less_k,prime_g_one,primel_prod_gz],
              simpset() addsimps [primel_hd_tl]));
qed "primel_prod_less";

Goal "[| primel xs; p*prod xs = p; p:prime |] ==> xs=[]";
by (auto_tac (claset() addIs [primel_one_empty,mn_eq_m_one,prime_g_zero], 
	      simpset()));
qed "prod_one_empty";

Goal "[| ALL m. m < prod ys --> (ALL xs ys. primel xs & primel ys & \
\        prod xs = prod ys & prod xs = m --> xs <~~> ys); primel list; \
\        primel x; prod list = prod x; prod x < prod ys |] ==> x <~~> list";
by (Asm_full_simp_tac 1);
qed "uniq_ex_lemma";

Goal "ALL xs ys. (primel xs & primel ys & prod xs = prod ys & prod xs = n \
\     --> xs <~~> ys)";
by (res_inst_tac [("n","n")] less_induct 1);
by Safe_tac;
by (case_tac "xs" 1);
by (force_tac (claset() addIs [primel_one_empty], simpset()) 1);
by (rtac (perm_primel_ex RS exE) 1);
by (ALLGOALS Asm_full_simp_tac);
by (rtac (perm.trans RS perm_sym) 1);
by (assume_tac 1);
by (rtac perm.Cons 1);
by (case_tac "x=[]" 1);
by (asm_full_simp_tac (simpset() addsimps [perm_sing_eq,primel_hd_tl]) 1);
by (res_inst_tac [("p","a")] prod_one_empty 1);
by (ALLGOALS Asm_full_simp_tac);
by (etac uniq_ex_lemma 1);
by (auto_tac (claset() addIs [primel_tl,perm_primel],
	      simpset() addsimps [primel_hd_tl]));
by (res_inst_tac [("k","a"),("n","prod list"),("m","prod x")] mult_left_cancel 1);
by (res_inst_tac [("x","a")] primel_prod_less 3);
by (rtac prod_xy_prod 2);
by (res_inst_tac [("s","prod ys")] trans 2);
by (etac perm_prod 3);
by (etac (perm_prod RS sym) 5); 
by (auto_tac (claset() addIs [perm_primel,prime_g_zero], simpset()));
qed_spec_mp "factor_unique";

Goal "[| xs <~~> ys; nondec xs; nondec ys |] ==> xs = ys"; 
by (rtac trans 1);
by (rtac trans 1);
by (etac nondec_sort_eq 1);
by (etac perm_sort_eq 1);
by (etac (nondec_sort_eq RS sym) 1);
qed "perm_nondec_unique";

Goal "ALL n. 1<n --> (EX! l. primel l & nondec l & prod l = n)";
by Safe_tac;
by (etac nondec_factor_exists 1);
by (rtac perm_nondec_unique 1);
by (rtac factor_unique 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "unique_prime_factorization";
