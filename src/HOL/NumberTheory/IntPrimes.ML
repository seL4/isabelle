(*  Title:	IntPrimes.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

dvd relation, GCD, Euclid's extended algorithm, primes, congruences
(all on the Integers)

Comparable to 'Primes' theory but dvd is included here as it is not present in
'IntDiv'. Also includes extended GCD and congruences not
present in 'Primes'.  Also a few extra theorems concerning 'mod'
*)

eta_contract:=false;


(************************************************)
(** Divides relation 'dvd'                     **)
(************************************************)

Goalw [dvd_def] "(m::int) dvd #0";
by (blast_tac (claset() addIs [zmult_0_right RS sym]) 1);
qed "zdvd_0_right";
AddIffs [zdvd_0_right];

Goalw [dvd_def] "#0 dvd (m::int) ==> m = #0";
by Auto_tac;
qed "zdvd_0_left";

Goalw [dvd_def] "#1 dvd (m::int)";
by (Simp_tac 1);
qed "zdvd_1_left";
AddIffs [zdvd_1_left];

Goalw [dvd_def] "m dvd (m::int)";
by (blast_tac (claset() addIs [zmult_1_right RS sym]) 1);
qed "zdvd_refl";
Addsimps [zdvd_refl];

Goalw [dvd_def] "[| m dvd n; n dvd k |] ==> m dvd (k::int)";
by (blast_tac (claset() addIs [zmult_assoc] ) 1);
qed "zdvd_trans";

Goalw [dvd_def] "(m dvd -n) = (m dvd (n::int))";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zdvd_zminus_iff";  

Goalw [dvd_def] "(-m dvd n) = (m dvd (n::int))";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zdvd_zminus2_iff";  

Goalw [dvd_def] "[| #0<m; #0<n; m dvd n; n dvd m |] ==> m = (n::int)";
by Auto_tac;
by (asm_full_simp_tac
    (simpset() addsimps [zmult_assoc,zmult_eq_self_iff,
                         int_0_less_mult_iff, zmult_eq_1_iff]) 1);
qed "zdvd_anti_sym";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m+n :: int)";
by (blast_tac (claset() addIs [zadd_zmult_distrib2 RS sym]) 1);
qed "zdvd_zadd";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m-n :: int)";
by (blast_tac (claset() addIs [zdiff_zmult_distrib2 RS sym]) 1);
qed "zdvd_zdiff";

Goal "[| k dvd (m-n); k dvd n |] ==> k dvd (m::int)";
by (subgoal_tac "m=n+(m-n)" 1);
by (etac ssubst 1);
by (blast_tac (claset() addIs [zdvd_zadd]) 1);
by (Simp_tac 1);
qed "zdvd_zdiffD";

Goalw [dvd_def] "k dvd (n::int) ==> k dvd (m*n)";
by (blast_tac (claset() addIs [zmult_left_commute]) 1);
qed "zdvd_zmult";

Goal "k dvd (m::int) ==> k dvd (m*n)";
by (stac zmult_commute 1);
by (etac zdvd_zmult 1);
qed "zdvd_zmult2";

(* k dvd (m*k) *)
AddIffs [zdvd_refl RS zdvd_zmult, zdvd_refl RS zdvd_zmult2];

Goalw [dvd_def] "(j*k) dvd n ==> j dvd (n::int)";
by (full_simp_tac (simpset() addsimps [zmult_assoc]) 1);
by (Blast_tac 1);
qed "zdvd_zmultD2";

Goal "(j*k) dvd n ==> k dvd (n::int)";
by (rtac zdvd_zmultD2 1);
by (stac zmult_commute 1);
by (assume_tac 1);
qed "zdvd_zmultD";

Goalw [dvd_def] "[| i dvd m; j dvd (n::int) |] ==> (i*j) dvd (m*n)";
by (Clarify_tac 1);
by (res_inst_tac [("x","k*ka")] exI 1);
by (asm_simp_tac (simpset() addsimps zmult_ac) 1);
qed "zdvd_zmult_mono";

Goal "k dvd (n + k*m) = k dvd (n::int)";
by (rtac iffI 1);
by (etac zdvd_zadd 2);
by (subgoal_tac "n = (n+k*m)-k*m" 1);
by (etac ssubst 1);
by (etac zdvd_zdiff 1);
by (ALLGOALS Simp_tac);
qed "zdvd_reduce";

Goalw [dvd_def] "[| f dvd m; f dvd (n::int) |] ==> f dvd (m mod n)";
by (auto_tac (claset(), simpset() addsimps [zmod_zmult_zmult1]));
qed "zdvd_zmod";

Goal "[| k dvd (m mod n);  k dvd n |] ==> k dvd (m::int)";
by (subgoal_tac "k dvd (n*(m div n) + m mod n)" 1);
by (asm_simp_tac (simpset() addsimps [zdvd_zadd, zdvd_zmult2]) 2);
by (asm_full_simp_tac (simpset() addsimps [zmod_zdiv_equality RS sym]) 1);
qed "zdvd_zmod_imp_zdvd";

Goalw [dvd_def] "(k dvd n) = (n mod (k::int) = #0)";
by (zdiv_undefined_case_tac "k=#0" 1);
by Safe_tac;
by (res_inst_tac [("x","n div k")] exI 2);
by (rtac trans 2);
by (res_inst_tac [("b","k")] zmod_zdiv_equality 2);
by (ALLGOALS Asm_simp_tac);
qed "zdvd_iff_zmod_eq_0";

Goal "[| ~k<#0; k~=#0 |] ==> #0<(k::int)";
by (arith_tac 1);
val lemma = result();

Goalw [dvd_def] "[| #0<m; m<n |] ==> ~n dvd (m::int)";
by Auto_tac;
by (subgoal_tac "#0<n" 1);
by (blast_tac (claset() addIs [zless_trans]) 2);
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 1); 
by (subgoal_tac "n*k < n*#1" 1);
by (dtac (zmult_zless_cancel1 RS iffD1) 1); 
by Auto_tac;  
qed "zdvd_not_zless";


(************************************************)
(** Euclid's Algorithm and GCD                 **)
(************************************************)

val [zgcd_eq] = zgcd.simps;
Delsimps zgcd.simps;

Goal "zgcd(m,#0) = m";
by (rtac (zgcd_eq RS trans) 1);
by (Simp_tac 1);
qed "zgcd_0";
Addsimps [zgcd_0];

Goal"#0<(m::int) ==> zgcd(#0,m) = m";
by (auto_tac (claset(), simpset() addsimps zgcd.simps));
qed "zgcd_0_left";
Addsimps [zgcd_0_left];

Goal "#0<n ==> zgcd(m,n) = zgcd (n, m mod n)";
by (rtac (zgcd_eq RS trans) 1);
by (Asm_simp_tac 1);
qed "zgcd_non_0";

Goal "zgcd(m,#1) = #1";
by (simp_tac (simpset() addsimps [zgcd_non_0]) 1);
qed "zgcd_1";
Addsimps [zgcd_1];

Goal "(zgcd(#0,m) = #1) = (m = #1)";
by (auto_tac (claset(),simpset() addsimps zgcd.simps));
qed "zgcd_0_1_iff";
Addsimps [zgcd_0_1_iff];

Goal "#0<=(n::int) --> (zgcd(m,n) dvd m) & (zgcd(m,n) dvd n)";
by (induct_thm_tac zgcd.induct "m n" 1);
by (case_tac "n=#0" 1);
by (auto_tac (claset() addDs [zdvd_zmod_imp_zdvd],
              simpset() addsimps [zle_neq_implies_zless,neq_commute,
                                  pos_mod_sign,zgcd_non_0]));
by (ALLGOALS (rotate_tac 1));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zle_anti_sym])));
qed_spec_mp "zgcd_zdvd_both";

bind_thm ("zgcd_zdvd1", zgcd_zdvd_both RS conjunct1);
bind_thm ("zgcd_zdvd2", zgcd_zdvd_both RS conjunct2);

Goal "[| (n::int) <= #0;  #0 <= n; #0 ~= n |] ==> False";
by (asm_full_simp_tac (simpset() addsimps [zle_anti_sym]) 1);
val lemma_false = result();

Goal "#0<=(n::int) --> (f dvd m) --> (f dvd n) --> f dvd zgcd(m,n)";
by (induct_thm_tac zgcd.induct "m n" 1);
by (case_tac "n=#0" 1);
by (auto_tac (claset() addDs [lemma_false] addIs [pos_mod_sign,zdvd_zmod],
        simpset() addsimps [zgcd_non_0,neq_commute,zle_neq_implies_zless]));
qed_spec_mp "zgcd_greatest";

Goal "#0 < (n::int) --> #0 < zgcd (m, n)";
by (induct_thm_tac zgcd.induct "m n" 1);
by (auto_tac (claset(), simpset() addsimps zgcd.simps));
qed_spec_mp "zgcd_zless";

Goalw [is_zgcd_def] "#0<(n::int) ==> is_zgcd (zgcd(m,n)) m n";
by (asm_simp_tac (simpset() addsimps 
      [zgcd_greatest,zgcd_zdvd_both,zgcd_zless]) 1);
qed "is_zgcd";

Goalw [is_zgcd_def] "[| is_zgcd m a b; is_zgcd n a b |] ==> m=n";
by (blast_tac (claset() addIs [zdvd_anti_sym]) 1);
qed "is_zgcd_unique";

Goalw [is_zgcd_def] "[| is_zgcd m a b; k dvd a; k dvd b |] ==> k dvd m";
by (Blast_tac 1);
qed "is_zgcd_zdvd";

Goalw [is_zgcd_def] "is_zgcd k m n = is_zgcd k n m";
by (Blast_tac 1);
qed "is_zgcd_commute";

Goalw [is_zgcd_def] "is_zgcd k (-m) n = is_zgcd k m n";
by (asm_full_simp_tac (simpset() addsimps [zdvd_zminus_iff]) 1);
qed "is_zgcd_zminus";

Goal "#0<(n::int) ==> zgcd(-m,n) = zgcd(m,n)";
by (rtac is_zgcd_unique 1);
by (rtac is_zgcd 1);
by (asm_simp_tac (simpset() addsimps [is_zgcd,is_zgcd_zminus]) 2);
by (assume_tac 1);
qed "zgcd_zminus";

Goal "[| #0<(m::int); #0<n |] ==> zgcd(m,n) = zgcd(n,m)";
by (rtac is_zgcd_unique 1);
by (rtac is_zgcd 2);
by (asm_simp_tac (simpset() addsimps [is_zgcd,is_zgcd_commute]) 1);
by (assume_tac 1);
qed "zgcd_commute";

Goal "#0<=(m::int) ==> zgcd(#1,m) = #1";
by (case_tac "m=#0" 1);
by (stac zgcd_commute 2);
by (ALLGOALS (asm_full_simp_tac (simpset() 
      addsimps [zle_neq_implies_zless,neq_commute])));
qed "zgcd_1_left";
Addsimps [zgcd_1_left];

Goal "[| #0<(m::int); #0<n |] ==> zgcd(zgcd(k,m),n) = zgcd(k,zgcd(m,n))";
by (rtac is_zgcd_unique 1);
by (rtac is_zgcd 2);
by (rewrite_goals_tac [is_zgcd_def]);
by Auto_tac;
by (rtac zgcd_greatest 3);
by (res_inst_tac [("n","zgcd (k,m)")] zdvd_trans 2);
by (res_inst_tac [("n","zgcd (k,m)")] zdvd_trans 5);
by (rtac zgcd_greatest 8);
by (rtac zgcd_greatest 9);
by (res_inst_tac [("n","zgcd (m,n)")] zdvd_trans 12);
by (res_inst_tac [("n","zgcd (m,n)")] zdvd_trans 11);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zgcd_zdvd1,zgcd_zdvd2,zgcd_zless])));
qed "zgcd_assoc";

Goal "#0<=(n::int) --> #0<=k --> k * zgcd(m,n) = zgcd(k*m, k*n)";
by (induct_thm_tac zgcd.induct "m n" 1);
by (case_tac "n=#0" 1);
by (auto_tac (claset() addDs [lemma_false],
              simpset() addsimps [zle_neq_implies_zless,pos_mod_sign,
                                  zgcd_non_0,neq_commute]));
by (case_tac "k=#0" 1);
by (ALLGOALS (asm_full_simp_tac (simpset() 
      addsimps [zle_neq_implies_zless,zgcd_non_0,zmod_zmult_zmult1,
                int_0_less_mult_iff,neq_commute])));
qed_spec_mp "zgcd_zmult_distrib2";

Goal "#0<=m ==> zgcd(m,m) = m";
by (cut_inst_tac [("k","m"),("m","#1"),("n","#1")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_self";
Addsimps [zgcd_self];

Goal "[| #0<=k; #0<=n |] ==> zgcd(k, k*n) = k";
by (cut_inst_tac [("k","k"),("m","#1"),("n","n")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_zmult_eq_self";
Addsimps [zgcd_zmult_eq_self];

Goal "#0<=k ==> zgcd(k*n, k) = k";
by (cut_inst_tac [("k","k"),("m","n"),("n","#1")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_zmult_eq_self2";
Addsimps [zgcd_zmult_eq_self2];

Goal "[| #0<=(m::int); #0<=k; zgcd(n,k)=#1; k dvd (m*n) |] ==> k dvd m";
by (subgoal_tac "m = zgcd(m*n, m*k)" 1);
by (etac ssubst 1 THEN rtac zgcd_greatest 1);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zgcd_zmult_distrib2 RS sym,int_0_le_mult_iff])));
qed "zrelprime_zdvd_zmult";

Goalw [zprime_def] "[| p:zprime; ~p dvd n |] ==> zgcd(n,p) = #1";
by (cut_inst_tac [("m","n"),("n","p")] zgcd_zdvd_both 1);
by Auto_tac;
qed "zprime_imp_zrelprime";

Goal "[| p:zprime; #0<n; n<p |] ==> zgcd(n,p) = #1";
by (etac zprime_imp_zrelprime 1);
by (etac zdvd_not_zless 1);
by (assume_tac 1);
qed "zless_zprime_imp_zrelprime";

Goal "[| #0<=(m::int); p:zprime; p dvd (m*n) |] ==> p dvd m | p dvd n";
by Safe_tac;
by (rtac zrelprime_zdvd_zmult 1);
by (rtac zprime_imp_zrelprime 3);
by (SELECT_GOAL (rewrite_goals_tac [zprime_def]) 2);
by Auto_tac;
qed "zprime_zdvd_zmult";

Goal "#0<n ==> zgcd(m+n*k,n) = zgcd(m,n)";
by (rtac (zgcd_eq RS trans) 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
by (rtac trans 1);
by (rtac (zgcd_eq RS sym) 2);
by Auto_tac;
qed "zgcd_zadd_zmult";
Addsimps [zgcd_zadd_zmult];

Goal "#0<=n ==> zgcd(m,n) dvd zgcd(k*m,n)";
by (rtac zgcd_greatest 1);
by (rtac zdvd_trans 2);
by (rtac zgcd_zdvd1 2);
by (rtac zgcd_zdvd2 4);
by (ALLGOALS Asm_simp_tac);
qed "zgcd_zdvd_zgcd_zmult";

Goal "[| #0<k; #0<m; #0<n; zgcd(k,n) = #1 |] ==> zgcd(k*m,n) dvd zgcd(m,n)";
by (rtac zgcd_greatest 1);
by (res_inst_tac [("n","k")] zrelprime_zdvd_zmult 2);
by (stac zmult_commute 5);
by (stac (zgcd_assoc RS sym) 4);
by (rtac zless_imp_zle 3);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zgcd_zdvd1,zgcd_zdvd2,zgcd_zless,int_0_less_mult_iff])));
qed "zgcd_zmult_zdvd_zgcd";

Goal "[| #0<n; zgcd(k,n) = #1 |] ==> zgcd(k*m, n) = zgcd(m,n)";
by (rtac zdvd_anti_sym 1);
by (rtac zgcd_zdvd_zgcd_zmult 4);
by (case_tac "m=#0" 3);
by (case_tac "k=#0" 4);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zgcd_zless])));
by (case_tac "#0<k" 1);
by (ALLGOALS (case_tac "#0<m"));
by (rtac zgcd_zmult_zdvd_zgcd 1);
by (subgoal_tac "zgcd (k*(-m),n) dvd zgcd (-m,n)" 5);
by (rtac zgcd_zmult_zdvd_zgcd 6);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zgcd_zminus])));
by (subgoal_tac "zgcd ((-k)*m,n) dvd zgcd (m,n)" 2);
by (rtac zgcd_zmult_zdvd_zgcd 3);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zgcd_zminus])));
by (subgoal_tac "zgcd ((-k)*(-m),n) dvd zgcd (-m,n)" 3);
by (rtac zgcd_zmult_zdvd_zgcd 4);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zgcd_zminus])));
by (auto_tac (claset() addIs [zle_neq_implies_zless], simpset()));
qed "zgcd_zmult_cancel";

Goal "[| #0<m; zgcd(k,m) = #1; zgcd(n,m) = #1 |] ==> zgcd(k*n,m) = #1";
by (asm_simp_tac (simpset() addsimps [zgcd_zmult_cancel]) 1);
qed "zgcd_zgcd_zmult";

Goal "#0<m ==> (m dvd n) = (zgcd(n,m) = m)";
by Safe_tac;
by (res_inst_tac [("n","zgcd(n,m)")] zdvd_trans 2);
by (rtac zgcd_zdvd1 3);
by (ALLGOALS Asm_simp_tac);
by (rewtac dvd_def);
by Auto_tac;
qed "zdvd_iff_zgcd";


(************************************************)
(** Congruences                                **)
(************************************************)

Goalw [zcong_def] "[a=b](mod #1)";
by Auto_tac;
qed "zcong_1";
Addsimps [zcong_1];

Goalw [zcong_def] "[k = k] (mod m)";
by Auto_tac;
qed "zcong_refl";
Addsimps [zcong_refl];

Goalw [zcong_def,dvd_def] "[a = b](mod m) = [b = a](mod m)";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zcong_sym";

Goalw [zcong_def]
     "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a+c = b+d](mod m)";
by (res_inst_tac [("s","(a-b)+(c-d)")] subst 1);
by (rtac zdvd_zadd 2);
by Auto_tac;
qed "zcong_zadd";

Goalw [zcong_def]
     "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a-c = b-d](mod m)";
by (res_inst_tac [("s","(a-b)-(c-d)")] subst 1);
by (rtac zdvd_zdiff 2);
by Auto_tac;
qed "zcong_zdiff";

Goalw [zcong_def,dvd_def]
     "[| [a = b](mod m); [b = c](mod m) |] ==> [a = c](mod m)";
by Auto_tac;
by (res_inst_tac [("x","k+ka")] exI 1);
by (asm_full_simp_tac (simpset() addsimps zadd_ac@[zadd_zmult_distrib2]) 1);
qed "zcong_trans";
 
Goal "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a*c = b*d](mod m)";
by (res_inst_tac [("b","b*c")] zcong_trans 1);
by (rewtac zcong_def);
by (res_inst_tac [("s","c*(a-b)")] subst 1);
by (res_inst_tac [("s","b*(c-d)")] subst 3);
by (blast_tac (claset() addIs [zdvd_zmult]) 4);
by (blast_tac (claset() addIs [zdvd_zmult]) 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib2,
                                                zmult_commute])));
qed "zcong_zmult";

Goal "[a = b] (mod m) ==> [a*k = b*k](mod m)";
by (rtac zcong_zmult 1);
by (ALLGOALS Asm_simp_tac);
qed "zcong_scalar";

Goal "[a = b] (mod m) ==> [k*a = k*b](mod m)";
by (rtac zcong_zmult 1);
by (ALLGOALS Asm_simp_tac);
qed "zcong_scalar2";

Goalw [zcong_def] "[a*m = b*m](mod m)";
by (rtac zdvd_zdiff 1);
by (ALLGOALS Simp_tac);
qed "zcong_zmult_self";

Goalw [zcong_def]
      "[| p:zprime; #0<a; [a*a = #1](mod p) |] \
\     ==> [a=#1](mod p) | [a = p-#1](mod p)";
by (rtac zprime_zdvd_zmult 1);
by (res_inst_tac [("s","a*a - #1 + p*(#1-a)")] subst 3);
by (simp_tac (simpset() addsimps [zdvd_reduce]) 4);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zdiff_zmult_distrib,zmult_commute,zdiff_zmult_distrib2])));
qed "zcong_square";

Goal "[| #0<=m; zgcd(k,m) = #1 |] ==> [a*k = b*k](mod m) = [a = b](mod m)";
by Safe_tac;
by (blast_tac (claset() addIs [zcong_scalar]) 2);
by (case_tac "b<a" 1);
by (stac zcong_sym 2);
by (rewrite_goals_tac [zcong_def]);
by (ALLGOALS (rtac zrelprime_zdvd_zmult));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib])));
by (subgoal_tac "m dvd (-(a*k - b*k))" 1);
by (asm_full_simp_tac (simpset() addsimps [zminus_zdiff_eq]) 1);
by (stac zdvd_zminus_iff 1);
by (assume_tac 1);
qed "zcong_cancel";

Goal "[| #0<=m; zgcd(k,m) = #1 |] ==> [k*a = k*b](mod m) = [a = b](mod m)";
by (asm_simp_tac (simpset() addsimps [zmult_commute,zcong_cancel]) 1);
qed "zcong_cancel2";

Goalw [zcong_def,dvd_def]
      "[| #0<m; #0<n; [a = b] (mod m); [a = b] (mod n); zgcd(m,n) = #1 |] \
\     ==> [a=b](mod m*n)";
by Auto_tac;
by (subgoal_tac "m dvd (n*ka)" 1);
by (subgoal_tac "m dvd ka" 1);
by (case_tac "#0<=ka" 2);
by (stac (zdvd_zminus_iff RS sym) 3);
by (res_inst_tac [("n","n")] zrelprime_zdvd_zmult 2);
by (asm_simp_tac (simpset() addsimps [zgcd_commute]) 4);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute]) 4);
by (res_inst_tac [("n","n")] zrelprime_zdvd_zmult 4);
by (asm_simp_tac (simpset() addsimps [zgcd_commute]) 6);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute,zdvd_zminus_iff]) 6);
by (ALLGOALS Asm_simp_tac);
by (rewtac dvd_def);
by Safe_tac;
by (res_inst_tac [("x","kc")] exI 1);
by (res_inst_tac [("x","k")] exI 2);
by (simp_tac (simpset() addsimps zmult_ac) 1);
by Auto_tac;
qed "zcong_zgcd_zmult_zmod";

Goalw [zcong_def,dvd_def] 
      "[| #0<=a; a<m; #0<=b; b<m; [a = b] (mod m) |] ==> a = b";
by Auto_tac;  
by (dres_inst_tac [("f", "%z. z mod m")] arg_cong 1);  
by (cut_inst_tac [("z","a"),("w","b")] zless_linear 1);
by Auto_tac;  
by (subgoal_tac "(a - b) mod m = a-b" 2);
by (rtac mod_pos_pos_trivial 3); 
by Auto_tac;
by (subgoal_tac "(m + (a - b)) mod m = m + (a - b)" 1);
by (rtac mod_pos_pos_trivial 2); 
by Auto_tac;  
qed "zcong_zless_imp_eq";

Goal "[| p:zprime; #0<a; a<p; [a*a = #1](mod p) |] ==> a = #1 | a = p-#1";
by (cut_inst_tac [("p","p"),("a","a")] zcong_square 1);
by Safe_tac;
by (res_inst_tac [("Pa","a=p-#1")] swap 2);
by (rtac zcong_zless_imp_eq 1);
by (rtac zcong_zless_imp_eq 7);
by (rewtac zprime_def);
by Auto_tac;
qed "zcong_square_zless";

Goalw [zcong_def] "[| #0<a; a<m; #0<b; b<a |] ==> ~[a = b] (mod m) ";
by (rtac zdvd_not_zless 1);
by Auto_tac;
qed "zcong_not";

Goalw [zcong_def,dvd_def] "[| #0<=a; a<m; [a=#0](mod m) |] ==> a = #0";
by Auto_tac;
by (subgoal_tac "#0<m" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [int_0_le_mult_iff]) 1);
by (subgoal_tac "m*k<m*#1" 1);
by (dtac (zmult_zless_cancel1 RS iffD1) 1);
by Auto_tac;  
qed "zcong_zless_0";

Goal "#0<m ==> (EX! b. #0<=b & b<m & [a = b] (mod m))";
by Auto_tac;
by (subgoal_tac "[b = y] (mod m)" 2);
by (case_tac "b=#0" 2);
by (case_tac "y=#0" 3);
by (auto_tac (claset() addIs [zcong_trans,zcong_zless_0,
                              zcong_zless_imp_eq,zle_neq_implies_zless],
              simpset() addsimps [zcong_sym]));
by (rewrite_goals_tac [zcong_def,dvd_def]);
by (res_inst_tac [("x","a mod m")] exI 1);
by (auto_tac (claset(),simpset() addsimps [pos_mod_sign,pos_mod_bound]));
by (res_inst_tac [("x","-(a div m)")] exI 1);
by (cut_inst_tac [("a","a"),("b","m")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zcong_zless_unique";

Goalw [zcong_def,dvd_def] "([a = b] (mod m)) = (EX k. b = a + m*k)"; 
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zcong_iff_lin";

Goal "[| #0<m; zgcd(a,m) = #1; [a = b] (mod m) |] ==> zgcd(b,m) = #1";
by (auto_tac (claset(),simpset() addsimps [zcong_iff_lin]));
qed "zgcd_zcong_zgcd";

Goal "[| a=c; b=d |] ==> a-b = c-(d::int)";
by Auto_tac;
val lemma = result();

Goal "a - b = (m::int) * (a div m - b div m) + (a mod m - b mod m)";
by (res_inst_tac [("s","(m * (a div m) + a mod m) - \
\                 (m * (b div m) + b mod m)")] trans 1);
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 2);
by (rtac lemma 1);
by (ALLGOALS (rtac zmod_zdiv_equality));
val lemma = result();

Goalw [zcong_def] "[a = b] (mod m) = [a mod m = b mod m](mod m)";
by (res_inst_tac [("t","a-b")] ssubst 1);
by (res_inst_tac [("m","m")] lemma 1);
by (rtac trans 1);
by (res_inst_tac [("k","m"),("m","a div m - b div m")] zdvd_reduce 2);
by (simp_tac (simpset() addsimps [zadd_commute]) 1);
qed "zcong_zmod";

Goal "#0<m ==> [a = b] (mod m) = (a mod m = b mod m)";
by Auto_tac;
by (res_inst_tac [("m","m")] zcong_zless_imp_eq 1);
by (stac (zcong_zmod RS sym) 5);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_bound,pos_mod_sign])));
by (rewrite_goals_tac [zcong_def,dvd_def]);
by (res_inst_tac [("x","a div m - b div m")] exI 1);
by (res_inst_tac [("m1","m")] (lemma RS trans) 1);
by Auto_tac;
qed "zcong_zmod_eq";


(************************************************)
(** Modulo                                     **)
(************************************************)

Goalw [dvd_def] "[| #0<(m::int); m dvd b |] ==> (a mod b mod m) = (a mod m)";
by Auto_tac;
by (stac (zcong_zmod_eq RS sym) 1);
by (stac zcong_iff_lin 2);
by (res_inst_tac [("x","k*(a div (m*k))")] exI 2);
by (stac zadd_commute 2);
by (stac (zmult_assoc RS sym) 2);
by (rtac zmod_zdiv_equality 2);
by (assume_tac 1);
qed "zmod_zdvd_zmod";

(************************************************)
(** Extended GCD                               **)
(************************************************)

val [xzgcda_eq] = xzgcda.simps;
Delsimps xzgcda.simps;

Goal "zgcd(r',r) = k --> \
\     (EX sn tn. xzgcda (m,n,r',r,s',s,t',t) = (k,sn,tn))";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac zgcd_eq 1);
by (stac xzgcda_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "(EX sn tn. xzgcda (m,n,r',r,s',s,t',t) = (k,sn,tn)) --> \
\     zgcd(r',r) = k";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac zgcd_eq 1);
by (stac xzgcda_eq 1);
by Auto_tac;
val lemma2 = result();

Goalw [xzgcd_def] "(zgcd(m,n) = k) = (EX s t. xzgcd m n = (k,s,t))"; 
by (rtac iffI 1);
by (ALLGOALS (rtac mp));
by (rtac lemma2 3);
by (rtac lemma1 1);
by Auto_tac;
qed "xzgcd_correct";

(* xzgcd linear *)

Goal "(a-r*b)*m + (c-r*d)*(n::int) = (a*m + c*n) - r*(b*m + d*n)";
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib,zadd_zmult_distrib2,
                                  zmult_assoc]) 1);
val lemma = result();

Goal "[| r' = s'*m + t'*n; r = s*m + t*n |] \
\    ==> (r' mod r) = (s' - (r' div r)*s)*m + (t' - (r' div r)*t)*(n::int)"; 
by (rtac trans 1);
by (rtac (lemma RS sym) 2);
by (Asm_simp_tac 1);
by (stac eq_zdiff_eq 1);
by (rtac (trans RS sym) 1);
by (res_inst_tac [("b","s*m + t*n")] zmod_zdiv_equality 1);
by (simp_tac (simpset() addsimps [zmult_commute]) 1);
val lemma = result();

Goal "#0<r --> xzgcda(m,n,r',r,s',s,t',t) = (rn,sn,tn) \
\          --> r' = s'*m + t'*n -->  r = s*m + t*n --> rn = sn*m + tn*n";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac xzgcda_eq 1);
by (Simp_tac 1);
by (REPEAT (rtac impI 1));
by (case_tac "r' mod r = #0" 1);
by (asm_full_simp_tac (simpset() addsimps [xzgcda_eq]) 1);
by (SELECT_GOAL Safe_tac 1);
by (subgoal_tac "#0 < r' mod r" 1);
by (rtac zle_neq_implies_zless 2);
by (rtac pos_mod_sign 2);
by (cut_inst_tac [("m","m"),("n","n"),("r'","r'"),("r","r"),
                  ("s'","s'"),("s","s"),("t'","t'"),("t","t")] 
                 lemma 1);
by Auto_tac;
qed_spec_mp "xzgcda_linear";

Goalw [xzgcd_def] "[| #0<n; xzgcd m n = (r,s,t) |] ==> r = s*m + t*n";
by (etac xzgcda_linear 1);
by (assume_tac 1);
by Auto_tac;
qed "xzgcd_linear";

Goal "[| #0<n; zgcd(m,n) = k |] ==> (EX s t. k = s*m + t*n)";
by (full_simp_tac (simpset() addsimps [xzgcd_correct]) 1);
by Safe_tac;
by (REPEAT (rtac exI 1));
by (etac xzgcd_linear 1);
by Auto_tac;
qed "zgcd_ex_linear";

Goal "[| #0<n; zgcd(a,n) = #1 |] ==> EX x. [a*x = #1](mod n)";
by (cut_inst_tac [("m","a"),("n","n"),("k","#1")] zgcd_ex_linear 1);
by Safe_tac;
by (res_inst_tac [("x","s")] exI 1);
by (res_inst_tac [("b","s*a+t*n")] zcong_trans 1);
by (Asm_simp_tac 2);
by (rewtac zcong_def);
by (simp_tac (simpset() addsimps [zmult_commute,zdvd_zminus_iff]) 1);
qed "zcong_lineq_ex";

Goal "[| #0<n; zgcd(a,n) = #1 |] ==> EX! x. #0<=x & x<n & [a*x = b](mod n)";
by Auto_tac;
by (rtac zcong_zless_imp_eq 2);
by (stac (zcong_cancel2 RS sym) 6);
by (rtac zcong_trans 8);
by (ALLGOALS Asm_simp_tac);
by (asm_full_simp_tac (simpset() addsimps [zcong_sym]) 2);
by (cut_inst_tac [("a","a"),("n","n")] zcong_lineq_ex 1);
by Auto_tac;
by (res_inst_tac [("x","x*b mod n")] exI 1);
by Safe_tac;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_bound,pos_mod_sign])));
by (stac zcong_zmod 1);
by (stac (zmod_zmult1_eq RS sym) 1);
by (stac (zcong_zmod RS sym) 1);
by (subgoal_tac "[a*x*b = #1*b](mod n)" 1);
by (rtac zcong_zmult 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_assoc])));
qed "zcong_lineq_unique";

