(*  Title:	WilsonRuss.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)


(************  Inverse  **************)

Goal "#1<m ==> Suc(nat(m-#2)) = nat(m-#1)";
by (stac (int_int_eq RS sym) 1);
by Auto_tac;
val lemma = result();

Goalw [inv_def]
      "[| p:zprime; #0<a; a<p |] ==> [a*(inv p a) = #1] (mod p)";
by (stac zcong_zmod 1);
by (stac (zmod_zmult1_eq RS sym) 1);
by (stac (zcong_zmod RS sym) 1);
by (stac (power_Suc RS sym) 1);
by (stac lemma 1);
by (etac Little_Fermat 2);
by (etac zdvd_not_zless 2);
by (rewtac zprime_def);
by Auto_tac;
qed "inv_is_inv";

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> a ~= (inv p a)";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] zcong_square 1);
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 3);
by Auto_tac;
by (subgoal_tac "a=#1" 1);
by (res_inst_tac [("m","p")] zcong_zless_imp_eq 2);
by (subgoal_tac "a=p-#1" 7);
by (res_inst_tac [("m","p")] zcong_zless_imp_eq 8);
by Auto_tac;
qed "inv_distinct";

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a) ~= #0";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 1);
by (rewtac zcong_def);
by Auto_tac;
by (subgoal_tac "~p dvd #1" 1);
by (rtac zdvd_not_zless 2);
by (subgoal_tac "p dvd #1" 1);
by (stac (zdvd_zminus_iff RS sym) 2);
by Auto_tac;
qed "inv_not_0";

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a) ~= #1";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 1);
by (Asm_full_simp_tac 4);
by (subgoal_tac "a = #1" 4);
by (rtac zcong_zless_imp_eq 5);
by Auto_tac;
qed "inv_not_1";

Goalw [zcong_def] "[a*(p-#1) = #1](mod p) = [a = p-#1](mod p)"; 
by (simp_tac (simpset() addsimps [zdiff_zdiff_eq,zdiff_zdiff_eq2,
                                  zdiff_zmult_distrib2]) 1);
by (res_inst_tac [("s","p dvd -((a+#1)+(p*(-a)))")] trans 1);
by (simp_tac (simpset() addsimps [zmult_commute,zminus_zdiff_eq]) 1);
by (stac zdvd_zminus_iff 1);
by (stac zdvd_reduce 1);
by (res_inst_tac [("s","p dvd ((a+#1)+(p*(-#1)))")] trans 1);
by (stac zdvd_reduce 1);
by Auto_tac;
val lemma = result();

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a) ~= p-#1";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [lemma]) 1);
by (subgoal_tac "a = p-#1" 1);
by (rtac zcong_zless_imp_eq 2);
by Auto_tac;
qed "inv_not_p_minus_1";

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> #1<(inv p a)";
by (case_tac "#0<=(inv p a)" 1);
by (subgoal_tac "(inv p a) ~= #1" 1);
by (subgoal_tac "(inv p a) ~= #0" 1);
by (rtac zle_neq_implies_zless 1);
by (stac (zle_add1_eq_le RS sym) 1);
by (rtac zle_neq_implies_zless 1);
by (rtac inv_not_0 4);
by (rtac inv_not_1 7);
by Auto_tac;
by (rewrite_goals_tac [inv_def,zprime_def]);
by (asm_full_simp_tac (simpset() addsimps [pos_mod_sign]) 1);
qed "inv_g_1";

Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a)<p-#1";
by (case_tac "(inv p a)<p" 1);
by (rtac zle_neq_implies_zless 1);
by (rtac inv_not_p_minus_1 2);
by Auto_tac;
by (rewrite_goals_tac [inv_def,zprime_def]);
by (asm_full_simp_tac (simpset() addsimps [pos_mod_bound]) 1);
qed "inv_less_p_minus_1";

Goal "#5<=p ==> nat(p-#2)*nat(p-#2) = Suc(nat(p-#1)*nat(p-#3))";
by (stac (int_int_eq RS sym) 1);
by (asm_simp_tac (simpset() addsimps [zmult_int RS sym]) 1);
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib,
                                  zdiff_zmult_distrib2]) 1);
val lemma = result();

Goal "[x^y = #1](mod p) --> [x^(y*z) = #1](mod p)";
by (induct_tac "z" 1);
by (auto_tac (claset(),simpset() addsimps [zpower_zadd_distrib]));
by (subgoal_tac "zcong (x^y * x^(y*n)) (#1*#1) p" 1);
by (rtac zcong_zmult 2);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "zcong_zpower_zmult";

Goalw [inv_def] "[| p:zprime; #5<=p; #0<a; a<p |] ==> (inv p (inv p a)) = a";
by (stac zpower_zmod 1);
by (stac zpower_zpower 1);
by (rtac zcong_zless_imp_eq 1);
by (stac zcong_zmod 5); 
by (stac mod_mod_trivial 5);
by (stac (zcong_zmod RS sym) 5); 
by (stac lemma 5);
by (subgoal_tac "zcong (a * a^(nat (p - #1) * nat (p - #3))) (a*#1) p" 6);
by (rtac zcong_zmult 7);
by (rtac zcong_zpower_zmult 8);
by (etac Little_Fermat 8);
by (rtac zdvd_not_zless 8);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [pos_mod_bound,
                                                     pos_mod_sign])));
qed "inv_inv";


(*************  wset  *************)

val [wset_eq] = wset.simps;
Delsimps wset.simps;

val [prem1,prem2] =
Goal "[| !!a p. P {} a p; \
\        !!a p. [| #1<(a::int); P (wset (a-#1,p)) (a-#1) p |] \
\               ==> P (wset (a,p)) a p|] \
\    ==> P (wset (u,v)) u v";
by (rtac wset.induct 1);
by Safe_tac;
by (case_tac "#1<a" 2);
by (rtac prem2 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [wset_eq,prem1])));
qed "wset_induct";

Goal "[| #1<a; b~:(wset (a-#1,p)) |] \
\     ==> b:(wset (a,p)) --> b=a | b = inv p a";
by (stac wset_eq 1);
by (rewtac Let_def);
by (Asm_simp_tac 1);
qed_spec_mp "wset_mem_imp_or";

Goal "#1<a ==> a:(wset(a,p))";
by (stac wset_eq 1);
by (rewtac Let_def);
by (Asm_simp_tac 1);
qed "wset_mem_mem";
Addsimps [wset_mem_mem];

Goal "[| #1<a; b:wset(a-#1,p) |] ==> b:wset(a,p)";
by (stac wset_eq 1);
by (rewtac Let_def);
by Auto_tac;
qed "wset_subset";

Goal "p:zprime --> a<p-#1 --> b:(wset(a,p)) --> #1<b";
by (res_inst_tac [("u","a"),("v","p")] wset_induct 1);
by Auto_tac;
by (case_tac "b=a" 1);
by (case_tac "b=inv p a" 2);
by (subgoal_tac "b=a | b = inv p a" 3);
by (rtac wset_mem_imp_or 4);
by (Asm_simp_tac 2);
by (rtac inv_g_1 2);
by Auto_tac;
qed_spec_mp "wset_g_1";

Goal "p:zprime --> a<p-#1 --> b:(wset(a,p)) --> b<p-#1";
by (res_inst_tac [("u","a"),("v","p")] wset_induct 1);
by Auto_tac;
by (case_tac "b=a" 1);
by (case_tac "b=inv p a" 2);
by (subgoal_tac "b=a | b = inv p a" 3);
by (rtac wset_mem_imp_or 4);
by (Asm_simp_tac 2);
by (rtac inv_less_p_minus_1 2);
by Auto_tac;
qed_spec_mp "wset_less";

Goal "p:zprime --> a<p-#1 --> #1<b --> b<=a --> b:(wset(a,p))"; 
by (res_inst_tac [("u","a"),("v","p")] wset.induct 1);
by Auto_tac;
by (subgoal_tac "b=a" 1);
by (rtac zle_anti_sym 2);
by (rtac wset_subset 4);
by (Asm_simp_tac 1);
by Auto_tac;
qed_spec_mp "wset_mem";

Goal "p:zprime --> #5<=p --> a<p-#1 --> b:(wset (a,p)) \
\     --> (inv p b):(wset (a,p))";
by (res_inst_tac [("u","a"),("v","p")] wset_induct 1);
by Auto_tac;
by (case_tac "b=a" 1);
by (stac wset_eq 1);
by (rewtac Let_def);
by (rtac wset_subset 3);
by Auto_tac;
by (case_tac "b = inv p a" 1);
by (Asm_simp_tac 1);
by (stac inv_inv 1);
by (subgoal_tac "b=a | b = inv p a" 6);
by (rtac wset_mem_imp_or 7);
by Auto_tac;
qed_spec_mp "wset_mem_inv_mem";

Goal "[| p:zprime; #5<=p; a<p-#1; #1<b; b<p-#1; (inv p b):(wset (a,p)) |] \
\    ==> b:(wset (a,p))";
by (res_inst_tac [("s","inv p (inv p b)"),("t","b")] subst 1);
by (rtac wset_mem_inv_mem 2);
by (rtac inv_inv 1);
by (ALLGOALS (Asm_simp_tac));
qed "wset_inv_mem_mem";

Goal "finite (wset (a,p))";
by (res_inst_tac [("u","a"),("v","p")] wset_induct 1);
by (stac wset_eq 2);
by (rewtac Let_def);
by Auto_tac;
qed "wset_fin";

Goal "p:zprime --> #5<=p --> a<p-#1 --> [setprod (wset (a,p)) = #1](mod p)";
by (res_inst_tac [("u","a"),("v","p")] wset_induct 1);
by (stac wset_eq 2);
by (rewtac Let_def);
by Auto_tac;
by (stac setprod_insert 1);
by (stac setprod_insert 3);
by (subgoal_tac "zcong (a * (inv p a) * setprod(wset(a-#1,p))) (#1*#1) p" 5);
by (asm_full_simp_tac (simpset() addsimps [zmult_assoc]) 5);
by (rtac zcong_zmult 5);
by (rtac inv_is_inv 5);
by (Clarify_tac 4);
by (subgoal_tac "a:wset(a-#1,p)" 4);
by (rtac wset_inv_mem_mem 5);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [wset_fin])));
by (rtac inv_distinct 1);
by Auto_tac;
qed_spec_mp "wset_zcong_prod_1";

Goal "p:zprime ==> d22set(p-#2) = wset(p-#2,p)";
by Safe_tac;
by (etac wset_mem 1); 
by (rtac d22set_g_1 2);
by (rtac d22set_le 3);
by (rtac d22set_mem 4);
by (etac wset_g_1 4);
by (stac (zle_add1_eq_le RS sym) 6); 
by (subgoal_tac "p-#2+#1 = p-#1" 6);
by (Asm_simp_tac 6);
by (etac wset_less 6);
by Auto_tac;
qed "d22set_eq_wset";

(**********  Wilson  *************)

Goal "[| z-#1<=w; z-#1~=w |] ==> z<=(w::int)";
by (stac (zle_add1_eq_le RS sym) 1);
by (rtac zle_neq_implies_zless 1);
by Auto_tac;
val lemma = result();

Goalw [zprime_def,dvd_def] "[| p : zprime; p ~= #2; p ~= #3 |] ==> #5<=p";
by (case_tac "p=#4" 1);
by Auto_tac;
by (rtac notE 1);
by (assume_tac 2);
by (Simp_tac 1);
by (res_inst_tac [("x","#2")] exI 1);
by Safe_tac;
by (res_inst_tac [("x","#2")] exI 1);
by Auto_tac;
by (rtac lemma 1);
by (rtac lemma 1);
by (rtac lemma 1);
by Auto_tac;
qed "prime_g_5";

Goal "p:zprime ==> [zfact(p-#1) = #-1] (mod p)";
by (subgoal_tac "[(p-#1)*zfact(p-#2) = #-1*#1] (mod p)" 1);
by (rtac zcong_zmult 2);
by (SELECT_GOAL (rewtac zprime_def) 1);
by (stac zfact_eq 1);
by (res_inst_tac [("t","p-#1-#1"),("s","p-#2")] subst 1);
by Auto_tac;
by (SELECT_GOAL (rewtac zcong_def) 1);
by (Asm_simp_tac 1);
by (case_tac "p=#2" 1);
by (asm_full_simp_tac (simpset() addsimps [zfact_eq]) 1);
by (case_tac "p=#3" 1);
by (asm_full_simp_tac (simpset() addsimps [zfact_eq]) 1);
by (subgoal_tac "#5<=p" 1);
by (etac prime_g_5 2);
by (stac (d22set_prod_zfact RS sym) 1);
by (stac d22set_eq_wset 1);
by (rtac wset_zcong_prod_1 2);
by Auto_tac;
qed "WilsonRuss";
