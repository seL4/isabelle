(*  Title:	WilsonBij.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Wilson's Theorem using a more "abstract" approach based on
bijections between sets.  Does not use Fermat's Little Theorem
(unlike Russinoff)
 *)


(************  Inverse  **************)

Goalw [inv_def] 
      "[| p:zprime; #0<a; a<p |] \ 
\     ==> #0 <= (inv p a) & (inv p a)<p & [a*(inv p a) = #1](mod p)";
by (Asm_simp_tac 1);
by (rtac (zcong_lineq_unique RS ex1_implies_ex RS ex_someI) 1);
by (etac zless_zprime_imp_zrelprime 2);
by (rewtac zprime_def);
by Auto_tac;
qed "inv_correct";

bind_thm ("inv_ge",inv_correct RS conjunct1);
bind_thm ("inv_less",(inv_correct RS conjunct2) RS conjunct1);
bind_thm ("inv_is_inv",(inv_correct RS conjunct2) RS conjunct2);

(* Same as WilsonRuss *)
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

(* Same as WilsonRuss *)
Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a) ~= #1";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 1);
by (Asm_full_simp_tac 4);
by (subgoal_tac "a = #1" 4);
by (rtac zcong_zless_imp_eq 5);
by Auto_tac;
qed "inv_not_1";

(* Same as WilsonRuss *)
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

(* Same as WilsonRuss *)
Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a) ~= p-#1";
by Safe_tac;
by (cut_inst_tac [("a","a"),("p","p")] inv_is_inv 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [lemma]) 1);
by (subgoal_tac "a = p-#1" 1);
by (rtac zcong_zless_imp_eq 2);
by Auto_tac;
qed "inv_not_p_minus_1";

(* Below is slightly different as we don't expand 
   inv but use 'correct'-theos *)
Goal "[| p:zprime; #1<a; a<p-#1 |] ==> #1<(inv p a)";
by (subgoal_tac "(inv p a) ~= #1" 1);
by (subgoal_tac "(inv p a) ~= #0" 1);
by (rtac zle_neq_implies_zless 1);
by (stac (zle_add1_eq_le RS sym) 1);
by (rtac zle_neq_implies_zless 1);
by (rtac inv_not_0 4);
by (rtac inv_not_1 7);
by Auto_tac;
by (rtac inv_ge 1);
by Auto_tac;
qed "inv_g_1";

(* ditto *)
Goal "[| p:zprime; #1<a; a<p-#1 |] ==> (inv p a)<p-#1";
by (rtac zle_neq_implies_zless 1);
by (rtac inv_not_p_minus_1 2);
by Auto_tac;
by (rtac inv_less 1);
by Auto_tac;
qed "inv_less_p_minus_1";

(*************  Bijection  *******************)

Goal "#1<x ==> #0<=(x::int)";
by Auto_tac;
val l1 = result();

Goal "#1<x ==> #0<(x::int)";
by Auto_tac;
val l2 = result();

Goal "x<=p-#2 ==> x<(p::int)";
by Auto_tac;
val l3 = result();

Goal "x<=p-#2 ==> x<(p::int)-#1";
by Auto_tac;
val l4 = result();

Goalw [inj_on_def] "p : zprime ==> inj_on (inv p) (d22set (p-#2))";
by Auto_tac;
by (rtac zcong_zless_imp_eq 1);
by (stac (zcong_cancel RS sym) 5);
by (rtac zcong_trans 7);
by (stac zcong_sym 8);
by (etac inv_is_inv 7);
by (Asm_simp_tac 9);
by (etac inv_is_inv 9);
by (rtac zless_zprime_imp_zrelprime 6);
by (rtac inv_less 8);
by (rtac (inv_g_1 RS l2) 7);
by (rewtac zprime_def);
by (auto_tac (claset() addIs [d22set_g_1,d22set_le,l1,l2,l3,l4],simpset()));
qed "inv_inj";

Goal "p : zprime ==> (inv p)``(d22set (p-#2)) = (d22set (p-#2))";
by (rtac endo_inj_surj 1);
by (rtac d22set_fin 1);
by (etac inv_inj 2);
by Auto_tac;
by (rtac d22set_mem 1);
by (etac inv_g_1 1);
by (subgoal_tac "inv p xa < p - #1" 3);
by (etac inv_less_p_minus_1 4);
by (auto_tac (claset() addIs [d22set_g_1,d22set_le,l4],simpset()));
qed "inv_d22set_d22set";

Goalw [reciR_def] "p:zprime \
\    ==> (d22set(p-#2),d22set(p-#2)) : (bijR (reciR p))";
by (res_inst_tac [("s","(d22set(p-#2),(inv p)``(d22set(p-#2)))")] subst 1);
by (asm_simp_tac (simpset() addsimps [inv_d22set_d22set]) 1);
by (rtac inj_func_bijR 1);
by (rtac d22set_fin 3);
by (etac inv_inj 2);
by Auto_tac;
by (etac inv_is_inv 1);
by (etac inv_g_1 5);
by (etac inv_less_p_minus_1 7);
by (auto_tac (claset() addIs [d22set_g_1,d22set_le,l2,l3,l4],simpset()));
qed "d22set_d22set_bij";

Goalw [reciR_def,bijP_def] 
      "p:zprime ==>  bijP (reciR p) (d22set(p-#2))";
by Auto_tac;
by (rtac d22set_mem 1);
by Auto_tac;
qed "reciP_bijP";

Goalw [reciR_def,uniqP_def] 
      "p:zprime ==> uniqP (reciR p)";
by Auto_tac;
by (rtac zcong_zless_imp_eq 1);
by (stac (zcong_cancel2 RS sym) 5);
by (rtac zcong_trans 7);
by (stac zcong_sym 8);
by (rtac zless_zprime_imp_zrelprime 6);
by Auto_tac;
by (rtac zcong_zless_imp_eq 1);
by (stac (zcong_cancel RS sym) 5);
by (rtac zcong_trans 7);
by (stac zcong_sym 8);
by (rtac zless_zprime_imp_zrelprime 6);
by Auto_tac;
qed "reciP_uniq";

Goalw [reciR_def,symP_def] 
      "p:zprime ==> symP (reciR p)";
by (simp_tac (simpset() addsimps [zmult_commute]) 1);
by Auto_tac;
qed "reciP_sym";

Goal "p:zprime ==> d22set(p-#2) : (bijER (reciR p))";
by (rtac bijR_bijER 1);
by (etac d22set_d22set_bij 1);
by (etac reciP_bijP 1);
by (etac reciP_uniq 1);
by (etac reciP_sym 1);
qed "bijER_d22set";

(***********  Wilson  **************)

Goalw [reciR_def] 
      "[| p:zprime; A : bijER (reciR p) |] ==> [setprod A = #1](mod p)";
by (etac bijER.induct 1);
by (subgoal_tac "a=#1 | a=p-#1" 2);
by (rtac zcong_square_zless 3);
by Auto_tac;
by (stac setprod_insert 1);
by (stac setprod_insert 3);
by (auto_tac (claset(),simpset() addsimps [fin_bijER]));
by (subgoal_tac "zcong ((a * b) * setprod A) (#1*#1) p" 1);
by (asm_full_simp_tac (simpset() addsimps [zmult_assoc]) 1);
by (rtac zcong_zmult 1); 
by Auto_tac;
qed "bijER_zcong_prod_1";

Goal "p:zprime ==> [zfact(p-#1) = #-1](mod p)";
by (subgoal_tac "zcong ((p-#1)*zfact(p-#2)) (#-1*#1) p" 1);
by (rtac zcong_zmult 2);
by (full_simp_tac (simpset() addsimps [zprime_def]) 1); 
by (stac zfact_eq 1);
by (res_inst_tac [("t","p-#1-#1"),("s","p-#2")] subst 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [zcong_def]) 1); 
by (stac (d22set_prod_zfact RS sym) 1);
by (rtac bijER_zcong_prod_1 1);
by (rtac bijER_d22set 2);
by Auto_tac;
qed "WilsonBij";
