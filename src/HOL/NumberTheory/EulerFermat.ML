(*  Title:	EulerFermat.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Fermat's Little Theorem extended to Euler's Totient function.
More abstract approach than Boyer-Moore (which seems necessary
to achieve the extended version)
*)

(*LCP: not sure why this lemma is needed now*)
Goal "(abs z = (#1::int)) = (z = #1 | z = #-1)";
by (auto_tac (claset(), simpset() addsimps [zabs_def]));  
qed "abs_eq_1_iff";
AddIffs [abs_eq_1_iff];


(***  norRRset  ***)

Addsimps [RsetR.empty];

val [BnorRset_eq] = BnorRset.simps;
Delsimps BnorRset.simps;

val [prem1,prem2] =
Goal "[| !! a m. P {} a m; \
\       (!!a m. [| #0 < (a::int); P (BnorRset(a-#1,m::int)) (a-#1) m |] \
\               ==> P (BnorRset(a,m)) a m) |] \
\    ==> P (BnorRset(u,v)) u v";
by (rtac BnorRset.induct 1);
by Safe_tac;
by (case_tac "#0<a" 2);
by (rtac prem2 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [BnorRset_eq,prem1])));
qed "BnorRset_induct";

Goal "b:BnorRset(a,m) --> b<=a";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (stac BnorRset_eq 2);
by (rewtac Let_def);
by Auto_tac;
qed_spec_mp "Bnor_mem_zle"; 

Goal "a<b ==> b~:BnorRset(a,m)";
by (auto_tac (claset() addDs [Bnor_mem_zle], simpset()));  
qed "Bnor_mem_zle_swap";

Goal "b:BnorRset(a,m) --> #0<b";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (stac BnorRset_eq 2);
by (rewtac Let_def);
by Auto_tac;
qed_spec_mp "Bnor_mem_zg"; 

Goal "zgcd(b,m) = #1 --> #0<b --> b<=a --> b:BnorRset(a,m)";
by (induct_thm_tac BnorRset.induct "a m" 1);
by Auto_tac;
by (case_tac "a=b" 1);
by (asm_full_simp_tac (simpset() addsimps [zle_neq_implies_zless]) 2);
by (Asm_simp_tac 1);
by (ALLGOALS (stac BnorRset_eq));
by (rewtac Let_def);
by Auto_tac;
qed_spec_mp "Bnor_mem_if";

Goal "a<m --> BnorRset (a,m) : RsetR m";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (Simp_tac 1);
by (stac BnorRset_eq 1);
by (rewtac Let_def);
by Auto_tac;
by (rtac RsetR.insert 1);
by (rtac allI 3);
by (rtac impI 3);
by (rtac zcong_not 3);
by (subgoal_tac "a' <= a-#1" 6);
by (rtac Bnor_mem_zle 7);
by (rtac Bnor_mem_zg 5);
by Auto_tac;
qed_spec_mp "Bnor_in_RsetR";

Goal "finite (BnorRset (a,m))";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (stac BnorRset_eq 2);
by (rewtac Let_def);
by Auto_tac;
qed "Bnor_fin";

Goal "a <= b - #1 ==> a < (b::int)";
by Auto_tac;
val lemma = result();

Goalw [norRRset_def]
     "[| #1<m; zgcd(a,m) = #1 |] ==> (EX! b. [a = b](mod m) & b:(norRRset m))";
by (cut_inst_tac [("a","a"),("m","m")] zcong_zless_unique 1);
by Auto_tac;
by (res_inst_tac [("m","m")] zcong_zless_imp_eq 2);
by (auto_tac (claset() addIs [Bnor_mem_zle,Bnor_mem_zg,zcong_trans,
                              zless_imp_zle,lemma],
              simpset() addsimps [zcong_sym]));
by (res_inst_tac [("x","b")] exI 1);
by Safe_tac;
by (rtac Bnor_mem_if 1);
by (case_tac "b=#0" 2);
by (auto_tac (claset() addIs [zle_neq_implies_zless], simpset()));
by (SELECT_GOAL (rewtac zcong_def) 2);
by (subgoal_tac "zgcd(a,m) = m" 2);
by (stac (zdvd_iff_zgcd RS sym) 3);
by (rtac zgcd_zcong_zgcd 1);
by (ALLGOALS (asm_full_simp_tac (simpset() 
      addsimps [zdvd_zminus_iff,zcong_sym])));
qed "norR_mem_unique";


(***  noXRRset  ***)

Goalw [is_RRset_def] 
      "is_RRset A m ==> a:A --> zgcd (a,m) = #1";
by (rtac RsetR.induct 1);
by Auto_tac;
qed_spec_mp "RRset_gcd";

Goal "[| A : RsetR m;  #0<m; zgcd(x, m) = #1 |] ==> (%a. a*x)``A : RsetR m";
by (etac RsetR.induct 1);
by (ALLGOALS Simp_tac);
by (rtac RsetR.insert 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [zcong_cancel]) 2);
by (blast_tac (claset() addIs [zgcd_zgcd_zmult]) 1);
qed "RsetR_zmult_mono";

Goalw [norRRset_def,noXRRset_def]
      "[| #0<m; zgcd(x,m) = #1 |] \
\     ==> card (noXRRset m x) = card (norRRset m)";
by (rtac card_image 1);
by (auto_tac (claset(),simpset() addsimps [inj_on_def, Bnor_fin]));
by (asm_full_simp_tac (simpset() addsimps [BnorRset_eq]) 1);
qed "card_nor_eq_noX";

Goalw [is_RRset_def,phi_def]
      "[| #0<m; zgcd(x,m) = #1 |] ==> is_RRset (noXRRset m x) m";
by (auto_tac (claset(),simpset() addsimps [card_nor_eq_noX]));
by (rewrite_goals_tac [noXRRset_def,norRRset_def]);
by (rtac RsetR_zmult_mono 1);
by (rtac Bnor_in_RsetR 1);
by (ALLGOALS Asm_simp_tac);
qed "noX_is_RRset";

Goal "[| #1<m; is_RRset A m; a:A |] \
\     ==> zcong a (@ b. [a = b](mod m) & b : norRRset m) m & \
\         (@ b. [a = b](mod m) & b : norRRset m) : norRRset m";
by (rtac (norR_mem_unique RS ex1_implies_ex RS someI_ex) 1);
by (rtac RRset_gcd 2);
by (ALLGOALS Asm_simp_tac);
val lemma_some = result();

Goalw [RRset2norRR_def]
     "[| #1<m; is_RRset A m; a:A |] \
\     ==> [a = RRset2norRR A m a] (mod m) & (RRset2norRR A m a):(norRRset m)";
by (Asm_simp_tac 1);
by (rtac lemma_some 1);
by (ALLGOALS Asm_simp_tac);
qed "RRset2norRR_correct";

bind_thm ("RRset2norRR_correct1", RRset2norRR_correct RS conjunct1);
bind_thm ("RRset2norRR_correct2", RRset2norRR_correct RS conjunct2);

Goal "A : (RsetR m) ==> finite A";
by (etac RsetR.induct 1);
by Auto_tac;
qed "RsetR_fin";

Goalw [is_RRset_def] 
      "[| #1<m; is_RRset A m; [a = b](mod m) |] ==> a:A --> b:A --> a = b";
by (rtac RsetR.induct 1);
by (auto_tac (claset(), simpset() addsimps [zcong_sym]));
qed_spec_mp "RRset_zcong_eq";

Goal "[| P (@ a. P a); Q (@ a. Q a); (@ a. P a) = (@ a. Q a) |] \
\    ==> (EX a. P a & Q a)";
by Auto_tac;
val lemma = result();

Goalw [RRset2norRR_def,inj_on_def]
      "[| #1<m; is_RRset A m |] ==> inj_on (RRset2norRR A m) A";
by Auto_tac;
by (subgoal_tac "(EX b. ([x = b](mod m) & b : norRRset m) & \
\                       ([y = b](mod m) & b : norRRset m))" 1);
by (rtac lemma 2);
by (rtac lemma_some 3);
by (rtac lemma_some 2);
by (rtac RRset_zcong_eq 1);
by Auto_tac;
by (res_inst_tac [("b","b")] zcong_trans 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zcong_sym])));
qed "RRset2norRR_inj";

Goal "[| #1<m; is_RRset A m |] ==> (RRset2norRR A m)``A = (norRRset m)";
by (rtac card_seteq 1);
by (stac card_image 3);
by (rtac RRset2norRR_inj 4);
by Auto_tac;
by (rtac RRset2norRR_correct2 2);
by Auto_tac;
by (rewrite_goals_tac [is_RRset_def,phi_def,norRRset_def]);
by (auto_tac (claset(),simpset() addsimps [RsetR_fin,Bnor_fin]));
qed "RRset2norRR_eq_norR";

Goalw [inj_on_def] "[| a ~: A ; inj f |] ==> (f a) ~: f``A";
by Auto_tac;
val lemma = result();

Goal "x~=#0 ==> a<m --> setprod ((%a. a*x) `` BnorRset(a,m)) = \
\     setprod (BnorRset(a,m)) * x^card(BnorRset(a,m))";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (stac BnorRset_eq 2);
by (rewtac Let_def);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [Bnor_fin,Bnor_mem_zle_swap]) 1);
by (stac setprod_insert 1);
by (rtac lemma 2);
by (rewtac inj_on_def);
by (ALLGOALS (asm_full_simp_tac (simpset() 
      addsimps zmult_ac@[Bnor_fin,finite_imageI,Bnor_mem_zle_swap])));
qed_spec_mp "Bnor_prod_power";


(***  Fermat  ***)

Goalw [zcongm_def] 
      "(A,B) : bijR (zcongm m) ==> [setprod A = setprod B](mod m)";
by (etac bijR.induct 1);
by (subgoal_tac "a~:A & b~:B & finite A & finite B" 2); 
by (auto_tac (claset() addIs [fin_bijRl,fin_bijRr,zcong_zmult],
              simpset()));
qed "bijzcong_zcong_prod";

Goalw [norRRset_def,phi_def]
      "a<m --> zgcd (setprod (BnorRset (a,m)),m) = #1";
by (induct_thm_tac BnorRset_induct "a m" 1);
by (stac BnorRset_eq 2);
by (rewtac Let_def);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [Bnor_fin,Bnor_mem_zle_swap]) 1);
by (blast_tac (claset() addIs [zgcd_zgcd_zmult]) 1);
qed_spec_mp "Bnor_prod_zgcd";

Goalw [norRRset_def,phi_def]
      "[| #0<m; zgcd(x,m) = #1 |] ==> [x^phi(m) = #1] (mod m)";
by (case_tac "x=#0" 1);
by (case_tac "m=#1" 2);
by (rtac iffD1 3);
by (res_inst_tac [("k","setprod (BnorRset (m-#1,m))")] zcong_cancel2 3);
by (stac (Bnor_prod_power RS sym) 5);
by (rtac Bnor_prod_zgcd 4);
by (ALLGOALS Asm_full_simp_tac);
by (rtac bijzcong_zcong_prod 1);
by (fold_goals_tac [norRRset_def,noXRRset_def]);
by (stac (RRset2norRR_eq_norR RS sym) 1);
by (rtac inj_func_bijR 3);
by Auto_tac;
by (rewtac zcongm_def);
by (rtac RRset2norRR_correct1 3);
by (rtac RRset2norRR_inj 6);
by (auto_tac (claset() addIs [zle_neq_implies_zless], 
              simpset() addsimps [noX_is_RRset]));
by (rewrite_goals_tac [noXRRset_def,norRRset_def]);
by (rtac finite_imageI 1);
by (rtac Bnor_fin 1);
qed "EulerFermatTheorem";

Goalw [zprime_def] 
      "p:zprime ==> a<p --> (ALL b. #0<b & b<=a --> zgcd(b,p) = #1) \
\      --> card (BnorRset(a, p)) = nat a";
by (induct_thm_tac BnorRset.induct "a p" 1);
by (stac BnorRset_eq 1);
by (rewtac Let_def);
by Auto_tac;
qed_spec_mp "Bnor_prime";

Goalw [phi_def,norRRset_def]
      "p:zprime ==> phi(p) = nat (p-#1)"; 
by (rtac Bnor_prime 1);
by Auto_tac;
by (etac zless_zprime_imp_zrelprime 1);
by (ALLGOALS Asm_simp_tac);
qed "phi_prime";

Goal "[| p:zprime; ~p dvd x |] ==> [x^(nat (p-#1)) = #1] (mod p)";
by (stac (phi_prime RS sym) 1);
by (rtac EulerFermatTheorem 2);
by (etac zprime_imp_zrelprime 3);
by (rewtac zprime_def);
by Auto_tac;
qed "Little_Fermat";

