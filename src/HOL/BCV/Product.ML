(*  Title:      HOL/BCV/Product.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [lesub_def] "p <=(rA,rB) q == le rA rB p q";
by (Simp_tac 1);
qed "unfold_lesub_prod";

Goalw [lesub_def,le_def]
 "((a1,b1) <=(rA,rB) (a2,b2)) = (a1 <=_rA a2 & b1 <=_rB b2)";
by(Simp_tac 1);
qed "le_prod_Pair_conv";
AddIffs [le_prod_Pair_conv];

Goalw [lesssub_def]
 "((a1,b1) <_(Product.le rA rB) (a2,b2)) = \
\ (a1 <_rA a2 & b1 <=_rB b2 | a1 <=_rA a2 & b1 <_rB b2)";
by(Simp_tac 1);
by(Blast_tac 1);
qed "less_prod_Pair_conv";

Goalw [order_def] "order(Product.le rA rB) = (order rA & order rB)";
by(Simp_tac 1);
by(Blast_tac 1);
qed "order_le_prod";
AddIffs [order_le_prod];


Goalw [acc_def] "[| acc rA; acc rB |] ==> acc(Product.le rA rB)";
br wf_subset 1;
 be wf_lex_prod 1;
 ba 1;
by(auto_tac (claset(), simpset()
     addsimps [lesssub_def,less_prod_Pair_conv,lex_prod_def]));
qed "acc_le_prodI";
AddSIs [acc_le_prodI];


Goalw [closed_def,plussub_def,lift2_def,err_def,sup_def]
 "[| closed (err A) (lift2 f); closed (err B) (lift2 g) |] ==> \
\ closed (err(A<*>B)) (lift2(sup f g))";
by(asm_full_simp_tac (simpset() addsplits [err.split]) 1);
by(Blast_tac 1);
qed "closed_lift2_sup";

Goalw [plussub_def] "e1 +_(lift2 f) e2 == lift2 f e1 e2";
by (Simp_tac 1);
qed "unfold_plussub_lift2";

Goal
 "[| x:A; y:A; semilat(err A, Err.le r, lift2 f) |] ==> \
\ (x +_f y = Err) = (~(? z:A. x <=_r z & y <=_r z))";
br iffI 1;
 by (Clarify_tac 1);
 bd (OK_le_err_OK RS iffD2) 1;
 bd (OK_le_err_OK RS iffD2) 1;
 bd semilat_lub 1;
      ba 1;
     ba 1;
    by(Asm_simp_tac 1); 
   by(Asm_simp_tac 1); 
  by(Asm_simp_tac 1); 
 by(Asm_full_simp_tac 1);
by(case_tac "x +_f y" 1);
 ba 1;
by(rename_tac "z" 1);
by(subgoal_tac "OK z: err A" 1);
 by(ftac (rotate_prems 2 (read_instantiate_sg(sign_of Err.thy)[("x","OK(x::'a)"),("y","OK(y::'a)")]plus_le_conv RS iffD1))1);
     ba 1;
    by(Asm_simp_tac 1); 
    by(blast_tac (claset() addDs [semilatDorderI,order_refl]) 1);
   by(Asm_simp_tac 1); 
  by(Asm_simp_tac 1);
 by(Blast_tac 1);
by(etac subst 1);
by(rewrite_goals_tac [semilat_def,err_def,closed_def]);
by(Asm_full_simp_tac 1);
qed "plus_eq_Err_conv";
Addsimps [plus_eq_Err_conv];

Goalw [esl_def,Err.sl_def]
 "!!L1 L2. [| err_semilat L1; err_semilat L2 |] ==> err_semilat(Product.esl L1 L2)";
by(split_all_tac 1);
by(Asm_full_simp_tac 1);
by(simp_tac (HOL_basic_ss addsimps [semilat_Def]) 1);
by(asm_simp_tac(HOL_basic_ss addsimps[semilatDclosedI,closed_lift2_sup])1);
by(simp_tac (HOL_basic_ss addsimps
     [unfold_lesub_err,Err.le_def,unfold_plussub_lift2,sup_def]) 1);
by (auto_tac (claset() addEs [semilat_le_err_OK1,semilat_le_err_OK2],
      simpset() addsimps [lift2_def] addsplits [err.split]));
by(blast_tac (claset() addDs [semilatDorderI]) 1);
by(blast_tac (claset() addDs [semilatDorderI]) 1);

br (OK_le_err_OK RS iffD1) 1;
by(etac subst 1 THEN stac (OK_lift2_OK RS sym) 1 THEN rtac semilat_lub 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);

br (OK_le_err_OK RS iffD1) 1;
by(etac subst 1 THEN stac (OK_lift2_OK RS sym) 1 THEN rtac semilat_lub 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 1);

qed "err_semilat_Product_esl";
