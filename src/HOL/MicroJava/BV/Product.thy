(*  Title:      HOL/MicroJava/BV/Product.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Products as semilattices
*)

header {* \isaheader{Products as Semilattices} *}

theory Product = Err:

constdefs
 le :: "'a ord => 'b ord => ('a * 'b) ord"
"le rA rB == %(a,b) (a',b'). a <=_rA a' & b <=_rB b'"

 sup :: "'a ebinop => 'b ebinop => ('a * 'b)ebinop"
"sup f g == %(a1,b1)(a2,b2). Err.sup Pair (a1 +_f a2) (b1 +_g b2)"

 esl :: "'a esl => 'b esl => ('a * 'b ) esl"
"esl == %(A,rA,fA) (B,rB,fB). (A <*> B, le rA rB, sup fA fB)"

syntax "@lesubprod" :: "'a*'b => 'a ord => 'b ord => 'b => bool"
       ("(_ /<='(_,_') _)" [50, 0, 0, 51] 50)
translations "p <=(rA,rB) q" == "p <=_(Product.le rA rB) q"

lemma unfold_lesub_prod:
  "p <=(rA,rB) q == le rA rB p q"
  by (simp add: lesub_def)

lemma le_prod_Pair_conv [iff]:
  "((a1,b1) <=(rA,rB) (a2,b2)) = (a1 <=_rA a2 & b1 <=_rB b2)"
  by (simp add: lesub_def le_def)

lemma less_prod_Pair_conv:
  "((a1,b1) <_(Product.le rA rB) (a2,b2)) = 
  (a1 <_rA a2 & b1 <=_rB b2 | a1 <=_rA a2 & b1 <_rB b2)"
apply (unfold lesssub_def)
apply simp
apply blast
done

lemma order_le_prod [iff]:
  "order(Product.le rA rB) = (order rA & order rB)"
apply (unfold order_def)
apply simp
apply blast
done 


lemma acc_le_prodI [intro!]:
  "[| acc rA; acc rB |] ==> acc(Product.le rA rB)"
apply (unfold acc_def)
apply (rule wf_subset)
 apply (erule wf_lex_prod)
 apply assumption
apply (auto simp add: lesssub_def less_prod_Pair_conv lex_prod_def)
done


lemma closed_lift2_sup:
  "[| closed (err A) (lift2 f); closed (err B) (lift2 g) |] ==> 
  closed (err(A<*>B)) (lift2(sup f g))";
apply (unfold closed_def plussub_def lift2_def err_def sup_def)
apply (simp split: err.split)
apply blast
done 

lemma unfold_plussub_lift2:
  "e1 +_(lift2 f) e2 == lift2 f e1 e2"
  by (simp add: plussub_def)


lemma plus_eq_Err_conv [simp]:
  "[| x:A; y:A; semilat(err A, Err.le r, lift2 f) |] 
  ==> (x +_f y = Err) = (~(? z:A. x <=_r z & y <=_r z))"
proof -
  have plus_le_conv2:
    "!!r f z. [| z : err A; semilat (err A, r, f); OK x : err A; OK y : err A;
                 OK x +_f OK y <=_r z|] ==> OK x <=_r z \<and> OK y <=_r z"
    by (rule plus_le_conv [THEN iffD1])
  case rule_context
  thus ?thesis
  apply (rule_tac iffI)
   apply clarify
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule semilat_lub)
        apply assumption
       apply assumption
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac "x +_f y")
   apply assumption
  apply (rename_tac "z")
  apply (subgoal_tac "OK z: err A")
  apply (frule plus_le_conv2)
       apply assumption
      apply simp
      apply blast
     apply simp
    apply (blast dest: semilatDorderI order_refl)
   apply blast
  apply (erule subst)
  apply (unfold semilat_def err_def closed_def)
  apply simp
  done
qed

lemma err_semilat_Product_esl:
  "!!L1 L2. [| err_semilat L1; err_semilat L2 |] ==> err_semilat(Product.esl L1 L2)"
apply (unfold esl_def Err.sl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (simp (no_asm) only: semilat_Def)
apply (simp (no_asm_simp) only: semilatDclosedI closed_lift2_sup)
apply (simp (no_asm) only: unfold_lesub_err Err.le_def unfold_plussub_lift2 sup_def)
apply (auto elim: semilat_le_err_OK1 semilat_le_err_OK2
            simp add: lift2_def  split: err.split)
apply (blast dest: semilatDorderI)
apply (blast dest: semilatDorderI)

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule semilat_lub)
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule semilat_lub)
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
done 

end
