(*  Title:      HOLCF/ex/Loop.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Theory for a loop primitive like while
*)

(* ------------------------------------------------------------------------- *)
(* access to definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val step_def2 = prove_goalw Loop.thy [step_def]
"step`b`g`x = If b`x then g`x else x fi"
 (fn prems =>
        [
        (Simp_tac 1)
        ]);

val while_def2 = prove_goalw Loop.thy [while_def]
"while`b`g = fix`(LAM f x. If b`x then f`(g`x) else x fi)"
 (fn prems =>
        [
        (Simp_tac 1)
        ]);


(* ------------------------------------------------------------------------- *)
(* rekursive properties of while                                             *)
(* ------------------------------------------------------------------------- *)

val while_unfold = prove_goal Loop.thy 
"while`b`g`x = If b`x then while`b`g`(g`x) else x fi"
 (fn prems =>
        [
        (fix_tac5  while_def2 1),
        (Simp_tac 1)
        ]);

val while_unfold2 = prove_goal Loop.thy 
        "ALL x. while`b`g`x = while`b`g`(iterate k (step`b`g) x)"
 (fn prems =>
        [
        (nat_ind_tac "k" 1),
        (simp_tac HOLCF_ss 1),
        (rtac allI 1),
        (rtac trans 1),
        (stac while_unfold 1),
        (rtac refl 2),
        (stac iterate_Suc2 1),
        (rtac trans 1),
        (etac spec 2),
        (stac step_def2 1),
        (res_inst_tac [("p","b`x")] trE 1),
        (asm_simp_tac HOLCF_ss 1),
        (stac while_unfold 1),
        (res_inst_tac [("s","UU"),("t","b`UU")]ssubst 1),
        (etac (flat_codom RS disjE) 1),
        (atac 1),
        (etac spec 1),
        (simp_tac HOLCF_ss 1),
        (asm_simp_tac HOLCF_ss 1),
        (asm_simp_tac HOLCF_ss 1),
        (stac while_unfold 1),
        (asm_simp_tac HOLCF_ss 1)
        ]);

val while_unfold3 = prove_goal Loop.thy 
        "while`b`g`x = while`b`g`(step`b`g`x)"
 (fn prems =>
        [
        (res_inst_tac [("s",
                "while`b`g`(iterate (Suc 0) (step`b`g) x)")] trans 1),
        (rtac (while_unfold2 RS spec) 1),
        (Simp_tac 1)
        ]);


(* ------------------------------------------------------------------------- *)
(* properties of while and iterations                                        *)
(* ------------------------------------------------------------------------- *)

val loop_lemma1 = prove_goal Loop.thy
    "[| EX y. b`y=FF; iterate k (step`b`g) x = UU |] \
\    ==>iterate(Suc k) (step`b`g) x=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (Simp_tac 1),
        (rtac trans 1),
        (rtac step_def2 1),
        (asm_simp_tac HOLCF_ss 1),
        (etac exE 1),
        (etac (flat_codom RS disjE) 1),
        (asm_simp_tac HOLCF_ss 1),
        (asm_simp_tac HOLCF_ss 1)
        ]);

val loop_lemma2 = prove_goal Loop.thy
"[|EX y. b`y=FF;iterate (Suc k) (step`b`g) x ~=UU |]==>\
\iterate k (step`b`g) x ~=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac contrapos 1),
        (etac  loop_lemma1 2),
        (atac 1),
        (atac 1)
        ]);

val loop_lemma3 = prove_goal Loop.thy
"[| ALL x. INV x & b`x=TT & g`x~=UU --> INV (g`x);\
\   EX y. b`y=FF; INV x |] \
\==> iterate k (step`b`g) x ~=UU --> INV (iterate k (step`b`g) x)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (nat_ind_tac "k" 1),
        (Asm_simp_tac 1),
        (strip_tac 1),
        (simp_tac (simpset() addsimps [step_def2]) 1),
        (res_inst_tac [("p","b`(iterate k (step`b`g) x)")] trE 1),
        (etac notE 1),
        (asm_simp_tac (HOLCF_ss addsimps [step_def2] ) 1),
        (asm_simp_tac HOLCF_ss 1),
        (rtac mp 1),
        (etac spec 1),
        (asm_simp_tac (HOLCF_ss delsimps [iterate_Suc]
                                addsimps [loop_lemma2] ) 1),
        (res_inst_tac [("s","iterate (Suc k) (step`b`g) x"),
                ("t","g`(iterate k (step`b`g) x)")] ssubst 1),
        (atac 2),
        (asm_simp_tac (HOLCF_ss addsimps [step_def2] ) 1),
        (asm_simp_tac (HOLCF_ss delsimps [iterate_Suc]
                                addsimps [loop_lemma2] ) 1)
        ]);


val loop_lemma4 = prove_goal Loop.thy
"ALL x. b`(iterate k (step`b`g) x)=FF --> while`b`g`x= iterate k (step`b`g) x"
 (fn prems =>
        [
        (nat_ind_tac "k" 1),
        (Simp_tac 1),
        (strip_tac 1),
        (stac while_unfold 1),
        (asm_simp_tac HOLCF_ss 1),
        (rtac allI 1),
        (stac iterate_Suc2 1),
        (strip_tac 1),
        (rtac trans 1),
        (rtac while_unfold3 1),
        (asm_simp_tac HOLCF_ss 1)
        ]);

val loop_lemma5 = prove_goal Loop.thy
"ALL k. b`(iterate k (step`b`g) x) ~= FF ==>\
\ ALL m. while`b`g`(iterate m (step`b`g) x)=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac while_def2 1),
        (rtac fix_ind 1),
        (rtac (allI RS adm_all) 1),
        (rtac adm_eq 1),
        (cont_tacR 1),
        (Simp_tac  1),
        (rtac allI 1),
        (Simp_tac  1),
        (res_inst_tac [("p","b`(iterate m (step`b`g) x)")] trE 1),
        (asm_simp_tac HOLCF_ss 1),
        (asm_simp_tac HOLCF_ss 1),
        (res_inst_tac [("s","xa`(iterate (Suc m) (step`b`g) x)")] trans 1),
        (etac spec 2),
        (rtac cfun_arg_cong 1),
        (rtac trans 1),
        (rtac (iterate_Suc RS sym) 2),
        (asm_simp_tac (HOLCF_ss addsimps [step_def2]) 1),
        (dtac spec 1),
        (contr_tac 1)
        ]);


val loop_lemma6 = prove_goal Loop.thy
"ALL k. b`(iterate k (step`b`g) x) ~= FF ==> while`b`g`x=UU"
 (fn prems =>
        [
        (res_inst_tac [("t","x")] (iterate_0 RS subst) 1),
        (rtac (loop_lemma5 RS spec) 1),
        (resolve_tac prems 1)
        ]);

val loop_lemma7 = prove_goal Loop.thy
"while`b`g`x ~= UU ==> EX k. b`(iterate k (step`b`g) x) = FF"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac swap 1),
        (rtac loop_lemma6 1),
        (fast_tac HOL_cs 1)
        ]);

val loop_lemma8 = prove_goal Loop.thy
"while`b`g`x ~= UU ==> EX y. b`y=FF"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (dtac loop_lemma7 1),
        (fast_tac HOL_cs 1)
        ]);


(* ------------------------------------------------------------------------- *)
(* an invariant rule for loops                                               *)
(* ------------------------------------------------------------------------- *)

val loop_inv2 = prove_goal Loop.thy
"[| (ALL y. INV y & b`y=TT & g`y ~= UU --> INV (g`y));\
\   (ALL y. INV y & b`y=FF --> Q y);\
\   INV x; while`b`g`x~=UU |] ==> Q (while`b`g`x)"
 (fn prems =>
        [
        (res_inst_tac [("P","%k. b`(iterate k (step`b`g) x)=FF")] exE 1),
        (rtac loop_lemma7 1),
        (resolve_tac prems 1),
        (stac (loop_lemma4 RS spec RS mp) 1),
        (atac 1),
        (rtac (nth_elem (1,prems) RS spec RS mp) 1),
        (rtac conjI 1),
        (atac 2),
        (rtac (loop_lemma3 RS mp) 1),
        (resolve_tac prems 1),
        (rtac loop_lemma8 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1),
        (rtac notI2 1),
        (resolve_tac prems 1),
        (etac box_equals 1),
        (rtac (loop_lemma4 RS spec RS mp RS sym) 1),
        (atac 1),
        (rtac refl 1)
        ]);

val loop_inv3 = prove_goal Loop.thy
"[| !!y.[| INV y; b`y=TT; g`y~=UU|] ==> INV (g`y);\
\   !!y.[| INV y; b`y=FF|]==> Q y;\
\   INV x; while`b`g`x~=UU |] ==> Q (while`b`g`x)"
 (fn prems =>
        [
        (rtac loop_inv2 1),
        (rtac allI 1),
        (rtac impI 1),
        (resolve_tac prems 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1),
        (rtac allI 1),
        (rtac impI 1),
        (resolve_tac prems 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);

val loop_inv = prove_goal Loop.thy
"[| P(x);\
\   !!y. P y ==> INV y;\
\   !!y.[| INV y; b`y=TT; g`y~=UU|] ==> INV (g`y);\
\   !!y.[| INV y; b`y=FF|]==> Q y;\
\   while`b`g`x ~= UU |] ==> Q (while`b`g`x)"
 (fn prems =>
        [
        (rtac loop_inv3 1),
        (eresolve_tac prems 1),
        (atac 1),
        (atac 1),
        (resolve_tac prems 1),
        (atac 1),
        (atac 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);
