(*  Title:      HOLCF/ex/Loop.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Theory for a loop primitive like while
*)

(* ------------------------------------------------------------------------- *)
(* access to definitions                                                     *)
(* ------------------------------------------------------------------------- *)


Goalw [step_def] "step$b$g$x = If b$x then g$x else x fi";
by (Simp_tac 1);
qed "step_def2";

Goalw [while_def] "while$b$g = fix$(LAM f x. If b$x then f$(g$x) else x fi)";
by (Simp_tac 1);
qed "while_def2";


(* ------------------------------------------------------------------------- *)
(* rekursive properties of while                                             *)
(* ------------------------------------------------------------------------- *)

Goal "while$b$g$x = If b$x then while$b$g$(g$x) else x fi";
by (fix_tac5  while_def2 1);
by (Simp_tac 1);
qed "while_unfold";

Goal "ALL x. while$b$g$x = while$b$g$(iterate k (step$b$g) x)";
by (nat_ind_tac "k" 1);
by (simp_tac HOLCF_ss 1);
by (rtac allI 1);
by (rtac trans 1);
by (stac while_unfold 1);
by (rtac refl 2);
by (stac iterate_Suc2 1);
by (rtac trans 1);
by (etac spec 2);
by (stac step_def2 1);
by (res_inst_tac [("p","b$x")] trE 1);
by (asm_simp_tac HOLCF_ss 1);
by (stac while_unfold 1);
by (res_inst_tac [("s","UU"),("t","b$UU")]ssubst 1);
by (etac (flat_codom RS disjE) 1);
by (atac 1);
by (etac spec 1);
by (simp_tac HOLCF_ss 1);
by (asm_simp_tac HOLCF_ss 1);
by (asm_simp_tac HOLCF_ss 1);
by (stac while_unfold 1);
by (asm_simp_tac HOLCF_ss 1);
qed "while_unfold2";

Goal "while$b$g$x = while$b$g$(step$b$g$x)";
by (res_inst_tac [("s", "while$b$g$(iterate (Suc 0) (step$b$g) x)")] trans 1);
by (rtac (while_unfold2 RS spec) 1);
by (Simp_tac 1);
qed "while_unfold3";


(* ------------------------------------------------------------------------- *)
(* properties of while and iterations                                        *)
(* ------------------------------------------------------------------------- *)

Goal "[| EX y. b$y=FF; iterate k (step$b$g) x = UU |] \
\    ==>iterate(Suc k) (step$b$g) x=UU";
by (Simp_tac 1);
by (rtac trans 1);
by (rtac step_def2 1);
by (asm_simp_tac HOLCF_ss 1);
by (etac exE 1);
by (etac (flat_codom RS disjE) 1);
by (asm_simp_tac HOLCF_ss 1);
by (asm_simp_tac HOLCF_ss 1);
qed "loop_lemma1";

Goal "[|EX y. b$y=FF;iterate (Suc k) (step$b$g) x ~=UU |]==>\
\     iterate k (step$b$g) x ~=UU";

by (blast_tac (claset() addIs [loop_lemma1]) 1);
qed "loop_lemma2";

Goal "[| ALL x. INV x & b$x=TT & g$x~=UU --> INV (g$x);\
\        EX y. b$y=FF; INV x |] \
\     ==> iterate k (step$b$g) x ~=UU --> INV (iterate k (step$b$g) x)";
by (nat_ind_tac "k" 1);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (simp_tac (simpset() addsimps [step_def2]) 1);
by (res_inst_tac [("p","b$(iterate k (step$b$g) x)")] trE 1);
by (etac notE 1);
by (asm_simp_tac (HOLCF_ss addsimps [step_def2] ) 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac mp 1);
by (etac spec 1);
by (asm_simp_tac (HOLCF_ss delsimps [iterate_Suc] addsimps [loop_lemma2] ) 1);
by (res_inst_tac [("s","iterate (Suc k) (step$b$g) x"),
                  ("t","g$(iterate k (step$b$g) x)")] ssubst 1);
by (atac 2);
by (asm_simp_tac (HOLCF_ss addsimps [step_def2] ) 1);
by (asm_simp_tac (HOLCF_ss delsimps [iterate_Suc] addsimps [loop_lemma2] ) 1);
qed_spec_mp "loop_lemma3";

Goal "ALL x. b$(iterate k (step$b$g) x)=FF --> while$b$g$x= iterate k (step$b$g) x";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (strip_tac 1);
by (stac while_unfold 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac allI 1);
by (stac iterate_Suc2 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac while_unfold3 1);
by (Asm_simp_tac 1);
qed_spec_mp "loop_lemma4";

Goal "ALL k. b$(iterate k (step$b$g) x) ~= FF ==>\
\ ALL m. while$b$g$(iterate m (step$b$g) x)=UU";
by (stac while_def2 1);
by (rtac fix_ind 1);
by (rtac (allI RS adm_all) 1);
by (rtac adm_eq 1);
by (cont_tacR 1);
by (Simp_tac  1);
by (rtac allI 1);
by (Simp_tac  1);
by (res_inst_tac [("p","b$(iterate m (step$b$g) x)")] trE 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("s","xa$(iterate (Suc m) (step$b$g) x)")] trans 1);
by (etac spec 2);
by (rtac cfun_arg_cong 1);
by (rtac trans 1);
by (rtac (iterate_Suc RS sym) 2);
by (asm_simp_tac (HOLCF_ss addsimps [step_def2]) 1);
by (Blast_tac 1);
qed_spec_mp "loop_lemma5";


Goal "ALL k. b$(iterate k (step$b$g) x) ~= FF ==> while$b$g$x=UU";
by (res_inst_tac [("t","x")] (iterate_0 RS subst) 1);
by (etac (loop_lemma5) 1);
qed "loop_lemma6";

Goal "while$b$g$x ~= UU ==> EX k. b$(iterate k (step$b$g) x) = FF";
by (blast_tac (claset() addIs [loop_lemma6]) 1);
qed "loop_lemma7";


(* ------------------------------------------------------------------------- *)
(* an invariant rule for loops                                               *)
(* ------------------------------------------------------------------------- *)

Goal
"[| (ALL y. INV y & b$y=TT & g$y ~= UU --> INV (g$y));\
\   (ALL y. INV y & b$y=FF --> Q y);\
\   INV x; while$b$g$x~=UU |] ==> Q (while$b$g$x)";
by (res_inst_tac [("P","%k. b$(iterate k (step$b$g) x)=FF")] exE 1);
by (etac loop_lemma7 1);
by (stac (loop_lemma4) 1);
by (atac 1);
by (dtac spec 1 THEN etac mp 1);
by (rtac conjI 1);
by (atac 2);
by (rtac (loop_lemma3) 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [loop_lemma6]) 1);
by (assume_tac 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [loop_lemma4]) 1);
qed "loop_inv2";

val [premP,premI,premTT,premFF,premW] = Goal
"[| P(x); \
\   !!y. P y ==> INV y;\
\   !!y. [| INV y; b$y=TT; g$y~=UU|] ==> INV (g$y);\
\   !!y. [| INV y; b$y=FF|] ==> Q y;\
\   while$b$g$x ~= UU |] ==> Q (while$b$g$x)";
by (rtac loop_inv2 1);
by (rtac (premP RS premI) 3);
by (rtac premW 3);
by (blast_tac (claset() addIs [premTT]) 1);
by (blast_tac (claset() addIs [premFF]) 1);
qed "loop_inv";
