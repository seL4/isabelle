(*  Title:      ZF/Induct/FoldSet.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge


A "fold" functional for finite sets.  For n non-negative we have
fold f e {x1,...,xn} = f x1 (... (f xn e)) where f is at
least left-commutative.  
*)

(** foldSet **)

bind_thm("empty_fold_setE", 
             fold_set.mk_cases "<0, x> : fold_set(A, B, f,e)");
bind_thm("cons_fold_setE", 
             fold_set.mk_cases "<cons(x,C), y> : fold_set(A, B, f,e)");

bind_thm("fold_set_lhs", fold_set.dom_subset RS subsetD RS SigmaD1);
bind_thm("fold_set_rhs", fold_set.dom_subset RS subsetD RS SigmaD2);

(* add-hoc lemmas *)

Goal "[| x~:C; x~:B |] ==> cons(x,B)=cons(x,C) <-> B = C";
by (auto_tac (claset() addEs [equalityE], simpset()));
qed "cons_lemma1";

Goal "[| cons(x, B)=cons(y, C); x~=y; x~:B; y~:C |] \
\   ==>  B - {y} = C-{x} & x:C & y:B";
by (auto_tac (claset() addEs [equalityE], simpset()));
qed "cons_lemma2";


Open_locale "LC";
val f_lcomm = thm "lcomm";
val f_type  = thm "ftype";

Goal "[| <C-{x},y> : fold_set(A, B, f,e);  x:C; x:A |] \
\     ==> <C, f(x,y)> : fold_set(A, B, f, e)";
by (ftac fold_set_rhs 1);
by (etac (cons_Diff RS subst) 1 THEN resolve_tac fold_set.intrs 1);
by (auto_tac (claset() addIs [f_type], simpset()));
qed "Diff1_fold_set";

Goal "[| C:Fin(A); e:B |] ==> EX x. <C, x> : fold_set(A, B, f,e)";
by (etac Fin_induct 1);
by (ALLGOALS(Clarify_tac));
by (ftac fold_set_rhs 2);
by (cut_inst_tac [("x", "x"), ("y", "xa")] f_type 2);
by (REPEAT(blast_tac (claset() addIs fold_set.intrs) 1));
qed_spec_mp "Fin_imp_fold_set";


Goal "n:nat \
\     ==> ALL C x. |C|<n -->  e:B --> <C, x> : fold_set(A, B, f,e)-->\
\            (ALL y. <C, y> : fold_set(A, B, f,e) --> y=x)";
by (etac nat_induct 1);
by (auto_tac (claset(), simpset() addsimps [le_iff]));
by (etac fold_set.elim 1);
by (blast_tac  (claset() addEs [empty_fold_setE]) 1);
by (etac fold_set.elim 1);
by (blast_tac  (claset() addEs [empty_fold_setE]) 1);
by (Clarify_tac 1);
(*force simplification of "|C| < |cons(...)|"*)
by (rotate_tac 2 1);
by (etac rev_mp 1);
by (forw_inst_tac [("a", "Ca")] fold_set_lhs 1);
by (forw_inst_tac [("a", "Cb")] fold_set_lhs 1);
by (asm_simp_tac (simpset() addsimps [Fin_into_Finite RS Finite_imp_cardinal_cons])  1);
by (rtac impI 1);
(** LEVEL 10 **)
by (case_tac "x=xb" 1 THEN Auto_tac);
by (asm_full_simp_tac (simpset() addsimps [cons_lemma1]) 1); 
by (Blast_tac 1);
(*case x ~= xb*)
by (dtac cons_lemma2 1 THEN ALLGOALS Clarify_tac);
by (subgoal_tac "Ca = cons(xb, Cb) - {x}" 1);
by (blast_tac (claset() addEs [equalityE]) 2); 
(** LEVEL 20 **)
by (subgoal_tac "|Ca| le |Cb|" 1);
by (rtac succ_le_imp_le 2);
by (hyp_subst_tac 2);
by (subgoal_tac "Finite(cons(xb, Cb)) & x:cons(xb, Cb) " 2);
by (asm_simp_tac (simpset() addsimps [Finite_imp_succ_cardinal_Diff, 
                       Fin_into_Finite RS Finite_imp_cardinal_cons]) 2);
by (asm_simp_tac (simpset() addsimps [Fin.consI RS Fin_into_Finite]) 2);
by (res_inst_tac [("C1", "Ca-{xb}"), ("e1","e"), ("A1", "A")] 
    (Fin_imp_fold_set RS exE) 1);
by (blast_tac (claset() addIs [Diff_subset RS Fin_subset]) 1);
by (Blast_tac 1);
(** LEVEL 28 **)
by (ftac Diff1_fold_set 1 THEN assume_tac 1 THEN assume_tac 1);
by (subgoal_tac "ya = f(xb, xa)" 1);
by (blast_tac (claset() delrules [equalityCE]) 2);
by (subgoal_tac "<Cb-{x}, xa>: fold_set(A, B, f, e)" 1);
 by (Asm_full_simp_tac 2);
by (subgoal_tac "yb = f(x, xa)" 1);
 by (blast_tac (claset() delrules [equalityCE]
                        addDs [Diff1_fold_set]) 2);
by (asm_simp_tac (simpset() addsimps [f_lcomm]) 1);
qed_spec_mp "lemma";


Goal "[| <C, x> : fold_set(A, B, f, e); \
\        <C, y> : fold_set(A, B, f, e); e:B |] ==> y=x";
by (forward_tac [fold_set_lhs RS Fin_into_Finite] 1);
by (rewtac Finite_def);
by (Clarify_tac 1);
by (res_inst_tac [("n", "succ(n)")] lemma 1);
by (auto_tac (claset() addIs 
      [eqpoll_imp_lepoll RS lepoll_cardinal_le],
     simpset()));
qed "fold_set_determ";

Goalw [fold_def] 
     "[| <C,y> : fold_set(C, B, f, e); e:B |] ==> fold[B](f,e,C) = y";
by (rtac the_equality 1);
by (rtac fold_set_determ 2);
by Auto_tac;
qed "fold_equality";

Goalw [fold_def] "e:B ==> fold[B](f,e,0) = e";
by (blast_tac (claset() addSEs [empty_fold_setE]
            addIs fold_set.intrs) 1);
qed "fold_0";
Addsimps [fold_0];

Goal "[| x ~: C; x:A; e:B |] \
\     ==> <cons(x, C), v> : fold_set(A, B, f, e) <->  \
\         (EX y. <C, y> : fold_set(A, B, f, e) & v = f(x, y))";
by Auto_tac;
by (res_inst_tac [("A1", "A"), ("C1", "C")] (Fin_imp_fold_set RS exE) 1);
by (res_inst_tac [("x", "xa")] exI 3);
by (res_inst_tac [("b", "cons(x, C)")] Fin_subset 1);
by (auto_tac (claset() addDs [fold_set_lhs] 
                       addIs [f_type]@fold_set.intrs, simpset()));
by (blast_tac (claset() addIs [fold_set_determ, f_type]@fold_set.intrs) 1);
val lemma = result();

Goal "<D, x> : fold_set(C, B, f, e) \
\     ==> ALL A. C<=A --> <D, x> : fold_set(A, B, f, e)";
by (etac fold_set.induct 1);
by (auto_tac (claset() addIs fold_set.intrs, simpset()));
qed "lemma2";

Goal " C<=A ==> fold_set(C, B, f, e) <= fold_set(A, B, f, e)";
by (Clarify_tac 1);
by (forward_tac [impOfSubs fold_set.dom_subset] 1);
by (Clarify_tac 1);
by (auto_tac (claset() addDs [lemma2], simpset()));
qed "fold_set_mono";

Goal "<C,x> : fold_set(A, B, f, e) ==> <C, x> : fold_set(C,B, f,e)";
by (etac fold_set.induct 1);
by (auto_tac (claset() addSIs fold_set.intrs, simpset()));
by (res_inst_tac [("C1", "C"), ("A1", "cons(x, C)")] 
                      (fold_set_mono RS subsetD) 1);
by Auto_tac;
qed "fold_set_mono2";


Goalw [fold_def]
     "[| Finite(C); x ~: C; e:B |] \
\     ==> fold[B](f, e, cons(x, C)) = f(x, fold[B](f,e, C))";
by (asm_simp_tac (simpset() addsimps [lemma]) 1);
by (dtac Finite_into_Fin 1);
by (rtac the_equality 1);
by (dtac Fin_imp_fold_set 1);
by Auto_tac;
by (res_inst_tac [("x", "xa")] exI 1);
by Auto_tac;
by (resolve_tac [fold_set_mono RS subsetD] 1);
by (Blast_tac 2);
by (dtac fold_set_mono2 3);
by (auto_tac (claset() addIs [Fin_imp_fold_set],
              simpset() addsimps [symmetric fold_def, fold_equality]));
qed "fold_cons";


Goal "Finite(C) \
\     ==> ALL e:B. f(x, fold[B](f, e, C)) = fold[B](f, f(x, e), C)";
by (etac Finite_induct 1);
by (ALLGOALS(Clarify_tac));
by (asm_full_simp_tac (simpset() addsimps [f_type]) 1);
by (asm_simp_tac (simpset() 
         addsimps [f_lcomm, fold_cons, f_type]) 1);
qed_spec_mp "fold_commute";


Goal "Finite(C) ==> e:B -->fold[B](f, e, C):B";
by (etac  Finite_induct 1);
by (ALLGOALS(Clarify_tac));
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [fold_cons, f_type]) 1);
qed_spec_mp "fold_type";

Goal "x:D ==> cons(x, C) Int D = cons(x, C Int D)";
by Auto_tac;
qed "cons_Int_right_lemma1";

Goal "x~:D ==> cons(x, C) Int D = C Int D";
by Auto_tac;
qed "cons_Int_right_lemma2";

Goal "[| Finite(C); Finite(D); e:B|] \
\     ==> fold[B](f, fold[B](f, e, D), C)  \
\  =  fold[B](f, fold[B](f, e, (C Int D)), C Un D)";
by (etac  Finite_induct 1);
by (asm_full_simp_tac (simpset() addsimps [f_type, fold_type]) 1);
by (subgoal_tac  "Finite(Ba Int D) & \
                 \cons(x, Ba) Un D = cons(x, Ba Un D) & \
                 \Finite(Ba Un D)" 1);
by (auto_tac (claset() 
       addIs [Finite_Un,Int_lower1 RS subset_Finite], simpset()));
by (case_tac "x:D" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps 
            [cons_Int_right_lemma1,cons_Int_right_lemma2,
             fold_type, fold_cons,fold_commute,cons_absorb, f_type])));
qed "fold_nest_Un_Int";


Goal "[| Finite(C); Finite(D); C Int D = 0; e:B |] \
\     ==> fold[B](f,e,C Un D) =  fold[B](f, fold[B](f,e,D), C)";
by (asm_simp_tac (simpset() addsimps [fold_nest_Un_Int]) 1);
qed "fold_nest_Un_disjoint";

Close_locale "LC";


(** setsum **)

Goalw [setsum_def] "setsum(g, 0) = #0";
by (Simp_tac 1);
qed "setsum_0";
Addsimps [setsum_0];

Goalw [setsum_def]
     "[| Finite(C); c~:C |] \
\     ==> setsum(g, cons(c, C)) = g(c) $+ setsum(g, C)";
by (asm_simp_tac (simpset() addsimps [Finite_cons,export fold_cons]) 1);
qed "setsum_cons";
Addsimps [setsum_cons];

Goal "setsum((%i. #0), C) = #0";
by (case_tac "Finite(C)" 1);
by (asm_simp_tac (simpset() addsimps [setsum_def]) 2);
by (etac Finite_induct 1);
by Auto_tac;
qed "setsum_0";

(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
Goal "[| Finite(C); Finite(D) |] \
\     ==> setsum(g, C Un D) $+ setsum(g, C Int D) \
\       = setsum(g, C) $+ setsum(g, D)";
by (etac Finite_induct 1);
by (subgoal_tac "cons(x, B) Un D = cons(x, B Un D) & \
                \ Finite(B Un D) & Finite(B Int D)" 2);
by (auto_tac (claset() addIs [Finite_Un, Int_lower1 RS subset_Finite], 
              simpset()));
by (case_tac "x:D" 1);
by (subgoal_tac "cons(x, B) Int D = B Int D" 2);
by (subgoal_tac "cons(x, B) Int D = cons(x, B Int D)" 1);
by Auto_tac;
by (subgoal_tac "cons(x, B Un D) = B Un D" 1);
by Auto_tac;
qed "setsum_Un_Int";

Goal "setsum(g, C):int";
by (case_tac "Finite(C)" 1);
by (asm_simp_tac (simpset() addsimps [setsum_def]) 2);
by (etac Finite_induct 1);
by Auto_tac;
qed "setsum_type";
Addsimps [setsum_type];  AddTCs [setsum_type];

Goal "[| Finite(C); Finite(D); C Int D = 0 |] \
\     ==> setsum(g, C Un D) = setsum(g, C) $+ setsum(g,D)";  
by (stac (setsum_Un_Int RS sym) 1);
by (subgoal_tac "Finite(C Un D)" 3);
by (auto_tac (claset() addIs [Finite_Un], simpset()));
qed "setsum_Un_disjoint";

Goal "Finite(I) ==> (ALL i:I. Finite(C(i))) --> Finite(RepFun(I, C))";
by (etac Finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [Finite_0]));
by (stac (cons_eq RS sym) 1);
by (auto_tac (claset() addIs [Finite_Un, Finite_cons, Finite_0], simpset()));
qed_spec_mp "Finite_RepFun";

Goal "!!I. Finite(I) \
\     ==> (ALL i:I. Finite(C(i))) --> \
\         (ALL i:I. ALL j:I. i~=j --> C(i) Int C(j) = 0) --> \
\         setsum(f, UN i:I. C(i)) = setsum (%i. setsum(f, C(i)), I)"; 
by (etac Finite_induct 1);
by (ALLGOALS(Clarify_tac));
by Auto_tac;
by (subgoal_tac "ALL i:B. x ~= i" 1);
 by (Blast_tac 2); 
by (subgoal_tac "C(x) Int (UN i:B. C(i)) = 0" 1);
 by (Blast_tac 2);
by (subgoal_tac "Finite(UN i:B. C(i)) & Finite(C(x)) & Finite(B)" 1);
by (asm_simp_tac (simpset() addsimps [setsum_Un_disjoint]) 1);
by (auto_tac (claset() addIs [Finite_Union, Finite_RepFun], simpset()));
qed_spec_mp "setsum_UN_disjoint";


Goal "setsum(%x. f(x) $+ g(x),C) = setsum(f, C) $+ setsum(g, C)";
by (case_tac "Finite(C)" 1);
by (asm_simp_tac (simpset() addsimps [setsum_def]) 2);
by (etac Finite_induct 1);
by Auto_tac;
qed "setsum_addf";


val major::prems = Goal
 "[| A=B; !!x. x:B ==> f(x) = g(x) |] ==> \
\    setsum(f, A) = setsum(g, B)";
by (case_tac "Finite(B)" 1);
by (asm_simp_tac (simpset() addsimps [setsum_def, major]) 2);
by (subgoal_tac  "ALL C. C <= B --> (ALL x:C. f(x) = g(x)) \
                 \  --> setsum(f,C) = setsum(g, C)" 1);
by (cut_facts_tac [major] 1);
 by (asm_full_simp_tac (simpset() addsimps [major]@prems) 1); 
by (etac Finite_induct 1);
by (ALLGOALS(Clarify_tac));
by (subgoal_tac "C=0" 1);
by (Force_tac 1);
by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [major,subset_cons_iff]@prems) 1);
by Safe_tac;
by (ftac subset_Finite 1);
by (assume_tac 1);
by (Blast_tac 1);
by (ftac subset_Finite 1);
by (assume_tac 1);
by (subgoal_tac "C = cons(x, C - {x})" 1);
by (Blast_tac 2);
by (etac ssubst 1);
by (dtac spec 1); 
by (mp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Ball_def, major]@prems) 1); 
qed_spec_mp  "setsum_cong";

(** For the natural numbers, we have subtraction **)

Goal "[| Finite(A); Finite(B) |] \
\     ==> setsum(f, A Un B) = \
\         setsum(f, A) $+ setsum(f, B) $- setsum(f, A Int B)";
by (stac (setsum_Un_Int RS sym) 1);
by Auto_tac;
qed "setsum_Un";


Goal "Finite(A) ==> (ALL x:A. g(x) $<= #0) --> setsum(g, A) $<= #0";
by (etac Finite_induct 1);
by (auto_tac (claset() addIs [zneg_or_0_add_zneg_or_0_imp_zneg_or_0], simpset()));
qed_spec_mp "setsum_zneg_or_0";

Goal "Finite(A) \
\     ==> ALL n:nat. setsum(f,A) = $# succ(n) --> (EX a:A. #0 $< f(a))";
by (etac Finite_induct 1);
by (auto_tac (claset(), simpset() 
           delsimps [int_of_0, int_of_succ]
           addsimps [not_zless_iff_zle, int_of_0 RS sym]));
by (subgoal_tac "setsum(f, B) $<= #0" 1);
by (ALLGOALS(Asm_full_simp_tac));
by (blast_tac (claset() addIs [setsum_zneg_or_0]) 2);
by (subgoal_tac "$# 1 $<= f(x) $+ setsum(f, B)" 1);
by (dtac  (zdiff_zle_iff RS iffD2) 1);
by (subgoal_tac "$# 1 $<= $# 1 $- setsum(f,B)" 1);
by (dres_inst_tac [("x",  "$# 1")] zle_trans 1);
by (res_inst_tac [("j", "#1")] zless_zle_trans 2);
by Auto_tac;
qed "setsum_succD_lemma";

Goal "[| setsum(f, A) = $# succ(n); n:nat |]==> EX a:A. #0 $< f(a)";
by (case_tac "Finite(A)" 1);
by (blast_tac (claset() 
     addIs [setsum_succD_lemma RS bspec RS mp]) 1);
by (rewtac setsum_def);
by (auto_tac (claset(), 
       simpset() delsimps [int_of_0, int_of_succ] 
                 addsimps [int_succ_int_1 RS sym, int_of_0 RS sym]));
qed "setsum_succD";

Goal "Finite(A) ==> (ALL x:A. #0 $<= g(x)) --> #0 $<= setsum(g, A)";
by (etac Finite_induct 1);
by (Simp_tac 1);
by (auto_tac (claset() addIs [zpos_add_zpos_imp_zpos],  simpset()));
qed_spec_mp "g_zpos_imp_setsum_zpos";

Goal "[| Finite(A); ALL x. #0 $<= g(x) |] ==> #0 $<= setsum(g, A)";
by (etac Finite_induct 1);
by (auto_tac (claset() addIs [zpos_add_zpos_imp_zpos], simpset()));
qed_spec_mp "g_zpos_imp_setsum_zpos2";

Goal "Finite(A) \
\     ==> (ALL x:A. #0 $< g(x)) --> A ~= 0 --> (#0 $< setsum(g, A))";
by (etac Finite_induct 1);
by (auto_tac (claset() addIs [zspos_add_zspos_imp_zspos],simpset()));
qed_spec_mp "g_zspos_imp_setsum_zspos";

Goal "Finite(A) \
\     ==> ALL a. M(a) = #0 --> setsum(M, A) = setsum(M, A-{a})";
by (etac Finite_induct 1);
by (ALLGOALS(Clarify_tac));
by (Simp_tac 1);
by (case_tac "x=a" 1);
by (subgoal_tac "cons(x, B) - {a} = cons(x, B -{a}) & Finite(B - {a})" 2);
by (subgoal_tac "cons(a, B) - {a} = B" 1);
by (auto_tac (claset() addIs [Finite_Diff], simpset()));
qed_spec_mp "setsum_Diff";
