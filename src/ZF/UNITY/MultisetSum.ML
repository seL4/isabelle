(*  Title:      ZF/UNITY/MultusetSum.thy
    ID:         $Id$
    Author:     Sidi O Ehmety
    Copyright:  2002 University of Cambridge
Setsum for multisets.
*)

Goal "mset_of(normalize(M)) <= mset_of(M)";
by (auto_tac (claset(), simpset() addsimps [mset_of_def,normalize_def])); 
qed "mset_of_normalize";

Goalw [general_setsum_def]
"general_setsum(0, B, e, f, g) = e";
by Auto_tac;
qed "general_setsum_0";
Addsimps [general_setsum_0];

Goalw [general_setsum_def] 
"[| C:Fin(A); a:A; a~:C; e:B; ALL x:A. g(x):B; lcomm(B, B, f) |] ==> \
\ general_setsum(cons(a, C), B, e, f, g) = \
\   f(g(a), general_setsum(C, B, e, f,g))";
by  (auto_tac (claset(), simpset() addsimps [Fin_into_Finite RS Finite_cons, 
                                             cons_absorb]));
by (blast_tac (claset() addDs [Fin_into_Finite]) 2);
by (resolve_tac [thm"fold_typing.fold_cons"] 1);
by (auto_tac (claset(), simpset() addsimps [thm "fold_typing_def", lcomm_def]));
qed "general_setsum_cons";
Addsimps [general_setsum_cons];

(** lcomm **)

Goalw [lcomm_def]
"[| C<=A; lcomm(A, B, f) |] ==> lcomm(C, B,f)";
by Auto_tac;
by (Blast_tac 1);
qed "lcomm_mono";

Goalw [lcomm_def]
  "lcomm(Mult(A), Mult(A), op +#)";
by (auto_tac (claset(), simpset() 
    addsimps [Mult_iff_multiset, munion_lcommute]));
qed "munion_lcomm";
Addsimps [munion_lcomm];

(** msetsum **)

Goal
"[| C:Fin(A); ALL x:A. multiset(g(x))& mset_of(g(x))<=B  |]  \
\  ==> multiset(general_setsum(C, B -||> nat - {0}, 0, \\<lambda>u v. u +# v, g))";
by (etac Fin_induct 1);
by Auto_tac;
by (stac general_setsum_cons 1); 
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "multiset_general_setsum";

Goalw [msetsum_def] "msetsum(g, 0, B) = 0";
by Auto_tac;
qed "msetsum_0";
Addsimps [msetsum_0];

Goalw [msetsum_def]
"[| C:Fin(A); a~:C; a:A; ALL x:A. multiset(g(x)) & mset_of(g(x))<=B  |]  \
\  ==> msetsum(g, cons(a, C), B) = g(a) +#  msetsum(g, C, B)";
by (stac general_setsum_cons 1); 
by (auto_tac (claset(), simpset() addsimps [multiset_general_setsum, Mult_iff_multiset]));
qed "msetsum_cons";
Addsimps [msetsum_cons];

(* msetsum type *)

Goal "multiset(msetsum(g, C, B))";
by (asm_full_simp_tac (simpset() addsimps [msetsum_def]) 1); 
qed "msetsum_multiset";

Goal 
"[| C:Fin(A); ALL x:A. multiset(g(x)) & mset_of(g(x))<=B |] \ 
\ ==> mset_of(msetsum(g, C, B))<=B";
by (etac Fin_induct 1);
by Auto_tac;
qed "mset_of_msetsum";



(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
Goal 
"[| C:Fin(A); D:Fin(A); ALL x:A. multiset(g(x)) & mset_of(g(x))<=B |] \
\     ==> msetsum(g, C Un D, B) +# msetsum(g, C Int D, B) \
\       = msetsum(g, C, B) +# msetsum(g, D, B)";
by (etac Fin_induct 1);
by (subgoal_tac "cons(x, y) Un D = cons(x, y Un D)" 2);
by (auto_tac (claset(), simpset() addsimps [msetsum_multiset]));
by (subgoal_tac "y Un D:Fin(A) & y Int D : Fin(A)" 1);
by (Clarify_tac 1);
by (case_tac "x:D" 1);
by (subgoal_tac "cons(x, y) Int D = y Int D" 2);
by (subgoal_tac "cons(x, y) Int D = cons(x, y Int D)" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [cons_absorb,
                munion_assoc, msetsum_multiset])));
by (asm_simp_tac (simpset() addsimps [munion_lcommute, msetsum_multiset]) 1);
by Auto_tac;
qed "msetsum_Un_Int";


Goal "[| C:Fin(A); D:Fin(A); C Int D = 0; \
\  ALL x:A. multiset(g(x)) & mset_of(g(x))<=B |] \
\     ==> msetsum(g, C Un D, B) = msetsum(g, C, B) +# msetsum(g,D, B)";  
by (stac (msetsum_Un_Int RS sym) 1);
by (auto_tac (claset(),  simpset() addsimps [msetsum_multiset]));
qed "msetsum_Un_disjoint";

Goal "I:Fin(A) ==> (ALL i:I. C(i):Fin(B)) --> (UN i:I. C(i)):Fin(B)";
by (etac Fin_induct 1);
by Auto_tac;
qed_spec_mp "UN_Fin_lemma";
 
Goal "!!I. [| I:Fin(K); ALL i:K. C(i):Fin(A) |] ==> \
\ (ALL x:A. multiset(f(x)) & mset_of(f(x))<=B) -->  \
\ (ALL i:I. ALL j:I. i~=j --> C(i) Int C(j) = 0) --> \
\   msetsum(f, UN i:I. C(i), B) = msetsum (%i. msetsum(f, C(i),B), I, B)"; 
by (etac Fin_induct 1);
by (ALLGOALS(Clarify_tac));
by Auto_tac;
by (subgoal_tac "ALL i:y. x ~= i" 1);
 by (Blast_tac 2); 
by (subgoal_tac "C(x) Int (UN i:y. C(i)) = 0" 1);
 by (Blast_tac 2);
by (subgoal_tac " (UN i:y. C(i)):Fin(A) & C(x):Fin(A)" 1);
by (blast_tac (claset() addIs [UN_Fin_lemma] addDs [FinD]) 2);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps [msetsum_Un_disjoint]) 1);
by (subgoal_tac "ALL x:K. multiset(msetsum(f, C(x), B)) &\
                \ mset_of(msetsum(f, C(x), B)) <= B" 1);
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (dres_inst_tac [("x", "xa")] bspec 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [msetsum_multiset, mset_of_msetsum])));
qed_spec_mp "msetsum_UN_disjoint";

Goal 
"[| C:Fin(A); \
\ ALL x:A. multiset(f(x)) & mset_of(f(x))<=B; \
\ ALL x:A. multiset(g(x)) & mset_of(g(x))<=B |] ==>\
\ msetsum(%x. f(x) +# g(x), C, B) = msetsum(f, C, B) +# msetsum(g, C, B)";
by (subgoal_tac "ALL x:A. multiset(f(x) +# g(x)) & mset_of(f(x) +# g(x))<=B" 1);
by (etac Fin_induct 1);
by (ALLGOALS(Asm_simp_tac));
by (resolve_tac [trans] 1);
by (resolve_tac [msetsum_cons] 1);
by (assume_tac 1);
by (auto_tac (claset(), simpset() addsimps [msetsum_multiset, munion_assoc]));
by (asm_simp_tac (simpset() addsimps [msetsum_multiset, munion_lcommute]) 1);
qed "msetsum_addf";


val prems = Goal
 "[| C=D; !!x. x:D ==> f(x) = g(x) |] ==> \
\    msetsum(f, C, B) = msetsum(g, D, B)";
by (asm_full_simp_tac (simpset() addsimps [msetsum_def, general_setsum_def]@prems addcongs [fold_cong]) 1);
qed  "msetsum_cong";

Goal "[| multiset(M); multiset(N) |] ==> M +# N -# N = M";
by (asm_simp_tac (simpset() addsimps [multiset_equality]) 1);
qed "multiset_union_diff";


Goal "[| C:Fin(A); D:Fin(A); \
\ ALL x:A. multiset(f(x)) & mset_of(f(x))<=B  |] \
\  ==> msetsum(f, C Un D, B) = \
\         msetsum(f, C, B) +# msetsum(f, D, B) -# msetsum(f, C Int D, B)";
by (subgoal_tac "C Un D:Fin(A) & C Int D:Fin(A)" 1);
by (Clarify_tac 1);
by (stac (msetsum_Un_Int RS sym) 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps 
         [msetsum_multiset,multiset_union_diff])));
by (blast_tac (claset() addDs [FinD]) 1);
qed "msetsum_Un";


Goalw [nsetsum_def] "nsetsum(g, 0)=0";
by Auto_tac;
qed "nsetsum_0";
Addsimps [nsetsum_0];

Goalw [nsetsum_def, general_setsum_def] 
"[| Finite(C); x~:C |] \
\  ==> nsetsum(g, cons(x, C))= g(x) #+ nsetsum(g, C)";
by (auto_tac (claset(), simpset() addsimps [Finite_cons]));
by (res_inst_tac [("A", "cons(x, C)")] (thm"fold_typing.fold_cons") 1);
by (auto_tac (claset() addIs [thm"Finite_cons_lemma"], 
              simpset() addsimps [thm "fold_typing_def"]));
qed "nsetsum_cons";
Addsimps [nsetsum_cons];

Goal "nsetsum(g, C):nat";
by (case_tac "Finite(C)" 1);
by (asm_simp_tac (simpset() addsimps [nsetsum_def, general_setsum_def]) 2);
by (etac Finite_induct 1);
by Auto_tac;
qed "nsetsum_type";
Addsimps [nsetsum_type];  
AddTCs [nsetsum_type];
