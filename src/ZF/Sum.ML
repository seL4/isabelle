(*  Title:      ZF/Sum
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Disjoint sums in Zermelo-Fraenkel Set Theory 
*)

(*** Rules for the Part primitive ***)

Goalw [Part_def]
    "a : Part(A,h) <-> a:A & (EX y. a=h(y))";
by (rtac separation 1);
qed "Part_iff";

Goalw [Part_def]
    "[| a : A;  a=h(b) |] ==> a : Part(A,h)";
by (Blast_tac 1);
qed "Part_eqI";

bind_thm ("PartI", refl RSN (2,Part_eqI));

val major::prems = Goalw [Part_def]
    "[| a : Part(A,h);  !!z. [| a : A;  a=h(z) |] ==> P  \
\    |] ==> P";
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "PartE";

AddIs  [Part_eqI];
AddSEs [PartE];

Goalw [Part_def] "Part(A,h) <= A";
by (rtac Collect_subset 1);
qed "Part_subset";


(*** Rules for Disjoint Sums ***)

bind_thms ("sum_defs", [sum_def,Inl_def,Inr_def,case_def]);

Goalw (bool_def::sum_defs) "Sigma(bool,C) = C(0) + C(1)";
by (Blast_tac 1);
qed "Sigma_bool";

(** Introduction rules for the injections **)

Goalw sum_defs "a : A ==> Inl(a) : A+B";
by (Blast_tac 1);
qed "InlI";

Goalw sum_defs "b : B ==> Inr(b) : A+B";
by (Blast_tac 1);
qed "InrI";

(** Elimination rules **)

val major::prems = Goalw sum_defs
    "[| u: A+B;  \
\       !!x. [| x:A;  u=Inl(x) |] ==> P; \
\       !!y. [| y:B;  u=Inr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[SigmaE,singletonE,ssubst]) 1));
qed "sumE";

(** Injection and freeness equivalences, for rewriting **)

Goalw sum_defs "Inl(a)=Inl(b) <-> a=b";
by (Simp_tac 1);
qed "Inl_iff";

Goalw sum_defs "Inr(a)=Inr(b) <-> a=b";
by (Simp_tac 1);
qed "Inr_iff";

Goalw sum_defs "Inl(a)=Inr(b) <-> False";
by (Simp_tac 1);
qed "Inl_Inr_iff";

Goalw sum_defs "Inr(b)=Inl(a) <-> False";
by (Simp_tac 1);
qed "Inr_Inl_iff";

Goalw sum_defs "0+0 = 0";
by (Simp_tac 1);
qed "sum_empty";

(*Injection and freeness rules*)

bind_thm ("Inl_inject", (Inl_iff RS iffD1));
bind_thm ("Inr_inject", (Inr_iff RS iffD1));
bind_thm ("Inl_neq_Inr", (Inl_Inr_iff RS iffD1 RS FalseE));
bind_thm ("Inr_neq_Inl", (Inr_Inl_iff RS iffD1 RS FalseE));

AddSIs [InlI, InrI];
AddSEs [sumE, Inl_neq_Inr, Inr_neq_Inl];
AddSDs [Inl_inject, Inr_inject];

Addsimps [InlI, InrI, Inl_iff, Inr_iff, Inl_Inr_iff, Inr_Inl_iff, sum_empty];
AddTCs   [InlI, InrI];

Goal "Inl(a): A+B ==> a: A";
by (Blast_tac 1);
qed "InlD";

Goal "Inr(b): A+B ==> b: B";
by (Blast_tac 1);
qed "InrD";

Goal "u: A+B <-> (EX x. x:A & u=Inl(x)) | (EX y. y:B & u=Inr(y))";
by (Blast_tac 1);
qed "sum_iff";

Goal "A+B <= C+D <-> A<=C & B<=D";
by (Blast_tac 1);
qed "sum_subset_iff";

Goal "A+B = C+D <-> A=C & B=D";
by (simp_tac (simpset() addsimps [extension,sum_subset_iff]) 1);
by (Blast_tac 1);
qed "sum_equal_iff";

Goalw [sum_def] "A+A = 2*A";
by (Blast_tac 1);
qed "sum_eq_2_times";


(*** Eliminator -- case ***)

Goalw sum_defs "case(c, d, Inl(a)) = c(a)";
by (Simp_tac 1);
qed "case_Inl";

Goalw sum_defs "case(c, d, Inr(b)) = d(b)";
by (Simp_tac 1);
qed "case_Inr";

Addsimps [case_Inl, case_Inr];

val major::prems = Goal
    "[| u: A+B; \
\       !!x. x: A ==> c(x): C(Inl(x));   \
\       !!y. y: B ==> d(y): C(Inr(y)) \
\    |] ==> case(c,d,u) : C(u)";
by (rtac (major RS sumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "case_type";
AddTCs [case_type];

Goal "u: A+B ==>   \
\       R(case(c,d,u)) <-> \
\       ((ALL x:A. u = Inl(x) --> R(c(x))) & \
\       (ALL y:B. u = Inr(y) --> R(d(y))))";
by Auto_tac;
qed "expand_case";

val major::prems = Goal
  "[| z: A+B;   \
\     !!x. x:A ==> c(x)=c'(x);  \
\     !!y. y:B ==> d(y)=d'(y)   \
\  |] ==> case(c,d,z) = case(c',d',z)";
by (resolve_tac [major RS sumE] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "case_cong";

Goal "z: A+B ==>   \
\       case(c, d, case(%x. Inl(c'(x)), %y. Inr(d'(y)), z)) = \
\       case(%x. c(c'(x)), %y. d(d'(y)), z)";
by Auto_tac;
qed "case_case";


(*** More rules for Part(A,h) ***)

Goal "A<=B ==> Part(A,h)<=Part(B,h)";
by (Blast_tac 1);
qed "Part_mono";

Goal "Part(Collect(A,P), h) = Collect(Part(A,h), P)";
by (Blast_tac 1);
qed "Part_Collect";

bind_thm ("Part_CollectE", Part_Collect RS equalityD1 RS subsetD RS CollectE);

Goal "Part(A+B,Inl) = {Inl(x). x: A}";
by (Blast_tac 1);
qed "Part_Inl";

Goal "Part(A+B,Inr) = {Inr(y). y: B}";
by (Blast_tac 1);
qed "Part_Inr";

Goalw [Part_def] "a : Part(A,h) ==> a : A";
by (etac CollectD1 1);
qed "PartD1";

Goal "Part(A,%x. x) = A";
by (Blast_tac 1);
qed "Part_id";

Goal "Part(A+B, %x. Inr(h(x))) = {Inr(y). y: Part(B,h)}";
by (Blast_tac 1);
qed "Part_Inr2";

Goal "C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C";
by (Blast_tac 1);
qed "Part_sum_equality";
