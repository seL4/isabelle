(*  Title: 	ZF/Sum
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Disjoint sums in Zermelo-Fraenkel Set Theory 
*)

open Sum;

(*** Rules for the Part primitive ***)

goalw Sum.thy [Part_def]
    "a : Part(A,h) <-> a:A & (EX y. a=h(y))";
by (rtac separation 1);
qed "Part_iff";

goalw Sum.thy [Part_def]
    "!!a b A h. [| a : A;  a=h(b) |] ==> a : Part(A,h)";
by (REPEAT (ares_tac [exI,CollectI] 1));
qed "Part_eqI";

val PartI = refl RSN (2,Part_eqI);

val major::prems = goalw Sum.thy [Part_def]
    "[| a : Part(A,h);  !!z. [| a : A;  a=h(z) |] ==> P  \
\    |] ==> P";
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "PartE";

goalw Sum.thy [Part_def] "Part(A,h) <= A";
by (rtac Collect_subset 1);
qed "Part_subset";


(*** Rules for Disjoint Sums ***)

val sum_defs = [sum_def,Inl_def,Inr_def,case_def];

goalw Sum.thy (bool_def::sum_defs) "Sigma(bool,C) = C(0) + C(1)";
by (fast_tac eq_cs 1);
qed "Sigma_bool";

(** Introduction rules for the injections **)

goalw Sum.thy sum_defs "!!a A B. a : A ==> Inl(a) : A+B";
by (REPEAT (ares_tac [UnI1,SigmaI,singletonI] 1));
qed "InlI";

goalw Sum.thy sum_defs "!!b A B. b : B ==> Inr(b) : A+B";
by (REPEAT (ares_tac [UnI2,SigmaI,singletonI] 1));
qed "InrI";

(** Elimination rules **)

val major::prems = goalw Sum.thy sum_defs
    "[| u: A+B;  \
\       !!x. [| x:A;  u=Inl(x) |] ==> P; \
\       !!y. [| y:B;  u=Inr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[SigmaE,singletonE,ssubst]) 1));
qed "sumE";

(** Injection and freeness equivalences, for rewriting **)

goalw Sum.thy sum_defs "Inl(a)=Inl(b) <-> a=b";
by (simp_tac ZF_ss 1);
qed "Inl_iff";

goalw Sum.thy sum_defs "Inr(a)=Inr(b) <-> a=b";
by (simp_tac ZF_ss 1);
qed "Inr_iff";

goalw Sum.thy sum_defs "Inl(a)=Inr(b) <-> False";
by (simp_tac (ZF_ss addsimps [one_not_0 RS not_sym]) 1);
qed "Inl_Inr_iff";

goalw Sum.thy sum_defs "Inr(b)=Inl(a) <-> False";
by (simp_tac (ZF_ss addsimps [one_not_0]) 1);
qed "Inr_Inl_iff";

(*Injection and freeness rules*)

val Inl_inject = standard (Inl_iff RS iffD1);
val Inr_inject = standard (Inr_iff RS iffD1);
val Inl_neq_Inr = standard (Inl_Inr_iff RS iffD1 RS FalseE);
val Inr_neq_Inl = standard (Inr_Inl_iff RS iffD1 RS FalseE);

val sum_cs = ZF_cs addSIs [PartI, InlI, InrI] 
                   addSEs [PartE, sumE, Inl_neq_Inr, Inr_neq_Inl]
                   addSDs [Inl_inject, Inr_inject];

goal Sum.thy "!!A B. Inl(a): A+B ==> a: A";
by (fast_tac sum_cs 1);
qed "InlD";

goal Sum.thy "!!A B. Inr(b): A+B ==> b: B";
by (fast_tac sum_cs 1);
qed "InrD";

goal Sum.thy "u: A+B <-> (EX x. x:A & u=Inl(x)) | (EX y. y:B & u=Inr(y))";
by (fast_tac sum_cs 1);
qed "sum_iff";

goal Sum.thy "A+B <= C+D <-> A<=C & B<=D";
by (fast_tac sum_cs 1);
qed "sum_subset_iff";

goal Sum.thy "A+B = C+D <-> A=C & B=D";
by (simp_tac (ZF_ss addsimps [extension,sum_subset_iff]) 1);
by (fast_tac ZF_cs 1);
qed "sum_equal_iff";


(*** Eliminator -- case ***)

goalw Sum.thy sum_defs "case(c, d, Inl(a)) = c(a)";
by (rtac (split RS trans) 1);
by (rtac cond_0 1);
qed "case_Inl";

goalw Sum.thy sum_defs "case(c, d, Inr(b)) = d(b)";
by (rtac (split RS trans) 1);
by (rtac cond_1 1);
qed "case_Inr";

val major::prems = goal Sum.thy
    "[| u: A+B; \
\       !!x. x: A ==> c(x): C(Inl(x));   \
\       !!y. y: B ==> d(y): C(Inr(y)) \
\    |] ==> case(c,d,u) : C(u)";
by (rtac (major RS sumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps
			    (prems@[case_Inl,case_Inr]))));
qed "case_type";

goal Sum.thy
  "!!u. u: A+B ==>   \
\       R(case(c,d,u)) <-> \
\       ((ALL x:A. u = Inl(x) --> R(c(x))) & \
\       (ALL y:B. u = Inr(y) --> R(d(y))))";
by (etac sumE 1);
by (asm_simp_tac (ZF_ss addsimps [case_Inl]) 1);
by (fast_tac sum_cs 1);
by (asm_simp_tac (ZF_ss addsimps [case_Inr]) 1);
by (fast_tac sum_cs 1);
qed "expand_case";

val sum_ss = ZF_ss addsimps [InlI, InrI, Inl_iff, Inr_iff, 
			     Inl_Inr_iff, Inr_Inl_iff,
			     case_Inl, case_Inr];

(*** More rules for Part(A,h) ***)

goal Sum.thy "!!A B h. A<=B ==> Part(A,h)<=Part(B,h)";
by (fast_tac sum_cs 1);
qed "Part_mono";

goal Sum.thy "Part(Collect(A,P), h) = Collect(Part(A,h), P)";
by (fast_tac (sum_cs addSIs [equalityI]) 1);
qed "Part_Collect";

val Part_CollectE =
    Part_Collect RS equalityD1 RS subsetD RS CollectE |> standard;

goal Sum.thy "Part(A+B,Inl) = {Inl(x). x: A}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
qed "Part_Inl";

goal Sum.thy "Part(A+B,Inr) = {Inr(y). y: B}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
qed "Part_Inr";

goalw Sum.thy [Part_def] "!!a. a : Part(A,h) ==> a : A";
by (etac CollectD1 1);
qed "PartD1";

goal Sum.thy "Part(A,%x.x) = A";
by (fast_tac (sum_cs addIs [equalityI]) 1);
qed "Part_id";

goal Sum.thy "Part(A+B, %x.Inr(h(x))) = {Inr(y). y: Part(B,h)}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
qed "Part_Inr2";

goal Sum.thy "!!A B C. C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C";
by (fast_tac (sum_cs addIs [equalityI]) 1);
qed "Part_sum_equality";
