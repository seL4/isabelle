(*  Title: 	ZF/sum
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Disjoint sums in Zermelo-Fraenkel Set Theory 
*)

open Sum;

val sum_defs = [sum_def,Inl_def,Inr_def,case_def];

(** Introduction rules for the injections **)

goalw Sum.thy sum_defs "!!a A B. a : A ==> Inl(a) : A+B";
by (REPEAT (ares_tac [UnI1,SigmaI,singletonI] 1));
val InlI = result();

goalw Sum.thy sum_defs "!!b A B. b : B ==> Inr(b) : A+B";
by (REPEAT (ares_tac [UnI2,SigmaI,singletonI] 1));
val InrI = result();

(** Elimination rules **)

val major::prems = goalw Sum.thy sum_defs
    "[| u: A+B;  \
\       !!x. [| x:A;  u=Inl(x) |] ==> P; \
\       !!y. [| y:B;  u=Inr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[SigmaE,singletonE,ssubst]) 1));
val sumE = result();

(** Injection and freeness rules **)

val [major] = goalw Sum.thy sum_defs "Inl(a)=Inl(b) ==> a=b";
by (EVERY1 [rtac (major RS Pair_inject), assume_tac]);
val Inl_inject = result();

val [major] = goalw Sum.thy sum_defs "Inr(a)=Inr(b) ==> a=b";
by (EVERY1 [rtac (major RS Pair_inject), assume_tac]);
val Inr_inject = result();

val [major] = goalw Sum.thy sum_defs "Inl(a)=Inr(b) ==> P";
by (rtac (major RS Pair_inject) 1);
by (etac (sym RS one_neq_0) 1);
val Inl_neq_Inr = result();

val Inr_neq_Inl = sym RS Inl_neq_Inr;

(** Injection and freeness equivalences, for rewriting **)

goal Sum.thy "Inl(a)=Inl(b) <-> a=b";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [Inl_inject,subst_context] 1));
val Inl_iff = result();

goal Sum.thy "Inr(a)=Inr(b) <-> a=b";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [Inr_inject,subst_context] 1));
val Inr_iff = result();

goal Sum.thy "Inl(a)=Inr(b) <-> False";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [Inl_neq_Inr,FalseE] 1));
val Inl_Inr_iff = result();

goal Sum.thy "Inr(b)=Inl(a) <-> False";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [Inr_neq_Inl,FalseE] 1));
val Inr_Inl_iff = result();

val sum_cs = ZF_cs addIs [InlI,InrI] addSEs [sumE,Inl_neq_Inr,Inr_neq_Inl]
                   addSDs [Inl_inject,Inr_inject];

goal Sum.thy "u: A+B <-> (EX x. x:A & u=Inl(x)) | (EX y. y:B & u=Inr(y))";
by (fast_tac sum_cs 1);
val sum_iff = result();

goal Sum.thy "A+B <= C+D <-> A<=C & B<=D";
by (fast_tac sum_cs 1);
val sum_subset_iff = result();

goal Sum.thy "A+B = C+D <-> A=C & B=D";
by (simp_tac (ZF_ss addsimps [extension,sum_subset_iff]) 1);
by (fast_tac ZF_cs 1);
val sum_equal_iff = result();

(*** Eliminator -- case ***)

goalw Sum.thy sum_defs "case(c, d, Inl(a)) = c(a)";
by (rtac (split RS trans) 1);
by (rtac cond_0 1);
val case_Inl = result();

goalw Sum.thy sum_defs "case(c, d, Inr(b)) = d(b)";
by (rtac (split RS trans) 1);
by (rtac cond_1 1);
val case_Inr = result();

val major::prems = goal Sum.thy
    "[| u: A+B; \
\       !!x. x: A ==> c(x): C(Inl(x));   \
\       !!y. y: B ==> d(y): C(Inr(y)) \
\    |] ==> case(c,d,u) : C(u)";
by (rtac (major RS sumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps
			    (prems@[case_Inl,case_Inr]))));
val case_type = result();

(** Rules for the Part primitive **)

goalw Sum.thy [Part_def]
    "!!a b A h. [| a : A;  a=h(b) |] ==> a : Part(A,h)";
by (REPEAT (ares_tac [exI,CollectI] 1));
val Part_eqI = result();

val PartI = refl RSN (2,Part_eqI);

val major::prems = goalw Sum.thy [Part_def]
    "[| a : Part(A,h);  !!z. [| a : A;  a=h(z) |] ==> P  \
\    |] ==> P";
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
val PartE = result();

goalw Sum.thy [Part_def] "Part(A,h) <= A";
by (rtac Collect_subset 1);
val Part_subset = result();

goal Sum.thy "!!A B h. A<=B ==> Part(A,h)<=Part(B,h)";
by (fast_tac (ZF_cs addIs [PartI] addSEs [PartE]) 1);
val Part_mono = result();

goal Sum.thy "Part(A+B,Inl) = {Inl(x). x: A}";
by (fast_tac (sum_cs addIs [PartI,equalityI] addSEs [PartE]) 1);
val Part_Inl = result();

goal Sum.thy "Part(A+B,Inr) = {Inr(y). y: B}";
by (fast_tac (sum_cs addIs [PartI,equalityI] addSEs [PartE]) 1);
val Part_Inr = result();

goalw Sum.thy [Part_def] "!!a. a : Part(A,h) ==> a : A";
by (etac CollectD1 1);
val PartD1 = result();

goal Sum.thy "Part(A,%x.x) = A";
by (fast_tac (ZF_cs addIs [PartI,equalityI] addSEs [PartE]) 1);
val Part_id = result();

goal Sum.thy "Part(A+B, %x.Inr(h(x))) = {Inr(y). y: Part(B,h)}";
by (fast_tac (sum_cs addIs [PartI,equalityI] addSEs [PartE]) 1);
val Part_Inr2 = result();

goal Sum.thy "!!A B C. C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C";
by (rtac equalityI 1);
by (rtac Un_least 1);
by (rtac Part_subset 1);
by (rtac Part_subset 1);
by (fast_tac (ZF_cs addIs [PartI] addSEs [sumE]) 1);
val Part_sum_equality = result();
