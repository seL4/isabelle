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
val Part_iff = result();

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


(*** Rules for Disjoint Sums ***)

val sum_defs = [sum_def,Inl_def,Inr_def,case_def];

goalw Sum.thy (bool_def::sum_defs) "Sigma(bool,C) = C(0) + C(1)";
by (fast_tac eq_cs 1);
val Sigma_bool = result();

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

(** Injection and freeness equivalences, for rewriting **)

goalw Sum.thy sum_defs "Inl(a)=Inl(b) <-> a=b";
by (simp_tac ZF_ss 1);
val Inl_iff = result();

goalw Sum.thy sum_defs "Inr(a)=Inr(b) <-> a=b";
by (simp_tac ZF_ss 1);
val Inr_iff = result();

goalw Sum.thy sum_defs "Inl(a)=Inr(b) <-> False";
by (simp_tac (ZF_ss addsimps [one_not_0 RS not_sym]) 1);
val Inl_Inr_iff = result();

goalw Sum.thy sum_defs "Inr(b)=Inl(a) <-> False";
by (simp_tac (ZF_ss addsimps [one_not_0]) 1);
val Inr_Inl_iff = result();

(*Injection and freeness rules*)

val Inl_inject = standard (Inl_iff RS iffD1);
val Inr_inject = standard (Inr_iff RS iffD1);
val Inl_neq_Inr = standard (Inl_Inr_iff RS iffD1 RS FalseE);
val Inr_neq_Inl = standard (Inr_Inl_iff RS iffD1 RS FalseE);

val sum_cs = ZF_cs addSIs [PartI, InlI, InrI] 
                   addSEs [PartE, sumE, Inl_neq_Inr, Inr_neq_Inl]
                   addSDs [Inl_inject, Inr_inject];

val sum_ss = ZF_ss addsimps [InlI, InrI, Inl_iff, Inr_iff, 
			     Inl_Inr_iff, Inr_Inl_iff];

goal Sum.thy "!!A B. Inl(a): A+B ==> a: A";
by (fast_tac sum_cs 1);
val InlD = result();

goal Sum.thy "!!A B. Inr(b): A+B ==> b: B";
by (fast_tac sum_cs 1);
val InrD = result();

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
val expand_case = result();


goal Sum.thy "!!A B h. A<=B ==> Part(A,h)<=Part(B,h)";
by (fast_tac sum_cs 1);
val Part_mono = result();

goal Sum.thy "Part(Collect(A,P), h) = Collect(Part(A,h), P)";
by (fast_tac (sum_cs addSIs [equalityI]) 1);
val Part_Collect = result();

val Part_CollectE =
    Part_Collect RS equalityD1 RS subsetD RS CollectE |> standard;

goal Sum.thy "Part(A+B,Inl) = {Inl(x). x: A}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
val Part_Inl = result();

goal Sum.thy "Part(A+B,Inr) = {Inr(y). y: B}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
val Part_Inr = result();

goalw Sum.thy [Part_def] "!!a. a : Part(A,h) ==> a : A";
by (etac CollectD1 1);
val PartD1 = result();

goal Sum.thy "Part(A,%x.x) = A";
by (fast_tac (sum_cs addIs [equalityI]) 1);
val Part_id = result();

goal Sum.thy "Part(A+B, %x.Inr(h(x))) = {Inr(y). y: Part(B,h)}";
by (fast_tac (sum_cs addIs [equalityI]) 1);
val Part_Inr2 = result();

goal Sum.thy "!!A B C. C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C";
by (fast_tac (sum_cs addIs [equalityI]) 1);
val Part_sum_equality = result();
