(*  Title:      ZF/QPair.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Quine-inspired ordered pairs and disjoint sums, for non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.

Many proofs are borrowed from pair.ML and sum.ML

Do we EVER have rank(a) < rank(<a;b>) ?  Perhaps if the latter rank
    is not a limit ordinal? 
*)

(**** Quine ordered pairing ****)

(** Lemmas for showing that <a;b> uniquely determines a and b **)

Goalw [QPair_def] "<0;0> = 0";
by (Simp_tac 1);
qed "QPair_empty";

Goalw [QPair_def] "<a;b> = <c;d> <-> a=c & b=d";
by (rtac sum_equal_iff 1);
qed "QPair_iff";

bind_thm ("QPair_inject", QPair_iff RS iffD1 RS conjE);

Addsimps [QPair_empty, QPair_iff];
AddSEs   [QPair_inject];

Goal "<a;b> = <c;d> ==> a=c";
by (Blast_tac 1) ;
qed "QPair_inject1";

Goal "<a;b> = <c;d> ==> b=d";
by (Blast_tac 1) ;
qed "QPair_inject2";


(*** QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

Goalw [QSigma_def] "[| a:A;  b:B(a) |] ==> <a;b> : QSigma(A,B)";
by (Blast_tac 1) ;
qed "QSigmaI";

AddSIs [QSigmaI];

(*The general elimination rule*)
val major::prems= Goalw [QSigma_def] 
    "[| c: QSigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x;y> |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ;
qed "QSigmaE";

(** Elimination rules for <a;b>:A*B -- introducing no eigenvariables **)

val QSigmaE2 = 
  rule_by_tactic (REPEAT_FIRST (etac QPair_inject ORELSE' bound_hyp_subst_tac)
                  THEN prune_params_tac)
      (inst "c" "<a;b>" QSigmaE);  

AddSEs [QSigmaE2, QSigmaE];

Goal "<a;b> : QSigma(A,B) ==> a : A";
by (Blast_tac 1) ;
qed "QSigmaD1";

Goal "<a;b> : QSigma(A,B) ==> b : B(a)";
by (Blast_tac 1) ;
qed "QSigmaD2";


val prems= Goalw [QSigma_def] 
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    QSigma(A,B) = QSigma(A',B')";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "QSigma_cong";

Goal "QSigma(0,B) = 0";
by (Blast_tac 1) ;
qed "QSigma_empty1";

Goal "A <*> 0 = 0";
by (Blast_tac 1) ;
qed "QSigma_empty2";

Addsimps [QSigma_empty1, QSigma_empty2];


(*** Projections: qfst, qsnd ***)

Goalw [qfst_def]  "qfst(<a;b>) = a";
by (Blast_tac 1) ;
qed "qfst_conv";

Goalw [qsnd_def]  "qsnd(<a;b>) = b";
by (Blast_tac 1) ;
qed "qsnd_conv";

Addsimps [qfst_conv, qsnd_conv];

Goal "p:QSigma(A,B) ==> qfst(p) : A";
by (Auto_tac) ;
qed "qfst_type";

Goal "p:QSigma(A,B) ==> qsnd(p) : B(qfst(p))";
by (Auto_tac) ;
qed "qsnd_type";

Goal "a: QSigma(A,B) ==> <qfst(a); qsnd(a)> = a";
by Auto_tac;
qed "QPair_qfst_qsnd_eq";


(*** Eliminator - qsplit ***)

(*A META-equality, so that it applies to higher types as well...*)
Goalw [qsplit_def] "qsplit(%x y. c(x,y), <a;b>) == c(a,b)";
by (Simp_tac 1);
qed "qsplit";
Addsimps [qsplit];

val major::prems= Goal
    "[|  p:QSigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x;y>) \
\    |] ==> qsplit(%x y. c(x,y), p) : C(p)";
by (rtac (major RS QSigmaE) 1);
by (asm_simp_tac (simpset() addsimps prems) 1) ;
qed "qsplit_type";

Goalw [qsplit_def]
 "u: A<*>B ==> R(qsplit(c,u)) <-> (ALL x:A. ALL y:B. u = <x;y> --> R(c(x,y)))";
by Auto_tac;
qed "expand_qsplit";


(*** qsplit for predicates: result type o ***)

Goalw [qsplit_def] "R(a,b) ==> qsplit(R, <a;b>)";
by (Asm_simp_tac 1);
qed "qsplitI";

val major::sigma::prems = Goalw [qsplit_def]
    "[| qsplit(R,z);  z:QSigma(A,B);                    \
\       !!x y. [| z = <x;y>;  R(x,y) |] ==> P           \
\   |] ==> P";
by (rtac (sigma RS QSigmaE) 1);
by (cut_facts_tac [major] 1);
by (REPEAT (ares_tac prems 1));
by (Asm_full_simp_tac 1);
qed "qsplitE";

Goalw [qsplit_def] "qsplit(R,<a;b>) ==> R(a,b)";
by (Asm_full_simp_tac 1);
qed "qsplitD";


(*** qconverse ***)

Goalw [qconverse_def] "<a;b>:r ==> <b;a>:qconverse(r)";
by (Blast_tac 1) ;
qed "qconverseI";

Goalw [qconverse_def] "<a;b> : qconverse(r) ==> <b;a> : r";
by (Blast_tac 1) ;
qed "qconverseD";

val [major,minor]= Goalw [qconverse_def] 
    "[| yx : qconverse(r);  \
\       !!x y. [| yx=<y;x>;  <x;y>:r |] ==> P \
\    |] ==> P";
by (rtac (major RS ReplaceE) 1);
by (REPEAT (eresolve_tac [exE, conjE, minor] 1));
by (hyp_subst_tac 1);
by (assume_tac 1) ;
qed "qconverseE";

AddSIs [qconverseI];
AddSEs [qconverseD, qconverseE];

Goal "r<=QSigma(A,B) ==> qconverse(qconverse(r)) = r";
by (Blast_tac 1) ;
qed "qconverse_qconverse";

Goal "r <= A <*> B ==> qconverse(r) <= B <*> A";
by (Blast_tac 1) ;
qed "qconverse_type";

Goal "qconverse(A <*> B) = B <*> A";
by (Blast_tac 1) ;
qed "qconverse_prod";

Goal "qconverse(0) = 0";
by (Blast_tac 1) ;
qed "qconverse_empty";


(**** The Quine-inspired notion of disjoint sum ****)

val qsum_defs = [qsum_def,QInl_def,QInr_def,qcase_def];

(** Introduction rules for the injections **)

Goalw qsum_defs "a : A ==> QInl(a) : A <+> B";
by (Blast_tac 1);
qed "QInlI";

Goalw qsum_defs "b : B ==> QInr(b) : A <+> B";
by (Blast_tac 1);
qed "QInrI";

(** Elimination rules **)

val major::prems = Goalw qsum_defs
    "[| u: A <+> B;  \
\       !!x. [| x:A;  u=QInl(x) |] ==> P; \
\       !!y. [| y:B;  u=QInr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[QSigmaE,singletonE,ssubst]) 1));
qed "qsumE";

AddSIs [QInlI, QInrI];

(** Injection and freeness equivalences, for rewriting **)

Goalw qsum_defs "QInl(a)=QInl(b) <-> a=b";
by (Simp_tac 1);
qed "QInl_iff";

Goalw qsum_defs "QInr(a)=QInr(b) <-> a=b";
by (Simp_tac 1);
qed "QInr_iff";

Goalw qsum_defs "QInl(a)=QInr(b) <-> False";
by (Simp_tac 1);
qed "QInl_QInr_iff";

Goalw qsum_defs "QInr(b)=QInl(a) <-> False";
by (Simp_tac 1);
qed "QInr_QInl_iff";

Goalw qsum_defs "0<+>0 = 0";
by (Simp_tac 1);
qed "qsum_empty";

(*Injection and freeness rules*)

bind_thm ("QInl_inject", (QInl_iff RS iffD1));
bind_thm ("QInr_inject", (QInr_iff RS iffD1));
bind_thm ("QInl_neq_QInr", (QInl_QInr_iff RS iffD1 RS FalseE));
bind_thm ("QInr_neq_QInl", (QInr_QInl_iff RS iffD1 RS FalseE));

AddSEs [qsumE, QInl_neq_QInr, QInr_neq_QInl];
AddSDs [QInl_inject, QInr_inject];
Addsimps [QInl_iff, QInr_iff, QInl_QInr_iff, QInr_QInl_iff, qsum_empty];

Goal "QInl(a): A<+>B ==> a: A";
by (Blast_tac 1);
qed "QInlD";

Goal "QInr(b): A<+>B ==> b: B";
by (Blast_tac 1);
qed "QInrD";

(** <+> is itself injective... who cares?? **)

Goal "u: A <+> B <-> (EX x. x:A & u=QInl(x)) | (EX y. y:B & u=QInr(y))";
by (Blast_tac 1);
qed "qsum_iff";

Goal "A <+> B <= C <+> D <-> A<=C & B<=D";
by (Blast_tac 1);
qed "qsum_subset_iff";

Goal "A <+> B = C <+> D <-> A=C & B=D";
by (simp_tac (simpset() addsimps [extension,qsum_subset_iff]) 1);
by (Blast_tac 1);
qed "qsum_equal_iff";

(*** Eliminator -- qcase ***)

Goalw qsum_defs "qcase(c, d, QInl(a)) = c(a)";
by (Simp_tac 1);
qed "qcase_QInl";

Goalw qsum_defs "qcase(c, d, QInr(b)) = d(b)";
by (Simp_tac 1);
qed "qcase_QInr";

Addsimps [qcase_QInl, qcase_QInr];

val major::prems = Goal
    "[| u: A <+> B; \
\       !!x. x: A ==> c(x): C(QInl(x));   \
\       !!y. y: B ==> d(y): C(QInr(y)) \
\    |] ==> qcase(c,d,u) : C(u)";
by (rtac (major RS qsumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "qcase_type";

(** Rules for the Part primitive **)

Goal "Part(A <+> B,QInl) = {QInl(x). x: A}";
by (Blast_tac 1);
qed "Part_QInl";

Goal "Part(A <+> B,QInr) = {QInr(y). y: B}";
by (Blast_tac 1);
qed "Part_QInr";

Goal "Part(A <+> B, %x. QInr(h(x))) = {QInr(y). y: Part(B,h)}";
by (Blast_tac 1);
qed "Part_QInr2";

Goal "C <= A <+> B ==> Part(C,QInl) Un Part(C,QInr) = C";
by (Blast_tac 1);
qed "Part_qsum_equality";
