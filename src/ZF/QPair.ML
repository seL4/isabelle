(*  Title: 	ZF/QPair.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For QPair.thy.  

Quine-inspired ordered pairs and disjoint sums, for non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.

Many proofs are borrowed from pair.ML and sum.ML

Do we EVER have rank(a) < rank(<a;b>) ?  Perhaps if the latter rank
    is not a limit ordinal? 
*)


open QPair;

(**** Quine ordered pairing ****)

(** Lemmas for showing that <a;b> uniquely determines a and b **)

qed_goalw "QPair_iff" QPair.thy [QPair_def]
    "<a;b> = <c;d> <-> a=c & b=d"
 (fn _=> [rtac sum_equal_iff 1]);

bind_thm ("QPair_inject", (QPair_iff RS iffD1 RS conjE));

qed_goal "QPair_inject1" QPair.thy "<a;b> = <c;d> ==> a=c"
 (fn [major]=>
  [ (rtac (major RS QPair_inject) 1), (assume_tac 1) ]);

qed_goal "QPair_inject2" QPair.thy "<a;b> = <c;d> ==> b=d"
 (fn [major]=>
  [ (rtac (major RS QPair_inject) 1), (assume_tac 1) ]);


(*** QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

qed_goalw "QSigmaI" QPair.thy [QSigma_def]
    "[| a:A;  b:B(a) |] ==> <a;b> : QSigma(A,B)"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[singletonI,UN_I]) 1)) ]);

(*The general elimination rule*)
qed_goalw "QSigmaE" QPair.thy [QSigma_def]
    "[| c: QSigma(A,B);  \
\       !!x y.[| x:A;  y:B(x);  c=<x;y> |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

(** Elimination rules for <a;b>:A*B -- introducing no eigenvariables **)

val QSigmaE2 = 
  rule_by_tactic (REPEAT_FIRST (etac QPair_inject ORELSE' bound_hyp_subst_tac)
		  THEN prune_params_tac)
      (read_instantiate [("c","<a;b>")] QSigmaE);  

qed_goal "QSigmaD1" QPair.thy "<a;b> : QSigma(A,B) ==> a : A"
 (fn [major]=>
  [ (rtac (major RS QSigmaE2) 1), (assume_tac 1) ]);

qed_goal "QSigmaD2" QPair.thy "<a;b> : QSigma(A,B) ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS QSigmaE2) 1), (assume_tac 1) ]);

val qpair_cs = ZF_cs addSIs [QSigmaI] addSEs [QSigmaE2, QSigmaE, QPair_inject];


qed_goalw "QSigma_cong" QPair.thy [QSigma_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    QSigma(A,B) = QSigma(A',B')"
 (fn prems=> [ (simp_tac (ZF_ss addsimps prems) 1) ]);

qed_goal "QSigma_empty1" QPair.thy "QSigma(0,B) = 0"
 (fn _ => [ (fast_tac (qpair_cs addIs [equalityI]) 1) ]);

qed_goal "QSigma_empty2" QPair.thy "A <*> 0 = 0"
 (fn _ => [ (fast_tac (qpair_cs addIs [equalityI]) 1) ]);


(*** Eliminator - qsplit ***)

qed_goalw "qsplit" QPair.thy [qsplit_def]
    "qsplit(%x y.c(x,y), <a;b>) = c(a,b)"
 (fn _ => [ (fast_tac (qpair_cs addIs [the_equality]) 1) ]);

qed_goal "qsplit_type" QPair.thy
    "[|  p:QSigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x;y>) \
\    |] ==> qsplit(%x y.c(x,y), p) : C(p)"
 (fn major::prems=>
  [ (rtac (major RS QSigmaE) 1),
    (etac ssubst 1),
    (REPEAT (ares_tac (prems @ [qsplit RS ssubst]) 1)) ]);


(*** qconverse ***)

qed_goalw "qconverseI" QPair.thy [qconverse_def]
    "!!a b r. <a;b>:r ==> <b;a>:qconverse(r)"
 (fn _ => [ (fast_tac qpair_cs 1) ]);

qed_goalw "qconverseD" QPair.thy [qconverse_def]
    "!!a b r. <a;b> : qconverse(r) ==> <b;a> : r"
 (fn _ => [ (fast_tac qpair_cs 1) ]);

qed_goalw "qconverseE" QPair.thy [qconverse_def]
    "[| yx : qconverse(r);  \
\       !!x y. [| yx=<y;x>;  <x;y>:r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (eresolve_tac [exE, conjE, minor] 1)),
    (hyp_subst_tac 1),
    (assume_tac 1) ]);

val qconverse_cs = qpair_cs addSIs [qconverseI] 
			    addSEs [qconverseD,qconverseE];

qed_goal "qconverse_of_qconverse" QPair.thy
    "!!A B r. r<=QSigma(A,B) ==> qconverse(qconverse(r)) = r"
 (fn _ => [ (fast_tac (qconverse_cs addSIs [equalityI]) 1) ]);

qed_goal "qconverse_type" QPair.thy
    "!!A B r. r <= A <*> B ==> qconverse(r) <= B <*> A"
 (fn _ => [ (fast_tac qconverse_cs 1) ]);

qed_goal "qconverse_of_prod" QPair.thy "qconverse(A <*> B) = B <*> A"
 (fn _ => [ (fast_tac (qconverse_cs addSIs [equalityI]) 1) ]);

qed_goal "qconverse_empty" QPair.thy "qconverse(0) = 0"
 (fn _ => [ (fast_tac (qconverse_cs addSIs [equalityI]) 1) ]);


(*** qsplit for predicates: result type o ***)

goalw QPair.thy [qfsplit_def] "!!R a b. R(a,b) ==> qfsplit(R, <a;b>)";
by (REPEAT (ares_tac [refl,exI,conjI] 1));
qed "qfsplitI";

val major::prems = goalw QPair.thy [qfsplit_def]
    "[| qfsplit(R,z);  !!x y. [| z = <x;y>;  R(x,y) |] ==> P |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,exE,conjE]) 1));
qed "qfsplitE";

goal QPair.thy "!!R a b. qfsplit(R,<a;b>) ==> R(a,b)";
by (REPEAT (eresolve_tac [asm_rl,qfsplitE,QPair_inject,ssubst] 1));
qed "qfsplitD";


(**** The Quine-inspired notion of disjoint sum ****)

val qsum_defs = [qsum_def,QInl_def,QInr_def,qcase_def];

(** Introduction rules for the injections **)

goalw QPair.thy qsum_defs "!!a A B. a : A ==> QInl(a) : A <+> B";
by (REPEAT (ares_tac [UnI1,QSigmaI,singletonI] 1));
qed "QInlI";

goalw QPair.thy qsum_defs "!!b A B. b : B ==> QInr(b) : A <+> B";
by (REPEAT (ares_tac [UnI2,QSigmaI,singletonI] 1));
qed "QInrI";

(** Elimination rules **)

val major::prems = goalw QPair.thy qsum_defs
    "[| u: A <+> B;  \
\       !!x. [| x:A;  u=QInl(x) |] ==> P; \
\       !!y. [| y:B;  u=QInr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[QSigmaE,singletonE,ssubst]) 1));
qed "qsumE";

(** Injection and freeness equivalences, for rewriting **)

goalw QPair.thy qsum_defs "QInl(a)=QInl(b) <-> a=b";
by (simp_tac (ZF_ss addsimps [QPair_iff]) 1);
qed "QInl_iff";

goalw QPair.thy qsum_defs "QInr(a)=QInr(b) <-> a=b";
by (simp_tac (ZF_ss addsimps [QPair_iff]) 1);
qed "QInr_iff";

goalw QPair.thy qsum_defs "QInl(a)=QInr(b) <-> False";
by (simp_tac (ZF_ss addsimps [QPair_iff, one_not_0 RS not_sym]) 1);
qed "QInl_QInr_iff";

goalw QPair.thy qsum_defs "QInr(b)=QInl(a) <-> False";
by (simp_tac (ZF_ss addsimps [QPair_iff, one_not_0]) 1);
qed "QInr_QInl_iff";

(*Injection and freeness rules*)

bind_thm ("QInl_inject", (QInl_iff RS iffD1));
bind_thm ("QInr_inject", (QInr_iff RS iffD1));
bind_thm ("QInl_neq_QInr", (QInl_QInr_iff RS iffD1 RS FalseE));
bind_thm ("QInr_neq_QInl", (QInr_QInl_iff RS iffD1 RS FalseE));

val qsum_cs = 
    qpair_cs addSIs [PartI, QInlI, QInrI] 
             addSEs [PartE, qsumE, QInl_neq_QInr, QInr_neq_QInl]
             addSDs [QInl_inject, QInr_inject];

goal QPair.thy "!!A B. QInl(a): A<+>B ==> a: A";
by (fast_tac qsum_cs 1);
qed "QInlD";

goal QPair.thy "!!A B. QInr(b): A<+>B ==> b: B";
by (fast_tac qsum_cs 1);
qed "QInrD";

(** <+> is itself injective... who cares?? **)

goal QPair.thy
    "u: A <+> B <-> (EX x. x:A & u=QInl(x)) | (EX y. y:B & u=QInr(y))";
by (fast_tac qsum_cs 1);
qed "qsum_iff";

goal QPair.thy "A <+> B <= C <+> D <-> A<=C & B<=D";
by (fast_tac qsum_cs 1);
qed "qsum_subset_iff";

goal QPair.thy "A <+> B = C <+> D <-> A=C & B=D";
by (simp_tac (ZF_ss addsimps [extension,qsum_subset_iff]) 1);
by (fast_tac ZF_cs 1);
qed "qsum_equal_iff";

(*** Eliminator -- qcase ***)

goalw QPair.thy qsum_defs "qcase(c, d, QInl(a)) = c(a)";
by (rtac (qsplit RS trans) 1);
by (rtac cond_0 1);
qed "qcase_QInl";

goalw QPair.thy qsum_defs "qcase(c, d, QInr(b)) = d(b)";
by (rtac (qsplit RS trans) 1);
by (rtac cond_1 1);
qed "qcase_QInr";

val major::prems = goal QPair.thy
    "[| u: A <+> B; \
\       !!x. x: A ==> c(x): C(QInl(x));   \
\       !!y. y: B ==> d(y): C(QInr(y)) \
\    |] ==> qcase(c,d,u) : C(u)";
by (rtac (major RS qsumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps
			    (prems@[qcase_QInl,qcase_QInr]))));
qed "qcase_type";

(** Rules for the Part primitive **)

goal QPair.thy "Part(A <+> B,QInl) = {QInl(x). x: A}";
by (fast_tac (qsum_cs addIs [equalityI]) 1);
qed "Part_QInl";

goal QPair.thy "Part(A <+> B,QInr) = {QInr(y). y: B}";
by (fast_tac (qsum_cs addIs [equalityI]) 1);
qed "Part_QInr";

goal QPair.thy "Part(A <+> B, %x.QInr(h(x))) = {QInr(y). y: Part(B,h)}";
by (fast_tac (qsum_cs addIs [equalityI]) 1);
qed "Part_QInr2";

goal QPair.thy "!!A B C. C <= A <+> B ==> Part(C,QInl) Un Part(C,QInr) = C";
by (fast_tac (qsum_cs addIs [equalityI]) 1);
qed "Part_qsum_equality";
