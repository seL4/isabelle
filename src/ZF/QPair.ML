(*  Title:      ZF/QPair.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
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

qed_goalw "QPair_empty" thy [QPair_def]
    "<0;0> = 0"
 (fn _=> [Simp_tac 1]);

qed_goalw "QPair_iff" thy [QPair_def]
    "<a;b> = <c;d> <-> a=c & b=d"
 (fn _=> [rtac sum_equal_iff 1]);

bind_thm ("QPair_inject", (QPair_iff RS iffD1 RS conjE));

Addsimps [QPair_empty, QPair_iff];
AddSEs   [QPair_inject];

qed_goal "QPair_inject1" thy "<a;b> = <c;d> ==> a=c"
 (fn [major]=>
  [ (rtac (major RS QPair_inject) 1), (assume_tac 1) ]);

qed_goal "QPair_inject2" thy "<a;b> = <c;d> ==> b=d"
 (fn [major]=>
  [ (rtac (major RS QPair_inject) 1), (assume_tac 1) ]);


(*** QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product ***)

qed_goalw "QSigmaI" thy [QSigma_def]
    "!!A B. [| a:A;  b:B(a) |] ==> <a;b> : QSigma(A,B)"
 (fn _ => [ Fast_tac 1 ]);

AddSIs [QSigmaI];

(*The general elimination rule*)
qed_goalw "QSigmaE" thy [QSigma_def]
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

qed_goal "QSigmaD1" thy "<a;b> : QSigma(A,B) ==> a : A"
 (fn [major]=>
  [ (rtac (major RS QSigmaE2) 1), (assume_tac 1) ]);

qed_goal "QSigmaD2" thy "<a;b> : QSigma(A,B) ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS QSigmaE2) 1), (assume_tac 1) ]);

AddSEs [QSigmaE2, QSigmaE];


qed_goalw "QSigma_cong" thy [QSigma_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> \
\    QSigma(A,B) = QSigma(A',B')"
 (fn prems=> [ (simp_tac (!simpset addsimps prems) 1) ]);

qed_goal "QSigma_empty1" thy "QSigma(0,B) = 0"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "QSigma_empty2" thy "A <*> 0 = 0"
 (fn _ => [ (Fast_tac 1) ]);

Addsimps [QSigma_empty1, QSigma_empty2];


(*** Projections: qfst, qsnd ***)

qed_goalw "qfst_conv" thy [qfst_def] "qfst(<a;b>) = a"
 (fn _=> 
  [ (fast_tac (!claset addIs [the_equality]) 1) ]);

qed_goalw "qsnd_conv" thy [qsnd_def] "qsnd(<a;b>) = b"
 (fn _=> 
  [ (fast_tac (!claset addIs [the_equality]) 1) ]);

Addsimps [qfst_conv, qsnd_conv];

qed_goal "qfst_type" thy
    "!!p. p:QSigma(A,B) ==> qfst(p) : A"
 (fn _=> [ Auto_tac() ]);

qed_goal "qsnd_type" thy
    "!!p. p:QSigma(A,B) ==> qsnd(p) : B(qfst(p))"
 (fn _=> [ Auto_tac() ]);

goal thy "!!a A B. a: QSigma(A,B) ==> <qfst(a); qsnd(a)> = a";
by (Auto_tac());
qed "QPair_qfst_qsnd_eq";


(*** Eliminator - qsplit ***)

(*A META-equality, so that it applies to higher types as well...*)
qed_goalw "qsplit" thy [qsplit_def]
    "qsplit(%x y.c(x,y), <a;b>) == c(a,b)"
 (fn _ => [ (Simp_tac 1),
            (rtac reflexive_thm 1) ]);

Addsimps [qsplit];

qed_goal "qsplit_type" thy
    "[|  p:QSigma(A,B);   \
\        !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x;y>) \
\    |] ==> qsplit(%x y.c(x,y), p) : C(p)"
 (fn major::prems=>
  [ (rtac (major RS QSigmaE) 1),
    (asm_simp_tac (!simpset addsimps prems) 1) ]);

goalw thy [qsplit_def]
  "!!u. u: A<*>B ==>   \
\       R(qsplit(c,u)) <-> (ALL x:A. ALL y:B. u = <x;y> --> R(c(x,y)))";
by (Auto_tac());
qed "expand_qsplit";


(*** qsplit for predicates: result type o ***)

goalw thy [qsplit_def] "!!R a b. R(a,b) ==> qsplit(R, <a;b>)";
by (Asm_simp_tac 1);
qed "qsplitI";

val major::sigma::prems = goalw thy [qsplit_def]
    "[| qsplit(R,z);  z:QSigma(A,B);                    \
\       !!x y. [| z = <x;y>;  R(x,y) |] ==> P           \
\   |] ==> P";
by (rtac (sigma RS QSigmaE) 1);
by (cut_facts_tac [major] 1);
by (REPEAT (ares_tac prems 1));
by (Asm_full_simp_tac 1);
qed "qsplitE";

goalw thy [qsplit_def] "!!R a b. qsplit(R,<a;b>) ==> R(a,b)";
by (Asm_full_simp_tac 1);
qed "qsplitD";


(*** qconverse ***)

qed_goalw "qconverseI" thy [qconverse_def]
    "!!a b r. <a;b>:r ==> <b;a>:qconverse(r)"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "qconverseD" thy [qconverse_def]
    "!!a b r. <a;b> : qconverse(r) ==> <b;a> : r"
 (fn _ => [ (Fast_tac 1) ]);

qed_goalw "qconverseE" thy [qconverse_def]
    "[| yx : qconverse(r);  \
\       !!x y. [| yx=<y;x>;  <x;y>:r |] ==> P \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (eresolve_tac [exE, conjE, minor] 1)),
    (hyp_subst_tac 1),
    (assume_tac 1) ]);

AddSIs [qconverseI];
AddSEs [qconverseD, qconverseE];

qed_goal "qconverse_qconverse" thy
    "!!A B r. r<=QSigma(A,B) ==> qconverse(qconverse(r)) = r"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "qconverse_type" thy
    "!!A B r. r <= A <*> B ==> qconverse(r) <= B <*> A"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "qconverse_prod" thy "qconverse(A <*> B) = B <*> A"
 (fn _ => [ (Fast_tac 1) ]);

qed_goal "qconverse_empty" thy "qconverse(0) = 0"
 (fn _ => [ (Fast_tac 1) ]);


(**** The Quine-inspired notion of disjoint sum ****)

val qsum_defs = [qsum_def,QInl_def,QInr_def,qcase_def];

(** Introduction rules for the injections **)

goalw thy qsum_defs "!!a A B. a : A ==> QInl(a) : A <+> B";
by (Fast_tac 1);
qed "QInlI";

goalw thy qsum_defs "!!b A B. b : B ==> QInr(b) : A <+> B";
by (Fast_tac 1);
qed "QInrI";

(** Elimination rules **)

val major::prems = goalw thy qsum_defs
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

goalw thy qsum_defs "QInl(a)=QInl(b) <-> a=b";
by (Simp_tac 1);
qed "QInl_iff";

goalw thy qsum_defs "QInr(a)=QInr(b) <-> a=b";
by (Simp_tac 1);
qed "QInr_iff";

goalw thy qsum_defs "QInl(a)=QInr(b) <-> False";
by (Simp_tac 1);
qed "QInl_QInr_iff";

goalw thy qsum_defs "QInr(b)=QInl(a) <-> False";
by (Simp_tac 1);
qed "QInr_QInl_iff";

goalw thy qsum_defs "0<+>0 = 0";
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

goal thy "!!A B. QInl(a): A<+>B ==> a: A";
by (Fast_tac 1);
qed "QInlD";

goal thy "!!A B. QInr(b): A<+>B ==> b: B";
by (Fast_tac 1);
qed "QInrD";

(** <+> is itself injective... who cares?? **)

goal thy
    "u: A <+> B <-> (EX x. x:A & u=QInl(x)) | (EX y. y:B & u=QInr(y))";
by (Fast_tac 1);
qed "qsum_iff";

goal thy "A <+> B <= C <+> D <-> A<=C & B<=D";
by (Fast_tac 1);
qed "qsum_subset_iff";

goal thy "A <+> B = C <+> D <-> A=C & B=D";
by (simp_tac (!simpset addsimps [extension,qsum_subset_iff]) 1);
by (Fast_tac 1);
qed "qsum_equal_iff";

(*** Eliminator -- qcase ***)

goalw thy qsum_defs "qcase(c, d, QInl(a)) = c(a)";
by (Simp_tac 1);
qed "qcase_QInl";

goalw thy qsum_defs "qcase(c, d, QInr(b)) = d(b)";
by (Simp_tac 1);
qed "qcase_QInr";

Addsimps [qcase_QInl, qcase_QInr];

val major::prems = goal thy
    "[| u: A <+> B; \
\       !!x. x: A ==> c(x): C(QInl(x));   \
\       !!y. y: B ==> d(y): C(QInr(y)) \
\    |] ==> qcase(c,d,u) : C(u)";
by (rtac (major RS qsumE) 1);
by (ALLGOALS (etac ssubst));
by (ALLGOALS (asm_simp_tac (!simpset addsimps prems)));
qed "qcase_type";

(** Rules for the Part primitive **)

goal thy "Part(A <+> B,QInl) = {QInl(x). x: A}";
by (Fast_tac 1);
qed "Part_QInl";

goal thy "Part(A <+> B,QInr) = {QInr(y). y: B}";
by (Fast_tac 1);
qed "Part_QInr";

goal thy "Part(A <+> B, %x.QInr(h(x))) = {QInr(y). y: Part(B,h)}";
by (Fast_tac 1);
qed "Part_QInr2";

goal thy "!!A B C. C <= A <+> B ==> Part(C,QInl) Un Part(C,QInr) = C";
by (Fast_tac 1);
qed "Part_qsum_equality";
