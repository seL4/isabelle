(*  Title:      ZF/mono
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Monotonicity of various operations (for lattice properties see subset.ML)
*)

open mono;

(** Replacement, in its various formulations **)

(*Not easy to express monotonicity in P, since any "bigger" predicate
  would have to be single-valued*)
goal thy "!!A B. A<=B ==> Replace(A,P) <= Replace(B,P)";
by (fast_tac (!claset addSEs [ReplaceE]) 1);
qed "Replace_mono";

goal thy "!!A B. A<=B ==> {f(x). x:A} <= {f(x). x:B}";
by (Fast_tac 1);
qed "RepFun_mono";

goal thy "!!A B. A<=B ==> Pow(A) <= Pow(B)";
by (Fast_tac 1);
qed "Pow_mono";

goal thy "!!A B. A<=B ==> Union(A) <= Union(B)";
by (Fast_tac 1);
qed "Union_mono";

val prems = goal thy
    "[| A<=C;  !!x. x:A ==> B(x)<=D(x) \
\    |] ==> (UN x:A. B(x)) <= (UN x:C. D(x))";
by (fast_tac (!claset addIs (prems RL [subsetD])) 1);
qed "UN_mono";

(*Intersection is ANTI-monotonic.  There are TWO premises! *)
goal thy "!!A B. [| A<=B;  a:A |] ==> Inter(B) <= Inter(A)";
by (Fast_tac 1);
qed "Inter_anti_mono";

goal thy "!!C D. C<=D ==> cons(a,C) <= cons(a,D)";
by (Fast_tac 1);
qed "cons_mono";

goal thy "!!A B C D. [| A<=C;  B<=D |] ==> A Un B <= C Un D";
by (Fast_tac 1);
qed "Un_mono";

goal thy "!!A B C D. [| A<=C;  B<=D |] ==> A Int B <= C Int D";
by (Fast_tac 1);
qed "Int_mono";

goal thy "!!A B C D. [| A<=C;  D<=B |] ==> A-B <= C-D";
by (Fast_tac 1);
qed "Diff_mono";

(** Standard products, sums and function spaces **)

goal thy "!!A B C D. [| A<=C;  ALL x:A. B(x) <= D(x) |] ==> \
\                       Sigma(A,B) <= Sigma(C,D)";
by (Fast_tac 1);
qed "Sigma_mono_lemma";
val Sigma_mono = ballI RSN (2,Sigma_mono_lemma);

goalw thy sum_defs "!!A B C D. [| A<=C;  B<=D |] ==> A+B <= C+D";
by (REPEAT (ares_tac [subset_refl,Un_mono,Sigma_mono] 1));
qed "sum_mono";

(*Note that B->A and C->A are typically disjoint!*)
goal thy "!!A B C. B<=C ==> A->B <= A->C";
by (fast_tac (!claset addIs [lam_type] addEs [Pi_lamE]) 1);
qed "Pi_mono";

goalw thy [lam_def] "!!A B. A<=B ==> Lambda(A,c) <= Lambda(B,c)";
by (etac RepFun_mono 1);
qed "lam_mono";

(** Quine-inspired ordered pairs, products, injections and sums **)

goalw QPair.thy [QPair_def] "!!a b c d. [| a<=c;  b<=d |] ==> <a;b> <= <c;d>";
by (REPEAT (ares_tac [sum_mono] 1));
qed "QPair_mono";

goal QPair.thy "!!A B C D. [| A<=C;  ALL x:A. B(x) <= D(x) |] ==>  \
\                          QSigma(A,B) <= QSigma(C,D)";
by (Fast_tac 1);
qed "QSigma_mono_lemma";
val QSigma_mono = ballI RSN (2,QSigma_mono_lemma);

goalw QPair.thy [QInl_def] "!!a b. a<=b ==> QInl(a) <= QInl(b)";
by (REPEAT (ares_tac [subset_refl RS QPair_mono] 1));
qed "QInl_mono";

goalw QPair.thy [QInr_def] "!!a b. a<=b ==> QInr(a) <= QInr(b)";
by (REPEAT (ares_tac [subset_refl RS QPair_mono] 1));
qed "QInr_mono";

goal QPair.thy "!!A B C D. [| A<=C;  B<=D |] ==> A <+> B <= C <+> D";
by (Fast_tac 1);
qed "qsum_mono";


(** Converse, domain, range, field **)

goal thy "!!r s. r<=s ==> converse(r) <= converse(s)";
by (Fast_tac 1);
qed "converse_mono";

goal thy "!!r s. r<=s ==> domain(r)<=domain(s)";
by (Fast_tac 1);
qed "domain_mono";

bind_thm ("domain_rel_subset", [domain_mono, domain_subset] MRS subset_trans);

goal thy "!!r s. r<=s ==> range(r)<=range(s)";
by (Fast_tac 1);
qed "range_mono";

bind_thm ("range_rel_subset", [range_mono, range_subset] MRS subset_trans);

goal thy "!!r s. r<=s ==> field(r)<=field(s)";
by (Fast_tac 1);
qed "field_mono";

goal thy "!!r A. r <= A*A ==> field(r) <= A";
by (etac (field_mono RS subset_trans) 1);
by (Fast_tac 1);
qed "field_rel_subset";


(** Images **)

val [prem1,prem2] = goal thy
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r``A <= s``B";
by (fast_tac (!claset addIs [prem1, prem2 RS subsetD]) 1);
qed "image_pair_mono";

val [prem1,prem2] = goal thy
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r-``A <= s-``B";
by (fast_tac (!claset addIs [prem1, prem2 RS subsetD]) 1);
qed "vimage_pair_mono";

goal thy "!!r s. [| r<=s;  A<=B |] ==> r``A <= s``B";
by (Fast_tac 1);
qed "image_mono";

goal thy "!!r s. [| r<=s;  A<=B |] ==> r-``A <= s-``B";
by (Fast_tac 1);
qed "vimage_mono";

val [sub,PQimp] = goal thy
    "[| A<=B;  !!x. x:A ==> P(x) --> Q(x) |] ==> Collect(A,P) <= Collect(B,Q)";
by (fast_tac (!claset addIs [sub RS subsetD, PQimp RS mp]) 1);
qed "Collect_mono";

(** Monotonicity of implications -- some could go to FOL **)

goal thy "!!A B x. A<=B ==> x:A --> x:B";
by (Fast_tac 1);
qed "in_mono";

goal IFOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1&P2) --> (Q1&Q2)";
by (Int.fast_tac 1);
qed "conj_mono";

goal IFOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1|P2) --> (Q1|Q2)";
by (Int.fast_tac 1);
qed "disj_mono";

goal IFOL.thy "!!P1 P2 Q1 Q2.[| Q1-->P1; P2-->Q2 |] ==> (P1-->P2)-->(Q1-->Q2)";
by (Int.fast_tac 1);
qed "imp_mono";

goal IFOL.thy "P-->P";
by (rtac impI 1);
by (assume_tac 1);
qed "imp_refl";

val [PQimp] = goal IFOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (EX x.P(x)) --> (EX x.Q(x))";
by (fast_tac (!claset addIs [PQimp RS mp]) 1);
qed "ex_mono";

val [PQimp] = goal IFOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (ALL x.P(x)) --> (ALL x.Q(x))";
by (fast_tac (!claset addIs [PQimp RS mp]) 1);
qed "all_mono";

(*Used in intr_elim.ML and in individual datatype definitions*)
val basic_monos = [subset_refl, imp_refl, disj_mono, conj_mono, 
                   ex_mono, Collect_mono, Part_mono, in_mono];

