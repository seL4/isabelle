(*  Title: 	ZF/mono
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Monotonicity of various operations (for lattice properties see subset.ML)
*)

(** Replacement, in its various formulations **)

(*Not easy to express monotonicity in P, since any "bigger" predicate
  would have to be single-valued*)
goal ZF.thy "!!A B. A<=B ==> Replace(A,P) <= Replace(B,P)";
by (fast_tac (ZF_cs addSEs [ReplaceE]) 1);
val Replace_mono = result();

goal ZF.thy "!!A B. A<=B ==> {f(x). x:A} <= {f(x). x:B}";
by (fast_tac ZF_cs 1);
val RepFun_mono = result();

goal ZF.thy "!!A B. A<=B ==> Pow(A) <= Pow(B)";
by (fast_tac ZF_cs 1);
val Pow_mono = result();

goal ZF.thy "!!A B. A<=B ==> Union(A) <= Union(B)";
by (fast_tac ZF_cs 1);
val Union_mono = result();

val prems = goal ZF.thy
    "[| A<=C;  !!x. x:A ==> B(x)<=D(x) \
\    |] ==> (UN x:A. B(x)) <= (UN x:C. D(x))";
by (fast_tac (ZF_cs addIs (prems RL [subsetD])) 1);
val UN_mono = result();

(*Intersection is ANTI-monotonic.  There are TWO premises! *)
goal ZF.thy "!!A B. [| A<=B;  a:A |] ==> Inter(B) <= Inter(A)";
by (fast_tac ZF_cs 1);
val Inter_anti_mono = result();

goal ZF.thy "!!C D. C<=D ==> cons(a,C) <= cons(a,D)";
by (fast_tac ZF_cs 1);
val cons_mono = result();

goal ZF.thy "!!A B C D. [| A<=C;  B<=D |] ==> A Un B <= C Un D";
by (fast_tac ZF_cs 1);
val Un_mono = result();

goal ZF.thy "!!A B C D. [| A<=C;  B<=D |] ==> A Int B <= C Int D";
by (fast_tac ZF_cs 1);
val Int_mono = result();

goal ZF.thy "!!A B C D. [| A<=C;  D<=B |] ==> A-B <= C-D";
by (fast_tac ZF_cs 1);
val Diff_mono = result();

(** Standard products, sums and function spaces **)

goal ZF.thy "!!A B C D. [| A<=C;  ALL x:A. B(x) <= D(x) |] ==> \
\                       Sigma(A,B) <= Sigma(C,D)";
by (fast_tac ZF_cs 1);
val Sigma_mono_lemma = result();
val Sigma_mono = ballI RSN (2,Sigma_mono_lemma);

goalw Sum.thy sum_defs "!!A B C D. [| A<=C;  B<=D |] ==> A+B <= C+D";
by (REPEAT (ares_tac [subset_refl,Un_mono,Sigma_mono] 1));
val sum_mono = result();

(*Note that B->A and C->A are typically disjoint!*)
goal ZF.thy "!!A B C. B<=C ==> A->B <= A->C";
by (fast_tac (ZF_cs addIs [lam_type] addEs [Pi_lamE]) 1);
val Pi_mono = result();

goalw ZF.thy [lam_def] "!!A B. A<=B ==> Lambda(A,c) <= Lambda(B,c)";
by (etac RepFun_mono 1);
val lam_mono = result();

(** Quine-inspired ordered pairs, products, injections and sums **)

goalw QPair.thy [QPair_def] "!!a b c d. [| a<=c;  b<=d |] ==> <a;b> <= <c;d>";
by (REPEAT (ares_tac [sum_mono] 1));
val QPair_mono = result();

goal QPair.thy "!!A B C D. [| A<=C;  ALL x:A. B(x) <= D(x) |] ==>  \
\                          QSigma(A,B) <= QSigma(C,D)";
by (fast_tac qpair_cs 1);
val QSigma_mono_lemma = result();
val QSigma_mono = ballI RSN (2,QSigma_mono_lemma);

goalw QPair.thy [QInl_def] "!!a b. a<=b ==> QInl(a) <= QInl(b)";
by (REPEAT (ares_tac [subset_refl RS QPair_mono] 1));
val QInl_mono = result();

goalw QPair.thy [QInr_def] "!!a b. a<=b ==> QInr(a) <= QInr(b)";
by (REPEAT (ares_tac [subset_refl RS QPair_mono] 1));
val QInr_mono = result();

goal QPair.thy "!!A B C D. [| A<=C;  B<=D |] ==> A <+> B <= C <+> D";
by (fast_tac qsum_cs 1);
val qsum_mono = result();


(** Converse, domain, range, field **)

goal ZF.thy "!!r s. r<=s ==> converse(r) <= converse(s)";
by (fast_tac ZF_cs 1);
val converse_mono = result();

goal ZF.thy "!!r s. r<=s ==> domain(r)<=domain(s)";
by (fast_tac ZF_cs 1);
val domain_mono = result();

val domain_rel_subset = 
	[domain_mono, domain_subset] MRS subset_trans |> standard;

goal ZF.thy "!!r s. r<=s ==> range(r)<=range(s)";
by (fast_tac ZF_cs 1);
val range_mono = result();

val range_rel_subset = 
	[range_mono, range_subset] MRS subset_trans |> standard;

goal ZF.thy "!!r s. r<=s ==> field(r)<=field(s)";
by (fast_tac ZF_cs 1);
val field_mono = result();

goal ZF.thy "!!r A. r <= A*A ==> field(r) <= A";
by (etac (field_mono RS subset_trans) 1);
by (fast_tac ZF_cs 1);
val field_rel_subset = result();


(** Images **)

val [prem1,prem2] = goal ZF.thy
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r``A <= s``B";
by (fast_tac (ZF_cs addIs [prem1, prem2 RS subsetD]) 1);
val image_pair_mono = result();

val [prem1,prem2] = goal ZF.thy
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r-``A <= s-``B";
by (fast_tac (ZF_cs addIs [prem1, prem2 RS subsetD]) 1);
val vimage_pair_mono = result();

goal ZF.thy "!!r s. [| r<=s;  A<=B |] ==> r``A <= s``B";
by (fast_tac ZF_cs 1);
val image_mono = result();

goal ZF.thy "!!r s. [| r<=s;  A<=B |] ==> r-``A <= s-``B";
by (fast_tac ZF_cs 1);
val vimage_mono = result();

val [sub,PQimp] = goal ZF.thy
    "[| A<=B;  !!x. x:A ==> P(x) --> Q(x) |] ==> Collect(A,P) <= Collect(B,Q)";
by (fast_tac (ZF_cs addIs [sub RS subsetD, PQimp RS mp]) 1);
val Collect_mono = result();

(** Monotonicity of implications -- some could go to FOL **)

goal ZF.thy "!!A B x. A<=B ==> x:A --> x:B";
by (fast_tac ZF_cs 1);
val in_mono = result();

goal IFOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1&P2) --> (Q1&Q2)";
by (Int.fast_tac 1);
val conj_mono = result();

goal IFOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1|P2) --> (Q1|Q2)";
by (Int.fast_tac 1);
val disj_mono = result();

goal IFOL.thy "!!P1 P2 Q1 Q2.[| Q1-->P1; P2-->Q2 |] ==> (P1-->P2)-->(Q1-->Q2)";
by (Int.fast_tac 1);
val imp_mono = result();

goal IFOL.thy "P-->P";
by (rtac impI 1);
by (assume_tac 1);
val imp_refl = result();

val [PQimp] = goal IFOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (EX x.P(x)) --> (EX x.Q(x))";
by (fast_tac (FOL_cs addIs [PQimp RS mp]) 1);
val ex_mono = result();

val [PQimp] = goal IFOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (ALL x.P(x)) --> (ALL x.Q(x))";
by (fast_tac (FOL_cs addIs [PQimp RS mp]) 1);
val all_mono = result();

(*Used in intr_elim.ML and in individual datatype definitions*)
val basic_monos = [subset_refl, imp_refl, disj_mono, conj_mono, 
		   ex_mono, Collect_mono, Part_mono, in_mono];

