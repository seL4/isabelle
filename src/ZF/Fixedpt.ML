(*  Title:      ZF/fixedpt.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For fixedpt.thy.  Least and greatest fixed points; the Knaster-Tarski Theorem

Proved in the lattice of subsets of D, namely Pow(D), with Inter as glb
*)

open Fixedpt;

(*** Monotone operators ***)

val prems = goalw Fixedpt.thy [bnd_mono_def]
    "[| h(D)<=D;  \
\       !!W X. [| W<=D;  X<=D;  W<=X |] ==> h(W) <= h(X)  \
\    |] ==> bnd_mono(D,h)";  
by (REPEAT (ares_tac (prems@[conjI,allI,impI]) 1
     ORELSE etac subset_trans 1));
qed "bnd_monoI";

val [major] = goalw Fixedpt.thy [bnd_mono_def] "bnd_mono(D,h) ==> h(D) <= D";
by (rtac (major RS conjunct1) 1);
qed "bnd_monoD1";

val major::prems = goalw Fixedpt.thy [bnd_mono_def]
    "[| bnd_mono(D,h);  W<=X;  X<=D |] ==> h(W) <= h(X)";
by (rtac (major RS conjunct2 RS spec RS spec RS mp RS mp) 1);
by (REPEAT (resolve_tac prems 1));
qed "bnd_monoD2";

val [major,minor] = goal Fixedpt.thy
    "[| bnd_mono(D,h);  X<=D |] ==> h(X) <= D";
by (rtac (major RS bnd_monoD2 RS subset_trans) 1);
by (rtac (major RS bnd_monoD1) 3);
by (rtac minor 1);
by (rtac subset_refl 1);
qed "bnd_mono_subset";

goal Fixedpt.thy "!!A B. [| bnd_mono(D,h);  A <= D;  B <= D |] ==> \
\                         h(A) Un h(B) <= h(A Un B)";
by (REPEAT (ares_tac [Un_upper1, Un_upper2, Un_least] 1
     ORELSE etac bnd_monoD2 1));
qed "bnd_mono_Un";

(*Useful??*)
goal Fixedpt.thy "!!A B. [| bnd_mono(D,h);  A <= D;  B <= D |] ==> \
\                        h(A Int B) <= h(A) Int h(B)";
by (REPEAT (ares_tac [Int_lower1, Int_lower2, Int_greatest] 1
     ORELSE etac bnd_monoD2 1));
qed "bnd_mono_Int";

(**** Proof of Knaster-Tarski Theorem for the lfp ****)

(*lfp is contained in each pre-fixedpoint*)
goalw Fixedpt.thy [lfp_def]
    "!!A. [| h(A) <= A;  A<=D |] ==> lfp(D,h) <= A";
by (Blast_tac 1);
(*or  by (rtac (PowI RS CollectI RS Inter_lower) 1); *)
qed "lfp_lowerbound";

(*Unfolding the defn of Inter dispenses with the premise bnd_mono(D,h)!*)
goalw Fixedpt.thy [lfp_def,Inter_def] "lfp(D,h) <= D";
by (Blast_tac 1);
qed "lfp_subset";

(*Used in datatype package*)
val [rew] = goal Fixedpt.thy "A==lfp(D,h) ==> A <= D";
by (rewtac rew);
by (rtac lfp_subset 1);
qed "def_lfp_subset";

val prems = goalw Fixedpt.thy [lfp_def]
    "[| h(D) <= D;  !!X. [| h(X) <= X;  X<=D |] ==> A<=X |] ==> \
\    A <= lfp(D,h)";
by (rtac (Pow_top RS CollectI RS Inter_greatest) 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [CollectE,PowD] 1));
qed "lfp_greatest";

val hmono::prems = goal Fixedpt.thy
    "[| bnd_mono(D,h);  h(A)<=A;  A<=D |] ==> h(lfp(D,h)) <= A";
by (rtac (hmono RS bnd_monoD2 RS subset_trans) 1);
by (rtac lfp_lowerbound 1);
by (REPEAT (resolve_tac prems 1));
qed "lfp_lemma1";

val [hmono] = goal Fixedpt.thy
    "bnd_mono(D,h) ==> h(lfp(D,h)) <= lfp(D,h)";
by (rtac (bnd_monoD1 RS lfp_greatest) 1);
by (rtac lfp_lemma1 2);
by (REPEAT (ares_tac [hmono] 1));
qed "lfp_lemma2";

val [hmono] = goal Fixedpt.thy
    "bnd_mono(D,h) ==> lfp(D,h) <= h(lfp(D,h))";
by (rtac lfp_lowerbound 1);
by (rtac (hmono RS bnd_monoD2) 1);
by (rtac (hmono RS lfp_lemma2) 1);
by (rtac (hmono RS bnd_mono_subset) 2);
by (REPEAT (rtac lfp_subset 1));
qed "lfp_lemma3";

val prems = goal Fixedpt.thy
    "bnd_mono(D,h) ==> lfp(D,h) = h(lfp(D,h))";
by (REPEAT (resolve_tac (prems@[equalityI,lfp_lemma2,lfp_lemma3]) 1));
qed "lfp_Tarski";

(*Definition form, to control unfolding*)
val [rew,mono] = goal Fixedpt.thy
    "[| A==lfp(D,h);  bnd_mono(D,h) |] ==> A = h(A)";
by (rewtac rew);
by (rtac (mono RS lfp_Tarski) 1);
qed "def_lfp_Tarski";

(*** General induction rule for least fixedpoints ***)

val [hmono,indstep] = goal Fixedpt.thy
    "[| bnd_mono(D,h);  !!x. x : h(Collect(lfp(D,h),P)) ==> P(x) \
\    |] ==> h(Collect(lfp(D,h),P)) <= Collect(lfp(D,h),P)";
by (rtac subsetI 1);
by (rtac CollectI 1);
by (etac indstep 2);
by (rtac (hmono RS lfp_lemma2 RS subsetD) 1);
by (rtac (hmono RS bnd_monoD2 RS subsetD) 1);
by (REPEAT (ares_tac [Collect_subset, lfp_subset] 1));
qed "Collect_is_pre_fixedpt";

(*This rule yields an induction hypothesis in which the components of a
  data structure may be assumed to be elements of lfp(D,h)*)
val prems = goal Fixedpt.thy
    "[| bnd_mono(D,h);  a : lfp(D,h);                   \
\       !!x. x : h(Collect(lfp(D,h),P)) ==> P(x)        \
\    |] ==> P(a)";
by (rtac (Collect_is_pre_fixedpt RS lfp_lowerbound RS subsetD RS CollectD2) 1);
by (rtac (lfp_subset RS (Collect_subset RS subset_trans)) 3);
by (REPEAT (ares_tac prems 1));
qed "induct";

(*Definition form, to control unfolding*)
val rew::prems = goal Fixedpt.thy
    "[| A == lfp(D,h);  bnd_mono(D,h);  a:A;   \
\       !!x. x : h(Collect(A,P)) ==> P(x) \
\    |] ==> P(a)";
by (rtac induct 1);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems) 1));
qed "def_induct";

(*This version is useful when "A" is not a subset of D;
  second premise could simply be h(D Int A) <= D or !!X. X<=D ==> h(X)<=D *)
val [hsub,hmono] = goal Fixedpt.thy
    "[| h(D Int A) <= A;  bnd_mono(D,h) |] ==> lfp(D,h) <= A";
by (rtac (lfp_lowerbound RS subset_trans) 1);
by (rtac (hmono RS bnd_mono_subset RS Int_greatest) 1);
by (REPEAT (resolve_tac [hsub,Int_lower1,Int_lower2] 1));
qed "lfp_Int_lowerbound";

(*Monotonicity of lfp, where h precedes i under a domain-like partial order
  monotonicity of h is not strictly necessary; h must be bounded by D*)
val [hmono,imono,subhi] = goal Fixedpt.thy
    "[| bnd_mono(D,h);  bnd_mono(E,i);          \
\       !!X. X<=D ==> h(X) <= i(X)  |] ==> lfp(D,h) <= lfp(E,i)";
by (rtac (bnd_monoD1 RS lfp_greatest) 1);
by (rtac imono 1);
by (rtac (hmono RSN (2, lfp_Int_lowerbound)) 1);
by (rtac (Int_lower1 RS subhi RS subset_trans) 1);
by (rtac (imono RS bnd_monoD2 RS subset_trans) 1);
by (REPEAT (ares_tac [Int_lower2] 1));
qed "lfp_mono";

(*This (unused) version illustrates that monotonicity is not really needed,
  but both lfp's must be over the SAME set D;  Inter is anti-monotonic!*)
val [isubD,subhi] = goal Fixedpt.thy
    "[| i(D) <= D;  !!X. X<=D ==> h(X) <= i(X)  |] ==> lfp(D,h) <= lfp(D,i)";
by (rtac lfp_greatest 1);
by (rtac isubD 1);
by (rtac lfp_lowerbound 1);
by (etac (subhi RS subset_trans) 1);
by (REPEAT (assume_tac 1));
qed "lfp_mono2";


(**** Proof of Knaster-Tarski Theorem for the gfp ****)

(*gfp contains each post-fixedpoint that is contained in D*)
val prems = goalw Fixedpt.thy [gfp_def]
    "[| A <= h(A);  A<=D |] ==> A <= gfp(D,h)";
by (rtac (PowI RS CollectI RS Union_upper) 1);
by (REPEAT (resolve_tac prems 1));
qed "gfp_upperbound";

goalw Fixedpt.thy [gfp_def] "gfp(D,h) <= D";
by (Blast_tac 1);
qed "gfp_subset";

(*Used in datatype package*)
val [rew] = goal Fixedpt.thy "A==gfp(D,h) ==> A <= D";
by (rewtac rew);
by (rtac gfp_subset 1);
qed "def_gfp_subset";

val hmono::prems = goalw Fixedpt.thy [gfp_def]
    "[| bnd_mono(D,h);  !!X. [| X <= h(X);  X<=D |] ==> X<=A |] ==> \
\    gfp(D,h) <= A";
by (fast_tac (subset_cs addIs ((hmono RS bnd_monoD1)::prems)) 1);
qed "gfp_least";

val hmono::prems = goal Fixedpt.thy
    "[| bnd_mono(D,h);  A<=h(A);  A<=D |] ==> A <= h(gfp(D,h))";
by (rtac (hmono RS bnd_monoD2 RSN (2,subset_trans)) 1);
by (rtac gfp_subset 3);
by (rtac gfp_upperbound 2);
by (REPEAT (resolve_tac prems 1));
qed "gfp_lemma1";

val [hmono] = goal Fixedpt.thy
    "bnd_mono(D,h) ==> gfp(D,h) <= h(gfp(D,h))";
by (rtac gfp_least 1);
by (rtac gfp_lemma1 2);
by (REPEAT (ares_tac [hmono] 1));
qed "gfp_lemma2";

val [hmono] = goal Fixedpt.thy
    "bnd_mono(D,h) ==> h(gfp(D,h)) <= gfp(D,h)";
by (rtac gfp_upperbound 1);
by (rtac (hmono RS bnd_monoD2) 1);
by (rtac (hmono RS gfp_lemma2) 1);
by (REPEAT (rtac ([hmono, gfp_subset] MRS bnd_mono_subset) 1));
qed "gfp_lemma3";

val prems = goal Fixedpt.thy
    "bnd_mono(D,h) ==> gfp(D,h) = h(gfp(D,h))";
by (REPEAT (resolve_tac (prems@[equalityI,gfp_lemma2,gfp_lemma3]) 1));
qed "gfp_Tarski";

(*Definition form, to control unfolding*)
val [rew,mono] = goal Fixedpt.thy
    "[| A==gfp(D,h);  bnd_mono(D,h) |] ==> A = h(A)";
by (rewtac rew);
by (rtac (mono RS gfp_Tarski) 1);
qed "def_gfp_Tarski";


(*** Coinduction rules for greatest fixed points ***)

(*weak version*)
goal Fixedpt.thy "!!X h. [| a: X;  X <= h(X);  X <= D |] ==> a : gfp(D,h)";
by (REPEAT (ares_tac [gfp_upperbound RS subsetD] 1));
qed "weak_coinduct";

val [subs_h,subs_D,mono] = goal Fixedpt.thy
    "[| X <= h(X Un gfp(D,h));  X <= D;  bnd_mono(D,h) |] ==>  \
\    X Un gfp(D,h) <= h(X Un gfp(D,h))";
by (rtac (subs_h RS Un_least) 1);
by (rtac (mono RS gfp_lemma2 RS subset_trans) 1);
by (rtac (Un_upper2 RS subset_trans) 1);
by (rtac ([mono, subs_D, gfp_subset] MRS bnd_mono_Un) 1);
qed "coinduct_lemma";

(*strong version*)
goal Fixedpt.thy
    "!!X D. [| bnd_mono(D,h);  a: X;  X <= h(X Un gfp(D,h));  X <= D |] ==> \
\           a : gfp(D,h)";
by (rtac weak_coinduct 1);
by (etac coinduct_lemma 2);
by (REPEAT (ares_tac [gfp_subset, UnI1, Un_least] 1));
qed "coinduct";

(*Definition form, to control unfolding*)
val rew::prems = goal Fixedpt.thy
    "[| A == gfp(D,h);  bnd_mono(D,h);  a: X;  X <= h(X Un A);  X <= D |] ==> \
\    a : A";
by (rewtac rew);
by (rtac coinduct 1);
by (REPEAT (ares_tac (map (rewrite_rule [rew]) prems) 1));
qed "def_coinduct";

(*Lemma used immediately below!*)
val [subsA,XimpP] = goal ZF.thy
    "[| X <= A;  !!z. z:X ==> P(z) |] ==> X <= Collect(A,P)";
by (rtac (subsA RS subsetD RS CollectI RS subsetI) 1);
by (assume_tac 1);
by (etac XimpP 1);
qed "subset_Collect";

(*The version used in the induction/coinduction package*)
val prems = goal Fixedpt.thy
    "[| A == gfp(D, %w. Collect(D,P(w)));  bnd_mono(D, %w. Collect(D,P(w)));  \
\       a: X;  X <= D;  !!z. z: X ==> P(X Un A, z) |] ==> \
\    a : A";
by (rtac def_coinduct 1);
by (REPEAT (ares_tac (subset_Collect::prems) 1));
qed "def_Collect_coinduct";

(*Monotonicity of gfp!*)
val [hmono,subde,subhi] = goal Fixedpt.thy
    "[| bnd_mono(D,h);  D <= E;                 \
\       !!X. X<=D ==> h(X) <= i(X)  |] ==> gfp(D,h) <= gfp(E,i)";
by (rtac gfp_upperbound 1);
by (rtac (hmono RS gfp_lemma2 RS subset_trans) 1);
by (rtac (gfp_subset RS subhi) 1);
by (rtac ([gfp_subset, subde] MRS subset_trans) 1);
qed "gfp_mono";

