(*  Title: 	ZF/quniv
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For quniv.thy.  A small universe for lazy recursive types
*)

open QUniv;

(** Introduction and elimination rules avoid tiresome folding/unfolding **)

goalw QUniv.thy [quniv_def]
    "!!X A. X <= univ(eclose(A)) ==> X : quniv(A)";
by (etac PowI 1);
val qunivI = result();

goalw QUniv.thy [quniv_def]
    "!!X A. X : quniv(A) ==> X <= univ(eclose(A))";
by (etac PowD 1);
val qunivD = result();

goalw QUniv.thy [quniv_def] "!!A B. A<=B ==> quniv(A) <= quniv(B)";
by (etac (eclose_mono RS univ_mono RS Pow_mono) 1);
val quniv_mono = result();

(*** Closure properties ***)

goalw QUniv.thy [quniv_def] "univ(eclose(A)) <= quniv(A)";
by (rtac (Transset_iff_Pow RS iffD1) 1);
by (rtac (Transset_eclose RS Transset_univ) 1);
val univ_eclose_subset_quniv = result();

goal QUniv.thy "univ(A) <= quniv(A)";
by (rtac (arg_subset_eclose RS univ_mono RS subset_trans) 1);
by (rtac univ_eclose_subset_quniv 1);
val univ_subset_quniv = result();

val univ_into_quniv = standard (univ_subset_quniv RS subsetD);

goalw QUniv.thy [quniv_def] "Pow(univ(A)) <= quniv(A)";
by (rtac (arg_subset_eclose RS univ_mono RS Pow_mono) 1);
val Pow_univ_subset_quniv = result();

val univ_subset_into_quniv = standard
	(PowI RS (Pow_univ_subset_quniv RS subsetD));

val zero_in_quniv = standard (zero_in_univ RS univ_into_quniv);
val one_in_quniv = standard (one_in_univ RS univ_into_quniv);
val two_in_quniv = standard (two_in_univ RS univ_into_quniv);

val A_subset_quniv = standard
	([A_subset_univ, univ_subset_quniv] MRS subset_trans);

val A_into_quniv = A_subset_quniv RS subsetD;

(*** univ(A) closure for Quine-inspired pairs and injections ***)

(*Quine ordered pairs*)
goalw QUniv.thy [QPair_def]
    "!!A a. [| a <= univ(A);  b <= univ(A) |] ==> <a;b> <= univ(A)";
by (REPEAT (ares_tac [sum_subset_univ] 1));
val QPair_subset_univ = result();

(** Quine disjoint sum **)

goalw QUniv.thy [QInl_def] "!!A a. a <= univ(A) ==> QInl(a) <= univ(A)";
by (etac (empty_subsetI RS QPair_subset_univ) 1);
val QInl_subset_univ = result();

val naturals_subset_nat =
    rewrite_rule [Transset_def] (Ord_nat RS Ord_is_Transset)
    RS bspec;

val naturals_subset_univ = 
    [naturals_subset_nat, nat_subset_univ] MRS subset_trans;

goalw QUniv.thy [QInr_def] "!!A a. a <= univ(A) ==> QInr(a) <= univ(A)";
by (etac (nat_1I RS naturals_subset_univ RS QPair_subset_univ) 1);
val QInr_subset_univ = result();

(*** Closure for Quine-inspired products and sums ***)

(*Quine ordered pairs*)
goalw QUniv.thy [quniv_def,QPair_def]
    "!!A a. [| a: quniv(A);  b: quniv(A) |] ==> <a;b> : quniv(A)";
by (REPEAT (dtac PowD 1));
by (REPEAT (ares_tac [PowI, sum_subset_univ] 1));
val QPair_in_quniv = result();

goal QUniv.thy "quniv(A) <*> quniv(A) <= quniv(A)";
by (REPEAT (ares_tac [subsetI, QPair_in_quniv] 1
     ORELSE eresolve_tac [QSigmaE, ssubst] 1));
val QSigma_quniv = result();

val QSigma_subset_quniv = standard
    (QSigma_mono RS (QSigma_quniv RSN (2,subset_trans)));

(*The opposite inclusion*)
goalw QUniv.thy [quniv_def,QPair_def]
    "!!A a b. <a;b> : quniv(A) ==> a: quniv(A) & b: quniv(A)";
be ([Transset_eclose RS Transset_univ, PowD] MRS 
    Transset_includes_summands RS conjE) 1;
by (REPEAT (ares_tac [conjI,PowI] 1));
val quniv_QPair_D = result();

val quniv_QPair_E = standard (quniv_QPair_D RS conjE);

goal QUniv.thy "<a;b> : quniv(A) <-> a: quniv(A) & b: quniv(A)";
by (REPEAT (ares_tac [iffI, QPair_in_quniv, quniv_QPair_D] 1
     ORELSE etac conjE 1));
val quniv_QPair_iff = result();


(** Quine disjoint sum **)

goalw QUniv.thy [QInl_def] "!!A a. a: quniv(A) ==> QInl(a) : quniv(A)";
by (REPEAT (ares_tac [zero_in_quniv,QPair_in_quniv] 1));
val QInl_in_quniv = result();

goalw QUniv.thy [QInr_def] "!!A b. b: quniv(A) ==> QInr(b) : quniv(A)";
by (REPEAT (ares_tac [one_in_quniv, QPair_in_quniv] 1));
val QInr_in_quniv = result();

goal QUniv.thy "quniv(C) <+> quniv(C) <= quniv(C)";
by (REPEAT (ares_tac [subsetI, QInl_in_quniv, QInr_in_quniv] 1
     ORELSE eresolve_tac [qsumE, ssubst] 1));
val qsum_quniv = result();

val qsum_subset_quniv = standard
    (qsum_mono RS (qsum_quniv RSN (2,subset_trans)));

(*** The natural numbers ***)

val nat_subset_quniv = standard
	([nat_subset_univ, univ_subset_quniv] MRS subset_trans);

(* n:nat ==> n:quniv(A) *)
val nat_into_quniv = standard (nat_subset_quniv RS subsetD);

val bool_subset_quniv = standard
	([bool_subset_univ, univ_subset_quniv] MRS subset_trans);

val bool_into_quniv = standard (bool_subset_quniv RS subsetD);


(**** Properties of Vfrom analogous to the "take-lemma" ****)

(*** Intersecting a*b with Vfrom... ***)

(*This version says a, b exist one level down, in the smaller set Vfrom(X,i)*)
goal Univ.thy
    "!!X. [| {a,b} : Vfrom(X,succ(i));  Transset(X) |] ==> \
\         a: Vfrom(X,i)  &  b: Vfrom(X,i)";
by (dtac (Transset_Vfrom_succ RS equalityD1 RS subsetD RS PowD) 1);
by (assume_tac 1);
by (fast_tac ZF_cs 1);
val doubleton_in_Vfrom_D = result();

(*This weaker version says a, b exist at the same level*)
val Vfrom_doubleton_D = standard (Transset_Vfrom RS Transset_doubleton_D);

(** Using only the weaker theorem would prove <a,b> : Vfrom(X,i)
      implies a, b : Vfrom(X,i), which is useless for induction.
    Using only the stronger theorem would prove <a,b> : Vfrom(X,succ(succ(i)))
      implies a, b : Vfrom(X,i), leaving the succ(i) case untreated.
    The combination gives a reduction by precisely one level, which is
      most convenient for proofs.
**)

goalw Univ.thy [Pair_def]
    "!!X. [| <a,b> : Vfrom(X,succ(i));  Transset(X) |] ==> \
\         a: Vfrom(X,i)  &  b: Vfrom(X,i)";
by (fast_tac (ZF_cs addSDs [doubleton_in_Vfrom_D, Vfrom_doubleton_D]) 1);
val Pair_in_Vfrom_D = result();

goal Univ.thy
 "!!X. Transset(X) ==> 		\
\      (a*b) Int Vfrom(X, succ(i)) <= (a Int Vfrom(X,i)) * (b Int Vfrom(X,i))";
by (fast_tac (ZF_cs addSDs [Pair_in_Vfrom_D]) 1);
val product_Int_Vfrom_subset = result();

(*** Intersecting <a;b> with Vfrom... ***)

goalw QUniv.thy [QPair_def,sum_def]
 "!!X. Transset(X) ==> 		\
\      <a;b> Int Vfrom(X, succ(i))  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>";
by (rtac (Int_Un_distrib RS ssubst) 1);
by (rtac Un_mono 1);
by (REPEAT (ares_tac [product_Int_Vfrom_subset RS subset_trans,
		      [Int_lower1, subset_refl] MRS Sigma_mono] 1));
val QPair_Int_Vfrom_succ_subset = result();

(** Pairs in quniv -- for handling the base case **)

goal QUniv.thy "!!X. <a,b> : quniv(X) ==> <a,b> : univ(eclose(X))";
by (etac ([qunivD, Transset_eclose] MRS Transset_Pair_subset_univ) 1);
val Pair_in_quniv_D = result();

goal QUniv.thy "a*b Int quniv(A) = a*b Int univ(eclose(A))";
by (rtac equalityI 1);
by (rtac ([subset_refl, univ_eclose_subset_quniv] MRS Int_mono) 2);
by (fast_tac (ZF_cs addSEs [Pair_in_quniv_D]) 1);
val product_Int_quniv_eq = result();

goalw QUniv.thy [QPair_def,sum_def]
    "<a;b> Int quniv(A) = <a;b> Int univ(eclose(A))";
by (simp_tac (ZF_ss addsimps [Int_Un_distrib, product_Int_quniv_eq]) 1);
val QPair_Int_quniv_eq = result();

(**** "Take-lemma" rules for proving c: quniv(A) ****)

goalw QUniv.thy [quniv_def] "Transset(quniv(A))";
by (rtac (Transset_eclose RS Transset_univ RS Transset_Pow) 1);
val Transset_quniv = result();

val [aprem, iprem] = goal QUniv.thy
    "[| a: quniv(quniv(X));  	\
\       !!i. i:nat ==> a Int Vfrom(quniv(X),i) : quniv(A) \
\    |] ==> a : quniv(A)";
by (rtac (univ_Int_Vfrom_subset RS qunivI) 1);
by (rtac (aprem RS qunivD) 1);
by (rtac (Transset_quniv RS Transset_eclose_eq_arg RS ssubst) 1);
by (etac (iprem RS qunivD) 1);
val quniv_Int_Vfrom = result();

(** Rules for level 0 **)

goal QUniv.thy "<a;b> Int quniv(A) : quniv(A)";
by (rtac (QPair_Int_quniv_eq RS ssubst) 1);
by (rtac (Int_lower2 RS qunivI) 1);
val QPair_Int_quniv_in_quniv = result();

(*Unused; kept as an example.  QInr rule is similar*)
goalw QUniv.thy [QInl_def] "QInl(a) Int quniv(A) : quniv(A)";
by (rtac QPair_Int_quniv_in_quniv 1);
val QInl_Int_quniv_in_quniv = result();

goal QUniv.thy "!!a A X. a : quniv(A) ==> a Int X : quniv(A)";
by (etac ([Int_lower1, qunivD] MRS subset_trans RS qunivI) 1);
val Int_quniv_in_quniv = result();

goal QUniv.thy 
 "!!X. a Int X : quniv(A) ==> a Int Vfrom(X, 0) : quniv(A)";
by (etac (Vfrom_0 RS ssubst) 1);
val Int_Vfrom_0_in_quniv = result();

(** Rules for level succ(i), decreasing it to i **)

goal QUniv.thy 
 "!!X. [| a Int Vfrom(X,i) : quniv(A);	\
\         b Int Vfrom(X,i) : quniv(A);	\
\         Transset(X) 			\
\      |] ==> <a;b> Int Vfrom(X, succ(i)) : quniv(A)";
by (rtac (QPair_Int_Vfrom_succ_subset RS subset_trans RS qunivI) 1);
by (rtac (QPair_in_quniv RS qunivD) 2);
by (REPEAT (assume_tac 1));
val QPair_Int_Vfrom_succ_in_quniv = result();

val zero_Int_in_quniv = standard
    ([Int_lower1,empty_subsetI] MRS subset_trans RS qunivI);

val one_Int_in_quniv = standard
    ([Int_lower1, one_in_quniv RS qunivD] MRS subset_trans RS qunivI);

(*Unused; kept as an example.  QInr rule is similar*)
goalw QUniv.thy [QInl_def]
 "!!X. [| a Int Vfrom(X,i) : quniv(A);	Transset(X) 		\
\      |] ==> QInl(a) Int Vfrom(X, succ(i)) : quniv(A)";
by (rtac QPair_Int_Vfrom_succ_in_quniv 1);
by (REPEAT (ares_tac [zero_Int_in_quniv] 1));
val QInl_Int_Vfrom_succ_in_quniv = result();

(** Rules for level i -- preserving the level, not decreasing it **)

goalw QUniv.thy [QPair_def]
 "!!X. Transset(X) ==> 		\
\      <a;b> Int Vfrom(X,i)  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>";
by (etac (Transset_Vfrom RS Transset_sum_Int_subset) 1);
val QPair_Int_Vfrom_subset = result();

goal QUniv.thy 
 "!!X. [| a Int Vfrom(X,i) : quniv(A);	\
\         b Int Vfrom(X,i) : quniv(A);	\
\         Transset(X) 			\
\      |] ==> <a;b> Int Vfrom(X,i) : quniv(A)";
by (rtac (QPair_Int_Vfrom_subset RS subset_trans RS qunivI) 1);
by (rtac (QPair_in_quniv RS qunivD) 2);
by (REPEAT (assume_tac 1));
val QPair_Int_Vfrom_in_quniv = result();


(**** "Take-lemma" rules for proving a=b by coinduction ****)

(** Unfortunately, the technique used above does not apply here, since
    the base case appears impossible to prove: it involves an intersection
    with eclose(X) for arbitrary X.  So a=b is proved by transfinite induction
    over ALL ordinals, using Vset(i) instead of Vfrom(X,i).
**)

(*Rule for level 0*)
goal QUniv.thy "a Int Vset(0) <= b";
by (rtac (Vfrom_0 RS ssubst) 1);
by (fast_tac ZF_cs 1);
val Int_Vset_0_subset = result();

(*Rule for level succ(i), decreasing it to i*)
goal QUniv.thy 
 "!!i. [| a Int Vset(i) <= c;	\
\         b Int Vset(i) <= d	\
\      |] ==> <a;b> Int Vset(succ(i))  <=  <c;d>";
by (rtac ([Transset_0 RS QPair_Int_Vfrom_succ_subset, QPair_mono] 
	  MRS subset_trans) 1);
by (REPEAT (assume_tac 1));
val QPair_Int_Vset_succ_subset_trans = result();

(*Unused; kept as an example.  QInr rule is similar*)
goalw QUniv.thy [QInl_def] 
 "!!i. a Int Vset(i) <= b ==> QInl(a) Int Vset(succ(i)) <= QInl(b)";
by (etac (Int_lower1 RS QPair_Int_Vset_succ_subset_trans) 1);
val QInl_Int_Vset_succ_subset_trans = result();

(*Rule for level i -- preserving the level, not decreasing it*)
goal QUniv.thy 
 "!!i. [| a Int Vset(i) <= c;	\
\         b Int Vset(i) <= d	\
\      |] ==> <a;b> Int Vset(i)  <=  <c;d>";
by (rtac ([Transset_0 RS QPair_Int_Vfrom_subset, QPair_mono] 
	  MRS subset_trans) 1);
by (REPEAT (assume_tac 1));
val QPair_Int_Vset_subset_trans = result();



