(*  Title:      ZF/QUniv
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A small universe for lazy recursive types
*)

(** Properties involving Transset and Sum **)

Goalw [sum_def] "[| Transset(C); A+B <= C |] ==> A <= C & B <= C";
by (dtac (Un_subset_iff RS iffD1) 1);
by (blast_tac (claset() addDs [Transset_includes_range]) 1);
qed "Transset_includes_summands";

Goalw [sum_def] "Transset(C) ==> (A+B) Int C <= (A Int C) + (B Int C)";
by (stac Int_Un_distrib 1);
by (blast_tac (claset() addDs [Transset_Pair_D]) 1);
qed "Transset_sum_Int_subset";

(** Introduction and elimination rules avoid tiresome folding/unfolding **)

Goalw [quniv_def]
    "X <= univ(eclose(A)) ==> X : quniv(A)";
by (etac PowI 1);
qed "qunivI";

Goalw [quniv_def]
    "X : quniv(A) ==> X <= univ(eclose(A))";
by (etac PowD 1);
qed "qunivD";

Goalw [quniv_def] "A<=B ==> quniv(A) <= quniv(B)";
by (etac (eclose_mono RS univ_mono RS Pow_mono) 1);
qed "quniv_mono";

(*** Closure properties ***)

Goalw [quniv_def] "univ(eclose(A)) <= quniv(A)";
by (rtac (Transset_iff_Pow RS iffD1) 1);
by (rtac (Transset_eclose RS Transset_univ) 1);
qed "univ_eclose_subset_quniv";

(*Key property for proving A_subset_quniv; requires eclose in def of quniv*)
Goal "univ(A) <= quniv(A)";
by (rtac (arg_subset_eclose RS univ_mono RS subset_trans) 1);
by (rtac univ_eclose_subset_quniv 1);
qed "univ_subset_quniv";

bind_thm ("univ_into_quniv", univ_subset_quniv RS subsetD);

Goalw [quniv_def] "Pow(univ(A)) <= quniv(A)";
by (rtac (arg_subset_eclose RS univ_mono RS Pow_mono) 1);
qed "Pow_univ_subset_quniv";

bind_thm ("univ_subset_into_quniv", 
          PowI RS (Pow_univ_subset_quniv RS subsetD));

bind_thm ("zero_in_quniv", zero_in_univ RS univ_into_quniv);
bind_thm ("one_in_quniv", one_in_univ RS univ_into_quniv);
bind_thm ("two_in_quniv", two_in_univ RS univ_into_quniv);

bind_thm ("A_subset_quniv",
          [A_subset_univ, univ_subset_quniv] MRS subset_trans);

val A_into_quniv = A_subset_quniv RS subsetD;

(*** univ(A) closure for Quine-inspired pairs and injections ***)

(*Quine ordered pairs*)
Goalw [QPair_def]
    "[| a <= univ(A);  b <= univ(A) |] ==> <a;b> <= univ(A)";
by (REPEAT (ares_tac [sum_subset_univ] 1));
qed "QPair_subset_univ";

(** Quine disjoint sum **)

Goalw [QInl_def] "a <= univ(A) ==> QInl(a) <= univ(A)";
by (etac (empty_subsetI RS QPair_subset_univ) 1);
qed "QInl_subset_univ";

val naturals_subset_nat =
    rewrite_rule [Transset_def] (Ord_nat RS Ord_is_Transset)
    RS bspec;

val naturals_subset_univ = 
    [naturals_subset_nat, nat_subset_univ] MRS subset_trans;

Goalw [QInr_def] "a <= univ(A) ==> QInr(a) <= univ(A)";
by (etac (nat_1I RS naturals_subset_univ RS QPair_subset_univ) 1);
qed "QInr_subset_univ";

(*** Closure for Quine-inspired products and sums ***)

(*Quine ordered pairs*)
Goalw [quniv_def,QPair_def]
    "[| a: quniv(A);  b: quniv(A) |] ==> <a;b> : quniv(A)";
by (REPEAT (dtac PowD 1));
by (REPEAT (ares_tac [PowI, sum_subset_univ] 1));
qed "QPair_in_quniv";

Goal "quniv(A) <*> quniv(A) <= quniv(A)";
by (REPEAT (ares_tac [subsetI, QPair_in_quniv] 1
     ORELSE eresolve_tac [QSigmaE, ssubst] 1));
qed "QSigma_quniv";

bind_thm ("QSigma_subset_quniv",
          [QSigma_mono, QSigma_quniv] MRS subset_trans);

(*The opposite inclusion*)
Goalw [quniv_def,QPair_def]
    "<a;b> : quniv(A) ==> a: quniv(A) & b: quniv(A)";
by (etac ([Transset_eclose RS Transset_univ, PowD] MRS 
          Transset_includes_summands RS conjE) 1);
by (REPEAT (ares_tac [conjI,PowI] 1));
qed "quniv_QPair_D";

bind_thm ("quniv_QPair_E", quniv_QPair_D RS conjE);

Goal "<a;b> : quniv(A) <-> a: quniv(A) & b: quniv(A)";
by (REPEAT (ares_tac [iffI, QPair_in_quniv, quniv_QPair_D] 1
     ORELSE etac conjE 1));
qed "quniv_QPair_iff";


(** Quine disjoint sum **)

Goalw [QInl_def] "a: quniv(A) ==> QInl(a) : quniv(A)";
by (REPEAT (ares_tac [zero_in_quniv,QPair_in_quniv] 1));
qed "QInl_in_quniv";

Goalw [QInr_def] "b: quniv(A) ==> QInr(b) : quniv(A)";
by (REPEAT (ares_tac [one_in_quniv, QPair_in_quniv] 1));
qed "QInr_in_quniv";

Goal "quniv(C) <+> quniv(C) <= quniv(C)";
by (REPEAT (ares_tac [subsetI, QInl_in_quniv, QInr_in_quniv] 1
     ORELSE eresolve_tac [qsumE, ssubst] 1));
qed "qsum_quniv";

bind_thm ("qsum_subset_quniv", [qsum_mono, qsum_quniv] MRS subset_trans);


(*** The natural numbers ***)

bind_thm ("nat_subset_quniv",
          [nat_subset_univ, univ_subset_quniv] MRS subset_trans);

(* n:nat ==> n:quniv(A) *)
bind_thm ("nat_into_quniv", (nat_subset_quniv RS subsetD));

bind_thm ("bool_subset_quniv",
          [bool_subset_univ, univ_subset_quniv] MRS subset_trans);

bind_thm ("bool_into_quniv", bool_subset_quniv RS subsetD);


(*** Intersecting <a;b> with Vfrom... ***)

Goalw [QPair_def,sum_def]
 "Transset(X) ==>          \
\      <a;b> Int Vfrom(X, succ(i))  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>";
by (stac Int_Un_distrib 1);
by (rtac Un_mono 1);
by (REPEAT (ares_tac [product_Int_Vfrom_subset RS subset_trans,
                      [Int_lower1, subset_refl] MRS Sigma_mono] 1));
qed "QPair_Int_Vfrom_succ_subset";

(**** "Take-lemma" rules for proving a=b by coinduction and c: quniv(A) ****)

(*Rule for level i -- preserving the level, not decreasing it*)

Goalw [QPair_def]
 "Transset(X) ==>          \
\      <a;b> Int Vfrom(X,i)  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>";
by (etac (Transset_Vfrom RS Transset_sum_Int_subset) 1);
qed "QPair_Int_Vfrom_subset";

(*[| a Int Vset(i) <= c; b Int Vset(i) <= d |] ==> <a;b> Int Vset(i) <= <c;d>*)
bind_thm ("QPair_Int_Vset_subset_trans", 
          [Transset_0 RS QPair_Int_Vfrom_subset, QPair_mono] MRS subset_trans);

Goal "Ord(i) ==> <a;b> Int Vset(i) <= (UN j:i. <a Int Vset(j); b Int Vset(j)>)";
by (etac Ord_cases 1 THEN REPEAT_FIRST hyp_subst_tac);
(*0 case*)
by (stac Vfrom_0 1);
by (Fast_tac 1);
(*succ(j) case*)
by (rtac (Transset_0 RS QPair_Int_Vfrom_succ_subset RS subset_trans) 1);
by (rtac (succI1 RS UN_upper) 1);
(*Limit(i) case*)
by (asm_simp_tac
    (simpset() addsimps [Limit_Vfrom_eq, Int_UN_distrib, 
			 UN_mono, QPair_Int_Vset_subset_trans]) 1);
qed "QPair_Int_Vset_subset_UN";
