(*  Title:      ZF/QUniv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A small universe for lazy recursive types
*)

(** Properties involving Transset and Sum **)

theory QUniv = Univ + QPair + mono + equalities:

(*Disjoint sums as a datatype*)
rep_datatype 
  elimination	sumE
  induction	TrueI
  case_eqns	case_Inl case_Inr

(*Variant disjoint sums as a datatype*)
rep_datatype 
  elimination	qsumE
  induction	TrueI
  case_eqns	qcase_QInl qcase_QInr

constdefs
  quniv :: "i => i"
   "quniv(A) == Pow(univ(eclose(A)))"


lemma Transset_includes_summands:
     "[| Transset(C); A+B <= C |] ==> A <= C & B <= C"
apply (simp add: sum_def Un_subset_iff) 
apply (blast dest: Transset_includes_range)
done

lemma Transset_sum_Int_subset:
     "Transset(C) ==> (A+B) Int C <= (A Int C) + (B Int C)"
apply (simp add: sum_def Int_Un_distrib2) 
apply (blast dest: Transset_Pair_D)
done

(** Introduction and elimination rules avoid tiresome folding/unfolding **)

lemma qunivI: "X <= univ(eclose(A)) ==> X : quniv(A)"
by (simp add: quniv_def)

lemma qunivD: "X : quniv(A) ==> X <= univ(eclose(A))"
by (simp add: quniv_def)

lemma quniv_mono: "A<=B ==> quniv(A) <= quniv(B)"
apply (unfold quniv_def)
apply (erule eclose_mono [THEN univ_mono, THEN Pow_mono])
done

(*** Closure properties ***)

lemma univ_eclose_subset_quniv: "univ(eclose(A)) <= quniv(A)"
apply (simp add: quniv_def Transset_iff_Pow [symmetric]) 
apply (rule Transset_eclose [THEN Transset_univ])
done

(*Key property for proving A_subset_quniv; requires eclose in def of quniv*)
lemma univ_subset_quniv: "univ(A) <= quniv(A)"
apply (rule arg_subset_eclose [THEN univ_mono, THEN subset_trans])
apply (rule univ_eclose_subset_quniv)
done

lemmas univ_into_quniv = univ_subset_quniv [THEN subsetD, standard]

lemma Pow_univ_subset_quniv: "Pow(univ(A)) <= quniv(A)"
apply (unfold quniv_def)
apply (rule arg_subset_eclose [THEN univ_mono, THEN Pow_mono])
done

lemmas univ_subset_into_quniv =
    PowI [THEN Pow_univ_subset_quniv [THEN subsetD], standard]

lemmas zero_in_quniv = zero_in_univ [THEN univ_into_quniv, standard]
lemmas one_in_quniv = one_in_univ [THEN univ_into_quniv, standard]
lemmas two_in_quniv = two_in_univ [THEN univ_into_quniv, standard]

lemmas A_subset_quniv =  subset_trans [OF A_subset_univ univ_subset_quniv]

lemmas A_into_quniv = A_subset_quniv [THEN subsetD, standard]

(*** univ(A) closure for Quine-inspired pairs and injections ***)

(*Quine ordered pairs*)
lemma QPair_subset_univ: 
    "[| a <= univ(A);  b <= univ(A) |] ==> <a;b> <= univ(A)"
by (simp add: QPair_def sum_subset_univ)

(** Quine disjoint sum **)

lemma QInl_subset_univ: "a <= univ(A) ==> QInl(a) <= univ(A)"
apply (unfold QInl_def)
apply (erule empty_subsetI [THEN QPair_subset_univ])
done

lemmas naturals_subset_nat = 
    Ord_nat [THEN Ord_is_Transset, unfolded Transset_def, THEN bspec, standard]

lemmas naturals_subset_univ =
    subset_trans [OF naturals_subset_nat nat_subset_univ]

lemma QInr_subset_univ: "a <= univ(A) ==> QInr(a) <= univ(A)"
apply (unfold QInr_def)
apply (erule nat_1I [THEN naturals_subset_univ, THEN QPair_subset_univ])
done

(*** Closure for Quine-inspired products and sums ***)

(*Quine ordered pairs*)
lemma QPair_in_quniv: 
    "[| a: quniv(A);  b: quniv(A) |] ==> <a;b> : quniv(A)"
by (simp add: quniv_def QPair_def sum_subset_univ) 

lemma QSigma_quniv: "quniv(A) <*> quniv(A) <= quniv(A)" 
by (blast intro: QPair_in_quniv)

lemmas QSigma_subset_quniv =  subset_trans [OF QSigma_mono QSigma_quniv]

(*The opposite inclusion*)
lemma quniv_QPair_D: 
    "<a;b> : quniv(A) ==> a: quniv(A) & b: quniv(A)"
apply (unfold quniv_def QPair_def)
apply (rule Transset_includes_summands [THEN conjE]) 
apply (rule Transset_eclose [THEN Transset_univ])
apply (erule PowD, blast) 
done

lemmas quniv_QPair_E = quniv_QPair_D [THEN conjE, standard]

lemma quniv_QPair_iff: "<a;b> : quniv(A) <-> a: quniv(A) & b: quniv(A)"
by (blast intro: QPair_in_quniv dest: quniv_QPair_D)


(** Quine disjoint sum **)

lemma QInl_in_quniv: "a: quniv(A) ==> QInl(a) : quniv(A)"
by (simp add: QInl_def zero_in_quniv QPair_in_quniv)

lemma QInr_in_quniv: "b: quniv(A) ==> QInr(b) : quniv(A)"
by (simp add: QInr_def one_in_quniv QPair_in_quniv)

lemma qsum_quniv: "quniv(C) <+> quniv(C) <= quniv(C)"
by (blast intro: QInl_in_quniv QInr_in_quniv)

lemmas qsum_subset_quniv = subset_trans [OF qsum_mono qsum_quniv]


(*** The natural numbers ***)

lemmas nat_subset_quniv =  subset_trans [OF nat_subset_univ univ_subset_quniv]

(* n:nat ==> n:quniv(A) *)
lemmas nat_into_quniv = nat_subset_quniv [THEN subsetD, standard]

lemmas bool_subset_quniv = subset_trans [OF bool_subset_univ univ_subset_quniv]

lemmas bool_into_quniv = bool_subset_quniv [THEN subsetD, standard]


(*** Intersecting <a;b> with Vfrom... ***)

lemma QPair_Int_Vfrom_succ_subset: 
 "Transset(X) ==>           
       <a;b> Int Vfrom(X, succ(i))  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>"
by (simp add: QPair_def sum_def Int_Un_distrib2 Un_mono
              product_Int_Vfrom_subset [THEN subset_trans]
              Sigma_mono [OF Int_lower1 subset_refl])

(**** "Take-lemma" rules for proving a=b by coinduction and c: quniv(A) ****)

(*Rule for level i -- preserving the level, not decreasing it*)

lemma QPair_Int_Vfrom_subset: 
 "Transset(X) ==>           
       <a;b> Int Vfrom(X,i)  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>"
apply (unfold QPair_def)
apply (erule Transset_Vfrom [THEN Transset_sum_Int_subset])
done

(*[| a Int Vset(i) <= c; b Int Vset(i) <= d |] ==> <a;b> Int Vset(i) <= <c;d>*)
lemmas QPair_Int_Vset_subset_trans =
     subset_trans [OF Transset_0 [THEN QPair_Int_Vfrom_subset] QPair_mono]

lemma QPair_Int_Vset_subset_UN:
     "Ord(i) ==> <a;b> Int Vset(i) <= (UN j:i. <a Int Vset(j); b Int Vset(j)>)"
apply (erule Ord_cases)
(*0 case*)
apply (simp add: Vfrom_0)
(*succ(j) case*)
apply (erule ssubst) 
apply (rule Transset_0 [THEN QPair_Int_Vfrom_succ_subset, THEN subset_trans])
apply (rule succI1 [THEN UN_upper])
(*Limit(i) case*)
apply (simp del: UN_simps 
        add: Limit_Vfrom_eq Int_UN_distrib UN_mono QPair_Int_Vset_subset_trans)
done

ML
{*
val Transset_includes_summands = thm "Transset_includes_summands";
val Transset_sum_Int_subset = thm "Transset_sum_Int_subset";
val qunivI = thm "qunivI";
val qunivD = thm "qunivD";
val quniv_mono = thm "quniv_mono";
val univ_eclose_subset_quniv = thm "univ_eclose_subset_quniv";
val univ_subset_quniv = thm "univ_subset_quniv";
val univ_into_quniv = thm "univ_into_quniv";
val Pow_univ_subset_quniv = thm "Pow_univ_subset_quniv";
val univ_subset_into_quniv = thm "univ_subset_into_quniv";
val zero_in_quniv = thm "zero_in_quniv";
val one_in_quniv = thm "one_in_quniv";
val two_in_quniv = thm "two_in_quniv";
val A_subset_quniv = thm "A_subset_quniv";
val A_into_quniv = thm "A_into_quniv";
val QPair_subset_univ = thm "QPair_subset_univ";
val QInl_subset_univ = thm "QInl_subset_univ";
val naturals_subset_nat = thm "naturals_subset_nat";
val naturals_subset_univ = thm "naturals_subset_univ";
val QInr_subset_univ = thm "QInr_subset_univ";
val QPair_in_quniv = thm "QPair_in_quniv";
val QSigma_quniv = thm "QSigma_quniv";
val QSigma_subset_quniv = thm "QSigma_subset_quniv";
val quniv_QPair_D = thm "quniv_QPair_D";
val quniv_QPair_E = thm "quniv_QPair_E";
val quniv_QPair_iff = thm "quniv_QPair_iff";
val QInl_in_quniv = thm "QInl_in_quniv";
val QInr_in_quniv = thm "QInr_in_quniv";
val qsum_quniv = thm "qsum_quniv";
val qsum_subset_quniv = thm "qsum_subset_quniv";
val nat_subset_quniv = thm "nat_subset_quniv";
val nat_into_quniv = thm "nat_into_quniv";
val bool_subset_quniv = thm "bool_subset_quniv";
val bool_into_quniv = thm "bool_into_quniv";
val QPair_Int_Vfrom_succ_subset = thm "QPair_Int_Vfrom_succ_subset";
val QPair_Int_Vfrom_subset = thm "QPair_Int_Vfrom_subset";
val QPair_Int_Vset_subset_trans = thm "QPair_Int_Vset_subset_trans";
val QPair_Int_Vset_subset_UN = thm "QPair_Int_Vset_subset_UN";
*}

end
