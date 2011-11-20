(*  Title:      ZF/QUniv.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header{*A Small Universe for Lazy Recursive Types*}

theory QUniv imports Univ QPair begin

(*Disjoint sums as a datatype*)
rep_datatype 
  elimination   sumE
  induction     TrueI
  case_eqns     case_Inl case_Inr

(*Variant disjoint sums as a datatype*)
rep_datatype 
  elimination   qsumE
  induction     TrueI
  case_eqns     qcase_QInl qcase_QInr

definition
  quniv :: "i => i"  where
   "quniv(A) == Pow(univ(eclose(A)))"


subsection{*Properties involving Transset and Sum*}

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

subsection{*Introduction and Elimination Rules*}

lemma qunivI: "X <= univ(eclose(A)) ==> X : quniv(A)"
by (simp add: quniv_def)

lemma qunivD: "X : quniv(A) ==> X <= univ(eclose(A))"
by (simp add: quniv_def)

lemma quniv_mono: "A<=B ==> quniv(A) <= quniv(B)"
apply (unfold quniv_def)
apply (erule eclose_mono [THEN univ_mono, THEN Pow_mono])
done

subsection{*Closure Properties*}

lemma univ_eclose_subset_quniv: "univ(eclose(A)) <= quniv(A)"
apply (simp add: quniv_def Transset_iff_Pow [symmetric]) 
apply (rule Transset_eclose [THEN Transset_univ])
done

(*Key property for proving A_subset_quniv; requires eclose in def of quniv*)
lemma univ_subset_quniv: "univ(A) <= quniv(A)"
apply (rule arg_subset_eclose [THEN univ_mono, THEN subset_trans])
apply (rule univ_eclose_subset_quniv)
done

lemmas univ_into_quniv = univ_subset_quniv [THEN subsetD]

lemma Pow_univ_subset_quniv: "Pow(univ(A)) <= quniv(A)"
apply (unfold quniv_def)
apply (rule arg_subset_eclose [THEN univ_mono, THEN Pow_mono])
done

lemmas univ_subset_into_quniv =
    PowI [THEN Pow_univ_subset_quniv [THEN subsetD]]

lemmas zero_in_quniv = zero_in_univ [THEN univ_into_quniv]
lemmas one_in_quniv = one_in_univ [THEN univ_into_quniv]
lemmas two_in_quniv = two_in_univ [THEN univ_into_quniv]

lemmas A_subset_quniv =  subset_trans [OF A_subset_univ univ_subset_quniv]

lemmas A_into_quniv = A_subset_quniv [THEN subsetD]

(*** univ(A) closure for Quine-inspired pairs and injections ***)

(*Quine ordered pairs*)
lemma QPair_subset_univ: 
    "[| a <= univ(A);  b <= univ(A) |] ==> <a;b> <= univ(A)"
by (simp add: QPair_def sum_subset_univ)

subsection{*Quine Disjoint Sum*}

lemma QInl_subset_univ: "a <= univ(A) ==> QInl(a) <= univ(A)"
apply (unfold QInl_def)
apply (erule empty_subsetI [THEN QPair_subset_univ])
done

lemmas naturals_subset_nat = 
    Ord_nat [THEN Ord_is_Transset, unfolded Transset_def, THEN bspec]

lemmas naturals_subset_univ =
    subset_trans [OF naturals_subset_nat nat_subset_univ]

lemma QInr_subset_univ: "a <= univ(A) ==> QInr(a) <= univ(A)"
apply (unfold QInr_def)
apply (erule nat_1I [THEN naturals_subset_univ, THEN QPair_subset_univ])
done

subsection{*Closure for Quine-Inspired Products and Sums*}

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

lemmas quniv_QPair_E = quniv_QPair_D [THEN conjE]

lemma quniv_QPair_iff: "<a;b> : quniv(A) <-> a: quniv(A) & b: quniv(A)"
by (blast intro: QPair_in_quniv dest: quniv_QPair_D)


subsection{*Quine Disjoint Sum*}

lemma QInl_in_quniv: "a: quniv(A) ==> QInl(a) : quniv(A)"
by (simp add: QInl_def zero_in_quniv QPair_in_quniv)

lemma QInr_in_quniv: "b: quniv(A) ==> QInr(b) : quniv(A)"
by (simp add: QInr_def one_in_quniv QPair_in_quniv)

lemma qsum_quniv: "quniv(C) <+> quniv(C) <= quniv(C)"
by (blast intro: QInl_in_quniv QInr_in_quniv)

lemmas qsum_subset_quniv = subset_trans [OF qsum_mono qsum_quniv]


subsection{*The Natural Numbers*}

lemmas nat_subset_quniv =  subset_trans [OF nat_subset_univ univ_subset_quniv]

(* n:nat ==> n:quniv(A) *)
lemmas nat_into_quniv = nat_subset_quniv [THEN subsetD]

lemmas bool_subset_quniv = subset_trans [OF bool_subset_univ univ_subset_quniv]

lemmas bool_into_quniv = bool_subset_quniv [THEN subsetD]


(*Intersecting <a;b> with Vfrom...*)

lemma QPair_Int_Vfrom_succ_subset: 
 "Transset(X) ==>           
       <a;b> Int Vfrom(X, succ(i))  <=  <a Int Vfrom(X,i);  b Int Vfrom(X,i)>"
by (simp add: QPair_def sum_def Int_Un_distrib2 Un_mono
              product_Int_Vfrom_subset [THEN subset_trans]
              Sigma_mono [OF Int_lower1 subset_refl])

subsection{*"Take-Lemma" Rules*}

(*for proving a=b by coinduction and c: quniv(A)*)

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
     "Ord(i) ==> <a;b> Int Vset(i) <= (\<Union>j\<in>i. <a Int Vset(j); b Int Vset(j)>)"
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

end
