(*  Title:      ZF/QUniv.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section\<open>A Small Universe for Lazy Recursive Types\<close>

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
  quniv :: "i \<Rightarrow> i"  where
   "quniv(A) \<equiv> Pow(univ(eclose(A)))"


subsection\<open>Properties involving Transset and Sum\<close>

lemma Transset_includes_summands:
     "\<lbrakk>Transset(C); A+B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C \<and> B \<subseteq> C"
apply (simp add: sum_def Un_subset_iff)
apply (blast dest: Transset_includes_range)
done

lemma Transset_sum_Int_subset:
     "Transset(C) \<Longrightarrow> (A+B) \<inter> C \<subseteq> (A \<inter> C) + (B \<inter> C)"
apply (simp add: sum_def Int_Un_distrib2)
apply (blast dest: Transset_Pair_D)
done

subsection\<open>Introduction and Elimination Rules\<close>

lemma qunivI: "X \<subseteq> univ(eclose(A)) \<Longrightarrow> X \<in> quniv(A)"
by (simp add: quniv_def)

lemma qunivD: "X \<in> quniv(A) \<Longrightarrow> X \<subseteq> univ(eclose(A))"
by (simp add: quniv_def)

lemma quniv_mono: "A<=B \<Longrightarrow> quniv(A) \<subseteq> quniv(B)"
  unfolding quniv_def
apply (erule eclose_mono [THEN univ_mono, THEN Pow_mono])
done

subsection\<open>Closure Properties\<close>

lemma univ_eclose_subset_quniv: "univ(eclose(A)) \<subseteq> quniv(A)"
apply (simp add: quniv_def Transset_iff_Pow [symmetric])
apply (rule Transset_eclose [THEN Transset_univ])
done

(*Key property for proving A_subset_quniv; requires eclose in definition of quniv*)
lemma univ_subset_quniv: "univ(A) \<subseteq> quniv(A)"
apply (rule arg_subset_eclose [THEN univ_mono, THEN subset_trans])
apply (rule univ_eclose_subset_quniv)
done

lemmas univ_into_quniv = univ_subset_quniv [THEN subsetD]

lemma Pow_univ_subset_quniv: "Pow(univ(A)) \<subseteq> quniv(A)"
  unfolding quniv_def
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
    "\<lbrakk>a \<subseteq> univ(A);  b \<subseteq> univ(A)\<rbrakk> \<Longrightarrow> <a;b> \<subseteq> univ(A)"
by (simp add: QPair_def sum_subset_univ)

subsection\<open>Quine Disjoint Sum\<close>

lemma QInl_subset_univ: "a \<subseteq> univ(A) \<Longrightarrow> QInl(a) \<subseteq> univ(A)"
  unfolding QInl_def
apply (erule empty_subsetI [THEN QPair_subset_univ])
done

lemmas naturals_subset_nat =
    Ord_nat [THEN Ord_is_Transset, unfolded Transset_def, THEN bspec]

lemmas naturals_subset_univ =
    subset_trans [OF naturals_subset_nat nat_subset_univ]

lemma QInr_subset_univ: "a \<subseteq> univ(A) \<Longrightarrow> QInr(a) \<subseteq> univ(A)"
  unfolding QInr_def
apply (erule nat_1I [THEN naturals_subset_univ, THEN QPair_subset_univ])
done

subsection\<open>Closure for Quine-Inspired Products and Sums\<close>

(*Quine ordered pairs*)
lemma QPair_in_quniv:
    "\<lbrakk>a: quniv(A);  b: quniv(A)\<rbrakk> \<Longrightarrow> <a;b> \<in> quniv(A)"
by (simp add: quniv_def QPair_def sum_subset_univ)

lemma QSigma_quniv: "quniv(A) <*> quniv(A) \<subseteq> quniv(A)"
by (blast intro: QPair_in_quniv)

lemmas QSigma_subset_quniv =  subset_trans [OF QSigma_mono QSigma_quniv]

(*The opposite inclusion*)
lemma quniv_QPair_D:
    "<a;b> \<in> quniv(A) \<Longrightarrow> a: quniv(A) \<and> b: quniv(A)"
apply (unfold quniv_def QPair_def)
apply (rule Transset_includes_summands [THEN conjE])
apply (rule Transset_eclose [THEN Transset_univ])
apply (erule PowD, blast)
done

lemmas quniv_QPair_E = quniv_QPair_D [THEN conjE]

lemma quniv_QPair_iff: "<a;b> \<in> quniv(A) \<longleftrightarrow> a: quniv(A) \<and> b: quniv(A)"
by (blast intro: QPair_in_quniv dest: quniv_QPair_D)


subsection\<open>Quine Disjoint Sum\<close>

lemma QInl_in_quniv: "a: quniv(A) \<Longrightarrow> QInl(a) \<in> quniv(A)"
by (simp add: QInl_def zero_in_quniv QPair_in_quniv)

lemma QInr_in_quniv: "b: quniv(A) \<Longrightarrow> QInr(b) \<in> quniv(A)"
by (simp add: QInr_def one_in_quniv QPair_in_quniv)

lemma qsum_quniv: "quniv(C) <+> quniv(C) \<subseteq> quniv(C)"
by (blast intro: QInl_in_quniv QInr_in_quniv)

lemmas qsum_subset_quniv = subset_trans [OF qsum_mono qsum_quniv]


subsection\<open>The Natural Numbers\<close>

lemmas nat_subset_quniv =  subset_trans [OF nat_subset_univ univ_subset_quniv]

(* n:nat \<Longrightarrow> n:quniv(A) *)
lemmas nat_into_quniv = nat_subset_quniv [THEN subsetD]

lemmas bool_subset_quniv = subset_trans [OF bool_subset_univ univ_subset_quniv]

lemmas bool_into_quniv = bool_subset_quniv [THEN subsetD]


(*Intersecting <a;b> with Vfrom...*)

lemma QPair_Int_Vfrom_succ_subset:
 "Transset(X) \<Longrightarrow>
       <a;b> \<inter> Vfrom(X, succ(i))  \<subseteq>  <a \<inter> Vfrom(X,i);  b \<inter> Vfrom(X,i)>"
by (simp add: QPair_def sum_def Int_Un_distrib2 Un_mono
              product_Int_Vfrom_subset [THEN subset_trans]
              Sigma_mono [OF Int_lower1 subset_refl])

subsection\<open>"Take-Lemma" Rules\<close>

(*for proving a=b by coinduction and c: quniv(A)*)

(*Rule for level i -- preserving the level, not decreasing it*)

lemma QPair_Int_Vfrom_subset:
 "Transset(X) \<Longrightarrow>
       <a;b> \<inter> Vfrom(X,i)  \<subseteq>  <a \<inter> Vfrom(X,i);  b \<inter> Vfrom(X,i)>"
  unfolding QPair_def
apply (erule Transset_Vfrom [THEN Transset_sum_Int_subset])
done

(*@{term"\<lbrakk>a \<inter> Vset(i) \<subseteq> c; b \<inter> Vset(i) \<subseteq> d\<rbrakk> \<Longrightarrow> <a;b> \<inter> Vset(i) \<subseteq> <c;d>"}*)
lemmas QPair_Int_Vset_subset_trans =
     subset_trans [OF Transset_0 [THEN QPair_Int_Vfrom_subset] QPair_mono]

lemma QPair_Int_Vset_subset_UN:
     "Ord(i) \<Longrightarrow> <a;b> \<inter> Vset(i) \<subseteq> (\<Union>j\<in>i. <a \<inter> Vset(j); b \<inter> Vset(j)>)"
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
