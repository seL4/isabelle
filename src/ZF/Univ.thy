(*  Title:      ZF/univ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The cumulative hierarchy and a small universe for recursive types

Standard notation for Vset(i) is V(i), but users might want V for a variable

NOTE: univ(A) could be a translation; would simplify many proofs!
  But Ind_Syntax.univ refers to the constant "Univ.univ"
*)

theory Univ = Epsilon + Sum + Finite + mono:

constdefs
  Vfrom       :: "[i,i]=>i"
    "Vfrom(A,i) == transrec(i, %x f. A Un (\<Union>y\<in>x. Pow(f`y)))"

syntax   Vset :: "i=>i"
translations
    "Vset(x)"   ==      "Vfrom(0,x)"


constdefs
  Vrec        :: "[i, [i,i]=>i] =>i"
    "Vrec(a,H) == transrec(rank(a), %x g. lam z: Vset(succ(x)).
 		 	   H(z, lam w:Vset(x). g`rank(w)`w)) ` a"

  Vrecursor   :: "[[i,i]=>i, i] =>i"
    "Vrecursor(H,a) == transrec(rank(a), %x g. lam z: Vset(succ(x)).
				H(lam w:Vset(x). g`rank(w)`w, z)) ` a"

  univ        :: "i=>i"
    "univ(A) == Vfrom(A,nat)"


text{*NOT SUITABLE FOR REWRITING -- RECURSIVE!*}
lemma Vfrom: "Vfrom(A,i) = A Un (\<Union>j\<in>i. Pow(Vfrom(A,j)))"
apply (subst Vfrom_def [THEN def_transrec])
apply simp
done

subsubsection{* Monotonicity *}

lemma Vfrom_mono [rule_format]:
     "A<=B ==> \<forall>j. i<=j --> Vfrom(A,i) <= Vfrom(B,j)"
apply (rule_tac a=i in eps_induct)
apply (rule impI [THEN allI])
apply (subst Vfrom)
apply (subst Vfrom)
apply (erule Un_mono)
apply (erule UN_mono, blast) 
done

lemma VfromI: "[| a \<in> Vfrom(A,j);  j<i |] ==> a \<in> Vfrom(A,i)"
by (blast dest: Vfrom_mono [OF subset_refl le_imp_subset [OF leI]]) 


subsubsection{* A fundamental equality: Vfrom does not require ordinals! *}

lemma Vfrom_rank_subset1: "Vfrom(A,x) <= Vfrom(A,rank(x))"
apply (rule_tac a=x in eps_induct)
apply (subst Vfrom)
apply (subst Vfrom)
apply (blast intro!: rank_lt [THEN ltD])
done

lemma Vfrom_rank_subset2: "Vfrom(A,rank(x)) <= Vfrom(A,x)"
apply (rule_tac a=x in eps_induct)
apply (subst Vfrom)
apply (subst Vfrom)
apply (rule subset_refl [THEN Un_mono])
apply (rule UN_least)
txt{*expand rank(x1) = (\<Union>y\<in>x1. succ(rank(y))) in assumptions*}
apply (erule rank [THEN equalityD1, THEN subsetD, THEN UN_E])
apply (rule subset_trans)
apply (erule_tac [2] UN_upper)
apply (rule subset_refl [THEN Vfrom_mono, THEN subset_trans, THEN Pow_mono])
apply (erule ltI [THEN le_imp_subset])
apply (rule Ord_rank [THEN Ord_succ])
apply (erule bspec, assumption)
done

lemma Vfrom_rank_eq: "Vfrom(A,rank(x)) = Vfrom(A,x)"
apply (rule equalityI)
apply (rule Vfrom_rank_subset2)
apply (rule Vfrom_rank_subset1)
done


subsection{* Basic closure properties *}

lemma zero_in_Vfrom: "y:x ==> 0 \<in> Vfrom(A,x)"
by (subst Vfrom, blast)

lemma i_subset_Vfrom: "i <= Vfrom(A,i)"
apply (rule_tac a=i in eps_induct)
apply (subst Vfrom, blast)
done

lemma A_subset_Vfrom: "A <= Vfrom(A,i)"
apply (subst Vfrom)
apply (rule Un_upper1)
done

lemmas A_into_Vfrom = A_subset_Vfrom [THEN subsetD]

lemma subset_mem_Vfrom: "a <= Vfrom(A,i) ==> a \<in> Vfrom(A,succ(i))"
by (subst Vfrom, blast)

subsubsection{* Finite sets and ordered pairs *}

lemma singleton_in_Vfrom: "a \<in> Vfrom(A,i) ==> {a} \<in> Vfrom(A,succ(i))"
by (rule subset_mem_Vfrom, safe)

lemma doubleton_in_Vfrom:
     "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i) |] ==> {a,b} \<in> Vfrom(A,succ(i))"
by (rule subset_mem_Vfrom, safe)

lemma Pair_in_Vfrom:
    "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i) |] ==> <a,b> \<in> Vfrom(A,succ(succ(i)))"
apply (unfold Pair_def)
apply (blast intro: doubleton_in_Vfrom) 
done

lemma succ_in_Vfrom: "a <= Vfrom(A,i) ==> succ(a) \<in> Vfrom(A,succ(succ(i)))"
apply (intro subset_mem_Vfrom succ_subsetI, assumption)
apply (erule subset_trans) 
apply (rule Vfrom_mono [OF subset_refl subset_succI]) 
done

subsection{* 0, successor and limit equations fof Vfrom *}

lemma Vfrom_0: "Vfrom(A,0) = A"
by (subst Vfrom, blast)

lemma Vfrom_succ_lemma: "Ord(i) ==> Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))"
apply (rule Vfrom [THEN trans])
apply (rule equalityI [THEN subst_context, 
                       OF _ succI1 [THEN RepFunI, THEN Union_upper]])
apply (rule UN_least)
apply (rule subset_refl [THEN Vfrom_mono, THEN Pow_mono])
apply (erule ltI [THEN le_imp_subset])
apply (erule Ord_succ)
done

lemma Vfrom_succ: "Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))"
apply (rule_tac x1 = "succ (i)" in Vfrom_rank_eq [THEN subst])
apply (rule_tac x1 = "i" in Vfrom_rank_eq [THEN subst])
apply (subst rank_succ)
apply (rule Ord_rank [THEN Vfrom_succ_lemma])
done

(*The premise distinguishes this from Vfrom(A,0);  allowing X=0 forces
  the conclusion to be Vfrom(A,Union(X)) = A Un (\<Union>y\<in>X. Vfrom(A,y)) *)
lemma Vfrom_Union: "y:X ==> Vfrom(A,Union(X)) = (\<Union>y\<in>X. Vfrom(A,y))"
apply (subst Vfrom)
apply (rule equalityI)
txt{*first inclusion*}
apply (rule Un_least)
apply (rule A_subset_Vfrom [THEN subset_trans])
apply (rule UN_upper, assumption)
apply (rule UN_least)
apply (erule UnionE)
apply (rule subset_trans)
apply (erule_tac [2] UN_upper,
       subst Vfrom, erule subset_trans [OF UN_upper Un_upper2])
txt{*opposite inclusion*}
apply (rule UN_least)
apply (subst Vfrom, blast)
done

subsection{* Vfrom applied to Limit ordinals *}

(*NB. limit ordinals are non-empty:
      Vfrom(A,0) = A = A Un (\<Union>y\<in>0. Vfrom(A,y)) *)
lemma Limit_Vfrom_eq:
    "Limit(i) ==> Vfrom(A,i) = (\<Union>y\<in>i. Vfrom(A,y))"
apply (rule Limit_has_0 [THEN ltD, THEN Vfrom_Union, THEN subst], assumption)
apply (simp add: Limit_Union_eq) 
done

lemma Limit_VfromE:
    "[| a \<in> Vfrom(A,i);  ~R ==> Limit(i);
        !!x. [| x<i;  a \<in> Vfrom(A,x) |] ==> R
     |] ==> R"
apply (rule classical)
apply (rule Limit_Vfrom_eq [THEN equalityD1, THEN subsetD, THEN UN_E])
  prefer 2 apply assumption
 apply blast 
apply (blast intro: ltI Limit_is_Ord)
done

lemmas zero_in_VLimit = Limit_has_0 [THEN ltD, THEN zero_in_Vfrom, standard]

lemma singleton_in_VLimit:
    "[| a \<in> Vfrom(A,i);  Limit(i) |] ==> {a} \<in> Vfrom(A,i)"
apply (erule Limit_VfromE, assumption)
apply (erule singleton_in_Vfrom [THEN VfromI])
apply (blast intro: Limit_has_succ) 
done

lemmas Vfrom_UnI1 = 
    Un_upper1 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD], standard]
lemmas Vfrom_UnI2 = 
    Un_upper2 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD], standard]

text{*Hard work is finding a single j:i such that {a,b}<=Vfrom(A,j)*}
lemma doubleton_in_VLimit:
    "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i) |] ==> {a,b} \<in> Vfrom(A,i)"
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption)
apply (blast intro:  VfromI [OF doubleton_in_Vfrom]
                     Vfrom_UnI1 Vfrom_UnI2 Limit_has_succ Un_least_lt)
done

lemma Pair_in_VLimit:
    "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i) |] ==> <a,b> \<in> Vfrom(A,i)"
txt{*Infer that a, b occur at ordinals x,xa < i.*}
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption)
txt{*Infer that succ(succ(x Un xa)) < i *}
apply (blast intro: VfromI [OF Pair_in_Vfrom]
                    Vfrom_UnI1 Vfrom_UnI2 Limit_has_succ Un_least_lt)
done

lemma product_VLimit: "Limit(i) ==> Vfrom(A,i) * Vfrom(A,i) <= Vfrom(A,i)"
by (blast intro: Pair_in_VLimit)

lemmas Sigma_subset_VLimit =
     subset_trans [OF Sigma_mono product_VLimit]

lemmas nat_subset_VLimit =
     subset_trans [OF nat_le_Limit [THEN le_imp_subset] i_subset_Vfrom]

lemma nat_into_VLimit: "[| n: nat;  Limit(i) |] ==> n \<in> Vfrom(A,i)"
by (blast intro: nat_subset_VLimit [THEN subsetD])

subsubsection{* Closure under disjoint union *}

lemmas zero_in_VLimit = Limit_has_0 [THEN ltD, THEN zero_in_Vfrom, standard]

lemma one_in_VLimit: "Limit(i) ==> 1 \<in> Vfrom(A,i)"
by (blast intro: nat_into_VLimit)

lemma Inl_in_VLimit:
    "[| a \<in> Vfrom(A,i); Limit(i) |] ==> Inl(a) \<in> Vfrom(A,i)"
apply (unfold Inl_def)
apply (blast intro: zero_in_VLimit Pair_in_VLimit)
done

lemma Inr_in_VLimit:
    "[| b \<in> Vfrom(A,i); Limit(i) |] ==> Inr(b) \<in> Vfrom(A,i)"
apply (unfold Inr_def)
apply (blast intro: one_in_VLimit Pair_in_VLimit)
done

lemma sum_VLimit: "Limit(i) ==> Vfrom(C,i)+Vfrom(C,i) <= Vfrom(C,i)"
by (blast intro!: Inl_in_VLimit Inr_in_VLimit)

lemmas sum_subset_VLimit = subset_trans [OF sum_mono sum_VLimit]



subsection{* Properties assuming Transset(A) *}

lemma Transset_Vfrom: "Transset(A) ==> Transset(Vfrom(A,i))"
apply (rule_tac a=i in eps_induct)
apply (subst Vfrom)
apply (blast intro!: Transset_Union_family Transset_Un Transset_Pow)
done

lemma Transset_Vfrom_succ:
     "Transset(A) ==> Vfrom(A, succ(i)) = Pow(Vfrom(A,i))"
apply (rule Vfrom_succ [THEN trans])
apply (rule equalityI [OF _ Un_upper2])
apply (rule Un_least [OF _ subset_refl])
apply (rule A_subset_Vfrom [THEN subset_trans])
apply (erule Transset_Vfrom [THEN Transset_iff_Pow [THEN iffD1]])
done

lemma Transset_Pair_subset: "[| <a,b> <= C; Transset(C) |] ==> a: C & b: C"
by (unfold Pair_def Transset_def, blast)

lemma Transset_Pair_subset_VLimit:
     "[| <a,b> <= Vfrom(A,i);  Transset(A);  Limit(i) |]
      ==> <a,b> \<in> Vfrom(A,i)"
apply (erule Transset_Pair_subset [THEN conjE])
apply (erule Transset_Vfrom)
apply (blast intro: Pair_in_VLimit)
done

lemma Union_in_Vfrom:
     "[| X \<in> Vfrom(A,j);  Transset(A) |] ==> Union(X) \<in> Vfrom(A, succ(j))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def, blast)
done

lemma Union_in_VLimit:
     "[| X \<in> Vfrom(A,i);  Limit(i);  Transset(A) |] ==> Union(X) \<in> Vfrom(A,i)"
apply (rule Limit_VfromE, assumption+)
apply (blast intro: Limit_has_succ VfromI Union_in_Vfrom)
done


(*** Closure under product/sum applied to elements -- thus Vfrom(A,i)
     is a model of simple type theory provided A is a transitive set
     and i is a limit ordinal
***)

text{*General theorem for membership in Vfrom(A,i) when i is a limit ordinal*}
lemma in_VLimit:
  "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);
      !!x y j. [| j<i; 1:j; x \<in> Vfrom(A,j); y \<in> Vfrom(A,j) |]
               ==> EX k. h(x,y) \<in> Vfrom(A,k) & k<i |]
   ==> h(a,b) \<in> Vfrom(A,i)"
txt{*Infer that a, b occur at ordinals x,xa < i.*}
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption, atomize)
apply (drule_tac x=a in spec) 
apply (drule_tac x=b in spec) 
apply (drule_tac x="x Un xa Un 2" in spec) 
apply (simp add: Un_least_lt_iff lt_Ord Vfrom_UnI1 Vfrom_UnI2) 
apply (blast intro: Limit_has_0 Limit_has_succ VfromI)
done

subsubsection{* products *}

lemma prod_in_Vfrom:
    "[| a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A) |]
     ==> a*b \<in> Vfrom(A, succ(succ(succ(j))))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def)
apply (blast intro: Pair_in_Vfrom)
done

lemma prod_in_VLimit:
  "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A) |]
   ==> a*b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: prod_in_Vfrom Limit_has_succ)
done

subsubsection{* Disjoint sums, aka Quine ordered pairs *}

lemma sum_in_Vfrom:
    "[| a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A);  1:j |]
     ==> a+b \<in> Vfrom(A, succ(succ(succ(j))))"
apply (unfold sum_def)
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def)
apply (blast intro: zero_in_Vfrom Pair_in_Vfrom i_subset_Vfrom [THEN subsetD])
done

lemma sum_in_VLimit:
  "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A) |]
   ==> a+b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: sum_in_Vfrom Limit_has_succ)
done

subsubsection{* function space! *}

lemma fun_in_Vfrom:
    "[| a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A) |] ==>
          a->b \<in> Vfrom(A, succ(succ(succ(succ(j)))))"
apply (unfold Pi_def)
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (rule Collect_subset [THEN subset_trans])
apply (subst Vfrom)
apply (rule subset_trans [THEN subset_trans])
apply (rule_tac [3] Un_upper2)
apply (rule_tac [2] succI1 [THEN UN_upper])
apply (rule Pow_mono)
apply (unfold Transset_def)
apply (blast intro: Pair_in_Vfrom)
done

lemma fun_in_VLimit:
  "[| a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A) |]
   ==> a->b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: fun_in_Vfrom Limit_has_succ)
done

lemma Pow_in_Vfrom:
    "[| a \<in> Vfrom(A,j);  Transset(A) |] ==> Pow(a) \<in> Vfrom(A, succ(succ(j)))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def)
apply (subst Vfrom, blast)
done

lemma Pow_in_VLimit:
     "[| a \<in> Vfrom(A,i);  Limit(i);  Transset(A) |] ==> Pow(a) \<in> Vfrom(A,i)"
by (blast elim: Limit_VfromE intro: Limit_has_succ Pow_in_Vfrom VfromI)


subsection{* The set Vset(i) *}

lemma Vset: "Vset(i) = (\<Union>j\<in>i. Pow(Vset(j)))"
by (subst Vfrom, blast)

lemmas Vset_succ = Transset_0 [THEN Transset_Vfrom_succ, standard]
lemmas Transset_Vset = Transset_0 [THEN Transset_Vfrom, standard]

subsubsection{* Characterisation of the elements of Vset(i) *}

lemma VsetD [rule_format]: "Ord(i) ==> \<forall>b. b \<in> Vset(i) --> rank(b) < i"
apply (erule trans_induct)
apply (subst Vset, safe)
apply (subst rank)
apply (blast intro: ltI UN_succ_least_lt) 
done

lemma VsetI_lemma [rule_format]:
     "Ord(i) ==> \<forall>b. rank(b) \<in> i --> b \<in> Vset(i)"
apply (erule trans_induct)
apply (rule allI)
apply (subst Vset)
apply (blast intro!: rank_lt [THEN ltD])
done

lemma VsetI: "rank(x)<i ==> x \<in> Vset(i)"
by (blast intro: VsetI_lemma elim: ltE)

text{*Merely a lemma for the next result*}
lemma Vset_Ord_rank_iff: "Ord(i) ==> b \<in> Vset(i) <-> rank(b) < i"
by (blast intro: VsetD VsetI)

lemma Vset_rank_iff [simp]: "b \<in> Vset(a) <-> rank(b) < rank(a)"
apply (rule Vfrom_rank_eq [THEN subst])
apply (rule Ord_rank [THEN Vset_Ord_rank_iff])
done

text{*This is rank(rank(a)) = rank(a) *}
declare Ord_rank [THEN rank_of_Ord, simp]

lemma rank_Vset: "Ord(i) ==> rank(Vset(i)) = i"
apply (subst rank)
apply (rule equalityI, safe)
apply (blast intro: VsetD [THEN ltD]) 
apply (blast intro: VsetD [THEN ltD] Ord_trans) 
apply (blast intro: i_subset_Vfrom [THEN subsetD]
                    Ord_in_Ord [THEN rank_of_Ord, THEN ssubst])
done

subsubsection{* Reasoning about sets in terms of their elements' ranks *}

lemma arg_subset_Vset_rank: "a <= Vset(rank(a))"
apply (rule subsetI)
apply (erule rank_lt [THEN VsetI])
done

lemma Int_Vset_subset:
    "[| !!i. Ord(i) ==> a Int Vset(i) <= b |] ==> a <= b"
apply (rule subset_trans) 
apply (rule Int_greatest [OF subset_refl arg_subset_Vset_rank])
apply (blast intro: Ord_rank) 
done

subsubsection{* Set up an environment for simplification *}

lemma rank_Inl: "rank(a) < rank(Inl(a))"
apply (unfold Inl_def)
apply (rule rank_pair2)
done

lemma rank_Inr: "rank(a) < rank(Inr(a))"
apply (unfold Inr_def)
apply (rule rank_pair2)
done

lemmas rank_rls = rank_Inl rank_Inr rank_pair1 rank_pair2

subsubsection{* Recursion over Vset levels! *}

text{*NOT SUITABLE FOR REWRITING: recursive!*}
lemma Vrec: "Vrec(a,H) = H(a, lam x:Vset(rank(a)). Vrec(x,H))"
apply (unfold Vrec_def)
apply (subst transrec)
apply simp
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text{*This form avoids giant explosions in proofs.  NOTE USE OF == *}
lemma def_Vrec:
    "[| !!x. h(x)==Vrec(x,H) |] ==>
     h(a) = H(a, lam x: Vset(rank(a)). h(x))"
apply simp 
apply (rule Vrec)
done

text{*NOT SUITABLE FOR REWRITING: recursive!*}
lemma Vrecursor:
     "Vrecursor(H,a) = H(lam x:Vset(rank(a)). Vrecursor(H,x),  a)"
apply (unfold Vrecursor_def)
apply (subst transrec, simp)
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text{*This form avoids giant explosions in proofs.  NOTE USE OF == *}
lemma def_Vrecursor:
     "h == Vrecursor(H) ==> h(a) = H(lam x: Vset(rank(a)). h(x),  a)"
apply simp
apply (rule Vrecursor)
done


subsection{* univ(A) *}

lemma univ_mono: "A<=B ==> univ(A) <= univ(B)"
apply (unfold univ_def)
apply (erule Vfrom_mono)
apply (rule subset_refl)
done

lemma Transset_univ: "Transset(A) ==> Transset(univ(A))"
apply (unfold univ_def)
apply (erule Transset_Vfrom)
done

subsubsection{* univ(A) as a limit *}

lemma univ_eq_UN: "univ(A) = (\<Union>i\<in>nat. Vfrom(A,i))"
apply (unfold univ_def)
apply (rule Limit_nat [THEN Limit_Vfrom_eq])
done

lemma subset_univ_eq_Int: "c <= univ(A) ==> c = (\<Union>i\<in>nat. c Int Vfrom(A,i))"
apply (rule subset_UN_iff_eq [THEN iffD1])
apply (erule univ_eq_UN [THEN subst])
done

lemma univ_Int_Vfrom_subset:
    "[| a <= univ(X);
        !!i. i:nat ==> a Int Vfrom(X,i) <= b |]
     ==> a <= b"
apply (subst subset_univ_eq_Int, assumption)
apply (rule UN_least, simp) 
done

lemma univ_Int_Vfrom_eq:
    "[| a <= univ(X);   b <= univ(X);
        !!i. i:nat ==> a Int Vfrom(X,i) = b Int Vfrom(X,i)
     |] ==> a = b"
apply (rule equalityI)
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE) 
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE) 
done

subsubsection{* Closure properties *}

lemma zero_in_univ: "0 \<in> univ(A)"
apply (unfold univ_def)
apply (rule nat_0I [THEN zero_in_Vfrom])
done

lemma A_subset_univ: "A <= univ(A)"
apply (unfold univ_def)
apply (rule A_subset_Vfrom)
done

lemmas A_into_univ = A_subset_univ [THEN subsetD, standard]

subsubsection{* Closure under unordered and ordered pairs *}

lemma singleton_in_univ: "a: univ(A) ==> {a} \<in> univ(A)"
apply (unfold univ_def)
apply (blast intro: singleton_in_VLimit Limit_nat)
done

lemma doubleton_in_univ:
    "[| a: univ(A);  b: univ(A) |] ==> {a,b} \<in> univ(A)"
apply (unfold univ_def)
apply (blast intro: doubleton_in_VLimit Limit_nat)
done

lemma Pair_in_univ:
    "[| a: univ(A);  b: univ(A) |] ==> <a,b> \<in> univ(A)"
apply (unfold univ_def)
apply (blast intro: Pair_in_VLimit Limit_nat)
done

lemma Union_in_univ:
     "[| X: univ(A);  Transset(A) |] ==> Union(X) \<in> univ(A)"
apply (unfold univ_def)
apply (blast intro: Union_in_VLimit Limit_nat)
done

lemma product_univ: "univ(A)*univ(A) <= univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN product_VLimit])
done


subsubsection{* The natural numbers *}

lemma nat_subset_univ: "nat <= univ(A)"
apply (unfold univ_def)
apply (rule i_subset_Vfrom)
done

text{* n:nat ==> n:univ(A) *}
lemmas nat_into_univ = nat_subset_univ [THEN subsetD, standard]

subsubsection{* instances for 1 and 2 *}

lemma one_in_univ: "1 \<in> univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN one_in_VLimit])
done

text{*unused!*}
lemma two_in_univ: "2 \<in> univ(A)"
by (blast intro: nat_into_univ)

lemma bool_subset_univ: "bool <= univ(A)"
apply (unfold bool_def)
apply (blast intro!: zero_in_univ one_in_univ)
done

lemmas bool_into_univ = bool_subset_univ [THEN subsetD, standard]


subsubsection{* Closure under disjoint union *}

lemma Inl_in_univ: "a: univ(A) ==> Inl(a) \<in> univ(A)"
apply (unfold univ_def)
apply (erule Inl_in_VLimit [OF _ Limit_nat])
done

lemma Inr_in_univ: "b: univ(A) ==> Inr(b) \<in> univ(A)"
apply (unfold univ_def)
apply (erule Inr_in_VLimit [OF _ Limit_nat])
done

lemma sum_univ: "univ(C)+univ(C) <= univ(C)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN sum_VLimit])
done

lemmas sum_subset_univ = subset_trans [OF sum_mono sum_univ]


subsubsection{* Closure under binary union -- use Un_least *}
subsubsection{* Closure under Collect -- use  (Collect_subset RS subset_trans)  *}
subsubsection{* Closure under RepFun -- use   RepFun_subset  *}


subsection{* Finite Branching Closure Properties *}

subsubsection{* Closure under finite powerset *}

lemma Fin_Vfrom_lemma:
     "[| b: Fin(Vfrom(A,i));  Limit(i) |] ==> EX j. b <= Vfrom(A,j) & j<i"
apply (erule Fin_induct)
apply (blast dest!: Limit_has_0, safe)
apply (erule Limit_VfromE, assumption)
apply (blast intro!: Un_least_lt intro: Vfrom_UnI1 Vfrom_UnI2)
done

lemma Fin_VLimit: "Limit(i) ==> Fin(Vfrom(A,i)) <= Vfrom(A,i)"
apply (rule subsetI)
apply (drule Fin_Vfrom_lemma, safe)
apply (rule Vfrom [THEN ssubst])
apply (blast dest!: ltD)
done

lemmas Fin_subset_VLimit = subset_trans [OF Fin_mono Fin_VLimit]

lemma Fin_univ: "Fin(univ(A)) <= univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN Fin_VLimit])
done

subsubsection{* Closure under finite powers: functions from a natural number *}

lemma nat_fun_VLimit:
     "[| n: nat;  Limit(i) |] ==> n -> Vfrom(A,i) <= Vfrom(A,i)"
apply (erule nat_fun_subset_Fin [THEN subset_trans])
apply (blast del: subsetI
    intro: subset_refl Fin_subset_VLimit Sigma_subset_VLimit nat_subset_VLimit)
done

lemmas nat_fun_subset_VLimit = subset_trans [OF Pi_mono nat_fun_VLimit]

lemma nat_fun_univ: "n: nat ==> n -> univ(A) <= univ(A)"
apply (unfold univ_def)
apply (erule nat_fun_VLimit [OF _ Limit_nat])
done


subsubsection{* Closure under finite function space *}

text{*General but seldom-used version; normally the domain is fixed*}
lemma FiniteFun_VLimit1:
     "Limit(i) ==> Vfrom(A,i) -||> Vfrom(A,i) <= Vfrom(A,i)"
apply (rule FiniteFun.dom_subset [THEN subset_trans])
apply (blast del: subsetI
             intro: Fin_subset_VLimit Sigma_subset_VLimit subset_refl)
done

lemma FiniteFun_univ1: "univ(A) -||> univ(A) <= univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN FiniteFun_VLimit1])
done

text{*Version for a fixed domain*}
lemma FiniteFun_VLimit:
     "[| W <= Vfrom(A,i); Limit(i) |] ==> W -||> Vfrom(A,i) <= Vfrom(A,i)"
apply (rule subset_trans) 
apply (erule FiniteFun_mono [OF _ subset_refl])
apply (erule FiniteFun_VLimit1)
done

lemma FiniteFun_univ:
    "W <= univ(A) ==> W -||> univ(A) <= univ(A)"
apply (unfold univ_def)
apply (erule FiniteFun_VLimit [OF _ Limit_nat])
done

lemma FiniteFun_in_univ:
     "[| f: W -||> univ(A);  W <= univ(A) |] ==> f \<in> univ(A)"
by (erule FiniteFun_univ [THEN subsetD], assumption)

text{*Remove <= from the rule above*}
lemmas FiniteFun_in_univ' = FiniteFun_in_univ [OF _ subsetI]


subsection{** For QUniv.  Properties of Vfrom analogous to the "take-lemma" **}

subsection{* Intersecting a*b with Vfrom... *}

text{*This version says a, b exist one level down, in the smaller set Vfrom(X,i)*}
lemma doubleton_in_Vfrom_D:
     "[| {a,b} \<in> Vfrom(X,succ(i));  Transset(X) |]
      ==> a \<in> Vfrom(X,i)  &  b \<in> Vfrom(X,i)"
by (drule Transset_Vfrom_succ [THEN equalityD1, THEN subsetD, THEN PowD], 
    assumption, fast)

text{*This weaker version says a, b exist at the same level*}
lemmas Vfrom_doubleton_D = Transset_Vfrom [THEN Transset_doubleton_D, standard]

(** Using only the weaker theorem would prove <a,b> \<in> Vfrom(X,i)
      implies a, b \<in> Vfrom(X,i), which is useless for induction.
    Using only the stronger theorem would prove <a,b> \<in> Vfrom(X,succ(succ(i)))
      implies a, b \<in> Vfrom(X,i), leaving the succ(i) case untreated.
    The combination gives a reduction by precisely one level, which is
      most convenient for proofs.
**)

lemma Pair_in_Vfrom_D:
    "[| <a,b> \<in> Vfrom(X,succ(i));  Transset(X) |]
     ==> a \<in> Vfrom(X,i)  &  b \<in> Vfrom(X,i)"
apply (unfold Pair_def)
apply (blast dest!: doubleton_in_Vfrom_D Vfrom_doubleton_D)
done

lemma product_Int_Vfrom_subset:
     "Transset(X) ==>
      (a*b) Int Vfrom(X, succ(i)) <= (a Int Vfrom(X,i)) * (b Int Vfrom(X,i))"
by (blast dest!: Pair_in_Vfrom_D)


ML
{*

val Vfrom = thm "Vfrom";
val Vfrom_mono = thm "Vfrom_mono";
val Vfrom_rank_subset1 = thm "Vfrom_rank_subset1";
val Vfrom_rank_subset2 = thm "Vfrom_rank_subset2";
val Vfrom_rank_eq = thm "Vfrom_rank_eq";
val zero_in_Vfrom = thm "zero_in_Vfrom";
val i_subset_Vfrom = thm "i_subset_Vfrom";
val A_subset_Vfrom = thm "A_subset_Vfrom";
val subset_mem_Vfrom = thm "subset_mem_Vfrom";
val singleton_in_Vfrom = thm "singleton_in_Vfrom";
val doubleton_in_Vfrom = thm "doubleton_in_Vfrom";
val Pair_in_Vfrom = thm "Pair_in_Vfrom";
val succ_in_Vfrom = thm "succ_in_Vfrom";
val Vfrom_0 = thm "Vfrom_0";
val Vfrom_succ = thm "Vfrom_succ";
val Vfrom_Union = thm "Vfrom_Union";
val Limit_Vfrom_eq = thm "Limit_Vfrom_eq";
val zero_in_VLimit = thm "zero_in_VLimit";
val singleton_in_VLimit = thm "singleton_in_VLimit";
val Vfrom_UnI1 = thm "Vfrom_UnI1";
val Vfrom_UnI2 = thm "Vfrom_UnI2";
val doubleton_in_VLimit = thm "doubleton_in_VLimit";
val Pair_in_VLimit = thm "Pair_in_VLimit";
val product_VLimit = thm "product_VLimit";
val Sigma_subset_VLimit = thm "Sigma_subset_VLimit";
val nat_subset_VLimit = thm "nat_subset_VLimit";
val nat_into_VLimit = thm "nat_into_VLimit";
val zero_in_VLimit = thm "zero_in_VLimit";
val one_in_VLimit = thm "one_in_VLimit";
val Inl_in_VLimit = thm "Inl_in_VLimit";
val Inr_in_VLimit = thm "Inr_in_VLimit";
val sum_VLimit = thm "sum_VLimit";
val sum_subset_VLimit = thm "sum_subset_VLimit";
val Transset_Vfrom = thm "Transset_Vfrom";
val Transset_Vfrom_succ = thm "Transset_Vfrom_succ";
val Transset_Pair_subset = thm "Transset_Pair_subset";
val Union_in_Vfrom = thm "Union_in_Vfrom";
val Union_in_VLimit = thm "Union_in_VLimit";
val in_VLimit = thm "in_VLimit";
val prod_in_Vfrom = thm "prod_in_Vfrom";
val prod_in_VLimit = thm "prod_in_VLimit";
val sum_in_Vfrom = thm "sum_in_Vfrom";
val sum_in_VLimit = thm "sum_in_VLimit";
val fun_in_Vfrom = thm "fun_in_Vfrom";
val fun_in_VLimit = thm "fun_in_VLimit";
val Pow_in_Vfrom = thm "Pow_in_Vfrom";
val Pow_in_VLimit = thm "Pow_in_VLimit";
val Vset = thm "Vset";
val Vset_succ = thm "Vset_succ";
val Transset_Vset = thm "Transset_Vset";
val VsetD = thm "VsetD";
val VsetI = thm "VsetI";
val Vset_Ord_rank_iff = thm "Vset_Ord_rank_iff";
val Vset_rank_iff = thm "Vset_rank_iff";
val rank_Vset = thm "rank_Vset";
val arg_subset_Vset_rank = thm "arg_subset_Vset_rank";
val Int_Vset_subset = thm "Int_Vset_subset";
val rank_Inl = thm "rank_Inl";
val rank_Inr = thm "rank_Inr";
val Vrec = thm "Vrec";
val def_Vrec = thm "def_Vrec";
val Vrecursor = thm "Vrecursor";
val def_Vrecursor = thm "def_Vrecursor";
val univ_mono = thm "univ_mono";
val Transset_univ = thm "Transset_univ";
val univ_eq_UN = thm "univ_eq_UN";
val subset_univ_eq_Int = thm "subset_univ_eq_Int";
val univ_Int_Vfrom_subset = thm "univ_Int_Vfrom_subset";
val univ_Int_Vfrom_eq = thm "univ_Int_Vfrom_eq";
val zero_in_univ = thm "zero_in_univ";
val A_subset_univ = thm "A_subset_univ";
val A_into_univ = thm "A_into_univ";
val singleton_in_univ = thm "singleton_in_univ";
val doubleton_in_univ = thm "doubleton_in_univ";
val Pair_in_univ = thm "Pair_in_univ";
val Union_in_univ = thm "Union_in_univ";
val product_univ = thm "product_univ";
val nat_subset_univ = thm "nat_subset_univ";
val nat_into_univ = thm "nat_into_univ";
val one_in_univ = thm "one_in_univ";
val two_in_univ = thm "two_in_univ";
val bool_subset_univ = thm "bool_subset_univ";
val bool_into_univ = thm "bool_into_univ";
val Inl_in_univ = thm "Inl_in_univ";
val Inr_in_univ = thm "Inr_in_univ";
val sum_univ = thm "sum_univ";
val sum_subset_univ = thm "sum_subset_univ";
val Fin_VLimit = thm "Fin_VLimit";
val Fin_subset_VLimit = thm "Fin_subset_VLimit";
val Fin_univ = thm "Fin_univ";
val nat_fun_VLimit = thm "nat_fun_VLimit";
val nat_fun_subset_VLimit = thm "nat_fun_subset_VLimit";
val nat_fun_univ = thm "nat_fun_univ";
val FiniteFun_VLimit1 = thm "FiniteFun_VLimit1";
val FiniteFun_univ1 = thm "FiniteFun_univ1";
val FiniteFun_VLimit = thm "FiniteFun_VLimit";
val FiniteFun_univ = thm "FiniteFun_univ";
val FiniteFun_in_univ = thm "FiniteFun_in_univ";
val FiniteFun_in_univ' = thm "FiniteFun_in_univ'";
val doubleton_in_Vfrom_D = thm "doubleton_in_Vfrom_D";
val Vfrom_doubleton_D = thm "Vfrom_doubleton_D";
val Pair_in_Vfrom_D = thm "Pair_in_Vfrom_D";
val product_Int_Vfrom_subset = thm "product_Int_Vfrom_subset";

val rank_rls = thms "rank_rls";
val rank_ss = simpset() addsimps [VsetI] 
              addsimps rank_rls @ (rank_rls RLN (2, [lt_trans]));

*}

end
