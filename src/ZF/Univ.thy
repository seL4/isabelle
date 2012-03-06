(*  Title:      ZF/Univ.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Standard notation for Vset(i) is V(i), but users might want V for a
variable.

NOTE: univ(A) could be a translation; would simplify many proofs!
  But Ind_Syntax.univ refers to the constant "Univ.univ"
*)

header{*The Cumulative Hierarchy and a Small Universe for Recursive Types*}

theory Univ imports Epsilon Cardinal begin

definition
  Vfrom       :: "[i,i]=>i"  where
    "Vfrom(A,i) == transrec(i, %x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))"

abbreviation
  Vset :: "i=>i" where
  "Vset(x) == Vfrom(0,x)"


definition
  Vrec        :: "[i, [i,i]=>i] =>i"  where
    "Vrec(a,H) == transrec(rank(a), %x g. \<lambda>z\<in>Vset(succ(x)).
                           H(z, \<lambda>w\<in>Vset(x). g`rank(w)`w)) ` a"

definition
  Vrecursor   :: "[[i,i]=>i, i] =>i"  where
    "Vrecursor(H,a) == transrec(rank(a), %x g. \<lambda>z\<in>Vset(succ(x)).
                                H(\<lambda>w\<in>Vset(x). g`rank(w)`w, z)) ` a"

definition
  univ        :: "i=>i"  where
    "univ(A) == Vfrom(A,nat)"


subsection{*Immediate Consequences of the Definition of @{term "Vfrom(A,i)"}*}

text{*NOT SUITABLE FOR REWRITING -- RECURSIVE!*}
lemma Vfrom: "Vfrom(A,i) = A \<union> (\<Union>j\<in>i. Pow(Vfrom(A,j)))"
by (subst Vfrom_def [THEN def_transrec], simp)

subsubsection{* Monotonicity *}

lemma Vfrom_mono [rule_format]:
     "A<=B ==> \<forall>j. i<=j \<longrightarrow> Vfrom(A,i) \<subseteq> Vfrom(B,j)"
apply (rule_tac a=i in eps_induct)
apply (rule impI [THEN allI])
apply (subst Vfrom [of A])
apply (subst Vfrom [of B])
apply (erule Un_mono)
apply (erule UN_mono, blast)
done

lemma VfromI: "[| a \<in> Vfrom(A,j);  j<i |] ==> a \<in> Vfrom(A,i)"
by (blast dest: Vfrom_mono [OF subset_refl le_imp_subset [OF leI]])


subsubsection{* A fundamental equality: Vfrom does not require ordinals! *}



lemma Vfrom_rank_subset1: "Vfrom(A,x) \<subseteq> Vfrom(A,rank(x))"
proof (induct x rule: eps_induct)
  fix x
  assume "\<forall>y\<in>x. Vfrom(A,y) \<subseteq> Vfrom(A,rank(y))"
  thus "Vfrom(A, x) \<subseteq> Vfrom(A, rank(x))"
    by (simp add: Vfrom [of _ x] Vfrom [of _ "rank(x)"],
        blast intro!: rank_lt [THEN ltD])
qed

lemma Vfrom_rank_subset2: "Vfrom(A,rank(x)) \<subseteq> Vfrom(A,x)"
apply (rule_tac a=x in eps_induct)
apply (subst Vfrom)
apply (subst Vfrom, rule subset_refl [THEN Un_mono])
apply (rule UN_least)
txt{*expand @{text "rank(x1) = (\<Union>y\<in>x1. succ(rank(y)))"} in assumptions*}
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


subsection{* Basic Closure Properties *}

lemma zero_in_Vfrom: "y:x ==> 0 \<in> Vfrom(A,x)"
by (subst Vfrom, blast)

lemma i_subset_Vfrom: "i \<subseteq> Vfrom(A,i)"
apply (rule_tac a=i in eps_induct)
apply (subst Vfrom, blast)
done

lemma A_subset_Vfrom: "A \<subseteq> Vfrom(A,i)"
apply (subst Vfrom)
apply (rule Un_upper1)
done

lemmas A_into_Vfrom = A_subset_Vfrom [THEN subsetD]

lemma subset_mem_Vfrom: "a \<subseteq> Vfrom(A,i) ==> a \<in> Vfrom(A,succ(i))"
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

lemma succ_in_Vfrom: "a \<subseteq> Vfrom(A,i) ==> succ(a) \<in> Vfrom(A,succ(succ(i)))"
apply (intro subset_mem_Vfrom succ_subsetI, assumption)
apply (erule subset_trans)
apply (rule Vfrom_mono [OF subset_refl subset_succI])
done

subsection{* 0, Successor and Limit Equations for @{term Vfrom} *}

lemma Vfrom_0: "Vfrom(A,0) = A"
by (subst Vfrom, blast)

lemma Vfrom_succ_lemma: "Ord(i) ==> Vfrom(A,succ(i)) = A \<union> Pow(Vfrom(A,i))"
apply (rule Vfrom [THEN trans])
apply (rule equalityI [THEN subst_context,
                       OF _ succI1 [THEN RepFunI, THEN Union_upper]])
apply (rule UN_least)
apply (rule subset_refl [THEN Vfrom_mono, THEN Pow_mono])
apply (erule ltI [THEN le_imp_subset])
apply (erule Ord_succ)
done

lemma Vfrom_succ: "Vfrom(A,succ(i)) = A \<union> Pow(Vfrom(A,i))"
apply (rule_tac x1 = "succ (i)" in Vfrom_rank_eq [THEN subst])
apply (rule_tac x1 = i in Vfrom_rank_eq [THEN subst])
apply (subst rank_succ)
apply (rule Ord_rank [THEN Vfrom_succ_lemma])
done

(*The premise distinguishes this from Vfrom(A,0);  allowing X=0 forces
  the conclusion to be Vfrom(A,\<Union>(X)) = A \<union> (\<Union>y\<in>X. Vfrom(A,y)) *)
lemma Vfrom_Union: "y:X ==> Vfrom(A,\<Union>(X)) = (\<Union>y\<in>X. Vfrom(A,y))"
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

subsection{* @{term Vfrom} applied to Limit Ordinals *}

(*NB. limit ordinals are non-empty:
      Vfrom(A,0) = A = A \<union> (\<Union>y\<in>0. Vfrom(A,y)) *)
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

lemma singleton_in_VLimit:
    "[| a \<in> Vfrom(A,i);  Limit(i) |] ==> {a} \<in> Vfrom(A,i)"
apply (erule Limit_VfromE, assumption)
apply (erule singleton_in_Vfrom [THEN VfromI])
apply (blast intro: Limit_has_succ)
done

lemmas Vfrom_UnI1 =
    Un_upper1 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD]]
lemmas Vfrom_UnI2 =
    Un_upper2 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD]]

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
txt{*Infer that @{term"succ(succ(x \<union> xa)) < i"} *}
apply (blast intro: VfromI [OF Pair_in_Vfrom]
                    Vfrom_UnI1 Vfrom_UnI2 Limit_has_succ Un_least_lt)
done

lemma product_VLimit: "Limit(i) ==> Vfrom(A,i) * Vfrom(A,i) \<subseteq> Vfrom(A,i)"
by (blast intro: Pair_in_VLimit)

lemmas Sigma_subset_VLimit =
     subset_trans [OF Sigma_mono product_VLimit]

lemmas nat_subset_VLimit =
     subset_trans [OF nat_le_Limit [THEN le_imp_subset] i_subset_Vfrom]

lemma nat_into_VLimit: "[| n: nat;  Limit(i) |] ==> n \<in> Vfrom(A,i)"
by (blast intro: nat_subset_VLimit [THEN subsetD])

subsubsection{* Closure under Disjoint Union *}

lemmas zero_in_VLimit = Limit_has_0 [THEN ltD, THEN zero_in_Vfrom]

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

lemma sum_VLimit: "Limit(i) ==> Vfrom(C,i)+Vfrom(C,i) \<subseteq> Vfrom(C,i)"
by (blast intro!: Inl_in_VLimit Inr_in_VLimit)

lemmas sum_subset_VLimit = subset_trans [OF sum_mono sum_VLimit]



subsection{* Properties assuming @{term "Transset(A)"} *}

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

lemma Transset_Pair_subset: "[| <a,b> \<subseteq> C; Transset(C) |] ==> a: C & b: C"
by (unfold Pair_def Transset_def, blast)

lemma Transset_Pair_subset_VLimit:
     "[| <a,b> \<subseteq> Vfrom(A,i);  Transset(A);  Limit(i) |]
      ==> <a,b> \<in> Vfrom(A,i)"
apply (erule Transset_Pair_subset [THEN conjE])
apply (erule Transset_Vfrom)
apply (blast intro: Pair_in_VLimit)
done

lemma Union_in_Vfrom:
     "[| X \<in> Vfrom(A,j);  Transset(A) |] ==> \<Union>(X) \<in> Vfrom(A, succ(j))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def, blast)
done

lemma Union_in_VLimit:
     "[| X \<in> Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \<Union>(X) \<in> Vfrom(A,i)"
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
               ==> \<exists>k. h(x,y) \<in> Vfrom(A,k) & k<i |]
   ==> h(a,b) \<in> Vfrom(A,i)"
txt{*Infer that a, b occur at ordinals x,xa < i.*}
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption, atomize)
apply (drule_tac x=a in spec)
apply (drule_tac x=b in spec)
apply (drule_tac x="x \<union> xa \<union> 2" in spec)
apply (simp add: Un_least_lt_iff lt_Ord Vfrom_UnI1 Vfrom_UnI2)
apply (blast intro: Limit_has_0 Limit_has_succ VfromI)
done

subsubsection{* Products *}

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

subsubsection{* Disjoint Sums, or Quine Ordered Pairs *}

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

subsubsection{* Function Space! *}

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


subsection{* The Set @{term "Vset(i)"} *}

lemma Vset: "Vset(i) = (\<Union>j\<in>i. Pow(Vset(j)))"
by (subst Vfrom, blast)

lemmas Vset_succ = Transset_0 [THEN Transset_Vfrom_succ]
lemmas Transset_Vset = Transset_0 [THEN Transset_Vfrom]

subsubsection{* Characterisation of the elements of @{term "Vset(i)"} *}

lemma VsetD [rule_format]: "Ord(i) ==> \<forall>b. b \<in> Vset(i) \<longrightarrow> rank(b) < i"
apply (erule trans_induct)
apply (subst Vset, safe)
apply (subst rank)
apply (blast intro: ltI UN_succ_least_lt)
done

lemma VsetI_lemma [rule_format]:
     "Ord(i) ==> \<forall>b. rank(b) \<in> i \<longrightarrow> b \<in> Vset(i)"
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

lemma Finite_Vset: "i \<in> nat ==> Finite(Vset(i))";
apply (erule nat_induct)
 apply (simp add: Vfrom_0)
apply (simp add: Vset_succ)
done

subsubsection{* Reasoning about Sets in Terms of Their Elements' Ranks *}

lemma arg_subset_Vset_rank: "a \<subseteq> Vset(rank(a))"
apply (rule subsetI)
apply (erule rank_lt [THEN VsetI])
done

lemma Int_Vset_subset:
    "[| !!i. Ord(i) ==> a \<inter> Vset(i) \<subseteq> b |] ==> a \<subseteq> b"
apply (rule subset_trans)
apply (rule Int_greatest [OF subset_refl arg_subset_Vset_rank])
apply (blast intro: Ord_rank)
done

subsubsection{* Set Up an Environment for Simplification *}

lemma rank_Inl: "rank(a) < rank(Inl(a))"
apply (unfold Inl_def)
apply (rule rank_pair2)
done

lemma rank_Inr: "rank(a) < rank(Inr(a))"
apply (unfold Inr_def)
apply (rule rank_pair2)
done

lemmas rank_rls = rank_Inl rank_Inr rank_pair1 rank_pair2

subsubsection{* Recursion over Vset Levels! *}

text{*NOT SUITABLE FOR REWRITING: recursive!*}
lemma Vrec: "Vrec(a,H) = H(a, \<lambda>x\<in>Vset(rank(a)). Vrec(x,H))"
apply (unfold Vrec_def)
apply (subst transrec, simp)
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text{*This form avoids giant explosions in proofs.  NOTE USE OF == *}
lemma def_Vrec:
    "[| !!x. h(x)==Vrec(x,H) |] ==>
     h(a) = H(a, \<lambda>x\<in>Vset(rank(a)). h(x))"
apply simp
apply (rule Vrec)
done

text{*NOT SUITABLE FOR REWRITING: recursive!*}
lemma Vrecursor:
     "Vrecursor(H,a) = H(\<lambda>x\<in>Vset(rank(a)). Vrecursor(H,x),  a)"
apply (unfold Vrecursor_def)
apply (subst transrec, simp)
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text{*This form avoids giant explosions in proofs.  NOTE USE OF == *}
lemma def_Vrecursor:
     "h == Vrecursor(H) ==> h(a) = H(\<lambda>x\<in>Vset(rank(a)). h(x),  a)"
apply simp
apply (rule Vrecursor)
done


subsection{* The Datatype Universe: @{term "univ(A)"} *}

lemma univ_mono: "A<=B ==> univ(A) \<subseteq> univ(B)"
apply (unfold univ_def)
apply (erule Vfrom_mono)
apply (rule subset_refl)
done

lemma Transset_univ: "Transset(A) ==> Transset(univ(A))"
apply (unfold univ_def)
apply (erule Transset_Vfrom)
done

subsubsection{* The Set @{term"univ(A)"} as a Limit *}

lemma univ_eq_UN: "univ(A) = (\<Union>i\<in>nat. Vfrom(A,i))"
apply (unfold univ_def)
apply (rule Limit_nat [THEN Limit_Vfrom_eq])
done

lemma subset_univ_eq_Int: "c \<subseteq> univ(A) ==> c = (\<Union>i\<in>nat. c \<inter> Vfrom(A,i))"
apply (rule subset_UN_iff_eq [THEN iffD1])
apply (erule univ_eq_UN [THEN subst])
done

lemma univ_Int_Vfrom_subset:
    "[| a \<subseteq> univ(X);
        !!i. i:nat ==> a \<inter> Vfrom(X,i) \<subseteq> b |]
     ==> a \<subseteq> b"
apply (subst subset_univ_eq_Int, assumption)
apply (rule UN_least, simp)
done

lemma univ_Int_Vfrom_eq:
    "[| a \<subseteq> univ(X);   b \<subseteq> univ(X);
        !!i. i:nat ==> a \<inter> Vfrom(X,i) = b \<inter> Vfrom(X,i)
     |] ==> a = b"
apply (rule equalityI)
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE)
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE)
done

subsection{* Closure Properties for @{term "univ(A)"}*}

lemma zero_in_univ: "0 \<in> univ(A)"
apply (unfold univ_def)
apply (rule nat_0I [THEN zero_in_Vfrom])
done

lemma zero_subset_univ: "{0} \<subseteq> univ(A)"
by (blast intro: zero_in_univ)

lemma A_subset_univ: "A \<subseteq> univ(A)"
apply (unfold univ_def)
apply (rule A_subset_Vfrom)
done

lemmas A_into_univ = A_subset_univ [THEN subsetD]

subsubsection{* Closure under Unordered and Ordered Pairs *}

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
     "[| X: univ(A);  Transset(A) |] ==> \<Union>(X) \<in> univ(A)"
apply (unfold univ_def)
apply (blast intro: Union_in_VLimit Limit_nat)
done

lemma product_univ: "univ(A)*univ(A) \<subseteq> univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN product_VLimit])
done


subsubsection{* The Natural Numbers *}

lemma nat_subset_univ: "nat \<subseteq> univ(A)"
apply (unfold univ_def)
apply (rule i_subset_Vfrom)
done

text{* n:nat ==> n:univ(A) *}
lemmas nat_into_univ = nat_subset_univ [THEN subsetD]

subsubsection{* Instances for 1 and 2 *}

lemma one_in_univ: "1 \<in> univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN one_in_VLimit])
done

text{*unused!*}
lemma two_in_univ: "2 \<in> univ(A)"
by (blast intro: nat_into_univ)

lemma bool_subset_univ: "bool \<subseteq> univ(A)"
apply (unfold bool_def)
apply (blast intro!: zero_in_univ one_in_univ)
done

lemmas bool_into_univ = bool_subset_univ [THEN subsetD]


subsubsection{* Closure under Disjoint Union *}

lemma Inl_in_univ: "a: univ(A) ==> Inl(a) \<in> univ(A)"
apply (unfold univ_def)
apply (erule Inl_in_VLimit [OF _ Limit_nat])
done

lemma Inr_in_univ: "b: univ(A) ==> Inr(b) \<in> univ(A)"
apply (unfold univ_def)
apply (erule Inr_in_VLimit [OF _ Limit_nat])
done

lemma sum_univ: "univ(C)+univ(C) \<subseteq> univ(C)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN sum_VLimit])
done

lemmas sum_subset_univ = subset_trans [OF sum_mono sum_univ]

lemma Sigma_subset_univ:
  "[|A \<subseteq> univ(D); \<And>x. x \<in> A \<Longrightarrow> B(x) \<subseteq> univ(D)|] ==> Sigma(A,B) \<subseteq> univ(D)"
apply (simp add: univ_def)
apply (blast intro: Sigma_subset_VLimit del: subsetI)
done


(*Closure under binary union -- use Un_least
  Closure under Collect -- use  Collect_subset [THEN subset_trans]
  Closure under RepFun -- use   RepFun_subset *)


subsection{* Finite Branching Closure Properties *}

subsubsection{* Closure under Finite Powerset *}

lemma Fin_Vfrom_lemma:
     "[| b: Fin(Vfrom(A,i));  Limit(i) |] ==> \<exists>j. b \<subseteq> Vfrom(A,j) & j<i"
apply (erule Fin_induct)
apply (blast dest!: Limit_has_0, safe)
apply (erule Limit_VfromE, assumption)
apply (blast intro!: Un_least_lt intro: Vfrom_UnI1 Vfrom_UnI2)
done

lemma Fin_VLimit: "Limit(i) ==> Fin(Vfrom(A,i)) \<subseteq> Vfrom(A,i)"
apply (rule subsetI)
apply (drule Fin_Vfrom_lemma, safe)
apply (rule Vfrom [THEN ssubst])
apply (blast dest!: ltD)
done

lemmas Fin_subset_VLimit = subset_trans [OF Fin_mono Fin_VLimit]

lemma Fin_univ: "Fin(univ(A)) \<subseteq> univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN Fin_VLimit])
done

subsubsection{* Closure under Finite Powers: Functions from a Natural Number *}

lemma nat_fun_VLimit:
     "[| n: nat;  Limit(i) |] ==> n -> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (erule nat_fun_subset_Fin [THEN subset_trans])
apply (blast del: subsetI
    intro: subset_refl Fin_subset_VLimit Sigma_subset_VLimit nat_subset_VLimit)
done

lemmas nat_fun_subset_VLimit = subset_trans [OF Pi_mono nat_fun_VLimit]

lemma nat_fun_univ: "n: nat ==> n -> univ(A) \<subseteq> univ(A)"
apply (unfold univ_def)
apply (erule nat_fun_VLimit [OF _ Limit_nat])
done


subsubsection{* Closure under Finite Function Space *}

text{*General but seldom-used version; normally the domain is fixed*}
lemma FiniteFun_VLimit1:
     "Limit(i) ==> Vfrom(A,i) -||> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (rule FiniteFun.dom_subset [THEN subset_trans])
apply (blast del: subsetI
             intro: Fin_subset_VLimit Sigma_subset_VLimit subset_refl)
done

lemma FiniteFun_univ1: "univ(A) -||> univ(A) \<subseteq> univ(A)"
apply (unfold univ_def)
apply (rule Limit_nat [THEN FiniteFun_VLimit1])
done

text{*Version for a fixed domain*}
lemma FiniteFun_VLimit:
     "[| W \<subseteq> Vfrom(A,i); Limit(i) |] ==> W -||> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (rule subset_trans)
apply (erule FiniteFun_mono [OF _ subset_refl])
apply (erule FiniteFun_VLimit1)
done

lemma FiniteFun_univ:
    "W \<subseteq> univ(A) ==> W -||> univ(A) \<subseteq> univ(A)"
apply (unfold univ_def)
apply (erule FiniteFun_VLimit [OF _ Limit_nat])
done

lemma FiniteFun_in_univ:
     "[| f: W -||> univ(A);  W \<subseteq> univ(A) |] ==> f \<in> univ(A)"
by (erule FiniteFun_univ [THEN subsetD], assumption)

text{*Remove @{text "\<subseteq>"} from the rule above*}
lemmas FiniteFun_in_univ' = FiniteFun_in_univ [OF _ subsetI]


subsection{** For QUniv.  Properties of Vfrom analogous to the "take-lemma" **}

text{* Intersecting a*b with Vfrom... *}

text{*This version says a, b exist one level down, in the smaller set Vfrom(X,i)*}
lemma doubleton_in_Vfrom_D:
     "[| {a,b} \<in> Vfrom(X,succ(i));  Transset(X) |]
      ==> a \<in> Vfrom(X,i)  &  b \<in> Vfrom(X,i)"
by (drule Transset_Vfrom_succ [THEN equalityD1, THEN subsetD, THEN PowD],
    assumption, fast)

text{*This weaker version says a, b exist at the same level*}
lemmas Vfrom_doubleton_D = Transset_Vfrom [THEN Transset_doubleton_D]

(** Using only the weaker theorem would prove <a,b> : Vfrom(X,i)
      implies a, b : Vfrom(X,i), which is useless for induction.
    Using only the stronger theorem would prove <a,b> : Vfrom(X,succ(succ(i)))
      implies a, b : Vfrom(X,i), leaving the succ(i) case untreated.
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
      (a*b) \<inter> Vfrom(X, succ(i)) \<subseteq> (a \<inter> Vfrom(X,i)) * (b \<inter> Vfrom(X,i))"
by (blast dest!: Pair_in_Vfrom_D)


ML
{*
val rank_ss = @{simpset} addsimps [@{thm VsetI}]
              addsimps @{thms rank_rls} @ (@{thms rank_rls} RLN (2, [@{thm lt_trans}]));
*}

end
