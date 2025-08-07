(*  Title:      ZF/Univ.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Standard notation for Vset(i) is V(i), but users might want V for a
variable.

NOTE: univ(A) could be a translation; would simplify many proofs!
  But Ind_Syntax.univ refers to the constant "Univ.univ"
*)

section\<open>The Cumulative Hierarchy and a Small Universe for Recursive Types\<close>

theory Univ imports Epsilon Cardinal begin

definition
  Vfrom       :: "[i,i]\<Rightarrow>i"  where
    "Vfrom(A,i) \<equiv> transrec(i, \<lambda>x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))"

abbreviation
  Vset :: "i\<Rightarrow>i" where
  "Vset(x) \<equiv> Vfrom(0,x)"


definition
  Vrec        :: "[i, [i,i]\<Rightarrow>i] \<Rightarrow>i"  where
    "Vrec(a,H) \<equiv> transrec(rank(a), \<lambda>x g. \<lambda>z\<in>Vset(succ(x)).
                           H(z, \<lambda>w\<in>Vset(x). g`rank(w)`w)) ` a"

definition
  Vrecursor   :: "[[i,i]\<Rightarrow>i, i] \<Rightarrow>i"  where
    "Vrecursor(H,a) \<equiv> transrec(rank(a), \<lambda>x g. \<lambda>z\<in>Vset(succ(x)).
                                H(\<lambda>w\<in>Vset(x). g`rank(w)`w, z)) ` a"

definition
  univ        :: "i\<Rightarrow>i"  where
    "univ(A) \<equiv> Vfrom(A,nat)"


subsection\<open>Immediate Consequences of the Definition of \<^term>\<open>Vfrom(A,i)\<close>\<close>

text\<open>NOT SUITABLE FOR REWRITING -- RECURSIVE!\<close>
lemma Vfrom: "Vfrom(A,i) = A \<union> (\<Union>j\<in>i. Pow(Vfrom(A,j)))"
by (subst Vfrom_def [THEN def_transrec], simp)

subsubsection\<open>Monotonicity\<close>

lemma Vfrom_mono [rule_format]:
     "A<=B \<Longrightarrow> \<forall>j. i<=j \<longrightarrow> Vfrom(A,i) \<subseteq> Vfrom(B,j)"
apply (rule_tac a=i in eps_induct)
apply (rule impI [THEN allI])
apply (subst Vfrom [of A])
apply (subst Vfrom [of B])
apply (erule Un_mono)
apply (erule UN_mono, blast)
done

lemma VfromI: "\<lbrakk>a \<in> Vfrom(A,j);  j<i\<rbrakk> \<Longrightarrow> a \<in> Vfrom(A,i)"
by (blast dest: Vfrom_mono [OF subset_refl le_imp_subset [OF leI]])


subsubsection\<open>A fundamental equality: Vfrom does not require ordinals!\<close>



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
txt\<open>expand \<open>rank(x1) = (\<Union>y\<in>x1. succ(rank(y)))\<close> in assumptions\<close>
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


subsection\<open>Basic Closure Properties\<close>

lemma zero_in_Vfrom: "y:x \<Longrightarrow> 0 \<in> Vfrom(A,x)"
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

lemma subset_mem_Vfrom: "a \<subseteq> Vfrom(A,i) \<Longrightarrow> a \<in> Vfrom(A,succ(i))"
by (subst Vfrom, blast)

subsubsection\<open>Finite sets and ordered pairs\<close>

lemma singleton_in_Vfrom: "a \<in> Vfrom(A,i) \<Longrightarrow> {a} \<in> Vfrom(A,succ(i))"
by (rule subset_mem_Vfrom, safe)

lemma doubleton_in_Vfrom:
     "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i)\<rbrakk> \<Longrightarrow> {a,b} \<in> Vfrom(A,succ(i))"
by (rule subset_mem_Vfrom, safe)

lemma Pair_in_Vfrom:
    "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> Vfrom(A,succ(succ(i)))"
  unfolding Pair_def
apply (blast intro: doubleton_in_Vfrom)
done

lemma succ_in_Vfrom: "a \<subseteq> Vfrom(A,i) \<Longrightarrow> succ(a) \<in> Vfrom(A,succ(succ(i)))"
apply (intro subset_mem_Vfrom succ_subsetI, assumption)
apply (erule subset_trans)
apply (rule Vfrom_mono [OF subset_refl subset_succI])
done

subsection\<open>0, Successor and Limit Equations for \<^term>\<open>Vfrom\<close>\<close>

lemma Vfrom_0: "Vfrom(A,0) = A"
by (subst Vfrom, blast)

lemma Vfrom_succ_lemma: "Ord(i) \<Longrightarrow> Vfrom(A,succ(i)) = A \<union> Pow(Vfrom(A,i))"
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
lemma Vfrom_Union: "y:X \<Longrightarrow> Vfrom(A,\<Union>(X)) = (\<Union>y\<in>X. Vfrom(A,y))"
apply (subst Vfrom)
apply (rule equalityI)
txt\<open>first inclusion\<close>
apply (rule Un_least)
apply (rule A_subset_Vfrom [THEN subset_trans])
apply (rule UN_upper, assumption)
apply (rule UN_least)
apply (erule UnionE)
apply (rule subset_trans)
apply (erule_tac [2] UN_upper,
       subst Vfrom, erule subset_trans [OF UN_upper Un_upper2])
txt\<open>opposite inclusion\<close>
apply (rule UN_least)
apply (subst Vfrom, blast)
done

subsection\<open>\<^term>\<open>Vfrom\<close> applied to Limit Ordinals\<close>

(*NB. limit ordinals are non-empty:
      Vfrom(A,0) = A = A \<union> (\<Union>y\<in>0. Vfrom(A,y)) *)
lemma Limit_Vfrom_eq:
    "Limit(i) \<Longrightarrow> Vfrom(A,i) = (\<Union>y\<in>i. Vfrom(A,y))"
apply (rule Limit_has_0 [THEN ltD, THEN Vfrom_Union, THEN subst], assumption)
apply (simp add: Limit_Union_eq)
done

lemma Limit_VfromE:
    "\<lbrakk>a \<in> Vfrom(A,i);  \<not>R \<Longrightarrow> Limit(i);
        \<And>x. \<lbrakk>x<i;  a \<in> Vfrom(A,x)\<rbrakk> \<Longrightarrow> R
\<rbrakk> \<Longrightarrow> R"
apply (rule classical)
apply (rule Limit_Vfrom_eq [THEN equalityD1, THEN subsetD, THEN UN_E])
  prefer 2 apply assumption
 apply blast
apply (blast intro: ltI Limit_is_Ord)
done

lemma singleton_in_VLimit:
    "\<lbrakk>a \<in> Vfrom(A,i);  Limit(i)\<rbrakk> \<Longrightarrow> {a} \<in> Vfrom(A,i)"
apply (erule Limit_VfromE, assumption)
apply (erule singleton_in_Vfrom [THEN VfromI])
apply (blast intro: Limit_has_succ)
done

lemmas Vfrom_UnI1 =
    Un_upper1 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD]]
lemmas Vfrom_UnI2 =
    Un_upper2 [THEN subset_refl [THEN Vfrom_mono, THEN subsetD]]

text\<open>Hard work is finding a single j:i such that {a,b}<=Vfrom(A,j)\<close>
lemma doubleton_in_VLimit:
    "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i)\<rbrakk> \<Longrightarrow> {a,b} \<in> Vfrom(A,i)"
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption)
apply (blast intro:  VfromI [OF doubleton_in_Vfrom]
                     Vfrom_UnI1 Vfrom_UnI2 Limit_has_succ Un_least_lt)
done

lemma Pair_in_VLimit:
    "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> Vfrom(A,i)"
txt\<open>Infer that a, b occur at ordinals x,xa < i.\<close>
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption)
txt\<open>Infer that \<^term>\<open>succ(succ(x \<union> xa)) < i\<close>\<close>
apply (blast intro: VfromI [OF Pair_in_Vfrom]
                    Vfrom_UnI1 Vfrom_UnI2 Limit_has_succ Un_least_lt)
done

lemma product_VLimit: "Limit(i) \<Longrightarrow> Vfrom(A,i) * Vfrom(A,i) \<subseteq> Vfrom(A,i)"
by (blast intro: Pair_in_VLimit)

lemmas Sigma_subset_VLimit =
     subset_trans [OF Sigma_mono product_VLimit]

lemmas nat_subset_VLimit =
     subset_trans [OF nat_le_Limit [THEN le_imp_subset] i_subset_Vfrom]

lemma nat_into_VLimit: "\<lbrakk>n: nat;  Limit(i)\<rbrakk> \<Longrightarrow> n \<in> Vfrom(A,i)"
by (blast intro: nat_subset_VLimit [THEN subsetD])

subsubsection\<open>Closure under Disjoint Union\<close>

lemmas zero_in_VLimit = Limit_has_0 [THEN ltD, THEN zero_in_Vfrom]

lemma one_in_VLimit: "Limit(i) \<Longrightarrow> 1 \<in> Vfrom(A,i)"
by (blast intro: nat_into_VLimit)

lemma Inl_in_VLimit:
    "\<lbrakk>a \<in> Vfrom(A,i); Limit(i)\<rbrakk> \<Longrightarrow> Inl(a) \<in> Vfrom(A,i)"
  unfolding Inl_def
apply (blast intro: zero_in_VLimit Pair_in_VLimit)
done

lemma Inr_in_VLimit:
    "\<lbrakk>b \<in> Vfrom(A,i); Limit(i)\<rbrakk> \<Longrightarrow> Inr(b) \<in> Vfrom(A,i)"
  unfolding Inr_def
apply (blast intro: one_in_VLimit Pair_in_VLimit)
done

lemma sum_VLimit: "Limit(i) \<Longrightarrow> Vfrom(C,i)+Vfrom(C,i) \<subseteq> Vfrom(C,i)"
by (blast intro!: Inl_in_VLimit Inr_in_VLimit)

lemmas sum_subset_VLimit = subset_trans [OF sum_mono sum_VLimit]



subsection\<open>Properties assuming \<^term>\<open>Transset(A)\<close>\<close>

lemma Transset_Vfrom: "Transset(A) \<Longrightarrow> Transset(Vfrom(A,i))"
apply (rule_tac a=i in eps_induct)
apply (subst Vfrom)
apply (blast intro!: Transset_Union_family Transset_Un Transset_Pow)
done

lemma Transset_Vfrom_succ:
     "Transset(A) \<Longrightarrow> Vfrom(A, succ(i)) = Pow(Vfrom(A,i))"
apply (rule Vfrom_succ [THEN trans])
apply (rule equalityI [OF _ Un_upper2])
apply (rule Un_least [OF _ subset_refl])
apply (rule A_subset_Vfrom [THEN subset_trans])
apply (erule Transset_Vfrom [THEN Transset_iff_Pow [THEN iffD1]])
done

lemma Transset_Pair_subset: "\<lbrakk>\<langle>a,b\<rangle> \<subseteq> C; Transset(C)\<rbrakk> \<Longrightarrow> a: C \<and> b: C"
by (unfold Pair_def Transset_def, blast)

lemma Transset_Pair_subset_VLimit:
     "\<lbrakk>\<langle>a,b\<rangle> \<subseteq> Vfrom(A,i);  Transset(A);  Limit(i)\<rbrakk>
      \<Longrightarrow> \<langle>a,b\<rangle> \<in> Vfrom(A,i)"
apply (erule Transset_Pair_subset [THEN conjE])
apply (erule Transset_Vfrom)
apply (blast intro: Pair_in_VLimit)
done

lemma Union_in_Vfrom:
     "\<lbrakk>X \<in> Vfrom(A,j);  Transset(A)\<rbrakk> \<Longrightarrow> \<Union>(X) \<in> Vfrom(A, succ(j))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def, blast)
done

lemma Union_in_VLimit:
     "\<lbrakk>X \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk> \<Longrightarrow> \<Union>(X) \<in> Vfrom(A,i)"
apply (rule Limit_VfromE, assumption+)
apply (blast intro: Limit_has_succ VfromI Union_in_Vfrom)
done


(*** Closure under product/sum applied to elements -- thus Vfrom(A,i)
     is a model of simple type theory provided A is a transitive set
     and i is a limit ordinal
***)

text\<open>General theorem for membership in Vfrom(A,i) when i is a limit ordinal\<close>
lemma in_VLimit:
  "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);
      \<And>x y j. \<lbrakk>j<i; 1:j; x \<in> Vfrom(A,j); y \<in> Vfrom(A,j)\<rbrakk>
               \<Longrightarrow> \<exists>k. h(x,y) \<in> Vfrom(A,k) \<and> k<i\<rbrakk>
   \<Longrightarrow> h(a,b) \<in> Vfrom(A,i)"
txt\<open>Infer that a, b occur at ordinals x,xa < i.\<close>
apply (erule Limit_VfromE, assumption)
apply (erule Limit_VfromE, assumption, atomize)
apply (drule_tac x=a in spec)
apply (drule_tac x=b in spec)
apply (drule_tac x="x \<union> xa \<union> 2" in spec)
apply (simp add: Un_least_lt_iff lt_Ord Vfrom_UnI1 Vfrom_UnI2)
apply (blast intro: Limit_has_0 Limit_has_succ VfromI)
done

subsubsection\<open>Products\<close>

lemma prod_in_Vfrom:
    "\<lbrakk>a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A)\<rbrakk>
     \<Longrightarrow> a*b \<in> Vfrom(A, succ(succ(succ(j))))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
  unfolding Transset_def
apply (blast intro: Pair_in_Vfrom)
done

lemma prod_in_VLimit:
  "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk>
   \<Longrightarrow> a*b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: prod_in_Vfrom Limit_has_succ)
done

subsubsection\<open>Disjoint Sums, or Quine Ordered Pairs\<close>

lemma sum_in_Vfrom:
    "\<lbrakk>a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A);  1:j\<rbrakk>
     \<Longrightarrow> a+b \<in> Vfrom(A, succ(succ(succ(j))))"
  unfolding sum_def
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
  unfolding Transset_def
apply (blast intro: zero_in_Vfrom Pair_in_Vfrom i_subset_Vfrom [THEN subsetD])
done

lemma sum_in_VLimit:
  "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk>
   \<Longrightarrow> a+b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: sum_in_Vfrom Limit_has_succ)
done

subsubsection\<open>Function Space!\<close>

lemma fun_in_Vfrom:
    "\<lbrakk>a \<in> Vfrom(A,j);  b \<in> Vfrom(A,j);  Transset(A)\<rbrakk> \<Longrightarrow>
          a->b \<in> Vfrom(A, succ(succ(succ(succ(j)))))"
  unfolding Pi_def
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (rule Collect_subset [THEN subset_trans])
apply (subst Vfrom)
apply (rule subset_trans [THEN subset_trans])
apply (rule_tac [3] Un_upper2)
apply (rule_tac [2] succI1 [THEN UN_upper])
apply (rule Pow_mono)
  unfolding Transset_def
apply (blast intro: Pair_in_Vfrom)
done

lemma fun_in_VLimit:
  "\<lbrakk>a \<in> Vfrom(A,i);  b \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk>
   \<Longrightarrow> a->b \<in> Vfrom(A,i)"
apply (erule in_VLimit, assumption+)
apply (blast intro: fun_in_Vfrom Limit_has_succ)
done

lemma Pow_in_Vfrom:
    "\<lbrakk>a \<in> Vfrom(A,j);  Transset(A)\<rbrakk> \<Longrightarrow> Pow(a) \<in> Vfrom(A, succ(succ(j)))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
  unfolding Transset_def
apply (subst Vfrom, blast)
done

lemma Pow_in_VLimit:
     "\<lbrakk>a \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk> \<Longrightarrow> Pow(a) \<in> Vfrom(A,i)"
by (blast elim: Limit_VfromE intro: Limit_has_succ Pow_in_Vfrom VfromI)


subsection\<open>The Set \<^term>\<open>Vset(i)\<close>\<close>

lemma Vset: "Vset(i) = (\<Union>j\<in>i. Pow(Vset(j)))"
by (subst Vfrom, blast)

lemmas Vset_succ = Transset_0 [THEN Transset_Vfrom_succ]
lemmas Transset_Vset = Transset_0 [THEN Transset_Vfrom]

subsubsection\<open>Characterisation of the elements of \<^term>\<open>Vset(i)\<close>\<close>

lemma VsetD [rule_format]: "Ord(i) \<Longrightarrow> \<forall>b. b \<in> Vset(i) \<longrightarrow> rank(b) < i"
apply (erule trans_induct)
apply (subst Vset, safe)
apply (subst rank)
apply (blast intro: ltI UN_succ_least_lt)
done

lemma VsetI_lemma [rule_format]:
     "Ord(i) \<Longrightarrow> \<forall>b. rank(b) \<in> i \<longrightarrow> b \<in> Vset(i)"
apply (erule trans_induct)
apply (rule allI)
apply (subst Vset)
apply (blast intro!: rank_lt [THEN ltD])
done

lemma VsetI: "rank(x)<i \<Longrightarrow> x \<in> Vset(i)"
by (blast intro: VsetI_lemma elim: ltE)

text\<open>Merely a lemma for the next result\<close>
lemma Vset_Ord_rank_iff: "Ord(i) \<Longrightarrow> b \<in> Vset(i) \<longleftrightarrow> rank(b) < i"
by (blast intro: VsetD VsetI)

lemma Vset_rank_iff [simp]: "b \<in> Vset(a) \<longleftrightarrow> rank(b) < rank(a)"
apply (rule Vfrom_rank_eq [THEN subst])
apply (rule Ord_rank [THEN Vset_Ord_rank_iff])
done

text\<open>This is rank(rank(a)) = rank(a)\<close>
declare Ord_rank [THEN rank_of_Ord, simp]

lemma rank_Vset: "Ord(i) \<Longrightarrow> rank(Vset(i)) = i"
apply (subst rank)
apply (rule equalityI, safe)
apply (blast intro: VsetD [THEN ltD])
apply (blast intro: VsetD [THEN ltD] Ord_trans)
apply (blast intro: i_subset_Vfrom [THEN subsetD]
                    Ord_in_Ord [THEN rank_of_Ord, THEN ssubst])
done

lemma Finite_Vset: "i \<in> nat \<Longrightarrow> Finite(Vset(i))"
apply (erule nat_induct)
 apply (simp add: Vfrom_0)
apply (simp add: Vset_succ)
done

subsubsection\<open>Reasoning about Sets in Terms of Their Elements' Ranks\<close>

lemma arg_subset_Vset_rank: "a \<subseteq> Vset(rank(a))"
apply (rule subsetI)
apply (erule rank_lt [THEN VsetI])
done

lemma Int_Vset_subset:
    "\<lbrakk>\<And>i. Ord(i) \<Longrightarrow> a \<inter> Vset(i) \<subseteq> b\<rbrakk> \<Longrightarrow> a \<subseteq> b"
apply (rule subset_trans)
apply (rule Int_greatest [OF subset_refl arg_subset_Vset_rank])
apply (blast intro: Ord_rank)
done

subsubsection\<open>Set Up an Environment for Simplification\<close>

lemma rank_Inl: "rank(a) < rank(Inl(a))"
  unfolding Inl_def
apply (rule rank_pair2)
done

lemma rank_Inr: "rank(a) < rank(Inr(a))"
  unfolding Inr_def
apply (rule rank_pair2)
done

lemmas rank_rls = rank_Inl rank_Inr rank_pair1 rank_pair2

subsubsection\<open>Recursion over Vset Levels!\<close>

text\<open>NOT SUITABLE FOR REWRITING: recursive!\<close>
lemma Vrec: "Vrec(a,H) = H(a, \<lambda>x\<in>Vset(rank(a)). Vrec(x,H))"
  unfolding Vrec_def
apply (subst transrec, simp)
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text\<open>This form avoids giant explosions in proofs. NOTE the form of the premise!\<close>
lemma def_Vrec:
    "\<lbrakk>\<And>x. h(x)\<equiv>Vrec(x,H)\<rbrakk> \<Longrightarrow>
     h(a) = H(a, \<lambda>x\<in>Vset(rank(a)). h(x))"
apply simp
apply (rule Vrec)
done

text\<open>NOT SUITABLE FOR REWRITING: recursive!\<close>
lemma Vrecursor:
     "Vrecursor(H,a) = H(\<lambda>x\<in>Vset(rank(a)). Vrecursor(H,x),  a)"
  unfolding Vrecursor_def
apply (subst transrec, simp)
apply (rule refl [THEN lam_cong, THEN subst_context], simp add: lt_def)
done

text\<open>This form avoids giant explosions in proofs. NOTE the form of the premise!\<close>
lemma def_Vrecursor:
     "h \<equiv> Vrecursor(H) \<Longrightarrow> h(a) = H(\<lambda>x\<in>Vset(rank(a)). h(x),  a)"
apply simp
apply (rule Vrecursor)
done


subsection\<open>The Datatype Universe: \<^term>\<open>univ(A)\<close>\<close>

lemma univ_mono: "A<=B \<Longrightarrow> univ(A) \<subseteq> univ(B)"
  unfolding univ_def
apply (erule Vfrom_mono)
apply (rule subset_refl)
done

lemma Transset_univ: "Transset(A) \<Longrightarrow> Transset(univ(A))"
  unfolding univ_def
apply (erule Transset_Vfrom)
done

subsubsection\<open>The Set \<^term>\<open>univ(A)\<close> as a Limit\<close>

lemma univ_eq_UN: "univ(A) = (\<Union>i\<in>nat. Vfrom(A,i))"
  unfolding univ_def
apply (rule Limit_nat [THEN Limit_Vfrom_eq])
done

lemma subset_univ_eq_Int: "c \<subseteq> univ(A) \<Longrightarrow> c = (\<Union>i\<in>nat. c \<inter> Vfrom(A,i))"
apply (rule subset_UN_iff_eq [THEN iffD1])
apply (erule univ_eq_UN [THEN subst])
done

lemma univ_Int_Vfrom_subset:
    "\<lbrakk>a \<subseteq> univ(X);
        \<And>i. i:nat \<Longrightarrow> a \<inter> Vfrom(X,i) \<subseteq> b\<rbrakk>
     \<Longrightarrow> a \<subseteq> b"
apply (subst subset_univ_eq_Int, assumption)
apply (rule UN_least, simp)
done

lemma univ_Int_Vfrom_eq:
    "\<lbrakk>a \<subseteq> univ(X);   b \<subseteq> univ(X);
        \<And>i. i:nat \<Longrightarrow> a \<inter> Vfrom(X,i) = b \<inter> Vfrom(X,i)
\<rbrakk> \<Longrightarrow> a = b"
apply (rule equalityI)
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE)
apply (rule univ_Int_Vfrom_subset, assumption)
apply (blast elim: equalityCE)
done

subsection\<open>Closure Properties for \<^term>\<open>univ(A)\<close>\<close>

lemma zero_in_univ: "0 \<in> univ(A)"
  unfolding univ_def
apply (rule nat_0I [THEN zero_in_Vfrom])
done

lemma zero_subset_univ: "{0} \<subseteq> univ(A)"
by (blast intro: zero_in_univ)

lemma A_subset_univ: "A \<subseteq> univ(A)"
  unfolding univ_def
apply (rule A_subset_Vfrom)
done

lemmas A_into_univ = A_subset_univ [THEN subsetD]

subsubsection\<open>Closure under Unordered and Ordered Pairs\<close>

lemma singleton_in_univ: "a: univ(A) \<Longrightarrow> {a} \<in> univ(A)"
  unfolding univ_def
apply (blast intro: singleton_in_VLimit Limit_nat)
done

lemma doubleton_in_univ:
    "\<lbrakk>a: univ(A);  b: univ(A)\<rbrakk> \<Longrightarrow> {a,b} \<in> univ(A)"
  unfolding univ_def
apply (blast intro: doubleton_in_VLimit Limit_nat)
done

lemma Pair_in_univ:
    "\<lbrakk>a: univ(A);  b: univ(A)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> univ(A)"
  unfolding univ_def
apply (blast intro: Pair_in_VLimit Limit_nat)
done

lemma Union_in_univ:
     "\<lbrakk>X: univ(A);  Transset(A)\<rbrakk> \<Longrightarrow> \<Union>(X) \<in> univ(A)"
  unfolding univ_def
apply (blast intro: Union_in_VLimit Limit_nat)
done

lemma product_univ: "univ(A)*univ(A) \<subseteq> univ(A)"
  unfolding univ_def
apply (rule Limit_nat [THEN product_VLimit])
done


subsubsection\<open>The Natural Numbers\<close>

lemma nat_subset_univ: "nat \<subseteq> univ(A)"
  unfolding univ_def
apply (rule i_subset_Vfrom)
done

lemma nat_into_univ: "n \<in> nat \<Longrightarrow> n \<in> univ(A)"
  by (rule nat_subset_univ [THEN subsetD])

subsubsection\<open>Instances for 1 and 2\<close>

lemma one_in_univ: "1 \<in> univ(A)"
  unfolding univ_def
apply (rule Limit_nat [THEN one_in_VLimit])
done

text\<open>unused!\<close>
lemma two_in_univ: "2 \<in> univ(A)"
by (blast intro: nat_into_univ)

lemma bool_subset_univ: "bool \<subseteq> univ(A)"
  unfolding bool_def
apply (blast intro!: zero_in_univ one_in_univ)
done

lemmas bool_into_univ = bool_subset_univ [THEN subsetD]


subsubsection\<open>Closure under Disjoint Union\<close>

lemma Inl_in_univ: "a: univ(A) \<Longrightarrow> Inl(a) \<in> univ(A)"
  unfolding univ_def
apply (erule Inl_in_VLimit [OF _ Limit_nat])
done

lemma Inr_in_univ: "b: univ(A) \<Longrightarrow> Inr(b) \<in> univ(A)"
  unfolding univ_def
apply (erule Inr_in_VLimit [OF _ Limit_nat])
done

lemma sum_univ: "univ(C)+univ(C) \<subseteq> univ(C)"
  unfolding univ_def
apply (rule Limit_nat [THEN sum_VLimit])
done

lemmas sum_subset_univ = subset_trans [OF sum_mono sum_univ]

lemma Sigma_subset_univ:
  "\<lbrakk>A \<subseteq> univ(D); \<And>x. x \<in> A \<Longrightarrow> B(x) \<subseteq> univ(D)\<rbrakk> \<Longrightarrow> Sigma(A,B) \<subseteq> univ(D)"
apply (simp add: univ_def)
apply (blast intro: Sigma_subset_VLimit del: subsetI)
done


(*Closure under binary union -- use Un_least
  Closure under Collect -- use  Collect_subset [THEN subset_trans]
  Closure under RepFun -- use   RepFun_subset *)


subsection\<open>Finite Branching Closure Properties\<close>

subsubsection\<open>Closure under Finite Powerset\<close>

lemma Fin_Vfrom_lemma:
     "\<lbrakk>b: Fin(Vfrom(A,i));  Limit(i)\<rbrakk> \<Longrightarrow> \<exists>j. b \<subseteq> Vfrom(A,j) \<and> j<i"
apply (erule Fin_induct)
apply (blast dest!: Limit_has_0, safe)
apply (erule Limit_VfromE, assumption)
apply (blast intro!: Un_least_lt intro: Vfrom_UnI1 Vfrom_UnI2)
done

lemma Fin_VLimit: "Limit(i) \<Longrightarrow> Fin(Vfrom(A,i)) \<subseteq> Vfrom(A,i)"
apply (rule subsetI)
apply (drule Fin_Vfrom_lemma, safe)
apply (rule Vfrom [THEN ssubst])
apply (blast dest!: ltD)
done

lemmas Fin_subset_VLimit = subset_trans [OF Fin_mono Fin_VLimit]

lemma Fin_univ: "Fin(univ(A)) \<subseteq> univ(A)"
  unfolding univ_def
apply (rule Limit_nat [THEN Fin_VLimit])
done

subsubsection\<open>Closure under Finite Powers: Functions from a Natural Number\<close>

lemma nat_fun_VLimit:
     "\<lbrakk>n: nat;  Limit(i)\<rbrakk> \<Longrightarrow> n -> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (erule nat_fun_subset_Fin [THEN subset_trans])
apply (blast del: subsetI
    intro: subset_refl Fin_subset_VLimit Sigma_subset_VLimit nat_subset_VLimit)
done

lemmas nat_fun_subset_VLimit = subset_trans [OF Pi_mono nat_fun_VLimit]

lemma nat_fun_univ: "n: nat \<Longrightarrow> n -> univ(A) \<subseteq> univ(A)"
  unfolding univ_def
apply (erule nat_fun_VLimit [OF _ Limit_nat])
done


subsubsection\<open>Closure under Finite Function Space\<close>

text\<open>General but seldom-used version; normally the domain is fixed\<close>
lemma FiniteFun_VLimit1:
     "Limit(i) \<Longrightarrow> Vfrom(A,i) -||> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (rule FiniteFun.dom_subset [THEN subset_trans])
apply (blast del: subsetI
             intro: Fin_subset_VLimit Sigma_subset_VLimit subset_refl)
done

lemma FiniteFun_univ1: "univ(A) -||> univ(A) \<subseteq> univ(A)"
  unfolding univ_def
apply (rule Limit_nat [THEN FiniteFun_VLimit1])
done

text\<open>Version for a fixed domain\<close>
lemma FiniteFun_VLimit:
     "\<lbrakk>W \<subseteq> Vfrom(A,i); Limit(i)\<rbrakk> \<Longrightarrow> W -||> Vfrom(A,i) \<subseteq> Vfrom(A,i)"
apply (rule subset_trans)
apply (erule FiniteFun_mono [OF _ subset_refl])
apply (erule FiniteFun_VLimit1)
done

lemma FiniteFun_univ:
    "W \<subseteq> univ(A) \<Longrightarrow> W -||> univ(A) \<subseteq> univ(A)"
  unfolding univ_def
apply (erule FiniteFun_VLimit [OF _ Limit_nat])
done

lemma FiniteFun_in_univ:
     "\<lbrakk>f: W -||> univ(A);  W \<subseteq> univ(A)\<rbrakk> \<Longrightarrow> f \<in> univ(A)"
by (erule FiniteFun_univ [THEN subsetD], assumption)

text\<open>Remove \<open>\<subseteq>\<close> from the rule above\<close>
lemmas FiniteFun_in_univ' = FiniteFun_in_univ [OF _ subsetI]


subsection\<open>* For QUniv.  Properties of Vfrom analogous to the "take-lemma" *\<close>

text\<open>Intersecting a*b with Vfrom...\<close>

text\<open>This version says a, b exist one level down, in the smaller set Vfrom(X,i)\<close>
lemma doubleton_in_Vfrom_D:
     "\<lbrakk>{a,b} \<in> Vfrom(X,succ(i));  Transset(X)\<rbrakk>
      \<Longrightarrow> a \<in> Vfrom(X,i)  \<and>  b \<in> Vfrom(X,i)"
by (drule Transset_Vfrom_succ [THEN equalityD1, THEN subsetD, THEN PowD],
    assumption, fast)

text\<open>This weaker version says a, b exist at the same level\<close>
lemmas Vfrom_doubleton_D = Transset_Vfrom [THEN Transset_doubleton_D]

(** Using only the weaker theorem would prove \<langle>a,b\<rangle> \<in> Vfrom(X,i)
      implies a, b \<in> Vfrom(X,i), which is useless for induction.
    Using only the stronger theorem would prove \<langle>a,b\<rangle> \<in> Vfrom(X,succ(succ(i)))
      implies a, b \<in> Vfrom(X,i), leaving the succ(i) case untreated.
    The combination gives a reduction by precisely one level, which is
      most convenient for proofs.
**)

lemma Pair_in_Vfrom_D:
    "\<lbrakk>\<langle>a,b\<rangle> \<in> Vfrom(X,succ(i));  Transset(X)\<rbrakk>
     \<Longrightarrow> a \<in> Vfrom(X,i)  \<and>  b \<in> Vfrom(X,i)"
  unfolding Pair_def
apply (blast dest!: doubleton_in_Vfrom_D Vfrom_doubleton_D)
done

lemma product_Int_Vfrom_subset:
     "Transset(X) \<Longrightarrow>
      (a*b) \<inter> Vfrom(X, succ(i)) \<subseteq> (a \<inter> Vfrom(X,i)) * (b \<inter> Vfrom(X,i))"
by (blast dest!: Pair_in_Vfrom_D)


ML
\<open>
val rank_ss =
  simpset_of (\<^context> |> Simplifier.add_simp @{thm VsetI}
    |> Simplifier.add_simps (@{thms rank_rls} @ (@{thms rank_rls} RLN (2, [@{thm lt_trans}]))));
\<close>

end
