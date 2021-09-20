(*  Title:      HOL/Library/Countable_Set.thy
    Author:     Johannes Hölzl
    Author:     Andrei Popescu
*)

section \<open>Countable sets\<close>

theory Countable_Set
imports Countable Infinite_Set
begin

subsection \<open>Predicate for countable sets\<close>

definition countable :: "'a set \<Rightarrow> bool" where
  "countable S \<longleftrightarrow> (\<exists>f::'a \<Rightarrow> nat. inj_on f S)"

lemma countableE:
  assumes S: "countable S" obtains f :: "'a \<Rightarrow> nat" where "inj_on f S"
  using S by (auto simp: countable_def)

lemma countableI: "inj_on (f::'a \<Rightarrow> nat) S \<Longrightarrow> countable S"
  by (auto simp: countable_def)

lemma countableI': "inj_on (f::'a \<Rightarrow> 'b::countable) S \<Longrightarrow> countable S"
  using comp_inj_on[of f S to_nat] by (auto intro: countableI)

lemma countableE_bij:
  assumes S: "countable S" obtains f :: "nat \<Rightarrow> 'a" and C :: "nat set" where "bij_betw f C S"
  using S by (blast elim: countableE dest: inj_on_imp_bij_betw bij_betw_inv)

lemma countableI_bij: "bij_betw f (C::nat set) S \<Longrightarrow> countable S"
  by (blast intro: countableI bij_betw_inv_into bij_betw_imp_inj_on)

lemma countable_finite: "finite S \<Longrightarrow> countable S"
  by (blast dest: finite_imp_inj_to_nat_seg countableI)

lemma countableI_bij1: "bij_betw f A B \<Longrightarrow> countable A \<Longrightarrow> countable B"
  by (blast elim: countableE_bij intro: bij_betw_trans countableI_bij)

lemma countableI_bij2: "bij_betw f B A \<Longrightarrow> countable A \<Longrightarrow> countable B"
  by (blast elim: countableE_bij intro: bij_betw_trans bij_betw_inv_into countableI_bij)

lemma countable_iff_bij[simp]: "bij_betw f A B \<Longrightarrow> countable A \<longleftrightarrow> countable B"
  by (blast intro: countableI_bij1 countableI_bij2)

lemma countable_subset: "A \<subseteq> B \<Longrightarrow> countable B \<Longrightarrow> countable A"
  by (auto simp: countable_def intro: subset_inj_on)

lemma countableI_type[intro, simp]: "countable (A:: 'a :: countable set)"
  using countableI[of to_nat A] by auto

subsection \<open>Enumerate a countable set\<close>

lemma countableE_infinite:
  assumes "countable S" "infinite S"
  obtains e :: "'a \<Rightarrow> nat" where "bij_betw e S UNIV"
proof -
  obtain f :: "'a \<Rightarrow> nat" where "inj_on f S"
    using \<open>countable S\<close> by (rule countableE)
  then have "bij_betw f S (f`S)"
    unfolding bij_betw_def by simp
  moreover
  from \<open>inj_on f S\<close> \<open>infinite S\<close> have inf_fS: "infinite (f`S)"
    by (auto dest: finite_imageD)
  then have "bij_betw (the_inv_into UNIV (enumerate (f`S))) (f`S) UNIV"
    by (intro bij_betw_the_inv_into bij_enumerate)
  ultimately have "bij_betw (the_inv_into UNIV (enumerate (f`S)) \<circ> f) S UNIV"
    by (rule bij_betw_trans)
  then show thesis ..
qed

lemma countable_infiniteE':
  assumes "countable A" "infinite A"
  obtains g where "bij_betw g (UNIV :: nat set) A"
  using bij_betw_inv[OF countableE_infinite[OF assms]] that by blast

lemma countable_enum_cases:
  assumes "countable S"
  obtains (finite) f :: "'a \<Rightarrow> nat" where "finite S" "bij_betw f S {..<card S}"
        | (infinite) f :: "'a \<Rightarrow> nat" where "infinite S" "bij_betw f S UNIV"
  using ex_bij_betw_finite_nat[of S] countableE_infinite \<open>countable S\<close>
  by (cases "finite S") (auto simp add: atLeast0LessThan)

definition to_nat_on :: "'a set \<Rightarrow> 'a \<Rightarrow> nat" where
  "to_nat_on S = (SOME f. if finite S then bij_betw f S {..< card S} else bij_betw f S UNIV)"

definition from_nat_into :: "'a set \<Rightarrow> nat \<Rightarrow> 'a" where
  "from_nat_into S n = (if n \<in> to_nat_on S ` S then inv_into S (to_nat_on S) n else SOME s. s\<in>S)"

lemma to_nat_on_finite: "finite S \<Longrightarrow> bij_betw (to_nat_on S) S {..< card S}"
  using ex_bij_betw_finite_nat unfolding to_nat_on_def
  by (intro someI2_ex[where Q="\<lambda>f. bij_betw f S {..<card S}"]) (auto simp add: atLeast0LessThan)

lemma to_nat_on_infinite: "countable S \<Longrightarrow> infinite S \<Longrightarrow> bij_betw (to_nat_on S) S UNIV"
  using countableE_infinite unfolding to_nat_on_def
  by (intro someI2_ex[where Q="\<lambda>f. bij_betw f S UNIV"]) auto

lemma bij_betw_from_nat_into_finite: "finite S \<Longrightarrow> bij_betw (from_nat_into S) {..< card S} S"
  unfolding from_nat_into_def[abs_def]
  using to_nat_on_finite[of S]
  apply (subst bij_betw_cong)
  apply (split if_split)
  apply (simp add: bij_betw_def)
  apply (auto cong: bij_betw_cong
              intro: bij_betw_inv_into to_nat_on_finite)
  done

lemma bij_betw_from_nat_into: "countable S \<Longrightarrow> infinite S \<Longrightarrow> bij_betw (from_nat_into S) UNIV S"
  unfolding from_nat_into_def[abs_def]
  using to_nat_on_infinite[of S, unfolded bij_betw_def]
  by (auto cong: bij_betw_cong intro: bij_betw_inv_into to_nat_on_infinite)

lemma countable_as_injective_image:
  assumes "countable A" "infinite A"
  obtains f :: "nat \<Rightarrow> 'a" where "A = range f" "inj f"
by (metis bij_betw_def bij_betw_from_nat_into [OF assms])

lemma inj_on_to_nat_on[intro]: "countable A \<Longrightarrow> inj_on (to_nat_on A) A"
  using to_nat_on_infinite[of A] to_nat_on_finite[of A]
  by (cases "finite A") (auto simp: bij_betw_def)

lemma to_nat_on_inj[simp]:
  "countable A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> to_nat_on A a = to_nat_on A b \<longleftrightarrow> a = b"
  using inj_on_to_nat_on[of A] by (auto dest: inj_onD)

lemma from_nat_into_to_nat_on[simp]: "countable A \<Longrightarrow> a \<in> A \<Longrightarrow> from_nat_into A (to_nat_on A a) = a"
  by (auto simp: from_nat_into_def intro!: inv_into_f_f)

lemma subset_range_from_nat_into: "countable A \<Longrightarrow> A \<subseteq> range (from_nat_into A)"
  by (auto intro: from_nat_into_to_nat_on[symmetric])

lemma from_nat_into: "A \<noteq> {} \<Longrightarrow> from_nat_into A n \<in> A"
  unfolding from_nat_into_def by (metis equals0I inv_into_into someI_ex)

lemma range_from_nat_into_subset: "A \<noteq> {} \<Longrightarrow> range (from_nat_into A) \<subseteq> A"
  using from_nat_into[of A] by auto

lemma range_from_nat_into[simp]: "A \<noteq> {} \<Longrightarrow> countable A \<Longrightarrow> range (from_nat_into A) = A"
  by (metis equalityI range_from_nat_into_subset subset_range_from_nat_into)

lemma image_to_nat_on: "countable A \<Longrightarrow> infinite A \<Longrightarrow> to_nat_on A ` A = UNIV"
  using to_nat_on_infinite[of A] by (simp add: bij_betw_def)

lemma to_nat_on_surj: "countable A \<Longrightarrow> infinite A \<Longrightarrow> \<exists>a\<in>A. to_nat_on A a = n"
  by (metis (no_types) image_iff iso_tuple_UNIV_I image_to_nat_on)

lemma to_nat_on_from_nat_into[simp]: "n \<in> to_nat_on A ` A \<Longrightarrow> to_nat_on A (from_nat_into A n) = n"
  by (simp add: f_inv_into_f from_nat_into_def)

lemma to_nat_on_from_nat_into_infinite[simp]:
  "countable A \<Longrightarrow> infinite A \<Longrightarrow> to_nat_on A (from_nat_into A n) = n"
  by (metis image_iff to_nat_on_surj to_nat_on_from_nat_into)

lemma from_nat_into_inj:
  "countable A \<Longrightarrow> m \<in> to_nat_on A ` A \<Longrightarrow> n \<in> to_nat_on A ` A \<Longrightarrow>
    from_nat_into A m = from_nat_into A n \<longleftrightarrow> m = n"
  by (subst to_nat_on_inj[symmetric, of A]) auto

lemma from_nat_into_inj_infinite[simp]:
  "countable A \<Longrightarrow> infinite A \<Longrightarrow> from_nat_into A m = from_nat_into A n \<longleftrightarrow> m = n"
  using image_to_nat_on[of A] from_nat_into_inj[of A m n] by simp

lemma eq_from_nat_into_iff:
  "countable A \<Longrightarrow> x \<in> A \<Longrightarrow> i \<in> to_nat_on A ` A \<Longrightarrow> x = from_nat_into A i \<longleftrightarrow> i = to_nat_on A x"
  by auto

lemma from_nat_into_surj: "countable A \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>n. from_nat_into A n = a"
  by (rule exI[of _ "to_nat_on A a"]) simp

lemma from_nat_into_inject[simp]:
  "A \<noteq> {} \<Longrightarrow> countable A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> countable B \<Longrightarrow> from_nat_into A = from_nat_into B \<longleftrightarrow> A = B"
  by (metis range_from_nat_into)

lemma inj_on_from_nat_into: "inj_on from_nat_into ({A. A \<noteq> {} \<and> countable A})"
  unfolding inj_on_def by auto

subsection \<open>Closure properties of countability\<close>

lemma countable_SIGMA[intro, simp]:
  "countable I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (A i)) \<Longrightarrow> countable (SIGMA i : I. A i)"
  by (intro countableI'[of "\<lambda>(i, a). (to_nat_on I i, to_nat_on (A i) a)"]) (auto simp: inj_on_def)

lemma countable_image[intro, simp]:
  assumes "countable A"
  shows "countable (f`A)"
proof -
  obtain g :: "'a \<Rightarrow> nat" where "inj_on g A"
    using assms by (rule countableE)
  moreover have "inj_on (inv_into A f) (f`A)" "inv_into A f ` f ` A \<subseteq> A"
    by (auto intro: inj_on_inv_into inv_into_into)
  ultimately show ?thesis
    by (blast dest: comp_inj_on subset_inj_on intro: countableI)
qed

lemma countable_image_inj_on: "countable (f ` A) \<Longrightarrow> inj_on f A \<Longrightarrow> countable A"
  by (metis countable_image the_inv_into_onto)

lemma countable_image_inj_Int_vimage:
   "\<lbrakk>inj_on f S; countable A\<rbrakk> \<Longrightarrow> countable (S \<inter> f -` A)"
  by (meson countable_image_inj_on countable_subset image_subset_iff_subset_vimage inf_le2 inj_on_Int)

lemma countable_image_inj_gen:
   "\<lbrakk>inj_on f S; countable A\<rbrakk> \<Longrightarrow> countable {x \<in> S. f x \<in> A}"
  using countable_image_inj_Int_vimage
  by (auto simp: vimage_def Collect_conj_eq)

lemma countable_image_inj_eq:
   "inj_on f S \<Longrightarrow> countable(f ` S) \<longleftrightarrow> countable S"
  using countable_image_inj_on by blast

lemma countable_image_inj:
   "\<lbrakk>countable A; inj f\<rbrakk> \<Longrightarrow> countable {x. f x \<in> A}"
  by (metis (mono_tags, lifting) countable_image_inj_eq countable_subset image_Collect_subsetI inj_on_inverseI the_inv_f_f)

lemma countable_UN[intro, simp]:
  fixes I :: "'i set" and A :: "'i => 'a set"
  assumes I: "countable I"
  assumes A: "\<And>i. i \<in> I \<Longrightarrow> countable (A i)"
  shows "countable (\<Union>i\<in>I. A i)"
proof -
  have "(\<Union>i\<in>I. A i) = snd ` (SIGMA i : I. A i)" by (auto simp: image_iff)
  then show ?thesis by (simp add: assms)
qed

lemma countable_Un[intro]: "countable A \<Longrightarrow> countable B \<Longrightarrow> countable (A \<union> B)"
  by (rule countable_UN[of "{True, False}" "\<lambda>True \<Rightarrow> A | False \<Rightarrow> B", simplified])
     (simp split: bool.split)

lemma countable_Un_iff[simp]: "countable (A \<union> B) \<longleftrightarrow> countable A \<and> countable B"
  by (metis countable_Un countable_subset inf_sup_ord(3,4))

lemma countable_Plus[intro, simp]:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> countable (A <+> B)"
  by (simp add: Plus_def)

lemma countable_empty[intro, simp]: "countable {}"
  by (blast intro: countable_finite)

lemma countable_insert[intro, simp]: "countable A \<Longrightarrow> countable (insert a A)"
  using countable_Un[of "{a}" A] by (auto simp: countable_finite)

lemma countable_Int1[intro, simp]: "countable A \<Longrightarrow> countable (A \<inter> B)"
  by (force intro: countable_subset)

lemma countable_Int2[intro, simp]: "countable B \<Longrightarrow> countable (A \<inter> B)"
  by (blast intro: countable_subset)

lemma countable_INT[intro, simp]: "i \<in> I \<Longrightarrow> countable (A i) \<Longrightarrow> countable (\<Inter>i\<in>I. A i)"
  by (blast intro: countable_subset)

lemma countable_Diff[intro, simp]: "countable A \<Longrightarrow> countable (A - B)"
  by (blast intro: countable_subset)

lemma countable_insert_eq [simp]: "countable (insert x A) = countable A"
    by auto (metis Diff_insert_absorb countable_Diff insert_absorb)

lemma countable_vimage: "B \<subseteq> range f \<Longrightarrow> countable (f -` B) \<Longrightarrow> countable B"
  by (metis Int_absorb2 countable_image image_vimage_eq)

lemma surj_countable_vimage: "surj f \<Longrightarrow> countable (f -` B) \<Longrightarrow> countable B"
  by (metis countable_vimage top_greatest)

lemma countable_Collect[simp]: "countable A \<Longrightarrow> countable {a \<in> A. \<phi> a}"
  by (metis Collect_conj_eq Int_absorb Int_commute Int_def countable_Int1)

lemma countable_Image:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> countable (X `` {y})"
  assumes "countable Y"
  shows "countable (X `` Y)"
proof -
  have "countable (X `` (\<Union>y\<in>Y. {y}))"
    unfolding Image_UN by (intro countable_UN assms)
  then show ?thesis by simp
qed

lemma countable_relpow:
  fixes X :: "'a rel"
  assumes Image_X: "\<And>Y. countable Y \<Longrightarrow> countable (X `` Y)"
  assumes Y: "countable Y"
  shows "countable ((X ^^ i) `` Y)"
  using Y by (induct i arbitrary: Y) (auto simp: relcomp_Image Image_X)

lemma countable_funpow:
  fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "\<And>A. countable A \<Longrightarrow> countable (f A)"
  and "countable A"
  shows "countable ((f ^^ n) A)"
by(induction n)(simp_all add: assms)

lemma countable_rtrancl:
  "(\<And>Y. countable Y \<Longrightarrow> countable (X `` Y)) \<Longrightarrow> countable Y \<Longrightarrow> countable (X\<^sup>* `` Y)"
  unfolding rtrancl_is_UN_relpow UN_Image by (intro countable_UN countableI_type countable_relpow)

lemma countable_lists[intro, simp]:
  assumes A: "countable A" shows "countable (lists A)"
proof -
  have "countable (lists (range (from_nat_into A)))"
    by (auto simp: lists_image)
  with A show ?thesis
    by (auto dest: subset_range_from_nat_into countable_subset lists_mono)
qed

lemma Collect_finite_eq_lists: "Collect finite = set ` lists UNIV"
  using finite_list by auto

lemma countable_Collect_finite: "countable (Collect (finite::'a::countable set\<Rightarrow>bool))"
  by (simp add: Collect_finite_eq_lists)

lemma countable_int: "countable \<int>"
  unfolding Ints_def by auto

lemma countable_rat: "countable \<rat>"
  unfolding Rats_def by auto

lemma Collect_finite_subset_eq_lists: "{A. finite A \<and> A \<subseteq> T} = set ` lists T"
  using finite_list by (auto simp: lists_eq_set)

lemma countable_Collect_finite_subset:
  "countable T \<Longrightarrow> countable {A. finite A \<and> A \<subseteq> T}"
  unfolding Collect_finite_subset_eq_lists by auto

lemma countable_Fpow: "countable S \<Longrightarrow> countable (Fpow S)"
  using countable_Collect_finite_subset
  by (force simp add: Fpow_def conj_commute)

lemma countable_set_option [simp]: "countable (set_option x)"
  by (cases x) auto

subsection \<open>Misc lemmas\<close>

lemma countable_subset_image:
   "countable B \<and> B \<subseteq> (f ` A) \<longleftrightarrow> (\<exists>A'. countable A' \<and> A' \<subseteq> A \<and> (B = f ` A'))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
    by (rule exI [where x="inv_into A f ` B"])
      (use \<open>?lhs\<close> in \<open>auto simp: f_inv_into_f subset_iff image_inv_into_cancel inv_into_into\<close>)
next
  assume ?rhs
  then show ?lhs by force
qed

lemma ex_subset_image_inj:
   "(\<exists>T. T \<subseteq> f ` S \<and> P T) \<longleftrightarrow> (\<exists>T. T \<subseteq> S \<and> inj_on f T \<and> P (f ` T))"
  by (auto simp: subset_image_inj)

lemma all_subset_image_inj:
   "(\<forall>T. T \<subseteq> f ` S \<longrightarrow> P T) \<longleftrightarrow> (\<forall>T. T \<subseteq> S \<and> inj_on f T \<longrightarrow> P(f ` T))"
  by (metis subset_image_inj)

lemma ex_countable_subset_image_inj:
   "(\<exists>T. countable T \<and> T \<subseteq> f ` S \<and> P T) \<longleftrightarrow>
    (\<exists>T. countable T \<and> T \<subseteq> S \<and> inj_on f T \<and> P (f ` T))"
  by (metis countable_image_inj_eq subset_image_inj)

lemma all_countable_subset_image_inj:
   "(\<forall>T. countable T \<and> T \<subseteq> f ` S \<longrightarrow> P T) \<longleftrightarrow> (\<forall>T. countable T \<and> T \<subseteq> S \<and> inj_on f T \<longrightarrow>P(f ` T))"
  by (metis countable_image_inj_eq subset_image_inj)

lemma ex_countable_subset_image:
   "(\<exists>T. countable T \<and> T \<subseteq> f ` S \<and> P T) \<longleftrightarrow> (\<exists>T. countable T \<and> T \<subseteq> S \<and> P (f ` T))"
  by (metis countable_subset_image)

lemma all_countable_subset_image:
   "(\<forall>T. countable T \<and> T \<subseteq> f ` S \<longrightarrow> P T) \<longleftrightarrow> (\<forall>T. countable T \<and> T \<subseteq> S \<longrightarrow> P(f ` T))"
  by (metis countable_subset_image)

lemma countable_image_eq:
   "countable(f ` S) \<longleftrightarrow> (\<exists>T. countable T \<and> T \<subseteq> S \<and> f ` S = f ` T)"
  by (metis countable_image countable_image_inj_eq order_refl subset_image_inj)

lemma countable_image_eq_inj:
   "countable(f ` S) \<longleftrightarrow> (\<exists>T. countable T \<and> T \<subseteq> S \<and> f ` S = f ` T \<and> inj_on f T)"
  by (metis countable_image_inj_eq order_refl subset_image_inj)

lemma infinite_countable_subset':
  assumes X: "infinite X" shows "\<exists>C\<subseteq>X. countable C \<and> infinite C"
proof -
  obtain f :: "nat \<Rightarrow> 'a" where "inj f" "range f \<subseteq> X"
    using infinite_countable_subset [OF X] by blast
  then show ?thesis
    by (intro exI[of _ "range f"]) (auto simp: range_inj_infinite)
qed

lemma countable_all:
  assumes S: "countable S"
  shows "(\<forall>s\<in>S. P s) \<longleftrightarrow> (\<forall>n::nat. from_nat_into S n \<in> S \<longrightarrow> P (from_nat_into S n))"
  using S[THEN subset_range_from_nat_into] by auto

lemma finite_sequence_to_countable_set:
  assumes "countable X"
  obtains F where "\<And>i. F i \<subseteq> X" "\<And>i. F i \<subseteq> F (Suc i)" "\<And>i. finite (F i)" "(\<Union>i. F i) = X"
proof -
  show thesis
    apply (rule that[of "\<lambda>i. if X = {} then {} else from_nat_into X ` {..i}"])
       apply (auto simp add: image_iff intro: from_nat_into split: if_splits)
    using assms from_nat_into_surj by (fastforce cong: image_cong)
qed

lemma transfer_countable[transfer_rule]:
  "bi_unique R \<Longrightarrow> rel_fun (rel_set R) (=) countable countable"
  by (rule rel_funI, erule (1) bi_unique_rel_set_lemma)
     (auto dest: countable_image_inj_on)

subsection \<open>Uncountable\<close>

abbreviation uncountable where
  "uncountable A \<equiv> \<not> countable A"

lemma uncountable_def: "uncountable A \<longleftrightarrow> A \<noteq> {} \<and> \<not> (\<exists>f::(nat \<Rightarrow> 'a). range f = A)"
  by (auto intro: inj_on_inv_into simp: countable_def)
     (metis all_not_in_conv inj_on_iff_surj subset_UNIV)

lemma uncountable_bij_betw: "bij_betw f A B \<Longrightarrow> uncountable B \<Longrightarrow> uncountable A"
  unfolding bij_betw_def by (metis countable_image)

lemma uncountable_infinite: "uncountable A \<Longrightarrow> infinite A"
  by (metis countable_finite)

lemma uncountable_minus_countable:
  "uncountable A \<Longrightarrow> countable B \<Longrightarrow> uncountable (A - B)"
  using countable_Un[of B "A - B"] by auto

lemma countable_Diff_eq [simp]: "countable (A - {x}) = countable A"
  by (meson countable_Diff countable_empty countable_insert uncountable_minus_countable)

text \<open>Every infinite set can be covered by a pairwise disjoint family of infinite sets.
      This version doesn't achieve equality, as it only covers a countable subset\<close>
lemma infinite_infinite_partition:
  assumes "infinite A"
  obtains C :: "nat \<Rightarrow> 'a set" 
    where "pairwise (\<lambda>i j. disjnt (C i) (C j)) UNIV" "(\<Union>i. C i) \<subseteq> A" "\<And>i. infinite (C i)"
proof -
  obtain f :: "nat\<Rightarrow>'a" where "range f \<subseteq> A" "inj f"
    using assms infinite_countable_subset by blast
  let ?C = "\<lambda>i. range (\<lambda>j. f (prod_encode (i,j)))"
  show thesis
  proof
    show "pairwise (\<lambda>i j. disjnt (?C i) (?C j)) UNIV"
      by (auto simp: pairwise_def disjnt_def inj_on_eq_iff [OF \<open>inj f\<close>] inj_on_eq_iff [OF inj_prod_encode, of _ UNIV])
    show "(\<Union>i. ?C i) \<subseteq> A"
      using \<open>range f \<subseteq> A\<close> by blast
    have "infinite (range (\<lambda>j. f (prod_encode (i, j))))" for i
      by (rule range_inj_infinite) (meson Pair_inject \<open>inj f\<close> inj_def prod_encode_eq)
    then show "\<And>i. infinite (?C i)"
      using that by auto
  qed
qed

end
