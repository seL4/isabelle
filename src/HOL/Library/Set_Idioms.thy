(*  Title:      HOL/Library/Set_Idioms.thy
    Author:     Lawrence Paulson (but borrowed from HOL Light)
*)

section \<open>Set Idioms\<close>

theory Set_Idioms
imports Countable_Set

begin


subsection\<open>Idioms for being a suitable union/intersection of something\<close>

definition union_of :: "('a set set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr \<open>union'_of\<close> 60)
  where "P union_of Q \<equiv> \<lambda>S. \<exists>\<U>. P \<U> \<and> \<U> \<subseteq> Collect Q \<and> \<Union>\<U> = S"

definition intersection_of :: "('a set set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr \<open>intersection'_of\<close> 60)
  where "P intersection_of Q \<equiv> \<lambda>S. \<exists>\<U>. P \<U> \<and> \<U> \<subseteq> Collect Q \<and> \<Inter>\<U> = S"

definition arbitrary:: "'a set set \<Rightarrow> bool" where "arbitrary \<U> \<equiv> True"

lemma union_of_inc: "\<lbrakk>P {S}; Q S\<rbrakk> \<Longrightarrow> (P union_of Q) S"
  by (auto simp: union_of_def)

lemma intersection_of_inc:
   "\<lbrakk>P {S}; Q S\<rbrakk> \<Longrightarrow> (P intersection_of Q) S"
  by (auto simp: intersection_of_def)

lemma union_of_mono:
   "\<lbrakk>(P union_of Q) S; \<And>x. Q x \<Longrightarrow> Q' x\<rbrakk> \<Longrightarrow> (P union_of Q') S"
  by (auto simp: union_of_def)

lemma intersection_of_mono:
   "\<lbrakk>(P intersection_of Q) S; \<And>x. Q x \<Longrightarrow> Q' x\<rbrakk> \<Longrightarrow> (P intersection_of Q') S"
  by (auto simp: intersection_of_def)

lemma all_union_of:
     "(\<forall>S. (P union_of Q) S \<longrightarrow> R S) \<longleftrightarrow> (\<forall>T. P T \<and> T \<subseteq> Collect Q \<longrightarrow> R(\<Union>T))"
  by (auto simp: union_of_def)

lemma all_intersection_of:
     "(\<forall>S. (P intersection_of Q) S \<longrightarrow> R S) \<longleftrightarrow> (\<forall>T. P T \<and> T \<subseteq> Collect Q \<longrightarrow> R(\<Inter>T))"
  by (auto simp: intersection_of_def)
             
lemma intersection_ofE:
     "\<lbrakk>(P intersection_of Q) S; \<And>T. \<lbrakk>P T; T \<subseteq> Collect Q\<rbrakk> \<Longrightarrow> R(\<Inter>T)\<rbrakk> \<Longrightarrow> R S"
  by (auto simp: intersection_of_def)

lemma union_of_empty:
     "P {} \<Longrightarrow> (P union_of Q) {}"
  by (auto simp: union_of_def)

lemma intersection_of_empty:
     "P {} \<Longrightarrow> (P intersection_of Q) UNIV"
  by (auto simp: intersection_of_def)

text\<open> The arbitrary and finite cases\<close>

lemma arbitrary_union_of_alt:
   "(arbitrary union_of Q) S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>U. Q U \<and> x \<in> U \<and> U \<subseteq> S)"
 (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (force simp: union_of_def arbitrary_def)
next
  assume ?rhs
  then have "{U. Q U \<and> U \<subseteq> S} \<subseteq> Collect Q" "\<Union>{U. Q U \<and> U \<subseteq> S} = S"
    by auto
  then show ?lhs
    unfolding union_of_def arbitrary_def by blast
qed

lemma arbitrary_union_of_empty [simp]: "(arbitrary union_of P) {}"
  by (force simp: union_of_def arbitrary_def)

lemma arbitrary_intersection_of_empty [simp]:
  "(arbitrary intersection_of P) UNIV"
  by (force simp: intersection_of_def arbitrary_def)

lemma arbitrary_union_of_inc:
  "P S \<Longrightarrow> (arbitrary union_of P) S"
  by (force simp: union_of_inc arbitrary_def)

lemma arbitrary_intersection_of_inc:
  "P S \<Longrightarrow> (arbitrary intersection_of P) S"
  by (force simp: intersection_of_inc arbitrary_def)

lemma arbitrary_union_of_complement:
   "(arbitrary union_of P) S \<longleftrightarrow> (arbitrary intersection_of (\<lambda>S. P(- S))) (- S)"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain \<U> where "\<U> \<subseteq> Collect P" "S = \<Union>\<U>"
    by (auto simp: union_of_def arbitrary_def)
  then show ?rhs
    unfolding intersection_of_def arbitrary_def
    by (rule_tac x="uminus ` \<U>" in exI) auto
next
  assume ?rhs
  then obtain \<U> where "\<U> \<subseteq> {S. P (- S)}" "\<Inter>\<U> = - S"
    by (auto simp: union_of_def intersection_of_def arbitrary_def)
  then show ?lhs
    unfolding union_of_def arbitrary_def
    by (rule_tac x="uminus ` \<U>" in exI) auto
qed

lemma arbitrary_intersection_of_complement:
   "(arbitrary intersection_of P) S \<longleftrightarrow> (arbitrary union_of (\<lambda>S. P(- S))) (- S)"
  by (simp add: arbitrary_union_of_complement)

lemma arbitrary_union_of_idempot [simp]:
  "arbitrary union_of arbitrary union_of P = arbitrary union_of P"
proof -
  have 1: "\<exists>\<U>'\<subseteq>Collect P. \<Union>\<U>' = \<Union>\<U>" if "\<U> \<subseteq> {S. \<exists>\<V>\<subseteq>Collect P. \<Union>\<V> = S}" for \<U>
  proof -
    let ?\<W> = "{V. \<exists>\<V>. \<V>\<subseteq>Collect P \<and> V \<in> \<V> \<and> (\<exists>S \<in> \<U>. \<Union>\<V> = S)}"
    have *: "\<And>x U. \<lbrakk>x \<in> U; U \<in> \<U>\<rbrakk> \<Longrightarrow> x \<in> \<Union>?\<W>"
      using that
      apply simp
      apply (drule subsetD, assumption, auto)
      done
    show ?thesis
    apply (rule_tac x="{V. \<exists>\<V>. \<V>\<subseteq>Collect P \<and> V \<in> \<V> \<and> (\<exists>S \<in> \<U>. \<Union>\<V> = S)}" in exI)
      using that by (blast intro: *)
  qed
  have 2: "\<exists>\<U>'\<subseteq>{S. \<exists>\<U>\<subseteq>Collect P. \<Union>\<U> = S}. \<Union>\<U>' = \<Union>\<U>" if "\<U> \<subseteq> Collect P" for \<U>
    by (metis (mono_tags, lifting) union_of_def arbitrary_union_of_inc that)
  show ?thesis
    unfolding union_of_def arbitrary_def by (force simp: 1 2)
qed

lemma arbitrary_intersection_of_idempot:
   "arbitrary intersection_of arbitrary intersection_of P = arbitrary intersection_of P" (is "?lhs = ?rhs")
proof -
  have "- ?lhs = - ?rhs"
    unfolding arbitrary_intersection_of_complement by simp
  then show ?thesis
    by simp
qed

lemma arbitrary_union_of_Union:
   "(\<And>S. S \<in> \<U> \<Longrightarrow> (arbitrary union_of P) S) \<Longrightarrow> (arbitrary union_of P) (\<Union>\<U>)"
  by (metis union_of_def arbitrary_def arbitrary_union_of_idempot mem_Collect_eq subsetI)

lemma arbitrary_union_of_Un:
   "\<lbrakk>(arbitrary union_of P) S; (arbitrary union_of P) T\<rbrakk>
           \<Longrightarrow> (arbitrary union_of P) (S \<union> T)"
  using arbitrary_union_of_Union [of "{S,T}"] by auto

lemma arbitrary_intersection_of_Inter:
   "(\<And>S. S \<in> \<U> \<Longrightarrow> (arbitrary intersection_of P) S) \<Longrightarrow> (arbitrary intersection_of P) (\<Inter>\<U>)"
  by (metis intersection_of_def arbitrary_def arbitrary_intersection_of_idempot mem_Collect_eq subsetI)

lemma arbitrary_intersection_of_Int:
   "\<lbrakk>(arbitrary intersection_of P) S; (arbitrary intersection_of P) T\<rbrakk>
           \<Longrightarrow> (arbitrary intersection_of P) (S \<inter> T)"
  using arbitrary_intersection_of_Inter [of "{S,T}"] by auto

lemma arbitrary_union_of_Int_eq:
  "(\<forall>S T. (arbitrary union_of P) S \<and> (arbitrary union_of P) T
               \<longrightarrow> (arbitrary union_of P) (S \<inter> T))
   \<longleftrightarrow> (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: arbitrary_union_of_inc)
next
  assume R: ?rhs
  show ?lhs
  proof clarify
    fix S :: "'a set" and T :: "'a set"
    assume "(arbitrary union_of P) S" and "(arbitrary union_of P) T"
    then obtain \<U> \<V> where *: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S" "\<V> \<subseteq> Collect P" "\<Union>\<V> = T"
      by (auto simp: union_of_def)
    then have "(arbitrary union_of P) (\<Union>C\<in>\<U>. \<Union>D\<in>\<V>. C \<inter> D)"
     using R by (blast intro: arbitrary_union_of_Union)
   then show "(arbitrary union_of P) (S \<inter> T)"
     by (simp add: Int_UN_distrib2 *)
 qed
qed

lemma arbitrary_intersection_of_Un_eq:
   "(\<forall>S T. (arbitrary intersection_of P) S \<and> (arbitrary intersection_of P) T
               \<longrightarrow> (arbitrary intersection_of P) (S \<union> T)) \<longleftrightarrow>
        (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary intersection_of P) (S \<union> T))"
  apply (simp add: arbitrary_intersection_of_complement)
  using arbitrary_union_of_Int_eq [of "\<lambda>S. P (- S)"]
  by (metis (no_types, lifting) arbitrary_def double_compl union_of_inc)

lemma finite_union_of_empty [simp]: "(finite union_of P) {}"
  by (simp add: union_of_empty)

lemma finite_intersection_of_empty [simp]: "(finite intersection_of P) UNIV"
  by (simp add: intersection_of_empty)

lemma finite_union_of_inc:
   "P S \<Longrightarrow> (finite union_of P) S"
  by (simp add: union_of_inc)

lemma finite_intersection_of_inc:
   "P S \<Longrightarrow> (finite intersection_of P) S"
  by (simp add: intersection_of_inc)

lemma finite_union_of_complement:
  "(finite union_of P) S \<longleftrightarrow> (finite intersection_of (\<lambda>S. P(- S))) (- S)"
  unfolding union_of_def intersection_of_def
  apply safe
   apply (rule_tac x="uminus ` \<U>" in exI, fastforce)+
  done

lemma finite_intersection_of_complement:
   "(finite intersection_of P) S \<longleftrightarrow> (finite union_of (\<lambda>S. P(- S))) (- S)"
  by (simp add: finite_union_of_complement)

lemma finite_union_of_idempot [simp]:
  "finite union_of finite union_of P = finite union_of P"
proof -
  have "(finite union_of P) S" if S: "(finite union_of finite union_of P) S" for S
  proof -
    obtain \<U> where "finite \<U>" "S = \<Union>\<U>" and \<U>: "\<forall>U\<in>\<U>. \<exists>\<U>. finite \<U> \<and> (\<U> \<subseteq> Collect P) \<and> \<Union>\<U> = U"
      using S unfolding union_of_def by (auto simp: subset_eq)
    then obtain f where "\<forall>U\<in>\<U>. finite (f U) \<and> (f U \<subseteq> Collect P) \<and> \<Union>(f U) = U"
      by metis
    then show ?thesis
      unfolding union_of_def \<open>S = \<Union>\<U>\<close>
      by (rule_tac x = "snd ` Sigma \<U> f" in exI) (fastforce simp: \<open>finite \<U>\<close>)
  qed
  moreover
  have "(finite union_of finite union_of P) S" if "(finite union_of P) S" for S
    by (simp add: finite_union_of_inc that)
  ultimately show ?thesis
    by force
qed

lemma finite_intersection_of_idempot [simp]:
   "finite intersection_of finite intersection_of P = finite intersection_of P"
  by (force simp: finite_intersection_of_complement)

lemma finite_union_of_Union:
   "\<lbrakk>finite \<U>; \<And>S. S \<in> \<U> \<Longrightarrow> (finite union_of P) S\<rbrakk> \<Longrightarrow> (finite union_of P) (\<Union>\<U>)"
  using finite_union_of_idempot [of P]
  by (metis mem_Collect_eq subsetI union_of_def)

lemma finite_union_of_Un:
   "\<lbrakk>(finite union_of P) S; (finite union_of P) T\<rbrakk> \<Longrightarrow> (finite union_of P) (S \<union> T)"
  by (auto simp: union_of_def)

lemma finite_intersection_of_Inter:
   "\<lbrakk>finite \<U>; \<And>S. S \<in> \<U> \<Longrightarrow> (finite intersection_of P) S\<rbrakk> \<Longrightarrow> (finite intersection_of P) (\<Inter>\<U>)"
  using finite_intersection_of_idempot [of P]
  by (metis intersection_of_def mem_Collect_eq subsetI)

lemma finite_intersection_of_Int:
   "\<lbrakk>(finite intersection_of P) S; (finite intersection_of P) T\<rbrakk>
           \<Longrightarrow> (finite intersection_of P) (S \<inter> T)"
  by (auto simp: intersection_of_def)

lemma finite_union_of_Int_eq:
   "(\<forall>S T. (finite union_of P) S \<and> (finite union_of P) T \<longrightarrow> (finite union_of P) (S \<inter> T))
    \<longleftrightarrow> (\<forall>S T. P S \<and> P T \<longrightarrow> (finite union_of P) (S \<inter> T))"
(is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: finite_union_of_inc)
next
  assume R: ?rhs
  show ?lhs
  proof clarify
    fix S :: "'a set" and T :: "'a set"
    assume "(finite union_of P) S" and "(finite union_of P) T"
    then obtain \<U> \<V> where *: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S" "finite \<U>" "\<V> \<subseteq> Collect P" "\<Union>\<V> = T" "finite \<V>"
      by (auto simp: union_of_def)
    then have "(finite union_of P) (\<Union>C\<in>\<U>. \<Union>D\<in>\<V>. C \<inter> D)"
      using R
      by (blast intro: finite_union_of_Union)
   then show "(finite union_of P) (S \<inter> T)"
     by (simp add: Int_UN_distrib2 *)
 qed
qed

lemma finite_intersection_of_Un_eq:
   "(\<forall>S T. (finite intersection_of P) S \<and>
               (finite intersection_of P) T
               \<longrightarrow> (finite intersection_of P) (S \<union> T)) \<longleftrightarrow>
        (\<forall>S T. P S \<and> P T \<longrightarrow> (finite intersection_of P) (S \<union> T))"
  apply (simp add: finite_intersection_of_complement)
  using finite_union_of_Int_eq [of "\<lambda>S. P (- S)"]
  by (metis (no_types, lifting) double_compl)


abbreviation finite' :: "'a set \<Rightarrow> bool"
  where "finite' A \<equiv> finite A \<and> A \<noteq> {}"

lemma finite'_intersection_of_Int:
   "\<lbrakk>(finite' intersection_of P) S; (finite' intersection_of P) T\<rbrakk>
           \<Longrightarrow> (finite' intersection_of P) (S \<inter> T)"
  by (auto simp: intersection_of_def)

lemma finite'_intersection_of_inc:
   "P S \<Longrightarrow> (finite' intersection_of P) S"
  by (simp add: intersection_of_inc)


subsection \<open>The ``Relative to'' operator\<close>

text\<open>A somewhat cheap but handy way of getting localized forms of various topological concepts
(open, closed, borel, fsigma, gdelta etc.)\<close>

definition relative_to :: "['a set \<Rightarrow> bool, 'a set, 'a set] \<Rightarrow> bool" (infixl \<open>relative'_to\<close> 55)
  where "P relative_to S \<equiv> \<lambda>T. \<exists>U. P U \<and> S \<inter> U = T"

lemma relative_to_UNIV [simp]: "(P relative_to UNIV) S \<longleftrightarrow> P S"
  by (simp add: relative_to_def)

lemma relative_to_imp_subset:
   "(P relative_to S) T \<Longrightarrow> T \<subseteq> S"
  by (auto simp: relative_to_def)

lemma all_relative_to: "(\<forall>S. (P relative_to U) S \<longrightarrow> Q S) \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q(U \<inter> S))"
  by (auto simp: relative_to_def)

lemma relative_toE: "\<lbrakk>(P relative_to U) S; \<And>S. P S \<Longrightarrow> Q(U \<inter> S)\<rbrakk> \<Longrightarrow> Q S"
  by (auto simp: relative_to_def)

lemma relative_to_inc:
   "P S \<Longrightarrow> (P relative_to U) (U \<inter> S)"
  by (auto simp: relative_to_def)

lemma relative_to_relative_to [simp]:
   "P relative_to S relative_to T = P relative_to (S \<inter> T)"
  unfolding relative_to_def
  by auto

lemma relative_to_compl:
   "S \<subseteq> U \<Longrightarrow> ((P relative_to U) (U - S) \<longleftrightarrow> ((\<lambda>c. P(- c)) relative_to U) S)"
  unfolding relative_to_def
  by (metis Diff_Diff_Int Diff_eq double_compl inf.absorb_iff2)

lemma relative_to_subset_trans:
   "\<lbrakk>(P relative_to U) S; S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (P relative_to T) S"
  unfolding relative_to_def by auto

lemma relative_to_mono:
   "\<lbrakk>(P relative_to U) S; \<And>S. P S \<Longrightarrow> Q S\<rbrakk> \<Longrightarrow> (Q relative_to U) S"
  unfolding relative_to_def by auto

lemma relative_to_subset_inc: "\<lbrakk>S \<subseteq> U; P S\<rbrakk> \<Longrightarrow> (P relative_to U) S"
  unfolding relative_to_def by auto

lemma relative_to_Int:
   "\<lbrakk>(P relative_to S) C; (P relative_to S) D; \<And>X Y. \<lbrakk>P X; P Y\<rbrakk> \<Longrightarrow> P(X \<inter> Y)\<rbrakk>
         \<Longrightarrow>  (P relative_to S) (C \<inter> D)"
  unfolding relative_to_def by auto

lemma relative_to_Un:
   "\<lbrakk>(P relative_to S) C; (P relative_to S) D; \<And>X Y. \<lbrakk>P X; P Y\<rbrakk> \<Longrightarrow> P(X \<union> Y)\<rbrakk>
         \<Longrightarrow>  (P relative_to S) (C \<union> D)"
  unfolding relative_to_def by auto

lemma arbitrary_union_of_relative_to:
  "((arbitrary union_of P) relative_to U) = (arbitrary union_of (P relative_to U))" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Union>\<U>" "\<U> \<subseteq> Collect P"
      using L unfolding relative_to_def union_of_def by auto
    then show ?thesis
      unfolding relative_to_def union_of_def arbitrary_def
      by (rule_tac x="(\<lambda>X. U \<inter> X) ` \<U>" in exI) auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = \<Union>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T"
      using R unfolding relative_to_def union_of_def by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "\<exists>\<U>'\<subseteq>Collect P. \<Union>\<U>' = \<Union> (f ` \<U>)"
      by (metis image_subset_iff mem_Collect_eq)
    moreover have eq: "U \<inter> \<Union> (f ` \<U>) = \<Union>\<U>"
      using f by auto
    ultimately show ?thesis
      unfolding relative_to_def union_of_def arbitrary_def \<open>S = \<Union>\<U>\<close>
      by metis
  qed
  ultimately show ?thesis
    by blast
qed

lemma finite_union_of_relative_to:
  "((finite union_of P) relative_to U) = (finite union_of (P relative_to U))" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Union>\<U>" "\<U> \<subseteq> Collect P" "finite \<U>"
      using L unfolding relative_to_def union_of_def by auto
    then show ?thesis
      unfolding relative_to_def union_of_def
      by (rule_tac x="(\<lambda>X. U \<inter> X) ` \<U>" in exI) auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = \<Union>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T" "finite \<U>"
      using R unfolding relative_to_def union_of_def by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "\<exists>\<U>'\<subseteq>Collect P. \<Union>\<U>' = \<Union> (f ` \<U>)"
      by (metis image_subset_iff mem_Collect_eq)
    moreover have eq: "U \<inter> \<Union> (f ` \<U>) = \<Union>\<U>"
      using f by auto
    ultimately show ?thesis
      using \<open>finite \<U>\<close> f
      unfolding relative_to_def union_of_def \<open>S = \<Union>\<U>\<close>
      by (rule_tac x="\<Union> (f ` \<U>)" in exI) (metis finite_imageI image_subsetI mem_Collect_eq)
  qed
  ultimately show ?thesis
    by blast
qed

lemma countable_union_of_relative_to:
  "((countable union_of P) relative_to U) = (countable union_of (P relative_to U))" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Union>\<U>" "\<U> \<subseteq> Collect P" "countable \<U>"
      using L unfolding relative_to_def union_of_def by auto
    then show ?thesis
      unfolding relative_to_def union_of_def
      by (rule_tac x="(\<lambda>X. U \<inter> X) ` \<U>" in exI) auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = \<Union>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T" "countable \<U>"
      using R unfolding relative_to_def union_of_def by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "\<exists>\<U>'\<subseteq>Collect P. \<Union>\<U>' = \<Union> (f ` \<U>)"
      by (metis image_subset_iff mem_Collect_eq)
    moreover have eq: "U \<inter> \<Union> (f ` \<U>) = \<Union>\<U>"
      using f by auto
    ultimately show ?thesis
      using \<open>countable \<U>\<close> f
      unfolding relative_to_def union_of_def \<open>S = \<Union>\<U>\<close>
      by (rule_tac x="\<Union> (f ` \<U>)" in exI) (metis countable_image image_subsetI mem_Collect_eq)
  qed
  ultimately show ?thesis
    by blast
qed


lemma arbitrary_intersection_of_relative_to:
  "((arbitrary intersection_of P) relative_to U) = ((arbitrary intersection_of (P relative_to U)) relative_to U)" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where \<U>: "S = U \<inter> \<Inter>\<U>" "\<U> \<subseteq> Collect P"
      using L unfolding relative_to_def intersection_of_def by auto
    show ?thesis
      unfolding relative_to_def intersection_of_def arbitrary_def
    proof (intro exI conjI)
      show "U \<inter> (\<Inter>X\<in>\<U>. U \<inter> X) = S" "(\<inter>) U ` \<U> \<subseteq> {T. \<exists>Ua. P Ua \<and> U \<inter> Ua = T}"
        using \<U> by blast+
    qed auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Inter>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T"
      using R unfolding relative_to_def intersection_of_def  by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "f `  \<U> \<subseteq> Collect P"
      by auto
    moreover have eq: "U \<inter> \<Inter>(f ` \<U>) = U \<inter> \<Inter>\<U>"
      using f by auto
    ultimately show ?thesis
      unfolding relative_to_def intersection_of_def arbitrary_def \<open>S = U \<inter> \<Inter>\<U>\<close>
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma finite_intersection_of_relative_to:
  "((finite intersection_of P) relative_to U) = ((finite intersection_of (P relative_to U)) relative_to U)" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where \<U>: "S = U \<inter> \<Inter>\<U>" "\<U> \<subseteq> Collect P" "finite \<U>"
      using L unfolding relative_to_def intersection_of_def by auto
    show ?thesis
      unfolding relative_to_def intersection_of_def
    proof (intro exI conjI)
      show "U \<inter> (\<Inter>X\<in>\<U>. U \<inter> X) = S" "(\<inter>) U ` \<U> \<subseteq> {T. \<exists>Ua. P Ua \<and> U \<inter> Ua = T}"
        using \<U> by blast+
      show "finite ((\<inter>) U ` \<U>)"
        by (simp add: \<open>finite \<U>\<close>)
    qed auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Inter>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T" "finite \<U>"
      using R unfolding relative_to_def intersection_of_def  by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "f `  \<U> \<subseteq> Collect P"
      by auto
    moreover have eq: "U \<inter> \<Inter> (f ` \<U>) = U \<inter> \<Inter> \<U>"
      using f by auto
    ultimately show ?thesis
      unfolding relative_to_def intersection_of_def \<open>S = U \<inter> \<Inter>\<U>\<close>
      using \<open>finite \<U>\<close>
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma countable_intersection_of_relative_to:
  "((countable intersection_of P) relative_to U) = ((countable intersection_of (P relative_to U)) relative_to U)" (is "?lhs = ?rhs")
proof -
  have "?rhs S" if L: "?lhs S" for S
  proof -
    obtain \<U> where \<U>: "S = U \<inter> \<Inter>\<U>" "\<U> \<subseteq> Collect P" "countable \<U>"
      using L unfolding relative_to_def intersection_of_def by auto
    show ?thesis
      unfolding relative_to_def intersection_of_def
    proof (intro exI conjI)
      show "U \<inter> (\<Inter>X\<in>\<U>. U \<inter> X) = S" "(\<inter>) U ` \<U> \<subseteq> {T. \<exists>Ua. P Ua \<and> U \<inter> Ua = T}"
        using \<U> by blast+
      show "countable ((\<inter>) U ` \<U>)"
        by (simp add: \<open>countable \<U>\<close>)
    qed auto
  qed
  moreover have "?lhs S" if R: "?rhs S" for S
  proof -
    obtain \<U> where "S = U \<inter> \<Inter>\<U>" "\<forall>T\<in>\<U>. \<exists>V. P V \<and> U \<inter> V = T" "countable \<U>"
      using R unfolding relative_to_def intersection_of_def  by auto
    then obtain f where f: "\<And>T. T \<in> \<U> \<Longrightarrow> P (f T)" "\<And>T. T \<in> \<U> \<Longrightarrow> U \<inter> (f T) = T"
      by metis
    then have "f `  \<U> \<subseteq> Collect P"
      by auto
    moreover have eq: "U \<inter> \<Inter> (f ` \<U>) = U \<inter> \<Inter> \<U>"
      using f by auto
    ultimately show ?thesis
      unfolding relative_to_def intersection_of_def \<open>S = U \<inter> \<Inter>\<U>\<close>
      using \<open>countable \<U>\<close> countable_image
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma countable_union_of_empty [simp]: "(countable union_of P) {}"
  by (simp add: union_of_empty)

lemma countable_intersection_of_empty [simp]: "(countable intersection_of P) UNIV"
  by (simp add: intersection_of_empty)

lemma countable_union_of_inc: "P S \<Longrightarrow> (countable union_of P) S"
  by (simp add: union_of_inc)

lemma countable_intersection_of_inc: "P S \<Longrightarrow> (countable intersection_of P) S"
  by (simp add: intersection_of_inc)

lemma countable_union_of_complement:
  "(countable union_of P) S \<longleftrightarrow> (countable intersection_of (\<lambda>S. P(-S))) (-S)" 
  (is "?lhs=?rhs")
proof
  assume ?lhs
  then obtain \<U> where "countable \<U>" and \<U>: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S"
    by (metis union_of_def)
  define \<U>' where "\<U>' \<equiv> (\<lambda>C. -C) ` \<U>"
  have "\<U>' \<subseteq> {S. P (- S)}" "\<Inter>\<U>' = -S"
    using \<U>'_def \<U> by auto
  then show ?rhs
    unfolding intersection_of_def by (metis \<U>'_def \<open>countable \<U>\<close> countable_image)
next
  assume ?rhs
  then obtain \<U> where "countable \<U>" and \<U>: "\<U> \<subseteq> {S. P (- S)}" "\<Inter>\<U> = -S"
    by (metis intersection_of_def)
  define \<U>' where "\<U>' \<equiv> (\<lambda>C. -C) ` \<U>"
  have "\<U>' \<subseteq> Collect P" "\<Union> \<U>' = S"
    using \<U>'_def \<U> by auto
  then show ?lhs
    unfolding union_of_def
    by (metis \<U>'_def \<open>countable \<U>\<close> countable_image)
qed

lemma countable_intersection_of_complement:
   "(countable intersection_of P) S \<longleftrightarrow> (countable union_of (\<lambda>S. P(- S))) (- S)"
  by (simp add: countable_union_of_complement)

lemma countable_union_of_explicit:
  assumes "P {}"
  shows "(countable union_of P) S \<longleftrightarrow>
         (\<exists>T. (\<forall>n::nat. P(T n)) \<and> \<Union>(range T) = S)" (is "?lhs=?rhs")
proof
  assume ?lhs
  then obtain \<U> where "countable \<U>" and \<U>: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S"
    by (metis union_of_def)
  then show ?rhs
    by (metis SUP_bot Sup_empty assms from_nat_into mem_Collect_eq range_from_nat_into subsetD)
next
  assume ?rhs
  then show ?lhs
    by (metis countableI_type countable_image image_subset_iff mem_Collect_eq union_of_def)
qed

lemma countable_union_of_ascending:
  assumes empty: "P {}" and Un: "\<And>T U. \<lbrakk>P T; P U\<rbrakk> \<Longrightarrow> P(T \<union> U)"
  shows "(countable union_of P) S \<longleftrightarrow>
         (\<exists>T. (\<forall>n. P(T n)) \<and> (\<forall>n. T n \<subseteq> T(Suc n)) \<and> \<Union>(range T) = S)" (is "?lhs=?rhs")
proof
  assume ?lhs
  then obtain T where T: "\<And>n::nat. P(T n)" "\<Union>(range T) = S"
    by (meson empty countable_union_of_explicit)
  have "P (\<Union> (T ` {..n}))" for n
    by (induction n) (auto simp: atMost_Suc Un T)
  with T show ?rhs
    by (rule_tac x="\<lambda>n. \<Union>k\<le>n. T k" in exI) force
next
  assume ?rhs
  then show ?lhs
    using empty countable_union_of_explicit by auto
qed

lemma countable_union_of_idem [simp]:
  "countable union_of countable union_of P = countable union_of P"  (is "?lhs=?rhs")
proof
  fix S
  show "(countable union_of countable union_of P) S = (countable union_of P) S"
  proof
    assume L: "?lhs S"
    then obtain \<U> where "countable \<U>" and \<U>: "\<U> \<subseteq> Collect (countable union_of P)" "\<Union>\<U> = S"
      by (metis union_of_def)
    then have "\<forall>U \<in> \<U>. \<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> Collect P \<and> U = \<Union>\<V>"
      by (metis Ball_Collect union_of_def)
    then obtain \<F> where \<F>: "\<forall>U \<in> \<U>. countable (\<F> U) \<and> \<F> U \<subseteq> Collect P \<and> U = \<Union>(\<F> U)"
      by metis
    have "countable (\<Union> (\<F> ` \<U>))"
      using \<F> \<open>countable \<U>\<close> by blast
    moreover have "\<Union> (\<F> ` \<U>) \<subseteq> Collect P"
      by (simp add: Sup_le_iff \<F>)
    moreover have "\<Union> (\<Union> (\<F> ` \<U>)) = S"
      by auto (metis Union_iff \<F> \<U>(2))+
    ultimately show "?rhs S"
      by (meson union_of_def)
  qed (simp add: countable_union_of_inc)
qed

lemma countable_intersection_of_idem [simp]:
   "countable intersection_of countable intersection_of P =
        countable intersection_of P"
  by (force simp: countable_intersection_of_complement)

lemma countable_union_of_Union:
   "\<lbrakk>countable \<U>; \<And>S. S \<in> \<U> \<Longrightarrow> (countable union_of P) S\<rbrakk>
        \<Longrightarrow> (countable union_of P) (\<Union> \<U>)"
  by (metis Ball_Collect countable_union_of_idem union_of_def)

lemma countable_union_of_UN:
   "\<lbrakk>countable I; \<And>i. i \<in> I \<Longrightarrow> (countable union_of P) (U i)\<rbrakk>
        \<Longrightarrow> (countable union_of P) (\<Union>i\<in>I. U i)"
  by (metis (mono_tags, lifting) countable_image countable_union_of_Union imageE)

lemma countable_union_of_Un:
  "\<lbrakk>(countable union_of P) S; (countable union_of P) T\<rbrakk>
           \<Longrightarrow> (countable union_of P) (S \<union> T)"
  by (smt (verit) Union_Un_distrib countable_Un le_sup_iff union_of_def)

lemma countable_intersection_of_Inter:
   "\<lbrakk>countable \<U>; \<And>S. S \<in> \<U> \<Longrightarrow> (countable intersection_of P) S\<rbrakk>
        \<Longrightarrow> (countable intersection_of P) (\<Inter> \<U>)"
  by (metis countable_intersection_of_idem intersection_of_def mem_Collect_eq subsetI)

lemma countable_intersection_of_INT:
   "\<lbrakk>countable I; \<And>i. i \<in> I \<Longrightarrow> (countable intersection_of P) (U i)\<rbrakk>
        \<Longrightarrow> (countable intersection_of P) (\<Inter>i\<in>I. U i)"
  by (metis (mono_tags, lifting) countable_image countable_intersection_of_Inter imageE)

lemma countable_intersection_of_inter:
   "\<lbrakk>(countable intersection_of P) S; (countable intersection_of P) T\<rbrakk>
           \<Longrightarrow> (countable intersection_of P) (S \<inter> T)"
  by (simp add: countable_intersection_of_complement countable_union_of_Un)

lemma countable_union_of_Int:
  assumes S: "(countable union_of P) S" and T: "(countable union_of P) T"
    and Int: "\<And>S T. P S \<and> P T \<Longrightarrow> P(S \<inter> T)"
  shows "(countable union_of P) (S \<inter> T)"
proof -
  obtain \<U> where "countable \<U>" and \<U>: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S"
    using S by (metis union_of_def)
  obtain \<V> where "countable \<V>" and \<V>: "\<V> \<subseteq> Collect P" "\<Union>\<V> = T"
    using T by (metis union_of_def)
  have "\<And>U V. \<lbrakk>U \<in> \<U>; V \<in> \<V>\<rbrakk> \<Longrightarrow> (countable union_of P) (U \<inter> V)"
    using \<U> \<V> by (metis Ball_Collect countable_union_of_inc local.Int)
  then have "(countable union_of P) (\<Union>U\<in>\<U>. \<Union>V\<in>\<V>. U \<inter> V)"
    by (meson \<open>countable \<U>\<close> \<open>countable \<V>\<close> countable_union_of_UN)
  moreover have "S \<inter> T = (\<Union>U\<in>\<U>. \<Union>V\<in>\<V>. U \<inter> V)"
    by (simp add: \<U> \<V>)
  ultimately show ?thesis
    by presburger
qed

lemma countable_intersection_of_union:
  assumes S: "(countable intersection_of P) S" and T: "(countable intersection_of P) T"
    and Un: "\<And>S T. P S \<and> P T \<Longrightarrow> P(S \<union> T)"
  shows "(countable intersection_of P) (S \<union> T)"
  by (metis (mono_tags, lifting) Compl_Int S T Un compl_sup countable_intersection_of_complement countable_union_of_Int)

end
