(*  Author:     Johannes Hölzl, TU München
*)

section \<open>Partitions and Disjoint Sets\<close>

theory Disjoint_Sets
  imports FuncSet
begin

lemma mono_imp_UN_eq_last: "mono A \<Longrightarrow> (\<Union>i\<le>n. A i) = A n"
  unfolding mono_def by auto

subsection \<open>Set of Disjoint Sets\<close>

abbreviation disjoint :: "'a set set \<Rightarrow> bool" where "disjoint \<equiv> pairwise disjnt"

lemma disjoint_def: "disjoint A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>A. a \<noteq> b \<longrightarrow> a \<inter> b = {})"
  unfolding pairwise_def disjnt_def by auto

lemma disjointI:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<inter> b = {}) \<Longrightarrow> disjoint A"
  unfolding disjoint_def by auto

lemma disjointD:
  "disjoint A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<inter> b = {}"
  unfolding disjoint_def by auto

lemma disjoint_image: "inj_on f (\<Union>A) \<Longrightarrow> disjoint A \<Longrightarrow> disjoint ((`) f ` A)"
  unfolding inj_on_def disjoint_def by blast

lemma assumes "disjoint (A \<union> B)"
      shows   disjoint_unionD1: "disjoint A" and disjoint_unionD2: "disjoint B"
  using assms by (simp_all add: disjoint_def)
  
lemma disjoint_INT:
  assumes *: "\<And>i. i \<in> I \<Longrightarrow> disjoint (F i)"
  shows "disjoint {\<Inter>i\<in>I. X i | X. \<forall>i\<in>I. X i \<in> F i}"
proof (safe intro!: disjointI del: equalityI)
  fix A B :: "'a \<Rightarrow> 'b set" assume "(\<Inter>i\<in>I. A i) \<noteq> (\<Inter>i\<in>I. B i)"
  then obtain i where "A i \<noteq> B i" "i \<in> I"
    by auto
  moreover assume "\<forall>i\<in>I. A i \<in> F i" "\<forall>i\<in>I. B i \<in> F i"
  ultimately show "(\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i) = {}"
    using *[OF \<open>i\<in>I\<close>, THEN disjointD, of "A i" "B i"]
    by (auto simp flip: INT_Int_distrib)
qed

lemma diff_Union_pairwise_disjoint:
  assumes "pairwise disjnt \<A>" "\<B> \<subseteq> \<A>"
  shows "\<Union>\<A> - \<Union>\<B> = \<Union>(\<A> - \<B>)"
proof -
  have "False"
    if x: "x \<in> A" "x \<in> B" and AB: "A \<in> \<A>" "A \<notin> \<B>" "B \<in> \<B>" for x A B
  proof -
    have "A \<inter> B = {}"
      using assms disjointD AB by blast
  with x show ?thesis
    by blast
  qed
  then show ?thesis by auto
qed

lemma Int_Union_pairwise_disjoint:
  assumes "pairwise disjnt (\<A> \<union> \<B>)"
  shows "\<Union>\<A> \<inter> \<Union>\<B> = \<Union>(\<A> \<inter> \<B>)"
proof -
  have "False"
    if x: "x \<in> A" "x \<in> B" and AB: "A \<in> \<A>" "A \<notin> \<B>" "B \<in> \<B>" for x A B
  proof -
    have "A \<inter> B = {}"
      using assms disjointD AB by blast
  with x show ?thesis
    by blast
  qed
  then show ?thesis by auto
qed

lemma psubset_Union_pairwise_disjoint:
  assumes \<B>: "pairwise disjnt \<B>" and "\<A> \<subset> \<B> - {{}}"
  shows "\<Union>\<A> \<subset> \<Union>\<B>"
  unfolding psubset_eq
proof
  show "\<Union>\<A> \<subseteq> \<Union>\<B>"
    using assms by blast
  have "\<A> \<subseteq> \<B>" "\<Union>(\<B> - \<A> \<inter> (\<B> - {{}})) \<noteq> {}"
    using assms by blast+
  then show "\<Union>\<A> \<noteq> \<Union>\<B>"
    using diff_Union_pairwise_disjoint [OF \<B>] by blast
qed

subsubsection "Family of Disjoint Sets"

definition disjoint_family_on :: "('i \<Rightarrow> 'a set) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "disjoint_family_on A S \<longleftrightarrow> (\<forall>m\<in>S. \<forall>n\<in>S. m \<noteq> n \<longrightarrow> A m \<inter> A n = {})"

abbreviation "disjoint_family A \<equiv> disjoint_family_on A UNIV"

lemma disjoint_family_elem_disjnt:
  assumes "infinite A" "finite C"
      and df: "disjoint_family_on B A"
  obtains x where "x \<in> A" "disjnt C (B x)"
proof -
  have "False" if *: "\<forall>x \<in> A. \<exists>y. y \<in> C \<and> y \<in> B x"
  proof -
    obtain g where g: "\<forall>x \<in> A. g x \<in> C \<and> g x \<in> B x"
      using * by metis
    with df have "inj_on g A"
      by (fastforce simp add: inj_on_def disjoint_family_on_def)
    then have "infinite (g ` A)"
      using \<open>infinite A\<close> finite_image_iff by blast
    then show False
      by (meson \<open>finite C\<close> finite_subset g image_subset_iff)
  qed
  then show ?thesis
    by (force simp: disjnt_iff intro: that)
qed

lemma disjoint_family_onD:
  "disjoint_family_on A I \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  by (auto simp: disjoint_family_on_def)

lemma disjoint_family_subset: "disjoint_family A \<Longrightarrow> (\<And>x. B x \<subseteq> A x) \<Longrightarrow> disjoint_family B"
  by (force simp add: disjoint_family_on_def)

lemma disjoint_family_on_insert:
  "i \<notin> I \<Longrightarrow> disjoint_family_on A (insert i I) \<longleftrightarrow> A i \<inter> (\<Union>i\<in>I. A i) = {} \<and> disjoint_family_on A I"
  by (fastforce simp: disjoint_family_on_def)

lemma disjoint_family_on_bisimulation:
  assumes "disjoint_family_on f S"
  and "\<And>n m. n \<in> S \<Longrightarrow> m \<in> S \<Longrightarrow> n \<noteq> m \<Longrightarrow> f n \<inter> f m = {} \<Longrightarrow> g n \<inter> g m = {}"
  shows "disjoint_family_on g S"
  using assms unfolding disjoint_family_on_def by auto

lemma disjoint_family_on_mono:
  "A \<subseteq> B \<Longrightarrow> disjoint_family_on f B \<Longrightarrow> disjoint_family_on f A"
  unfolding disjoint_family_on_def by auto

lemma disjoint_family_Suc:
  "(\<And>n. A n \<subseteq> A (Suc n)) \<Longrightarrow> disjoint_family (\<lambda>i. A (Suc i) - A i)"
  using lift_Suc_mono_le[of A]
  by (auto simp add: disjoint_family_on_def)
     (metis insert_absorb insert_subset le_SucE le_antisym not_le_imp_less less_imp_le)

lemma disjoint_family_on_disjoint_image:
  "disjoint_family_on A I \<Longrightarrow> disjoint (A ` I)"
  unfolding disjoint_family_on_def disjoint_def by force
 
lemma disjoint_family_on_vimageI: "disjoint_family_on F I \<Longrightarrow> disjoint_family_on (\<lambda>i. f -` F i) I"
  by (auto simp: disjoint_family_on_def)

lemma disjoint_image_disjoint_family_on:
  assumes d: "disjoint (A ` I)" and i: "inj_on A I"
  shows "disjoint_family_on A I"
  unfolding disjoint_family_on_def
proof (intro ballI impI)
  fix n m assume nm: "m \<in> I" "n \<in> I" and "n \<noteq> m"
  with i[THEN inj_onD, of n m] show "A n \<inter> A m = {}"
    by (intro disjointD[OF d]) auto
qed

lemma disjoint_family_on_iff_disjoint_image:
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<noteq> {}"
  shows "disjoint_family_on A I \<longleftrightarrow> disjoint (A ` I) \<and> inj_on A I"
proof
  assume "disjoint_family_on A I"
  then show "disjoint (A ` I) \<and> inj_on A I"
    by (metis (mono_tags, lifting) assms disjoint_family_onD disjoint_family_on_disjoint_image inf.idem inj_onI)
qed (use disjoint_image_disjoint_family_on in metis)

lemma card_UN_disjoint':
  assumes "disjoint_family_on A I" "\<And>i. i \<in> I \<Longrightarrow> finite (A i)" "finite I"
  shows "card (\<Union>i\<in>I. A i) = (\<Sum>i\<in>I. card (A i))"
  using assms   by (simp add: card_UN_disjoint disjoint_family_on_def)

lemma disjoint_UN:
  assumes F: "\<And>i. i \<in> I \<Longrightarrow> disjoint (F i)" and *: "disjoint_family_on (\<lambda>i. \<Union>(F i)) I"
  shows "disjoint (\<Union>i\<in>I. F i)"
proof (safe intro!: disjointI del: equalityI)
  fix A B i j assume "A \<noteq> B" "A \<in> F i" "i \<in> I" "B \<in> F j" "j \<in> I"
  show "A \<inter> B = {}"
  proof cases
    assume "i = j" with F[of i] \<open>i \<in> I\<close> \<open>A \<in> F i\<close> \<open>B \<in> F j\<close> \<open>A \<noteq> B\<close> show "A \<inter> B = {}"
      by (auto dest: disjointD)
  next
    assume "i \<noteq> j"
    with * \<open>i\<in>I\<close> \<open>j\<in>I\<close> have "(\<Union>(F i)) \<inter> (\<Union>(F j)) = {}"
      by (rule disjoint_family_onD)
    with \<open>A\<in>F i\<close> \<open>i\<in>I\<close> \<open>B\<in>F j\<close> \<open>j\<in>I\<close>
    show "A \<inter> B = {}"
      by auto
  qed
qed

lemma distinct_list_bind: 
  assumes "distinct xs" "\<And>x. x \<in> set xs \<Longrightarrow> distinct (f x)" 
          "disjoint_family_on (set \<circ> f) (set xs)"
  shows   "distinct (List.bind xs f)"
  using assms
  by (induction xs)
     (auto simp: disjoint_family_on_def distinct_map inj_on_def set_list_bind)

lemma bij_betw_UNION_disjoint:
  assumes disj: "disjoint_family_on A' I"
  assumes bij: "\<And>i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
  shows   "bij_betw f (\<Union>i\<in>I. A i) (\<Union>i\<in>I. A' i)"
unfolding bij_betw_def
proof
  from bij show eq: "f ` \<Union>(A ` I) = \<Union>(A' ` I)"
    by (auto simp: bij_betw_def image_UN)
  show "inj_on f (\<Union>(A ` I))"
  proof (rule inj_onI, clarify)
    fix i j x y assume A: "i \<in> I" "j \<in> I" "x \<in> A i" "y \<in> A j" and B: "f x = f y"
    from A bij[of i] bij[of j] have "f x \<in> A' i" "f y \<in> A' j"
      by (auto simp: bij_betw_def)
    with B have "A' i \<inter> A' j \<noteq> {}" by auto
    with disj A have "i = j" unfolding disjoint_family_on_def by blast
    with A B bij[of i] show "x = y" by (auto simp: bij_betw_def dest: inj_onD)
  qed
qed

lemma disjoint_union: "disjoint C \<Longrightarrow> disjoint B \<Longrightarrow> \<Union>C \<inter> \<Union>B = {} \<Longrightarrow> disjoint (C \<union> B)"
  using disjoint_UN[of "{C, B}" "\<lambda>x. x"] by (auto simp add: disjoint_family_on_def)

text \<open>
  Sum/product of the union of a finite disjoint family
\<close>
context comm_monoid_set
begin

lemma UNION_disjoint_family:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "disjoint_family_on A I"
  shows "F g (\<Union>(A ` I)) = F (\<lambda>x. F g (A x)) I"
  using assms unfolding disjoint_family_on_def  by (rule UNION_disjoint)

lemma Union_disjoint_sets:
  assumes "\<forall>A\<in>C. finite A" and "disjoint C"
  shows "F g (\<Union>C) = (F \<circ> F) g C"
  using assms unfolding disjoint_def  by (rule Union_disjoint)

end

text \<open>
  The union of an infinite disjoint family of non-empty sets is infinite.
\<close>
lemma infinite_disjoint_family_imp_infinite_UNION:
  assumes "\<not>finite A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> {}" "disjoint_family_on f A"
  shows   "\<not>finite (\<Union>(f ` A))"
proof -
  define g where "g x = (SOME y. y \<in> f x)" for x
  have g: "g x \<in> f x" if "x \<in> A" for x
    unfolding g_def by (rule someI_ex, insert assms(2) that) blast
  have inj_on_g: "inj_on g A"
  proof (rule inj_onI, rule ccontr)
    fix x y assume A: "x \<in> A" "y \<in> A" "g x = g y" "x \<noteq> y"
    with g[of x] g[of y] have "g x \<in> f x" "g x \<in> f y" by auto
    with A \<open>x \<noteq> y\<close> assms show False
      by (auto simp: disjoint_family_on_def inj_on_def)
  qed
  from g have "g ` A \<subseteq> \<Union>(f ` A)" by blast
  moreover from inj_on_g \<open>\<not>finite A\<close> have "\<not>finite (g ` A)"
    using finite_imageD by blast
  ultimately show ?thesis using finite_subset by blast
qed  
  

subsection \<open>Construct Disjoint Sequences\<close>

definition disjointed :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set" where
  "disjointed A n = A n - (\<Union>i\<in>{0..<n}. A i)"

lemma finite_UN_disjointed_eq: "(\<Union>i\<in>{0..<n}. disjointed A i) = (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case by (simp add: atLeastLessThanSuc disjointed_def)
qed

lemma UN_disjointed_eq: "(\<Union>i. disjointed A i) = (\<Union>i. A i)"
  by (rule UN_finite2_eq [where k=0])
     (simp add: finite_UN_disjointed_eq)

lemma less_disjoint_disjointed: "m < n \<Longrightarrow> disjointed A m \<inter> disjointed A n = {}"
  by (auto simp add: disjointed_def)

lemma disjoint_family_disjointed: "disjoint_family (disjointed A)"
  by (simp add: disjoint_family_on_def)
     (metis neq_iff Int_commute less_disjoint_disjointed)

lemma disjointed_subset: "disjointed A n \<subseteq> A n"
  by (auto simp add: disjointed_def)

lemma disjointed_0[simp]: "disjointed A 0 = A 0"
  by (simp add: disjointed_def)

lemma disjointed_mono: "mono A \<Longrightarrow> disjointed A (Suc n) = A (Suc n) - A n"
  using mono_imp_UN_eq_last[of A] by (simp add: disjointed_def atLeastLessThanSuc_atLeastAtMost atLeast0AtMost)

subsection \<open>Partitions\<close>

text \<open>
  Partitions \<^term>\<open>P\<close> of a set \<^term>\<open>A\<close>. We explicitly disallow empty sets.
\<close>

definition partition_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
where
  "partition_on A P \<longleftrightarrow> \<Union>P = A \<and> disjoint P \<and> {} \<notin> P"

lemma partition_onI:
  "\<Union>P = A \<Longrightarrow> (\<And>p q. p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> p \<noteq> q \<Longrightarrow> disjnt p q) \<Longrightarrow> {} \<notin> P \<Longrightarrow> partition_on A P"
  by (auto simp: partition_on_def pairwise_def)

lemma partition_onD1: "partition_on A P \<Longrightarrow> A = \<Union>P"
  by (auto simp: partition_on_def)

lemma partition_onD2: "partition_on A P \<Longrightarrow> disjoint P"
  by (auto simp: partition_on_def)

lemma partition_onD3: "partition_on A P \<Longrightarrow> {} \<notin> P"
  by (auto simp: partition_on_def)

subsection \<open>Constructions of partitions\<close>

lemma partition_on_empty: "partition_on {} P \<longleftrightarrow> P = {}"
  unfolding partition_on_def by fastforce

lemma partition_on_space: "A \<noteq> {} \<Longrightarrow> partition_on A {A}"
  by (auto simp: partition_on_def disjoint_def)

lemma partition_on_singletons: "partition_on A ((\<lambda>x. {x}) ` A)"
  by (auto simp: partition_on_def disjoint_def)

lemma partition_on_transform:
  assumes P: "partition_on A P"
  assumes F_UN: "\<Union>(F ` P) = F (\<Union>P)" and F_disjnt: "\<And>p q. p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> disjnt p q \<Longrightarrow> disjnt (F p) (F q)"
  shows "partition_on (F A) (F ` P - {{}})"
proof -
  have "\<Union>(F ` P - {{}}) = F A"
    unfolding P[THEN partition_onD1] F_UN[symmetric] by auto
  with P show ?thesis
    by (auto simp add: partition_on_def pairwise_def intro!: F_disjnt)
qed

lemma partition_on_restrict: "partition_on A P \<Longrightarrow> partition_on (B \<inter> A) ((\<inter>) B ` P - {{}})"
  by (intro partition_on_transform) (auto simp: disjnt_def)

lemma partition_on_vimage: "partition_on A P \<Longrightarrow> partition_on (f -` A) ((-`) f ` P - {{}})"
  by (intro partition_on_transform) (auto simp: disjnt_def)

lemma partition_on_inj_image:
  assumes P: "partition_on A P" and f: "inj_on f A"
  shows "partition_on (f ` A) ((`) f ` P - {{}})"
proof (rule partition_on_transform[OF P])
  show "p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> disjnt p q \<Longrightarrow> disjnt (f ` p) (f ` q)" for p q
    using f[THEN inj_onD] P[THEN partition_onD1] by (auto simp: disjnt_def)
qed auto

lemma partition_on_insert:
  assumes "disjnt p (\<Union>P)"
  shows "partition_on A (insert p P) \<longleftrightarrow> partition_on (A-p) P \<and> p \<subseteq> A \<and> p \<noteq> {}"
  using assms
  by (auto simp: partition_on_def disjnt_iff pairwise_insert)

subsection \<open>Finiteness of partitions\<close>

lemma finitely_many_partition_on:
  assumes "finite A"
  shows "finite {P. partition_on A P}"
proof (rule finite_subset)
  show "{P. partition_on A P} \<subseteq> Pow (Pow A)"
    unfolding partition_on_def by auto
  show "finite (Pow (Pow A))"
    using assms by simp
qed

lemma finite_elements: "finite A \<Longrightarrow> partition_on A P \<Longrightarrow> finite P"
  using partition_onD1[of A P] by (simp add: finite_UnionD)

lemma product_partition:
  assumes "partition_on A P" and "\<And>p. p \<in> P \<Longrightarrow> finite p" 
  shows "card A = (\<Sum>p\<in>P. card p)"
  using assms unfolding partition_on_def  by (meson card_Union_disjoint)

subsection \<open>Equivalence of partitions and equivalence classes\<close>

lemma partition_on_quotient:
  assumes r: "equiv A r"
  shows "partition_on A (A // r)"
proof (rule partition_onI)
  from r have "r \<subseteq> A \<times> A" and "refl_on A r"
    by (auto elim: equivE)
  then show "\<Union>(A // r) = A" "{} \<notin> A // r"
    by (auto simp: refl_on_def quotient_def)

  fix p q assume "p \<in> A // r" "q \<in> A // r" "p \<noteq> q"
  then obtain x y where "x \<in> A" "y \<in> A" "p = r `` {x}" "q = r `` {y}"
    by (auto simp: quotient_def)
  with r equiv_class_eq_iff[OF r, of x y] \<open>p \<noteq> q\<close> show "disjnt p q"
    by (auto simp: disjnt_equiv_class)
qed

lemma equiv_partition_on:
  assumes P: "partition_on A P"
  shows "equiv A {(x, y). \<exists>p \<in> P. x \<in> p \<and> y \<in> p}"
proof (rule equivI)
  have "A = \<Union>P"
    using P by (auto simp: partition_on_def)

  show "{(x, y). \<exists>p \<in> P. x \<in> p \<and> y \<in> p} \<subseteq> A \<times> A"
    unfolding \<open>A = \<Union>P\<close> by blast

  show "refl_on A {(x, y). \<exists>p\<in>P. x \<in> p \<and> y \<in> p}"
    unfolding refl_on_def \<open>A = \<Union>P\<close> by auto
next
  show "trans {(x, y). \<exists>p\<in>P. x \<in> p \<and> y \<in> p}"
    using P by (auto simp only: trans_def disjoint_def partition_on_def)
next
  show "sym {(x, y). \<exists>p\<in>P. x \<in> p \<and> y \<in> p}"
    by (auto simp only: sym_def)
qed

lemma partition_on_eq_quotient:
  assumes P: "partition_on A P"
  shows "A // {(x, y). \<exists>p \<in> P. x \<in> p \<and> y \<in> p} = P"
  unfolding quotient_def
proof safe
  fix x assume "x \<in> A"
  then obtain p where "p \<in> P" "x \<in> p" "\<And>q. q \<in> P \<Longrightarrow> x \<in> q \<Longrightarrow> p = q"
    using P by (auto simp: partition_on_def disjoint_def)
  then have "{y. \<exists>p\<in>P. x \<in> p \<and> y \<in> p} = p"
    by (safe intro!: bexI[of _ p]) simp
  then show "{(x, y). \<exists>p\<in>P. x \<in> p \<and> y \<in> p} `` {x} \<in> P"
    by (simp add: \<open>p \<in> P\<close>)
next
  fix p assume "p \<in> P"
  then have "p \<noteq> {}"
    using P by (auto simp: partition_on_def)
  then obtain x where "x \<in> p"
    by auto
  then have "x \<in> A" "\<And>q. q \<in> P \<Longrightarrow> x \<in> q \<Longrightarrow> p = q"
    using P \<open>p \<in> P\<close> by (auto simp: partition_on_def disjoint_def)
  with \<open>p\<in>P\<close> \<open>x \<in> p\<close> have "{y. \<exists>p\<in>P. x \<in> p \<and> y \<in> p} = p"
    by (safe intro!: bexI[of _ p]) simp
  then show "p \<in> (\<Union>x\<in>A. {{(x, y). \<exists>p\<in>P. x \<in> p \<and> y \<in> p} `` {x}})"
    by (auto intro: \<open>x \<in> A\<close>)
qed

lemma partition_on_alt: "partition_on A P \<longleftrightarrow> (\<exists>r. equiv A r \<and> P = A // r)"
  by (auto simp: partition_on_eq_quotient intro!: partition_on_quotient intro: equiv_partition_on)

subsection \<open>Refinement of partitions\<close>

definition refines :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "refines A P Q \<equiv>
        partition_on A P \<and> partition_on A Q \<and> (\<forall>X\<in>P. \<exists>Y\<in>Q. X \<subseteq> Y)" 

lemma refines_refl: "partition_on A P \<Longrightarrow> refines A P P"
  using refines_def by blast

lemma refines_asym1:
  assumes "refines A P Q" "refines A Q P"
  shows "P \<subseteq> Q"
proof 
  fix X
  assume "X \<in> P"
  then obtain Y X' where "Y \<in> Q" "X \<subseteq> Y" "X' \<in> P" "Y \<subseteq> X'"
    by (meson assms refines_def)
  then have "X' = X"
    using assms(2) unfolding partition_on_def refines_def
    by (metis \<open>X \<in> P\<close> \<open>X \<subseteq> Y\<close> disjnt_self_iff_empty disjnt_subset1 pairwiseD)
  then show "X \<in> Q"
    using \<open>X \<subseteq> Y\<close> \<open>Y \<in> Q\<close> \<open>Y \<subseteq> X'\<close> by force
qed

lemma refines_asym: "\<lbrakk>refines A P Q; refines A Q P\<rbrakk> \<Longrightarrow> P=Q"
  by (meson antisym_conv refines_asym1)

lemma refines_trans: "\<lbrakk>refines A P Q; refines A Q R\<rbrakk> \<Longrightarrow> refines A P R"
  by (meson order.trans refines_def)

lemma refines_obtains_subset:
  assumes "refines A P Q" "q \<in> Q"
  shows "partition_on q {p \<in> P. p \<subseteq> q}"
proof -
  have "p \<subseteq> q \<or> disjnt p q" if "p \<in> P" for p
    using that assms unfolding refines_def partition_on_def disjoint_def
    by (metis disjnt_def disjnt_subset1)
  with assms have "q \<subseteq> Union {p \<in> P. p \<subseteq> q}"
    using assms 
   by (clarsimp simp: refines_def disjnt_iff partition_on_def) (metis Union_iff)
  with assms have "q = Union {p \<in> P. p \<subseteq> q}"
    by auto
  then show ?thesis
    using assms by (auto simp: refines_def disjoint_def partition_on_def)
qed 

subsection \<open>The coarsest common refinement of a set of partitions\<close>

definition common_refinement :: "'a set set set \<Rightarrow> 'a set set"
  where "common_refinement \<P> \<equiv> (\<Union>f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P). {\<Inter> (f ` \<P>)}) - {{}}" 

text \<open>With non-extensional function space\<close>
lemma common_refinement: "common_refinement \<P> = (\<Union>f \<in> (\<Pi> P\<in>\<P>. P). {\<Inter> (f ` \<P>)}) - {{}}" 
  (is "?lhs = ?rhs")
proof
  show "?rhs \<subseteq> ?lhs"
    apply (clarsimp simp add: common_refinement_def PiE_def Ball_def)
    by (metis restrict_Pi_cancel image_restrict_eq restrict_extensional)
qed (auto simp add: common_refinement_def PiE_def)

lemma common_refinement_exists: "\<lbrakk>X \<in> common_refinement \<P>; P \<in> \<P>\<rbrakk> \<Longrightarrow> \<exists>R\<in>P. X \<subseteq> R"
  by (auto simp add: common_refinement)

lemma Union_common_refinement: "\<Union> (common_refinement \<P>) = (\<Inter> P\<in>\<P>. \<Union>P)"
proof
  show "(\<Inter> P\<in>\<P>. \<Union>P) \<subseteq> \<Union> (common_refinement \<P>)"
  proof (clarsimp simp: common_refinement)
    fix x
    assume "\<forall>P\<in>\<P>. \<exists>X\<in>P. x \<in> X"
    then obtain F where F: "\<And>P. P\<in>\<P> \<Longrightarrow> F P \<in> P \<and> x \<in> F P"
      by metis
    then have "x \<in> \<Inter> (F ` \<P>)"
      by force
    with F show "\<exists>X\<in>(\<Union>x\<in>\<Pi> P\<in>\<P>. P. {\<Inter> (x ` \<P>)}) - {{}}. x \<in> X"
      by (auto simp add: Pi_iff Bex_def)
  qed
qed (auto simp: common_refinement_def)

lemma partition_on_common_refinement:
  assumes A: "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" and "\<P> \<noteq> {}"
  shows "partition_on A (common_refinement \<P>)"
proof (rule partition_onI)
  show "\<Union> (common_refinement \<P>) = A"
    using assms by (simp add: partition_on_def Union_common_refinement)
  fix P Q
  assume "P \<in> common_refinement \<P>" and "Q \<in> common_refinement \<P>" and "P \<noteq> Q"
  then obtain f g where f: "f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P)" and P: "P = \<Inter> (f ` \<P>)" and "P \<noteq> {}"
                  and   g: "g \<in> (\<Pi>\<^sub>E P\<in>\<P>. P)" and Q: "Q = \<Inter> (g ` \<P>)" and "Q \<noteq> {}"
    by (auto simp add: common_refinement_def)
  have "f=g" if "x \<in> P" "x \<in> Q" for x
  proof (rule extensionalityI [of _ \<P>])
    fix R
    assume "R \<in> \<P>"
    with that P Q f g A [unfolded partition_on_def, OF \<open>R \<in> \<P>\<close>]
    show "f R = g R"
      by (metis INT_E Int_iff PiE_iff disjointD emptyE)
  qed (use PiE_iff f g in auto)
  then show "disjnt P Q"
    by (metis P Q \<open>P \<noteq> Q\<close> disjnt_iff) 
qed (simp add: common_refinement_def)

lemma refines_common_refinement:
  assumes "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" "P \<in> \<P>"
  shows "refines A (common_refinement \<P>) P"
  unfolding refines_def
proof (intro conjI strip)
  fix X
  assume "X \<in> common_refinement \<P>"
  with assms show "\<exists>Y\<in>P. X \<subseteq> Y"
    by (auto simp: common_refinement_def)
qed (use assms partition_on_common_refinement in auto)

text \<open>The common refinement is itself refined by any other\<close>
lemma common_refinement_coarsest:
  assumes "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" "partition_on A R" "\<And>P. P \<in> \<P> \<Longrightarrow> refines A R P" "\<P> \<noteq> {}"
  shows "refines A R (common_refinement \<P>)"
  unfolding refines_def
proof (intro conjI ballI partition_on_common_refinement)
  fix X
  assume "X \<in> R"
  have "\<exists>p \<in> P. X \<subseteq> p" if "P \<in> \<P>" for P
    by (meson \<open>X \<in> R\<close> assms(3) refines_def that)
  then obtain F where f: "\<And>P. P \<in> \<P> \<Longrightarrow> F P \<in> P \<and> X \<subseteq> F P"
    by metis
  with \<open>partition_on A R\<close> \<open>X \<in> R\<close> \<open>\<P> \<noteq> {}\<close>
  have "\<Inter> (F ` \<P>) \<in> common_refinement \<P>"
    apply (simp add: partition_on_def common_refinement Pi_iff Bex_def)
    by (metis (no_types, lifting) cINF_greatest subset_empty)
  with f show "\<exists>Y\<in>common_refinement \<P>. X \<subseteq> Y"
    by (metis \<open>\<P> \<noteq> {}\<close> cINF_greatest)
qed (use assms in auto)

lemma finite_common_refinement:
  assumes "finite \<P>" "\<And>P. P \<in> \<P> \<Longrightarrow> finite P"
  shows "finite (common_refinement \<P>)"
proof -
  have "finite (\<Pi>\<^sub>E P\<in>\<P>. P)"
    by (simp add: assms finite_PiE)
  then show ?thesis
    by (auto simp: common_refinement_def)
qed

lemma card_common_refinement:
  assumes "finite \<P>" "\<And>P. P \<in> \<P> \<Longrightarrow> finite P"
  shows "card (common_refinement \<P>) \<le> (\<Prod>P \<in> \<P>. card P)"
proof -
  have "card (common_refinement \<P>) \<le> card (\<Union>f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P). {\<Inter> (f ` \<P>)})"
    unfolding common_refinement_def by (meson card_Diff1_le)
  also have "\<dots> \<le> (\<Sum>f\<in>(\<Pi>\<^sub>E P\<in>\<P>. P). card{\<Inter> (f ` \<P>)})"
    by (metis assms finite_PiE card_UN_le)
  also have "\<dots> = card(\<Pi>\<^sub>E P\<in>\<P>. P)"
    by simp
  also have "\<dots> = (\<Prod>P \<in> \<P>. card P)"
    by (simp add: assms(1) card_PiE dual_order.eq_iff)
  finally show ?thesis .
qed

end
