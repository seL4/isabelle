(*  Title:      HOL/Order_Relation.thy
    Author:     Tobias Nipkow
    Author:     Andrei Popescu, TU Muenchen
*)

section \<open>Orders as Relations\<close>

theory Order_Relation
imports Wfrec
begin

subsection \<open>Orders on a set\<close>

definition "preorder_on A r \<equiv> r \<subseteq> A \<times> A \<and> refl_on A r \<and> trans r"

definition "partial_order_on A r \<equiv> preorder_on A r \<and> antisym r"

definition "linear_order_on A r \<equiv> partial_order_on A r \<and> total_on A r"

definition "strict_linear_order_on A r \<equiv> trans r \<and> irrefl r \<and> total_on A r"

definition "well_order_on A r \<equiv> linear_order_on A r \<and> wf(r - Id)"

lemmas order_on_defs =
  preorder_on_def partial_order_on_def linear_order_on_def
  strict_linear_order_on_def well_order_on_def

lemma partial_order_onD:
  assumes "partial_order_on A r" shows "refl_on A r" and "trans r" and "antisym r" and "r \<subseteq> A \<times> A"
  using assms unfolding partial_order_on_def preorder_on_def by auto

lemma preorder_on_empty[simp]: "preorder_on {} {}"
  by (simp add: preorder_on_def trans_def)

lemma partial_order_on_empty[simp]: "partial_order_on {} {}"
  by (simp add: partial_order_on_def)

lemma lnear_order_on_empty[simp]: "linear_order_on {} {}"
  by (simp add: linear_order_on_def)

lemma well_order_on_empty[simp]: "well_order_on {} {}"
  by (simp add: well_order_on_def)


lemma preorder_on_converse[simp]: "preorder_on A (r\<inverse>) = preorder_on A r"
  by (auto simp add: preorder_on_def)

lemma partial_order_on_converse[simp]: "partial_order_on A (r\<inverse>) = partial_order_on A r"
  by (simp add: partial_order_on_def)

lemma linear_order_on_converse[simp]: "linear_order_on A (r\<inverse>) = linear_order_on A r"
  by (simp add: linear_order_on_def)


lemma partial_order_on_acyclic:
  "partial_order_on A r \<Longrightarrow> acyclic (r - Id)"
  by (simp add: acyclic_irrefl partial_order_on_def preorder_on_def trans_diff_Id)

lemma partial_order_on_well_order_on:               
  "finite r \<Longrightarrow> partial_order_on A r \<Longrightarrow> wf (r - Id)" 
  by (simp add: finite_acyclic_wf partial_order_on_acyclic) 

lemma strict_linear_order_on_diff_Id: "linear_order_on A r \<Longrightarrow> strict_linear_order_on A (r - Id)"
  by (simp add: order_on_defs trans_diff_Id)

lemma linear_order_on_singleton [simp]: "linear_order_on {x} {(x, x)}"
  by (simp add: order_on_defs)

lemma linear_order_on_acyclic:
  assumes "linear_order_on A r"
  shows "acyclic (r - Id)"
  using strict_linear_order_on_diff_Id[OF assms]
  by (auto simp add: acyclic_irrefl strict_linear_order_on_def)

lemma linear_order_on_well_order_on:
  assumes "finite r"
  shows "linear_order_on A r \<longleftrightarrow> well_order_on A r"
  unfolding well_order_on_def
  using assms finite_acyclic_wf[OF _ linear_order_on_acyclic, of r] by blast


subsection \<open>Orders on the field\<close>

abbreviation "Refl r \<equiv> refl_on (Field r) r"

abbreviation "Preorder r \<equiv> preorder_on (Field r) r"

abbreviation "Partial_order r \<equiv> partial_order_on (Field r) r"

abbreviation "Total r \<equiv> total_on (Field r) r"

abbreviation "Linear_order r \<equiv> linear_order_on (Field r) r"

abbreviation "Well_order r \<equiv> well_order_on (Field r) r"


lemma subset_Image_Image_iff:
  "Preorder r \<Longrightarrow> A \<subseteq> Field r \<Longrightarrow> B \<subseteq> Field r \<Longrightarrow>
    r `` A \<subseteq> r `` B \<longleftrightarrow> (\<forall>a\<in>A.\<exists>b\<in>B. (b, a) \<in> r)"
  apply (simp add: preorder_on_def refl_on_def Image_def subset_eq)
  apply (simp only: trans_def)
  apply fast
  done

lemma subset_Image1_Image1_iff:
  "Preorder r \<Longrightarrow> a \<in> Field r \<Longrightarrow> b \<in> Field r \<Longrightarrow> r `` {a} \<subseteq> r `` {b} \<longleftrightarrow> (b, a) \<in> r"
  by (simp add: subset_Image_Image_iff)

lemma Refl_antisym_eq_Image1_Image1_iff:
  assumes "Refl r"
    and as: "antisym r"
    and abf: "a \<in> Field r" "b \<in> Field r"
  shows "r `` {a} = r `` {b} \<longleftrightarrow> a = b"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have *: "\<And>x. (a, x) \<in> r \<longleftrightarrow> (b, x) \<in> r"
    by (simp add: set_eq_iff)
  have "(a, a) \<in> r" "(b, b) \<in> r" using \<open>Refl r\<close> abf by (simp_all add: refl_on_def)
  then have "(a, b) \<in> r" "(b, a) \<in> r" using *[of a] *[of b] by simp_all
  then show ?rhs
    using \<open>antisym r\<close>[unfolded antisym_def] by blast
next
  assume ?rhs
  then show ?lhs by fast
qed

lemma Partial_order_eq_Image1_Image1_iff:
  "Partial_order r \<Longrightarrow> a \<in> Field r \<Longrightarrow> b \<in> Field r \<Longrightarrow> r `` {a} = r `` {b} \<longleftrightarrow> a = b"
  by (auto simp: order_on_defs Refl_antisym_eq_Image1_Image1_iff)

lemma Total_Id_Field:
  assumes "Total r"
    and not_Id: "\<not> r \<subseteq> Id"
  shows "Field r = Field (r - Id)"
proof -
  have "Field r \<subseteq> Field (r - Id)"
  proof (rule subsetI)
    fix a assume *: "a \<in> Field r"
    from not_Id have "r \<noteq> {}" by fast
    with not_Id obtain b and c where "b \<noteq> c \<and> (b,c) \<in> r" by auto
    then have "b \<noteq> c \<and> {b, c} \<subseteq> Field r" by (auto simp: Field_def)
    with * obtain d where "d \<in> Field r" "d \<noteq> a" by auto
    with * \<open>Total r\<close> have "(a, d) \<in> r \<or> (d, a) \<in> r" by (simp add: total_on_def)
    with \<open>d \<noteq> a\<close> show "a \<in> Field (r - Id)" unfolding Field_def by blast
  qed
  then show ?thesis
    using mono_Field[of "r - Id" r] Diff_subset[of r Id] by auto
qed

subsection\<open>Relations given by a predicate and the field\<close>

definition relation_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set"
  where "relation_of P A \<equiv> { (a, b) \<in> A \<times> A. P a b }"

lemma sym_relation_of[simp]: "sym (relation_of R S) \<longleftrightarrow> symp_on S R"
proof (rule iffI)
  show "sym (relation_of R S) \<Longrightarrow> symp_on S R"
    by (auto simp: relation_of_def intro: symp_onI dest: symD)
next
  show "symp_on S R \<Longrightarrow> sym (relation_of R S)"
    by (auto simp: relation_of_def intro: symI dest: symp_onD)
qed

lemma asym_relation_of[simp]: "asym (relation_of R S) \<longleftrightarrow> asymp_on S R"
proof (rule iffI)
  show "asym (relation_of R S) \<Longrightarrow> asymp_on S R"
    by (auto simp: relation_of_def intro: asymp_onI dest: asymD)
next
  show "asymp_on S R \<Longrightarrow> asym (relation_of R S)"
    by (auto simp: relation_of_def intro: asymI dest: asymp_onD)
qed

lemma antisym_relation_of[simp]: "antisym (relation_of R S) \<longleftrightarrow> antisymp_on S R"
proof (rule iffI)
  show "antisym (relation_of R S) \<Longrightarrow> antisymp_on S R"
    by (simp add: antisym_on_def antisymp_on_def relation_of_def)
next
  show "antisymp_on S R \<Longrightarrow> antisym (relation_of R S)"
    by (simp add: antisym_on_def antisymp_on_def relation_of_def)
qed

lemma trans_relation_of[simp]: "trans (relation_of R S) \<longleftrightarrow> transp_on S R"
proof (rule iffI)
  show "trans (relation_of R S) \<Longrightarrow> transp_on S R"
    by (auto simp: relation_of_def intro: transp_onI dest: transD)
next
  show "transp_on S R \<Longrightarrow> trans (relation_of R S)"
    by (auto simp: relation_of_def intro: transI dest: transp_onD)
qed

lemma Field_relation_of:
  assumes "relation_of P A \<subseteq> A \<times> A" and "refl_on A (relation_of P A)"
  shows "Field (relation_of P A) = A"
  using assms unfolding refl_on_def Field_def by auto

lemma partial_order_on_relation_ofI:
  assumes refl: "\<And>a. a \<in> A \<Longrightarrow> P a a"
    and trans: "\<And>a b c. \<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> P a b \<Longrightarrow> P b c \<Longrightarrow> P a c"
    and antisym: "\<And>a b. \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> P a b \<Longrightarrow> P b a \<Longrightarrow> a = b"
  shows "partial_order_on A (relation_of P A)"
proof -
  have "relation_of P A \<subseteq> A \<times> A"
    unfolding relation_of_def by auto
  moreover have "refl_on A (relation_of P A)"
    using refl unfolding refl_on_def relation_of_def by auto
  moreover have "trans (relation_of P A)" and "antisym (relation_of P A)"
    unfolding relation_of_def
    by (auto intro: transI dest: trans, auto intro: antisymI dest: antisym)
  ultimately show ?thesis
    unfolding partial_order_on_def preorder_on_def by simp
qed

lemma Partial_order_relation_ofI:
  assumes "partial_order_on A (relation_of P A)"
  shows "Partial_order (relation_of P A)"
proof -
  have *: "Field (relation_of P A) = A"
    using assms by (simp_all only: Field_relation_of partial_order_on_def preorder_on_def)
  show ?thesis
    unfolding *
    using assms .
qed


subsection \<open>Orders on a type\<close>

abbreviation "strict_linear_order \<equiv> strict_linear_order_on UNIV"

abbreviation "linear_order \<equiv> linear_order_on UNIV"

abbreviation "well_order \<equiv> well_order_on UNIV"


subsection \<open>Order-like relations\<close>

text \<open>
  In this subsection, we develop basic concepts and results pertaining
  to order-like relations, i.e., to reflexive and/or transitive and/or symmetric and/or
  total relations. We also further define upper and lower bounds operators.
\<close>


subsubsection \<open>Auxiliaries\<close>

corollary well_order_on_domain: "well_order_on A r \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> a \<in> A \<and> b \<in> A"
  by (auto simp add: order_on_defs)

lemma well_order_on_Field: "well_order_on A r \<Longrightarrow> A = Field r"
  by (auto simp add: refl_on_def Field_def order_on_defs)

lemma well_order_on_Well_order: "well_order_on A r \<Longrightarrow> A = Field r \<and> Well_order r"
  using well_order_on_Field [of A] by auto

lemma Total_subset_Id:
  assumes "Total r"
    and "r \<subseteq> Id"
  shows "r = {} \<or> (\<exists>a. r = {(a, a)})"
proof -
  have "\<exists>a. r = {(a, a)}" if "r \<noteq> {}"
  proof -
    from that obtain a b where ab: "(a, b) \<in> r" by fast
    with \<open>r \<subseteq> Id\<close> have "a = b" by blast
    with ab have aa: "(a, a) \<in> r" by simp
    have "a = c \<and> a = d" if "(c, d) \<in> r" for c d
    proof -
      from that have "{a, c, d} \<subseteq> Field r"
        using ab unfolding Field_def by blast
      then have "((a, c) \<in> r \<or> (c, a) \<in> r \<or> a = c) \<and> ((a, d) \<in> r \<or> (d, a) \<in> r \<or> a = d)"
        using \<open>Total r\<close> unfolding total_on_def by blast
      with \<open>r \<subseteq> Id\<close> show ?thesis by blast
    qed
    then have "r \<subseteq> {(a, a)}" by auto
    with aa show ?thesis by blast
  qed
  then show ?thesis by blast
qed

lemma Linear_order_in_diff_Id:
  assumes "Linear_order r"
    and "a \<in> Field r"
    and "b \<in> Field r"
  shows "(a, b) \<in> r \<longleftrightarrow> (b, a) \<notin> r - Id"
  using assms unfolding order_on_defs total_on_def antisym_def Id_def refl_on_def by force


subsubsection \<open>The upper and lower bounds operators\<close>

text \<open>
  Here we define upper (``above") and lower (``below") bounds operators. We
  think of \<open>r\<close> as a \<^emph>\<open>non-strict\<close> relation. The suffix \<open>S\<close> at the names of
  some operators indicates that the bounds are strict -- e.g., \<open>underS a\<close> is
  the set of all strict lower bounds of \<open>a\<close> (w.r.t. \<open>r\<close>). Capitalization of
  the first letter in the name reminds that the operator acts on sets, rather
  than on individual elements.
\<close>

definition under :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "under r a \<equiv> {b. (b, a) \<in> r}"

definition underS :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "underS r a \<equiv> {b. b \<noteq> a \<and> (b, a) \<in> r}"

definition Under :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "Under r A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (b, a) \<in> r}"

definition UnderS :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "UnderS r A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (b, a) \<in> r}"

definition above :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "above r a \<equiv> {b. (a, b) \<in> r}"

definition aboveS :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "aboveS r a \<equiv> {b. b \<noteq> a \<and> (a, b) \<in> r}"

definition Above :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "Above r A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (a, b) \<in> r}"

definition AboveS :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "AboveS r A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (a, b) \<in> r}"

definition ofilter :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "ofilter r A \<equiv> A \<subseteq> Field r \<and> (\<forall>a \<in> A. under r a \<subseteq> A)"

text \<open>
  Note: In the definitions of \<open>Above[S]\<close> and \<open>Under[S]\<close>, we bounded
  comprehension by \<open>Field r\<close> in order to properly cover the case of \<open>A\<close> being
  empty.
\<close>

lemma underS_subset_under: "underS r a \<subseteq> under r a"
  by (auto simp add: underS_def under_def)

lemma underS_notIn: "a \<notin> underS r a"
  by (simp add: underS_def)

lemma Refl_under_in: "Refl r \<Longrightarrow> a \<in> Field r \<Longrightarrow> a \<in> under r a"
  by (simp add: refl_on_def under_def)

lemma AboveS_disjoint: "A \<inter> (AboveS r A) = {}"
  by (auto simp add: AboveS_def)

lemma in_AboveS_underS: "a \<in> Field r \<Longrightarrow> a \<in> AboveS r (underS r a)"
  by (auto simp add: AboveS_def underS_def)

lemma Refl_under_underS: "Refl r \<Longrightarrow> a \<in> Field r \<Longrightarrow> under r a = underS r a \<union> {a}"
  unfolding under_def underS_def
  using refl_on_def[of _ r] by fastforce

lemma underS_empty: "a \<notin> Field r \<Longrightarrow> underS r a = {}"
  by (auto simp: Field_def underS_def)

lemma under_Field: "under r a \<subseteq> Field r"
  by (auto simp: under_def Field_def)

lemma underS_Field: "underS r a \<subseteq> Field r"
  by (auto simp: underS_def Field_def)

lemma underS_Field2: "a \<in> Field r \<Longrightarrow> underS r a \<subset> Field r"
  using underS_notIn underS_Field by fast

lemma underS_Field3: "Field r \<noteq> {} \<Longrightarrow> underS r a \<subset> Field r"
  by (cases "a \<in> Field r") (auto simp: underS_Field2 underS_empty)

lemma AboveS_Field: "AboveS r A \<subseteq> Field r"
  by (auto simp: AboveS_def Field_def)

lemma under_incr:
  assumes "trans r"
    and "(a, b) \<in> r"
  shows "under r a \<subseteq> under r b"
  unfolding under_def
proof safe
  fix x assume "(x, a) \<in> r"
  with assms trans_def[of r] show "(x, b) \<in> r" by blast
qed

lemma underS_incr:
  assumes "trans r"
    and "antisym r"
    and ab: "(a, b) \<in> r"
  shows "underS r a \<subseteq> underS r b"
  unfolding underS_def
proof safe
  assume *: "b \<noteq> a" and **: "(b, a) \<in> r"
  with \<open>antisym r\<close> antisym_def[of r] ab show False
    by blast
next
  fix x assume "x \<noteq> a" "(x, a) \<in> r"
  with ab \<open>trans r\<close> trans_def[of r] show "(x, b) \<in> r"
    by blast
qed

lemma underS_incl_iff:
  assumes LO: "Linear_order r"
    and INa: "a \<in> Field r"
    and INb: "b \<in> Field r"
  shows "underS r a \<subseteq> underS r b \<longleftrightarrow> (a, b) \<in> r"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  with \<open>Linear_order r\<close> show ?lhs
    by (simp add: order_on_defs underS_incr)
next
  assume *: ?lhs
  have "(a, b) \<in> r" if "a = b"
    using assms that by (simp add: order_on_defs refl_on_def)
  moreover have False if "a \<noteq> b" "(b, a) \<in> r"
  proof -
    from that have "b \<in> underS r a" unfolding underS_def by blast
    with * have "b \<in> underS r b" by blast
    then show ?thesis by (simp add: underS_notIn)
  qed
  ultimately show "(a,b) \<in> r"
    using assms order_on_defs[of "Field r" r] total_on_def[of "Field r" r] by blast
qed

lemma finite_Partial_order_induct[consumes 3, case_names step]:
  assumes "Partial_order r"
    and "x \<in> Field r"
    and "finite r"
    and step: "\<And>x. x \<in> Field r \<Longrightarrow> (\<And>y. y \<in> aboveS r x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using assms(2)
proof (induct rule: wf_induct[of "r\<inverse> - Id"])
  case 1
  from assms(1,3) show "wf (r\<inverse> - Id)"
    using partial_order_on_well_order_on partial_order_on_converse by blast
next
  case prems: (2 x)
  show ?case
    by (rule step) (use prems in \<open>auto simp: aboveS_def intro: FieldI2\<close>)
qed

lemma finite_Linear_order_induct[consumes 3, case_names step]:
  assumes "Linear_order r"
    and "x \<in> Field r"
    and "finite r"
    and step: "\<And>x. x \<in> Field r \<Longrightarrow> (\<And>y. y \<in> aboveS r x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using assms(2)
proof (induct rule: wf_induct[of "r\<inverse> - Id"])
  case 1
  from assms(1,3) show "wf (r\<inverse> - Id)"
    using linear_order_on_well_order_on linear_order_on_converse
    unfolding well_order_on_def by blast
next
  case prems: (2 x)
  show ?case
    by (rule step) (use prems in \<open>auto simp: aboveS_def intro: FieldI2\<close>)
qed


subsection \<open>Variations on Well-Founded Relations\<close>

text \<open>
  This subsection contains some variations of the results from \<^theory>\<open>HOL.Wellfounded\<close>:
    \<^item> means for slightly more direct definitions by well-founded recursion;
    \<^item> variations of well-founded induction;
    \<^item> means for proving a linear order to be a well-order.
\<close>


subsubsection \<open>Characterizations of well-foundedness\<close>

text \<open>
  A transitive relation is well-founded iff it is ``locally'' well-founded,
  i.e., iff its restriction to the lower bounds of of any element is
  well-founded.
\<close>

lemma trans_wf_iff:
  assumes "trans r"
  shows "wf r \<longleftrightarrow> (\<forall>a. wf (r \<inter> (r\<inverse>``{a} \<times> r\<inverse>``{a})))"
proof -
  define R where "R a = r \<inter> (r\<inverse>``{a} \<times> r\<inverse>``{a})" for a
  have "wf (R a)" if "wf r" for a
    using that R_def wf_subset[of r "R a"] by auto
  moreover
  have "wf r" if *: "\<forall>a. wf(R a)"
    unfolding wf_def
  proof clarify
    fix phi a
    assume **: "\<forall>a. (\<forall>b. (b, a) \<in> r \<longrightarrow> phi b) \<longrightarrow> phi a"
    define chi where "chi b \<longleftrightarrow> (b, a) \<in> r \<longrightarrow> phi b" for b
    with * have "wf (R a)" by auto
    then have "(\<forall>b. (\<forall>c. (c, b) \<in> R a \<longrightarrow> chi c) \<longrightarrow> chi b) \<longrightarrow> (\<forall>b. chi b)"
      unfolding wf_def by blast
    also have "\<forall>b. (\<forall>c. (c, b) \<in> R a \<longrightarrow> chi c) \<longrightarrow> chi b"
    proof safe
      fix b
      assume "\<forall>c. (c, b) \<in> R a \<longrightarrow> chi c"
      moreover have "(b, a) \<in> r \<Longrightarrow> \<forall>c. (c, b) \<in> r \<and> (c, a) \<in> r \<longrightarrow> phi c \<Longrightarrow> phi b"
      proof -
        assume "(b, a) \<in> r" and "\<forall>c. (c, b) \<in> r \<and> (c, a) \<in> r \<longrightarrow> phi c"
        then have "\<forall>c. (c, b) \<in> r \<longrightarrow> phi c"
          using assms trans_def[of r] by blast
        with ** show "phi b" by blast
      qed
      ultimately show "chi b"
        by (auto simp add: chi_def R_def)
    qed
    finally have  "\<forall>b. chi b" .
    with ** chi_def show "phi a" by blast
  qed
  ultimately show ?thesis unfolding R_def by blast
qed

text\<open>A transitive relation is well-founded if all initial segments are finite.\<close>
corollary wf_finite_segments:
  assumes "irrefl r" and "trans r" and "\<And>x. finite {y. (y, x) \<in> r}"
  shows "wf r"
proof -
  have "\<And>a. acyclic (r \<inter> {x. (x, a) \<in> r} \<times> {x. (x, a) \<in> r})"
  proof -
    fix a
    have "trans (r \<inter> ({x. (x, a) \<in> r} \<times> {x. (x, a) \<in> r}))"
      using assms unfolding trans_def Field_def by blast
    then show "acyclic (r \<inter> {x. (x, a) \<in> r} \<times> {x. (x, a) \<in> r})"
      using assms acyclic_def assms irrefl_def by fastforce
  qed
  then show ?thesis
    by (clarsimp simp: trans_wf_iff wf_iff_acyclic_if_finite converse_def assms)
qed

text \<open>The next lemma is a variation of \<open>wf_eq_minimal\<close> from Wellfounded,
  allowing one to assume the set included in the field.\<close>

lemma wf_eq_minimal2: "wf r \<longleftrightarrow> (\<forall>A. A \<subseteq> Field r \<and> A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a', a) \<notin> r))"
proof-
  let ?phi = "\<lambda>A. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a',a) \<notin> r)"
  have "wf r \<longleftrightarrow> (\<forall>A. ?phi A)"
  proof
    assume "wf r"
    show  "\<forall>A. ?phi A"
    proof clarify
      fix A:: "'a set"
      assume "A \<noteq> {}"
      then obtain x where "x \<in> A"
        by auto
      show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> r"
        apply (rule wfE_min[of r x A])
          apply fact+
        by blast
    qed
  next
    assume *: "\<forall>A. ?phi A"
    then show "wf r"
      apply (clarsimp simp: ex_in_conv [THEN sym])
      apply (rule wfI_min)
      by fast
  qed
  also have "(\<forall>A. ?phi A) \<longleftrightarrow> (\<forall>B \<subseteq> Field r. ?phi B)"
  proof
    assume "\<forall>A. ?phi A"
    then show "\<forall>B \<subseteq> Field r. ?phi B" by simp
  next
    assume *: "\<forall>B \<subseteq> Field r. ?phi B"
    show "\<forall>A. ?phi A"
    proof clarify
      fix A :: "'a set"
      assume **: "A \<noteq> {}"
      define B where "B = A \<inter> Field r"
      show "\<exists>a \<in> A. \<forall>a' \<in> A. (a', a) \<notin> r"
      proof (cases "B = {}")
        case True
        with ** obtain a where a: "a \<in> A" "a \<notin> Field r"
          unfolding B_def by blast
        with a have "\<forall>a' \<in> A. (a',a) \<notin> r"
          unfolding Field_def by blast
        with a show ?thesis by blast
      next
        case False
        have "B \<subseteq> Field r" unfolding B_def by blast
        with False * obtain a where a: "a \<in> B" "\<forall>a' \<in> B. (a', a) \<notin> r"
          by blast
        have "(a', a) \<notin> r" if "a' \<in> A" for a'
        proof
          assume a'a: "(a', a) \<in> r"
          with that have "a' \<in> B" unfolding B_def Field_def by blast
          with a a'a show False by blast
        qed
        with a show ?thesis unfolding B_def by blast
      qed
    qed
  qed
  finally show ?thesis by blast
qed


subsubsection \<open>Characterizations of well-foundedness\<close>

text \<open>
  The next lemma and its corollary enable one to prove that a linear order is
  a well-order in a way which is more standard than via well-foundedness of
  the strict version of the relation.
\<close>

lemma Linear_order_wf_diff_Id:
  assumes "Linear_order r"
  shows "wf (r - Id) \<longleftrightarrow> (\<forall>A \<subseteq> Field r. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r))"
proof (cases "r \<subseteq> Id")
  case True
  then have *: "r - Id = {}" by blast
  have "wf (r - Id)" by (simp add: *)
  moreover have "\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r"
    if *: "A \<subseteq> Field r" and **: "A \<noteq> {}" for A
  proof -
    from \<open>Linear_order r\<close> True
    obtain a where a: "r = {} \<or> r = {(a, a)}"
      unfolding order_on_defs using Total_subset_Id [of r] by blast
    with * ** have "A = {a} \<and> r = {(a, a)}"
      unfolding Field_def by blast
    with a show ?thesis by blast
  qed
  ultimately show ?thesis by blast
next
  case False
  with \<open>Linear_order r\<close> have Field: "Field r = Field (r - Id)"
    unfolding order_on_defs using Total_Id_Field [of r] by blast
  show ?thesis
  proof
    assume *: "wf (r - Id)"
    show "\<forall>A \<subseteq> Field r. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r)"
    proof clarify
      fix A
      assume **: "A \<subseteq> Field r" and ***: "A \<noteq> {}"
      then have "\<exists>a \<in> A. \<forall>a' \<in> A. (a',a) \<notin> r - Id"
        using Field * unfolding wf_eq_minimal2 by simp
      moreover have "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r \<longleftrightarrow> (a', a) \<notin> r - Id"
        using Linear_order_in_diff_Id [OF \<open>Linear_order r\<close>] ** by blast
      ultimately show "\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r" by blast
    qed
  next
    assume *: "\<forall>A \<subseteq> Field r. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r)"
    show "wf (r - Id)"
      unfolding wf_eq_minimal2
    proof clarify
      fix A
      assume **: "A \<subseteq> Field(r - Id)" and ***: "A \<noteq> {}"
      then have "\<exists>a \<in> A. \<forall>a' \<in> A. (a,a') \<in> r"
        using Field * by simp
      moreover have "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r \<longleftrightarrow> (a', a) \<notin> r - Id"
        using Linear_order_in_diff_Id [OF \<open>Linear_order r\<close>] ** mono_Field[of "r - Id" r] by blast
      ultimately show "\<exists>a \<in> A. \<forall>a' \<in> A. (a',a) \<notin> r - Id"
        by blast
    qed
  qed
qed

corollary Linear_order_Well_order_iff:
  "Linear_order r \<Longrightarrow>
    Well_order r \<longleftrightarrow> (\<forall>A \<subseteq> Field r. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> r))"
  unfolding well_order_on_def using Linear_order_wf_diff_Id[of r] by blast

end
