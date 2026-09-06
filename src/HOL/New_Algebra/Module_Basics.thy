section \<open>Modules over a ring\<close>

theory Module_Basics
  imports Ring_Theory Finite_Composite
begin

text \<open>A (left) \<^emph>\<open>module\<close> over the ring @{term R}: an abelian group of elements @{term M} under
  @{text "\<oplus>"} with zero @{text "\<zero>\<^sub>M"}, together with a scalar multiplication @{text "\<odot>"} by ring
  elements satisfying the module axioms.  This is the exact generalisation of
  theory \<open>Vector_Space\<close> from a field of scalars to a ring; a vector space is a module
  whose scalar ring is a field.  We develop the elementary arithmetic (scaling by zero, by the ring
  negation, additivity of finite sums) and the notions of submodule and of a linear combination.\<close>

locale Module = Ring +
  fixes madd :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl \<open>\<oplus>\<close> 65)
    and mzero :: "'b" (\<open>\<zero>\<^sub>M\<close>)
    and mcarrier :: "'b set" (\<open>M\<close>)
    and scale :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixr \<open>\<odot>\<close> 75)
  assumes madd_group: "Abelian_Group M (\<oplus>) \<zero>\<^sub>M"
    and scale_closed: "\<lbrakk> a \<in> R; v \<in> M \<rbrakk> \<Longrightarrow> a \<odot> v \<in> M"
    and scale_distrib_madd: "\<lbrakk> a \<in> R; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> a \<odot> (u \<oplus> v) = (a \<odot> u) \<oplus> (a \<odot> v)"
    and scale_distrib_add: "\<lbrakk> a \<in> R; b \<in> R; v \<in> M \<rbrakk> \<Longrightarrow> (a + b) \<odot> v = (a \<odot> v) \<oplus> (b \<odot> v)"
    and scale_scale: "\<lbrakk> a \<in> R; b \<in> R; v \<in> M \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<odot> v = a \<odot> (b \<odot> v)"
    and scale_one: "v \<in> M \<Longrightarrow> \<one> \<odot> v = v"
begin

text \<open>The additive group of the module, available through the @{text madd} prefix.\<close>
sublocale madd: Abelian_Group M "(\<oplus>)" "\<zero>\<^sub>M"
  by (rule madd_group)

subsection \<open>Elementary closure and arithmetic\<close>

lemma mzero_closed [simp, intro]: "\<zero>\<^sub>M \<in> M" by simp

lemma madd_closed [simp, intro]: "\<lbrakk> u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> M" by simp

text \<open>Scaling the zero element gives the zero element.\<close>
lemma scale_zero_elem:
  assumes a: "a \<in> R"
  shows "a \<odot> \<zero>\<^sub>M = \<zero>\<^sub>M"
proof -
  have w: "a \<odot> \<zero>\<^sub>M \<in> M" using a by (simp add: scale_closed)
  then have eq: "a \<odot> \<zero>\<^sub>M = (a \<odot> \<zero>\<^sub>M) \<oplus> (a \<odot> \<zero>\<^sub>M)"
    by (metis assms madd.left_unit mzero_closed scale_distrib_madd) 
  then show ?thesis
    using madd.invertible_left_inverse2 w by fastforce
qed

text \<open>Scaling by the ring zero gives the zero element.\<close>
lemma scale_zero_scalar:
  assumes v: "v \<in> M"
  shows "\<zero> \<odot> v = \<zero>\<^sub>M"
proof -
  have w: "\<zero> \<odot> v \<in> M" using v by (simp add: scale_closed)
  have eq: "\<zero> \<odot> v = (\<zero> \<odot> v) \<oplus> (\<zero> \<odot> v)"
    using scale_distrib_add v by force 
  then show ?thesis
    using madd.commute_iff_inverse w by fastforce
qed

text \<open>Scaling by the ring negation is the additive inverse of the scaling.\<close>
lemma scale_neg_scalar:
  assumes a: "a \<in> R" and v: "v \<in> M"
  shows "(- a) \<odot> v = madd.inverse (a \<odot> v)"
proof -
  have "(a \<odot> v) \<oplus> ((- a) \<odot> v) = \<zero>\<^sub>M" using a v 
    by (simp add: scale_zero_scalar flip: scale_distrib_add)
  then show ?thesis 
    using a v by (simp add: scale_closed madd.inverse_equality madd.commutative)
qed

subsection \<open>Submodules\<close>

text \<open>A \<^emph>\<open>submodule\<close> is a subset containing the zero element and closed under addition and under
  scaling by arbitrary ring elements.\<close>
definition submodule :: "'b set \<Rightarrow> bool"
  where "submodule N \<equiv> N \<subseteq> M \<and> \<zero>\<^sub>M \<in> N \<and> (\<forall>u\<in>N. \<forall>v\<in>N. u \<oplus> v \<in> N) \<and> (\<forall>a\<in>R. \<forall>v\<in>N. a \<odot> v \<in> N)"

lemma submoduleI:
  assumes "N \<subseteq> M" and "\<zero>\<^sub>M \<in> N"
    and "\<And>u v. \<lbrakk> u \<in> N; v \<in> N \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> N"
    and "\<And>a v. \<lbrakk> a \<in> R; v \<in> N \<rbrakk> \<Longrightarrow> a \<odot> v \<in> N"
  shows "submodule N"
  using assms unfolding submodule_def by blast

lemma submodule_subset: "submodule N \<Longrightarrow> N \<subseteq> M" 
  by (simp add: submodule_def)

lemma submodule_zero: "submodule N \<Longrightarrow> \<zero>\<^sub>M \<in> N"
  by (simp add: submodule_def)

lemma submodule_add: "\<lbrakk> submodule N; u \<in> N; v \<in> N \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> N"
  by (simp add: submodule_def)

lemma submodule_scale: "\<lbrakk> submodule N; a \<in> R; v \<in> N \<rbrakk> \<Longrightarrow> a \<odot> v \<in> N"
  by (simp add: submodule_def)

text \<open>A submodule is closed under the module negation (scale by @{term "- \<one>"}).\<close>
lemma submodule_neg:
  assumes N: "submodule N" and v: "v \<in> N" shows "madd.inverse v \<in> N"
proof -
  have vM: "v \<in> M" using N v submodule_subset by blast
  have "madd.inverse v = (- \<one>) \<odot> v" using vM by (simp add: scale_neg_scalar scale_one)
  moreover have "(- \<one>) \<odot> v \<in> N" using N v by (auto intro: submodule_scale)
  ultimately show ?thesis by simp
qed

text \<open>The whole module and the trivial submodule are submodules.\<close>
lemma submodule_whole: "submodule M"
  by (rule submoduleI) (auto simp: scale_closed)

lemma submodule_trivial: "submodule {\<zero>\<^sub>M}"
  by (rule submoduleI) (auto simp: scale_zero_elem)

text \<open>The intersection of two submodules is a submodule.\<close>
lemma submodule_inter:
  assumes N: "submodule N" and K: "submodule K" shows "submodule (N \<inter> K)"
proof (rule submoduleI)
  show "N \<inter> K \<subseteq> M" using submodule_subset[OF N] by blast
  show "\<zero>\<^sub>M \<in> N \<inter> K" using submodule_zero[OF N] submodule_zero[OF K] by blast
  show "\<And>u v. \<lbrakk> u \<in> N \<inter> K; v \<in> N \<inter> K \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> N \<inter> K"
    using submodule_add[OF N] submodule_add[OF K] by blast
  show "\<And>a v. \<lbrakk> a \<in> R; v \<in> N \<inter> K \<rbrakk> \<Longrightarrow> a \<odot> v \<in> N \<inter> K"
    using submodule_scale[OF N] submodule_scale[OF K] by blast
qed


subsection \<open>The sum of two submodules\<close>

text \<open>The \<^emph>\<open>sum\<close> of two subsets of the module: all sums of an element of each.  This is the module
  analogue of \<open>ideal_sum\<close> in \<open>Chinese_Remainder\<close>, and is the smallest submodule containing both
  summands when they are themselves submodules.\<close>
definition submodule_sum :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b set"  (infixl \<open>\<oplus>\<^sub>S\<close> 65)
  where "N \<oplus>\<^sub>S K = {u \<oplus> v | u v. u \<in> N \<and> v \<in> K}"

lemma submodule_sum_memI: "\<lbrakk> u \<in> N; v \<in> K \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> N \<oplus>\<^sub>S K"
  unfolding submodule_sum_def by blast

lemma submodule_sum_memE:
  assumes "x \<in> N \<oplus>\<^sub>S K"
  obtains u v where "u \<in> N" "v \<in> K" "x = u \<oplus> v"
  using assms unfolding submodule_sum_def by blast

text \<open>The sum contains both summands, since each submodule contains @{term "\<zero>\<^sub>M"}.\<close>
lemma submodule_sum_incl_left:
  assumes N: "submodule N" and K: "submodule K" shows "N \<subseteq> N \<oplus>\<^sub>S K"
proof
  fix x assume x: "x \<in> N"
  then have xM: "x \<in> M" using submodule_subset[OF N] by blast
  have "x \<oplus> \<zero>\<^sub>M \<in> N \<oplus>\<^sub>S K" using x submodule_zero[OF K] by (rule submodule_sum_memI)
  then show "x \<in> N \<oplus>\<^sub>S K" using xM by simp
qed

lemma submodule_sum_incl_right:
  assumes N: "submodule N" and K: "submodule K" shows "K \<subseteq> N \<oplus>\<^sub>S K"
proof
  fix x assume x: "x \<in> K"
  then have xM: "x \<in> M" using submodule_subset[OF K] by blast
  have "\<zero>\<^sub>M \<oplus> x \<in> N \<oplus>\<^sub>S K" using submodule_zero[OF N] x by (rule submodule_sum_memI)
  then show "x \<in> N \<oplus>\<^sub>S K" using xM by simp
qed

text \<open>The sum of two submodules is a submodule.  Closure under addition needs commutativity of the
  module addition to re-pair the four summands; closure under scaling distributes.\<close>
theorem submodule_sum_submodule:
  assumes N: "submodule N" and K: "submodule K" shows "submodule (N \<oplus>\<^sub>S K)"
proof (rule submoduleI)
  show sub: "N \<oplus>\<^sub>S K \<subseteq> M"
  proof
    fix x assume "x \<in> N \<oplus>\<^sub>S K"
    then obtain u v where uv: "u \<in> N" "v \<in> K" "x = u \<oplus> v" by (rule submodule_sum_memE)
    then show "x \<in> M" using submodule_subset[OF N] submodule_subset[OF K] by auto
  qed
  show "\<zero>\<^sub>M \<in> N \<oplus>\<^sub>S K"
    using submodule_zero[OF N] submodule_zero[OF K]
    by (metis madd.left_unit mzero_closed submodule_sum_memI)
next
  fix x y assume "x \<in> N \<oplus>\<^sub>S K" and "y \<in> N \<oplus>\<^sub>S K"
  then obtain u v u' v' where
    a: "u \<in> N" "v \<in> K" "x = u \<oplus> v" and b: "u' \<in> N" "v' \<in> K" "y = u' \<oplus> v'"
    by (meson submodule_sum_memE)
  have uM: "u \<in> M" and u'M: "u' \<in> M" using a(1) b(1) submodule_subset[OF N] by auto
  have vM: "v \<in> M" and v'M: "v' \<in> M" using a(2) b(2) submodule_subset[OF K] by auto
  \<comment> \<open>Re-pair \<open>(u \<oplus> v) \<oplus> (u' \<oplus> v')\<close> as \<open>(u \<oplus> u') \<oplus> (v \<oplus> v')\<close>, using the confluent
    associative-commutative bundle of the additive group (bare \<open>associative\<close>/\<open>commutative\<close> do not
    reassociate reliably here).\<close>
  have "x \<oplus> y = (u \<oplus> v) \<oplus> (u' \<oplus> v')" using a(3) b(3) by simp
  also have "\<dots> = (u \<oplus> u') \<oplus> (v \<oplus> v')"
    using uM vM u'M v'M by (simp add: madd.ac)
  finally have "x \<oplus> y = (u \<oplus> u') \<oplus> (v \<oplus> v')" .
  moreover have "u \<oplus> u' \<in> N" using submodule_add[OF N a(1) b(1)] .
  moreover have "v \<oplus> v' \<in> K" using submodule_add[OF K a(2) b(2)] .
  ultimately show "x \<oplus> y \<in> N \<oplus>\<^sub>S K" by (simp add: submodule_sum_memI)
next
  fix a x assume aR: "a \<in> R" and xNK: "x \<in> N \<oplus>\<^sub>S K"
  \<comment> \<open>@{term xNK} named explicitly: a bare \<open>then\<close> would feed both assumptions to the rule.\<close>
  from xNK obtain u v where uv: "u \<in> N" "v \<in> K" "x = u \<oplus> v" by (rule submodule_sum_memE)
  have uM: "u \<in> M" using uv(1) submodule_subset[OF N] by blast
  have vM: "v \<in> M" using uv(2) submodule_subset[OF K] by blast
  have "a \<odot> x = (a \<odot> u) \<oplus> (a \<odot> v)"
    using uv(3) aR uM vM by (simp add: scale_distrib_madd)
  moreover have "a \<odot> u \<in> N" using submodule_scale[OF N aR uv(1)] .
  moreover have "a \<odot> v \<in> K" using submodule_scale[OF K aR uv(2)] .
  ultimately show "a \<odot> x \<in> N \<oplus>\<^sub>S K" by (simp add: submodule_sum_memI)
qed

text \<open>The sum is commutative, as a set.\<close>
lemma submodule_sum_commute:
  assumes N: "submodule N" and K: "submodule K" shows "N \<oplus>\<^sub>S K = K \<oplus>\<^sub>S N"
proof
  show "N \<oplus>\<^sub>S K \<subseteq> K \<oplus>\<^sub>S N"
  proof
    fix x assume "x \<in> N \<oplus>\<^sub>S K"
    then obtain u v where uv: "u \<in> N" "v \<in> K" "x = u \<oplus> v" by (rule submodule_sum_memE)
    have uM: "u \<in> M" using uv(1) submodule_subset[OF N] by blast
    have vM: "v \<in> M" using uv(2) submodule_subset[OF K] by blast
    have "x = v \<oplus> u" using uv(3) uM vM by (simp add: madd.commutative)
    then show "x \<in> K \<oplus>\<^sub>S N" using uv(1,2) by (simp add: submodule_sum_memI)
  qed
next
  show "K \<oplus>\<^sub>S N \<subseteq> N \<oplus>\<^sub>S K"
  proof
    fix x assume "x \<in> K \<oplus>\<^sub>S N"
    then obtain u v where uv: "u \<in> K" "v \<in> N" "x = u \<oplus> v" by (rule submodule_sum_memE)
    have uM: "u \<in> M" using uv(1) submodule_subset[OF K] by blast
    have vM: "v \<in> M" using uv(2) submodule_subset[OF N] by blast
    have "x = v \<oplus> u" using uv(3) uM vM by (simp add: madd.commutative)
    then show "x \<in> N \<oplus>\<^sub>S K" using uv(1,2) by (simp add: submodule_sum_memI)
  qed
qed

text \<open>A trivial intersection makes representations in the submodule sum unique.  The
  existence of such a representation is already exactly @{thm [source] submodule_sum_memE}; this
  cancellation lemma records the additional content supplied by disjointness.\<close>
lemma submodule_sum_decomposition_unique:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and u: "u \<in> N" and v: "v \<in> K"
    and u': "u' \<in> N" and v': "v' \<in> K"
    and eq: "u \<oplus> v = u' \<oplus> v'"
  shows "u = u' \<and> v = v'"
proof -
  have uM: "u \<in> M" and u'M: "u' \<in> M"
    using u u' submodule_subset[OF N] by auto
  have vM: "v \<in> M" and v'M: "v' \<in> M"
    using v v' submodule_subset[OF K] by auto
  have invu'M: "madd.inverse u' \<in> M" using u'M by simp
  have invvM: "madd.inverse v \<in> M" using vM by simp
  have differenceM: "u \<oplus> madd.inverse u' \<in> M" using uM invu'M by simp
  have difference_eq: "u \<oplus> madd.inverse u' = v' \<oplus> madd.inverse v"
  proof -
    have "(u \<oplus> madd.inverse u') \<oplus> v = (u \<oplus> v) \<oplus> madd.inverse u'"
      using uM u'M vM by (simp add: madd.ac)
    also have "... = (u' \<oplus> v') \<oplus> madd.inverse u'" using eq by simp
    also have "... = (v' \<oplus> u') \<oplus> madd.inverse u'"
      using madd.commutative[OF u'M v'M] by simp
    also have "... = v' \<oplus> (u' \<oplus> madd.inverse u')"
      by (rule madd.associative[OF v'M u'M invu'M])
    also have "... = v'" using u'M v'M by simp
    finally have cancellation: "(u \<oplus> madd.inverse u') \<oplus> v = v'" .
    have "((u \<oplus> madd.inverse u') \<oplus> v) \<oplus> madd.inverse v =
        (u \<oplus> madd.inverse u') \<oplus> (v \<oplus> madd.inverse v)"
      by (rule madd.associative[OF differenceM vM invvM])
    also have "... = u \<oplus> madd.inverse u'" using differenceM vM by simp
    finally have recovered: "((u \<oplus> madd.inverse u') \<oplus> v) \<oplus>
      madd.inverse v = u \<oplus> madd.inverse u'" .
    have "u \<oplus> madd.inverse u' =
        ((u \<oplus> madd.inverse u') \<oplus> v) \<oplus> madd.inverse v"
      using recovered by simp
    also have "... = v' \<oplus> madd.inverse v" using cancellation by simp
    finally show ?thesis .
  qed
  have difference_N: "u \<oplus> madd.inverse u' \<in> N"
    using submodule_add[OF N u submodule_neg[OF N u']] .
  have difference_K: "u \<oplus> madd.inverse u' \<in> K"
    using difference_eq submodule_add[OF K v' submodule_neg[OF K v]] by simp
  have difference_zero: "u \<oplus> madd.inverse u' = \<zero>\<^sub>M"
    using difference_N difference_K disjoint by blast
  have uu': "u = u'"
  proof -
    have "madd.inverse u' \<oplus> u' = \<zero>\<^sub>M"
      using u'M by (simp add: madd.invertible_left_inverse)
    then show ?thesis
      using madd.inverse_unique uM u'M difference_zero by blast
  qed
  have vv': "v = v'"
    using eq uu' uM vM v'M by simp
  show ?thesis using uu' vv' by blast
qed

subsection \<open>Linear combinations\<close>

text \<open>A linear combination of a finite set @{term B} of module elements with ring coefficients
  @{term c}: the module sum @{text "\<Oplus>\<^bsub>v\<in>B\<^esub> c v \<odot> v"}.\<close>
definition lincomb :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b"
  where "lincomb c B = madd.fincomp (\<lambda>v. c v \<odot> v) B"

lemma lincomb_closed:
  assumes B: "B \<subseteq> M" and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R"
  shows "lincomb c B \<in> M"
  unfolding lincomb_def using B c by (auto intro!: madd.fincomp_closed scale_closed)

lemma lincomb_empty [simp]: "lincomb c {} = \<zero>\<^sub>M"
  by (simp add: lincomb_def)

text \<open>The span of a set of module elements: all linear combinations over its finite subsets.\<close>
definition span :: "'b set \<Rightarrow> 'b set"
  where "span S = {lincomb c B | c B. finite B \<and> B \<subseteq> S \<and> (\<forall>v\<in>B. c v \<in> R)}"

lemma span_closed:
  assumes "S \<subseteq> M" and "x \<in> span S" shows "x \<in> M"
  using assms unfolding span_def by (auto intro: lincomb_closed)

lemma span_mono: "S \<subseteq> T \<Longrightarrow> span S \<subseteq> span T"
  unfolding span_def by blast

end

subsection \<open>A vector space is a module over a field\<close>

text \<open>The module axioms are exactly those of theory \<open>Vector_Space\<close>, so any vector space is
  a module.  (We record the relationship at the locale level; the field's ring reduct supplies the
  scalar ring.)  A dedicated theory could re-derive the theory \<open>Vector_Space\<close> development
  as the field specialisation of the present one.\<close>

end
