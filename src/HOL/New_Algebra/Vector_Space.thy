section \<open>Finite-dimensional vector spaces over a field\<close>

theory Vector_Space
  imports Free_Module
begin

text \<open>The import of \<open>FiniteProduct\<close> (through \<open>Module\<close>) re-merges HOL's @{text "+"}/@{text "-"} concrete
  syntax alongside the ring locale's, which is harmless in term positions (type inference disambiguates)
  but ambiguous in a locale-header instantiation argument.  We therefore remove the HOL syntax again,
  as \<open>Ring_Theory\<close> does.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A vector space over the field @{term R} (with field operations @{text "+, \<cdot>, \<zero>, \<one>"}):
  an abelian group of vectors @{term V} under @{text "\<oplus>"} with zero @{text "\<zero>\<^sub>V"}, together with a
  scalar multiplication @{text "\<odot>"} satisfying the module axioms.  The purpose of this layer is the
  structural theorem that a finite field has prime-power order: such a field is a
  finite-dimensional vector space over its prime subfield, so its cardinality is
  @{text "\<bar>F\<bar>\<^bsup>dim\<^esup>"}.  We develop just enough for that (spans, bases, and the cardinality of a span),
   deferring a full dimension theory.\<close>

locale Vector_Space = Field +
  fixes vadd :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl \<open>\<oplus>\<close> 65)
    and vzero :: "'b" (\<open>\<zero>\<^sub>V\<close>)
    and vcarrier :: "'b set" (\<open>V\<close>)
    and scale :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixr \<open>\<odot>\<close> 75)
  assumes vadd_group: "Abelian_Group V (\<oplus>) \<zero>\<^sub>V"
    and scale_closed: "\<lbrakk> a \<in> R; v \<in> V \<rbrakk> \<Longrightarrow> a \<odot> v \<in> V"
    and scale_distrib_vadd: "\<lbrakk> a \<in> R; u \<in> V; v \<in> V \<rbrakk> \<Longrightarrow> a \<odot> (u \<oplus> v) = (a \<odot> u) \<oplus> (a \<odot> v)"
    and scale_distrib_add: "\<lbrakk> a \<in> R; b \<in> R; v \<in> V \<rbrakk> \<Longrightarrow> (a + b) \<odot> v = (a \<odot> v) \<oplus> (b \<odot> v)"
    and scale_scale: "\<lbrakk> a \<in> R; b \<in> R; v \<in> V \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<odot> v = a \<odot> (b \<odot> v)"
    and scale_one: "v \<in> V \<Longrightarrow> \<one> \<odot> v = v"
begin

text \<open>The vector additive group, available through the @{text vadd} prefix.\<close>
sublocale vadd: Abelian_Group V "(\<oplus>)" "\<zero>\<^sub>V"
  by (rule vadd_group)

text \<open>Every vector space is a module (its scalar ring being a field is the additional constraint).
  This makes the module-level constructions --- \<open>lincomb\<close>, \<open>span\<close>, and the
  submodule/quotient machinery --- available inside the @{locale Vector_Space} locale under the
  \<open>vadd\<close>-prefixed operations.\<close>
sublocale mod: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)"
  by unfold_locales
     (auto simp: vadd_group scale_closed scale_distrib_vadd scale_distrib_add scale_scale scale_one)

text \<open>Every submodule of a vector space is itself a vector space under the restricted carrier
  and the same operations.  This bridge lets the module-level kernel, image, and quotient
  constructions reuse the vector-space basis and dimension API.\<close>

lemma submodule_vector_space:
  assumes N: "mod.submodule N"
  shows "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>V N (\<odot>)"
proof (intro Vector_Space.intro Vector_Space_axioms.intro)
  show "Field R (+) (\<cdot>) \<zero> \<one>" by unfold_locales
  have N_subgroup: "Subgroup N V (\<oplus>) \<zero>\<^sub>V"
  proof (rule vadd.subgroupI)
    show "N \<subseteq> V" using N by (rule mod.submodule_subset)
    show "\<zero>\<^sub>V \<in> N" using N by (rule mod.submodule_zero)
    show "\<And>u v. \<lbrakk>u \<in> N; v \<in> N\<rbrakk> \<Longrightarrow> u \<oplus> v \<in> N"
      using N by (rule mod.submodule_add)
  next
    fix v assume v: "v \<in> N"
    then have "v \<in> V" using N mod.submodule_subset by blast
    then show "vadd.invertible v" by simp
    show "vadd.inverse v \<in> N" using N v by (rule mod.submodule_neg)
  qed
  interpret Nadd: Subgroup N V "(\<oplus>)" "\<zero>\<^sub>V" by (rule N_subgroup)
  have comm: "u \<oplus> v = v \<oplus> u" if "u \<in> N" "v \<in> N" for u v
    using N that mod.submodule_subset vadd.commutative by blast
  show "Abelian_Group N (\<oplus>) \<zero>\<^sub>V"
    unfolding Abelian_Group_def commutative_monoid_def commutative_monoid_axioms_def
    using Nadd.sub.Group_axioms Nadd.sub.Monoid_axioms comm by auto
  show "\<And>a v. \<lbrakk>a \<in> R; v \<in> N\<rbrakk> \<Longrightarrow> a \<odot> v \<in> N"
    using N by (rule mod.submodule_scale)
  show "\<And>a u v. \<lbrakk>a \<in> R; u \<in> N; v \<in> N\<rbrakk> \<Longrightarrow>
      a \<odot> (u \<oplus> v) = (a \<odot> u) \<oplus> (a \<odot> v)"
    using N mod.submodule_subset by (blast intro: scale_distrib_vadd)
  show "\<And>a b v. \<lbrakk>a \<in> R; b \<in> R; v \<in> N\<rbrakk> \<Longrightarrow>
      (a + b) \<odot> v = (a \<odot> v) \<oplus> (b \<odot> v)"
    using N mod.submodule_subset by (blast intro: scale_distrib_add)
  show "\<And>a b v. \<lbrakk>a \<in> R; b \<in> R; v \<in> N\<rbrakk> \<Longrightarrow>
      (a \<cdot> b) \<odot> v = a \<odot> (b \<odot> v)"
    using N mod.submodule_subset by (blast intro: scale_scale)
  show "\<And>v. v \<in> N \<Longrightarrow> \<one> \<odot> v = v"
    using N mod.submodule_subset by (blast intro: scale_one)
qed

text \<open>Basic closure and unit facts.\<close>
lemma vzero_closed [simp, intro]: "\<zero>\<^sub>V \<in> V" by simp

lemma vadd_closed [simp, intro]: "\<lbrakk> u \<in> V; v \<in> V \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> V"
  by simp

lemma scale_zero_vec:
  assumes "a \<in> R"
  shows "a \<odot> \<zero>\<^sub>V = \<zero>\<^sub>V"
proof -
  have w: "a \<odot> \<zero>\<^sub>V \<in> V" using assms by (simp add: scale_closed)
  then have "(a \<odot> \<zero>\<^sub>V) \<oplus> \<zero>\<^sub>V = (a \<odot> \<zero>\<^sub>V) \<oplus> (a \<odot> \<zero>\<^sub>V)"
    by (metis assms scale_distrib_vadd vadd.right_unit vzero_closed)
  then show ?thesis
    using vadd.invertible_left_cancel[OF vadd.invertible[OF w] w vzero_closed w] by simp
qed

text \<open>\<^emph>\<open>Linear combinations and spans come from the module layer.\<close>  The \<open>mod\<close> sublocale above
  already supplies \<open>mod.lincomb\<close> and \<open>mod.span\<close> on @{term V}, with definitions
  identical to the ones this theory used to repeat verbatim.  We introduce local abbreviations so
  existing proofs continue to read \<open>lincomb\<close> and \<open>span\<close> unqualified, and re-export the two facts
  those proofs cite by name.\<close>
abbreviation lincomb :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b"
  where "lincomb \<equiv> mod.lincomb"

abbreviation span :: "'b set \<Rightarrow> 'b set"
  where "span \<equiv> mod.span"

lemmas lincomb_def = mod.lincomb_def
lemmas span_def = mod.span_def

lemma lincomb_closed:
  assumes B: "B \<subseteq> V" and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R"
  shows "lincomb c B \<in> V"
  using B c by (rule mod.lincomb_closed)

text \<open>\<^emph>\<open>Spanning and linear independence: the finite-dimensional forms.\<close>  The module layer defines
  \<open>mod.spanning\<close> and \<open>mod.lin_indep\<close> for arbitrary subsets (see \<open>Free_Module\<close>).  This
  theory is about the finite-dimensional case --- its basis and dimension results count coordinate
  vectors --- so we keep \<^emph>\<open>finite\<close> variants phrased with a total coefficient function
  @{term "c \<in> B \<rightarrow>\<^sub>E R"}, which is what the coordinate map needs, and relate them to the general
  notions by the bridging lemmas below.\<close>
definition spanning :: "'b set \<Rightarrow> bool"
  where "spanning B \<equiv> finite B \<and> B \<subseteq> V \<and> (\<forall>v\<in>V. \<exists>c\<in>B \<rightarrow>\<^sub>E R. v = lincomb c B)"

definition lin_indep :: "'b set \<Rightarrow> bool"
  where "lin_indep B \<equiv> finite B \<and> B \<subseteq> V \<and> (\<forall>c\<in>B \<rightarrow>\<^sub>E R. lincomb c B = \<zero>\<^sub>V \<longrightarrow> (\<forall>v\<in>B. c v = \<zero>))"

text \<open>A set @{term B} is a \<^emph>\<open>basis\<close> of @{term V} when it is a finite subset whose coordinate map
  --- sending each coefficient vector @{term "c \<in> B \<rightarrow>\<^sub>E R"} to the linear combination
  @{term "lincomb c B"} --- is a bijection onto @{term V}.  This packages spanning (surjectivity)
  and linear independence (injectivity) in exactly the form the cardinality count needs.\<close>
definition basis :: "'b set \<Rightarrow> bool"
  where "basis B \<equiv> finite B \<and> B \<subseteq> V \<and> bij_betw (\<lambda>c. lincomb c B) (B \<rightarrow>\<^sub>E R) V"

text \<open>\<^emph>\<open>Bridge: the finite forms agree with the module-level notions.\<close>  On a finite set the two
  spanning conditions coincide: \<open>mod.spanning\<close> says every vector lies in the span, and on a
  finite @{term B} a span membership is realised by a coefficient function on @{term B} itself
  (extended by @{term \<zero>} where the witnessing subset omits an element).\<close>
lemma spanning_iff_mod_spanning:
  assumes finB: "finite B" and BV: "B \<subseteq> V"
  shows "spanning B \<longleftrightarrow> mod.spanning B"
proof
  assume "spanning B"
  show "mod.spanning B"
  proof (rule mod.spanningI[OF BV])
    fix v assume v: "v \<in> V"
    with \<open>spanning B\<close> obtain c where c: "c \<in> B \<rightarrow>\<^sub>E R" "v = lincomb c B"
      unfolding spanning_def by blast
    show "v \<in> mod.span B"
      by (rule mod.spanI[OF finB subset_refl _ c(2)])
         (use c(1) in \<open>auto intro!: mod.coeffs_onI\<close>)
  qed
next
  assume ms: "mod.spanning B"
  have "\<forall>v\<in>V. \<exists>c\<in>B \<rightarrow>\<^sub>E R. v = lincomb c B"
  proof (rule ballI)
    fix v assume "v \<in> V"
    then have "v \<in> mod.span B" by (rule mod.spanningD[OF ms])
    then obtain c A where A: "finite A" "A \<subseteq> B" "mod.coeffs_on c A" "v = lincomb c A"
      by (rule mod.spanE)
    \<comment> \<open>Extend @{term c} by @{term \<zero>} off @{term A} and make it extensional on @{term B}; the
      combination is unchanged because the added coefficients are @{term \<zero>}.\<close>
    define c' where "c' = (\<lambda>u. if u \<in> A then c u else \<zero>)"
    have c'R: "mod.coeffs_on c' B"
      by (rule mod.coeffs_onI) (use mod.coeffs_onD[OF A(3)] in \<open>simp add: c'_def\<close>)
    have "lincomb c' A = lincomb c' B"
    proof (rule mod.lincomb_mono_zero[OF finB A(2) BV])
      show "\<And>u. u \<in> B \<setminus> A \<Longrightarrow> c' u = \<zero>" unfolding c'_def by simp
      show "mod.coeffs_on c' B" by (rule c'R)
    qed
    moreover have "lincomb c' A = lincomb c A"
      using A(2) BV mod.coeffs_onD[OF A(3)]
      by (intro mod.lincomb_cong) (auto simp: c'_def intro!: mod.coeffs_onI)
    ultimately have vc': "v = lincomb c' B" using A(4) by simp
    \<comment> \<open>Make it extensional on @{term B}; that changes no value on @{term B}.\<close>
    have "lincomb (restrict c' B) B = lincomb c' B"
      by (rule mod.lincomb_cong[OF BV]) (use c'R in simp_all)
    with vc' have "v = lincomb (restrict c' B) B" by simp
    moreover have "restrict c' B \<in> B \<rightarrow>\<^sub>E R"
      using mod.coeffs_onD[OF c'R] by auto
    ultimately show "\<exists>c\<in>B \<rightarrow>\<^sub>E R. v = lincomb c B" by blast
  qed
  with finB BV show "spanning B" unfolding spanning_def by blast
qed

text \<open>Likewise for independence.  The finite form quantifies over total coefficient functions on
  @{term B}; the module form over coefficient functions on finite subsets.  On a finite @{term B}
  these agree: restrict to the subset in one direction, extend by @{term \<zero>} in the other.\<close>
lemma lin_indep_iff_mod_lin_indep:
  assumes finB: "finite B" and BV: "B \<subseteq> V"
  shows "lin_indep B \<longleftrightarrow> mod.lin_indep B"
proof
  assume li: "lin_indep B"
  show "mod.lin_indep B"
  proof (rule mod.lin_indepI[OF BV])
    fix c A v
    assume A: "finite A" "A \<subseteq> B" and cA: "mod.coeffs_on c A"
      and zero: "lincomb c A = \<zero>\<^sub>V" and vA: "v \<in> A"
    define c' where "c' = restrict (\<lambda>u. if u \<in> A then c u else \<zero>) B"
    have c'R: "mod.coeffs_on c' B"
      by (rule mod.coeffs_onI) (use mod.coeffs_onD[OF cA] in \<open>simp add: c'_def\<close>)
    have c'PiE: "c' \<in> B \<rightarrow>\<^sub>E R" using mod.coeffs_onD[OF c'R] by (auto simp: c'_def)
    have "lincomb c' A = lincomb c A"
      using A(2) BV mod.coeffs_onD[OF cA]
      by (intro mod.lincomb_cong) (auto simp: c'_def intro!: mod.coeffs_onI)
    moreover have "lincomb c' A = lincomb c' B"
    proof (rule mod.lincomb_mono_zero[OF finB A(2) BV])
      show "\<And>u. u \<in> B \<setminus> A \<Longrightarrow> c' u = \<zero>" unfolding c'_def by simp
      show "mod.coeffs_on c' B" by (rule c'R)
    qed
    ultimately have "lincomb c' B = \<zero>\<^sub>V" using zero by simp
    with li c'PiE have all0: "\<forall>u\<in>B. c' u = \<zero>" unfolding lin_indep_def by blast
    have vB: "v \<in> B" using vA A(2) by blast
    then have "c' v = \<zero>" using all0 by blast
    then show "c v = \<zero>" using vA vB unfolding c'_def by simp
  qed
next
  assume ms: "mod.lin_indep B"
  \<comment> \<open>@{method rule} twice, not @{method intro}: \<open>intro\<close> is greedy and would also strip the inner
    bounded quantifier, leaving a goal the @{command show} below cannot match.\<close>
  have "\<forall>c\<in>B \<rightarrow>\<^sub>E R. lincomb c B = \<zero>\<^sub>V \<longrightarrow> (\<forall>v\<in>B. c v = \<zero>)"
  proof (rule ballI, rule impI)
    fix c assume c: "c \<in> B \<rightarrow>\<^sub>E R" and zero: "lincomb c B = \<zero>\<^sub>V"
    have cB: "mod.coeffs_on c B" using c by (auto intro!: mod.coeffs_onI)
    show "\<forall>v\<in>B. c v = \<zero>"
      using mod.lin_indepD[OF ms finB subset_refl cB zero] by blast
  qed
  with finB BV show "lin_indep B" unfolding lin_indep_def by blast
qed

text \<open>A basis spans: surjectivity of the coordinate map.\<close>
lemma basis_spanning:
  assumes "basis B" shows "spanning B"
  unfolding spanning_def
proof (intro conjI ballI)
  show "finite B" and "B \<subseteq> V" using assms by (auto simp: basis_def)
  fix v assume "v \<in> V"
  then show "\<exists>c\<in>B \<rightarrow>\<^sub>E R. v = lincomb c B"
    using assms by (force simp: basis_def bij_betw_def)
qed

text \<open>\<^emph>\<open>The dimension counting theorem.\<close>  Over a finite field, a space with a basis of size
  @{term n} has exactly @{term "card R ^ n"} elements: its coordinate map is a bijection onto
  the @{term "card R ^ n"} coefficient vectors @{term "B \<rightarrow>\<^sub>E R"}.\<close>
theorem card_eq_card_base_pow_dim:
  assumes "basis B"
  shows "card V = card R ^ card B"
  by (metis assms basis_def bij_betw_same_card card_funcsetE)

text \<open>\<^emph>\<open>Over a finite field, any two bases have the same size\<close> --- so the dimension is well defined.
  (Both give @{term "card V = card R ^ card B\<^sub>i"}, and @{term "card R \<ge> 2"} is injective as a base of
  exponentiation.)  The general (infinite-field) case needs the Steinitz exchange lemma and is left
  for later; the finite case already covers finite fields and their extensions.\<close>
theorem basis_card_unique_finite:
  assumes finR: "finite R" and B1: "basis B\<^sub>1" and B2: "basis B\<^sub>2"
  shows "card B\<^sub>1 = card B\<^sub>2"
proof -
  have "card R ^ card B\<^sub>1 = card V" using card_eq_card_base_pow_dim[OF B1] by simp
  also have "\<dots> = card R ^ card B\<^sub>2" using card_eq_card_base_pow_dim[OF B2] by simp
  finally have eq: "card R ^ card B\<^sub>1 = card R ^ card B\<^sub>2" .
  \<comment> \<open>The field has at least two elements (@{term "\<one> \<noteq> \<zero>"}), so exponentiation is injective.\<close>
  have sub: "{\<one>, \<zero>} \<subseteq> R" by auto
  have "card {\<one>, \<zero>} = 2" using nontrivial by simp
  then have "card R \<ge> 2" using card_mono[OF finR sub] by simp
  then show ?thesis using eq by simp
qed

text \<open>The dimension of the space: the size of a basis (well defined over a finite field).\<close>
definition dimension :: nat
  where "dimension = card (SOME B. basis B)"

lemma dimension_eq:
  assumes finR: "finite R" and B: "basis B" shows "dimension = card B"
  by (metis B basis_card_unique_finite dimension_def finR someI)

end

text \<open>A vector subspace packages a module-level submodule of a vector space and exposes the
  induced vector-space structure under the prefix \<open>sub\<close>.\<close>

locale vector_subspace = Vector_Space +
  fixes W :: "'b set"
  assumes W_submodule: "mod.submodule W"
begin

sublocale sub: Vector_Space R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" W "(\<odot>)"
  by (rule submodule_vector_space[OF W_submodule])

end

end
