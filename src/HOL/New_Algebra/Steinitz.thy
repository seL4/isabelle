section \<open>The Steinitz exchange lemma and dimension over an arbitrary field\<close>

theory Steinitz
  imports Vector_Space
begin

text \<open>Restore HOL's arithmetic notation, which \<open>Vector_Space\<close> (via its ancestor \<open>Ring_Theory\<close>)
  suppresses to disambiguate locale-parameter binding.  Steinitz does not bind \<open>+\<close> or \<open>-\<close> as
  locale parameters, so it is safe (and needed for e.g.\ nat subtraction) to restore them.\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

text \<open>Basis-cardinality uniqueness over a \<^emph>\<open>finite\<close> field was obtained in \<open>Vector_Space\<close>
  by a counting argument.  Here we develop the general (any field, in particular an infinite base
  such as \<open>\<rat>\<close>) theory via the \<^emph>\<open>Steinitz exchange lemma\<close>: from a spanning set and a linearly
  independent set, independent vectors can be exchanged into the spanning set one at a time, whence
  @{text "|independent| \<le> |spanning|"} and any two bases have equal size. It is the linchpin for 
  a general field-extension degree @{text "[K:F]"} and for transitivity of algebraicity.\<close>

context Vector_Space
begin

subsection \<open>Span basics\<close>

lemma span_closed:
  assumes "S \<subseteq> V" and "x \<in> span S"
  shows "x \<in> V"
  using assms lincomb_closed span_def by auto

lemma span_mono:
  assumes "S \<subseteq> T" shows "span S \<subseteq> span T"
  using assms unfolding span_def by blast

text \<open>Every vector of @{term S} lies in its span.\<close>
lemma span_incl:
  assumes "S \<subseteq> V" "v \<in> S"
  shows "v \<in> span S"
  using assms mod.span_incl by (meson in_mono)

lemma span_subset_V:
  assumes "S \<subseteq> V" shows "span S \<subseteq> V"
  using assms span_closed by blast

subsection \<open>Extension of a linear combination by zero coefficients\<close>

text \<open>Scaling by the field zero gives the zero vector: from @{term "(\<zero> + \<zero>) \<odot> v = \<zero> \<odot> v \<oplus> \<zero> \<odot> v"}
  and cancellation.\<close>
lemmas scale_zero_scalar = mod.scale_zero_scalar

text \<open>Extending a linear combination's support by vectors with zero coefficient leaves it unchanged:
  the extra terms @{term "\<zero> \<odot> v = \<zero>\<^sub>V"} vanish in the vector sum.\<close>
lemma lincomb_extend_zero:
  assumes B: "B \<subseteq> V" and C: "finite C" "C \<subseteq> V" and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R"
    and disj: "B \<inter> C = {}" and czero: "\<And>v. v \<in> C \<Longrightarrow> c v = \<zero>"
    and finB: "finite B"
  shows "lincomb c (B \<union> C) = lincomb c B"
proof -
  have Rc: "(\<lambda>v. c v \<odot> v) \<in> B \<rightarrow> V" using B c by (auto intro: scale_closed)
  have RcC: "(\<lambda>v. c v \<odot> v) \<in> C \<rightarrow> V" using C czero by (auto simp: scale_zero_scalar)
  have "lincomb c (B \<union> C) = vadd.fincomp (\<lambda>v. c v \<odot> v) (B \<union> C)" by (simp add: lincomb_def)
  also have "\<dots> = vadd.fincomp (\<lambda>v. c v \<odot> v) B \<oplus> vadd.fincomp (\<lambda>v. c v \<odot> v) C"
    using finB C(1) disj Rc RcC by (simp add: vadd.fincomp_Un_disjoint)
  also have "vadd.fincomp (\<lambda>v. c v \<odot> v) C = \<zero>\<^sub>V"
    using C czero by (auto intro!: vadd.fincomp_unit_eqI simp: scale_zero_scalar)
  also have "vadd.fincomp (\<lambda>v. c v \<odot> v) B \<oplus> \<zero>\<^sub>V = vadd.fincomp (\<lambda>v. c v \<odot> v) B"
    using Rc finB by (simp add: vadd.right_unit vadd.fincomp_closed)
  finally show ?thesis by (simp add: lincomb_def)
qed

subsection \<open>Span is a subspace\<close>

text \<open>Over a common finite support @{term B}, linear combinations add coefficientwise:
  @{term "lincomb c B \<oplus> lincomb d B = lincomb (\<lambda>v. c v + d v) B"} (by @{thm [source] vadd.fincomp_comp}
  and @{thm [source] scale_distrib_add}).\<close>
lemma lincomb_add:
  assumes B: "B \<subseteq> V" and finB: "finite B"
    and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R" and d: "\<And>v. v \<in> B \<Longrightarrow> d v \<in> R"
  shows "lincomb c B \<oplus> lincomb d B = lincomb (\<lambda>v. c v + d v) B"
proof -
  have Rc: "(\<lambda>v. c v \<odot> v) \<in> B \<rightarrow> V" using B c by (auto intro: scale_closed)
  have Rd: "(\<lambda>v. d v \<odot> v) \<in> B \<rightarrow> V" using B d by (auto intro: scale_closed)
  have "lincomb c B \<oplus> lincomb d B
          = vadd.fincomp (\<lambda>v. (c v \<odot> v) \<oplus> (d v \<odot> v)) B"
    using Rc Rd by (simp add: lincomb_def vadd.fincomp_comp)
  also have "\<dots> = vadd.fincomp (\<lambda>v. (c v + d v) \<odot> v) B"
    by (rule vadd.fincomp_cong') (use assms in \<open>auto simp: scale_distrib_add scale_closed\<close>)
  finally show ?thesis by (simp add: lincomb_def)
qed

text \<open>A scalar pulls through a vector finite sum: @{term "a \<odot> vadd.fincomp g A = vadd.fincomp (\<lambda>v. a \<odot> g v) A"}
  (by @{thm [source] scale_distrib_vadd}, induction on @{term A}).\<close>
lemmas scale_fincomp = mod.scale_fincomp

text \<open>Scaling a linear combination scales its coefficients:
  @{term "a \<odot> lincomb c B = lincomb (\<lambda>v. a \<cdot> c v) B"}.\<close>
lemma lincomb_scale:
  assumes B: "B \<subseteq> V" and finB: "finite B" and a: "a \<in> R"
    and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R"
  shows "a \<odot> lincomb c B = lincomb (\<lambda>v. a \<cdot> c v) B"
proof -
  have Rc: "(\<lambda>v. c v \<odot> v) \<in> B \<rightarrow> V" using B c by (auto intro: scale_closed)
  have "a \<odot> lincomb c B = vadd.fincomp (\<lambda>v. a \<odot> (c v \<odot> v)) B"
    by (simp add: Rc a finB lincomb_def scale_fincomp)
  also have "\<dots> = vadd.fincomp (\<lambda>v. (a \<cdot> c v) \<odot> v) B"
    using assms by (auto simp: scale_scale intro!: vadd.fincomp_cong' scale_closed)
  finally show ?thesis by (simp add: lincomb_def)
qed

subsection \<open>Span closure, idempotence and transitivity\<close>

text \<open>Two coefficient functions agreeing on the support give the same linear combination.\<close>
lemma lincomb_cong:
  assumes "B \<subseteq> V" and "\<And>v. v \<in> B \<Longrightarrow> d v \<in> R" and "\<And>v. v \<in> B \<Longrightarrow> c v = d v"
  shows "lincomb c B = lincomb d B"
  unfolding lincomb_def
  using assms
  by (force intro!: vadd.fincomp_cong'[OF refl] scale_closed)

text \<open>Enlarging the support of a linear combination by vectors whose coefficient is @{term \<zero>} leaves
  its value unchanged --- the general (non-disjoint) form of @{thm [source] lincomb_extend_zero},
  obtained by taking the extra part to be the vectors of \<open>D\<close> outside \<open>B\<close>.\<close>
lemma lincomb_zero_extend_eq:
  assumes B: "B \<subseteq> V" and D: "finite D" "D \<subseteq> V" and BD: "B \<subseteq> D"
    and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R" and czero: "\<And>v. \<lbrakk> v \<in> D; v \<notin> B \<rbrakk> \<Longrightarrow> c v = \<zero>"
  shows "lincomb c D = lincomb c B"
proof -
  define E where "E \<equiv> {v \<in> D. v \<notin> B}"
  obtain finB: "finite B" and finE: "finite E" and "E \<subseteq> V" 
    using finite_subset D BD unfolding E_def by auto
  have disj: "B \<inter> E = {}" unfolding E_def by blast
  have Ezero: "\<And>v. v \<in> E \<Longrightarrow> c v = \<zero>" using czero unfolding E_def by blast
  have "lincomb c (B \<union> E) = lincomb c B"
    by (rule lincomb_extend_zero[OF B finE \<open>E \<subseteq> V\<close> c disj Ezero finB])
  moreover have "B \<union> E = D" using BD unfolding E_def by blast
  ultimately show ?thesis by simp
qed

text \<open>The zero vector is the empty linear combination, hence lies in every span.\<close>
lemma span_zero: "\<zero>\<^sub>V \<in> span S"
  by simp

text \<open>A span is closed under scalar multiplication.\<close>
lemmas span_scale = mod.span_scale_closed

text \<open>A span is closed under vector addition.\<close>
lemmas span_vadd = mod.span_madd_closed

text \<open>Consequently a linear combination of vectors \<^emph>\<open>drawn from a span\<close> stays in the span: induction
  on the support, using @{thm [source] span_zero}, @{thm [source] span_scale}, @{thm [source] span_vadd}.\<close>
lemma span_lincomb_closed:
  assumes S: "S \<subseteq> V" and finB: "finite B" and BS: "B \<subseteq> span S"
    and cR: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R"
  shows "lincomb c B \<in> span S"
  using finB BS cR
proof (induct B rule: finite_induct)
  case empty
  have "lincomb c {} = \<zero>\<^sub>V" by (simp add: lincomb_def)
  then show ?case by (simp add: span_zero)
next
  case (insert x F)
  then have sF: "lincomb c F \<in> span S"
    by blast
  have split: "lincomb c (insert x F) = (c x \<odot> x) \<oplus> lincomb c F"
    using insert S by (simp add: lincomb_def scale_closed span_closed subset_eq)
  have sx: "c x \<odot> x \<in> span S"
    using S insert.prems(1,2) span_scale by auto
  show ?case using split sx sF S by (auto intro: span_vadd)
qed

text \<open>Span is idempotent, so it is a genuine closure operator.\<close>
lemma span_span:
  assumes S: "S \<subseteq> V" shows "span (span S) = span S"
  by (simp add: assms mod.span_incl mod.span_minimal mod.span_submodule span_subset_V subset_antisym)

text \<open>Transitivity: if @{term S} lies inside the span of @{term T}, its span does too.\<close>
lemma span_trans:
  assumes ST: "S \<subseteq> span T" and T: "T \<subseteq> V"
  shows "span S \<subseteq> span T"
  by (metis ST T span_mono span_span)

text \<open>The membership form of transitivity, matching the shape used in the exchange lemma: absorbing a
  spanned vector into the generating set does not enlarge the span.\<close>
lemma span_trans_mem:
  assumes "S \<subseteq> V" and "x \<in> span S" and "y \<in> span (insert x S)"
  shows "y \<in> span S"
  by (metis (no_types, opaque_lifting) assms insert_subset span_incl span_trans subset_eq)

subsection \<open>Vector subtraction inside a span\<close>

text \<open>Negating a scalar coefficient negates the scaled vector: \<open>(- a) \<odot> v\<close> is the vector-group inverse
  of \<open>a \<odot> v\<close>.  From @{term "(a + (- a)) \<odot> v = \<zero>\<^sub>V"}.\<close>
lemmas scale_neg_scalar = mod.scale_neg_scalar

text \<open>A span is closed under vector negation.\<close>
lemma span_neg:
  assumes "S \<subseteq> V" and "x \<in> span S"
  shows "vadd.inverse x \<in> span S"
  using mod.span_submodule mod.submodule_neg assms by presburger

text \<open>A span is closed under vector subtraction.\<close>
lemma span_diff:
  assumes S: "S \<subseteq> V" and x: "x \<in> span S" and y: "y \<in> span S"
  shows "x \<oplus> vadd.inverse y \<in> span S"
  by (simp add: S span_neg span_vadd x y)

subsection \<open>The exchange step\<close>

text \<open>\<^emph>\<open>Exchange step.\<close>  If @{term a} lies in the span of @{term "insert b S"} but not in the span of
  @{term S}, then @{term b} lies in the span of @{term "insert a S"} --- so @{term b} may be swapped
  out for @{term a}. \<close>
lemma in_span_insert:
  assumes S: "S \<subseteq> V" and b: "b \<in> V"
    and a: "a \<in> span (insert b S)" and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  have aV: "a \<in> V" using a S b span_closed by (metis insert_subset span_subset_V subsetD)
  \<comment> \<open>Split a linear combination over @{term "insert b S"} into its @{term b}-part and the rest.\<close>
  from a obtain c B where a_eq: "a = lincomb c B" and finB: "finite B"
    and BbS: "B \<subseteq> insert b S" and cR: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R" unfolding span_def by blast
  define B0 where "B0 = B \<setminus> {b}"
  define k where "k = (if b \<in> B then c b else \<zero>)"
  have kR: "k \<in> R" using cR by (auto simp: k_def additive.unit_closed)
  have finB0: "finite B0" using finB by (simp add: B0_def)
  have "B0 \<subseteq> S" "B0 \<subseteq> V" using BbS S by (auto simp: B0_def)
  have bnB0: "b \<notin> B0" by (simp add: B0_def)
  have cR0: "\<And>v. v \<in> B0 \<Longrightarrow> c v \<in> R" using cR by (auto simp: B0_def)
  define r where "r \<equiv> lincomb c B0"  \<comment> \<open>@the part of @{term a} inside @{term "span S"}\<close>
  have rspan: "r \<in> span S" using finB0 \<open>B0 \<subseteq> S\<close> cR0 unfolding r_def span_def by blast
  have rV: "r \<in> V" using rspan S span_closed by blast
  have a_split: "a = (k \<odot> b) \<oplus> r"
  proof (cases "b \<in> B")
    case True
    then have "lincomb c B = lincomb c (insert b B0)"
      by (simp add: B0_def insert_absorb)
    also have "\<dots> = (c b \<odot> b) \<oplus> lincomb c B0"
      unfolding lincomb_def using finB0 bnB0 cR0 \<open>B0 \<subseteq> V\<close> b cR True
      by (subst vadd.fincomp_insert) (auto intro: scale_closed)
    finally show ?thesis using True by (simp add: a_eq k_def r_def)
  next
    case False
    then show ?thesis using rV na rspan by (force simp: B0_def r_def a_eq)
  qed
  \<comment> \<open>@{term k} is nonzero, otherwise \<open>a = r\<close> would lie in \<open>span S\<close>.\<close>
  have kb: "k \<odot> b \<in> V" using kR b by (rule scale_closed)
  have knz: "k \<noteq> \<zero>"
    using a_split b na rV rspan scale_zero_scalar by force
  \<comment> \<open>Recover @{term b}: from @{term "a = k \<odot> b \<oplus> r"} we get \<open>k \<odot> b = a \<oplus> (- r)\<close>.\<close>
  have kinv: "multiplicative.inverse k \<in> R" using kR knz field_inverse by simp
  have kk: "multiplicative.inverse k \<cdot> k = \<one>"
    using kR knz field_inverse by (simp add: multiplicative.invertible_left_inverse)
  have "(k \<odot> b) = a \<oplus> vadd.inverse r"
    by (simp add: a_split kb rV vadd.associative)
  then have b_eq: "b = multiplicative.inverse k \<odot> (a \<oplus> vadd.inverse r)"
    by (metis b kR kinv kk scale_one scale_scale)
  \<comment> \<open>Both \<open>a\<close> and \<open>- r\<close> lie in \<open>span (insert a S)\<close>, so does their sum, then its scaling.\<close>
  have aS: "a \<in> span (insert a S)" "insert a S \<subseteq> V"  
    using aV S by (auto intro: span_incl)
  have rS: "r \<in> span (insert a S)" using rspan span_mono[of S "insert a S"] by blast
  have "a \<oplus> vadd.inverse r \<in> span (insert a S)" using aS rS by (auto intro: span_diff)
  then show ?thesis using aS kinv b_eq by (auto intro: span_scale)
qed

text \<open>\<^emph>\<open>Delete form.\<close>  If @{term a} is spanned by @{term S} but not by @{term "S \<setminus> {b}"}, then @{term b}
  can be exchanged into the generating set in place of @{term a}.\<close>
lemma in_span_delete:
  assumes S: "S \<subseteq> V" and b: "b \<in> V"
    and a: "a \<in> span S" and na: "a \<notin> span (S \<setminus> {b})"
  shows "b \<in> span (insert a (S \<setminus> {b}))"
proof -
  have "a \<in> span (insert b (S \<setminus> {b}))" using a span_mono[of S "insert b (S \<setminus> {b})"] by blast
  with assms show ?thesis
    by (meson Diff_subset in_span_insert subset_trans) 
qed

subsection \<open>Independence as irredundancy\<close>

text \<open>The geometric reading of linear independence: no member of an independent set lies in the span
  of the others.  This is the bridge from the coordinate definition @{const lin_indep} to the
  span-theoretic exchange arguments.  If some @{term "w \<in> B"} were in @{term "span (B \<setminus> {w})"}, its
  witnessing combination, moved to one side with coefficient @{term "- \<one>"} on @{term w}, would be a
  nontrivial dependence.\<close>
lemma lin_indep_not_in_span:
  assumes ind: "lin_indep B" and w: "w \<in> B"
  shows "w \<notin> span (B \<setminus> {w})"
proof
  assume "w \<in> span (B \<setminus> {w})"
  then obtain d C where w_eq: "w = lincomb d C" and finC: "finite C"
    and CB: "C \<subseteq> B \<setminus> {w}" and dR: "\<And>v. v \<in> C \<Longrightarrow> d v \<in> R" unfolding span_def by blast
  have finB: "finite B" and "B \<subseteq> V" using ind by (auto simp: lin_indep_def)
  have wV: "w \<in> V" using w \<open>B \<subseteq> V\<close> by blast
  have wnC: "w \<notin> C" using CB by blast
  define c where "c \<equiv> (\<lambda>v. if v = w then - \<one> else if v \<in> C then d v else \<zero>)"
  have cR: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R" using dR by (auto simp: c_def additive.unit_closed)
  have cPiE: "restrict c B \<in> B \<rightarrow>\<^sub>E R" using cR by (auto simp: c_def)
  \<comment> \<open>The combination over @{term B} splits into the @{term w}-term and the @{term C}-term (all other
      coefficients are zero), and equals @{term "\<zero>\<^sub>V"}.\<close>
  have CsubB: "C \<subseteq> B" using CB by blast
  have insCB: "insert w C \<subseteq> B" using w CsubB by blast
  have "lincomb (restrict c B) B = lincomb (restrict c B) (insert w C)"
  proof (intro lincomb_zero_extend_eq finB \<open>B \<subseteq> V\<close> insCB)
    show "insert w C \<subseteq> V" using insCB \<open>B \<subseteq> V\<close> by blast
    show "\<And>v. v \<in> insert w C \<Longrightarrow> restrict c B v \<in> R" using insCB cR by auto
  qed (auto simp add: c_def)
  also have "\<dots> = lincomb c (insert w C)"
    by (rule lincomb_cong) (use insCB \<open>B \<subseteq> V\<close> cR in auto)
  also have "\<dots> = (c w \<odot> w) \<oplus> lincomb c C"
    unfolding lincomb_def using finC wnC wV cR[OF w] cR CsubB \<open>B \<subseteq> V\<close>
    by (subst vadd.fincomp_insert) (auto intro!: scale_closed)
  also have "lincomb c C = lincomb d C"
    by (rule lincomb_cong) (use CsubB \<open>B \<subseteq> V\<close> dR wnC in \<open>auto simp: c_def\<close>)
  also have "c w \<odot> w = vadd.inverse w" using wV by (simp add: c_def scale_neg_scalar scale_one)
  also have "vadd.inverse w \<oplus> lincomb d C = vadd.inverse w \<oplus> w" using w_eq by simp
  also have "\<dots> = \<zero>\<^sub>V" using wV by simp
  finally have zero: "lincomb (restrict c B) B = \<zero>\<^sub>V" .
  \<comment> \<open>Independence forces every coefficient to vanish --- but the @{term w}-coefficient is @{term "- \<one> \<noteq> \<zero>"}.\<close>
  from ind cPiE zero have "restrict c B w = \<zero>" using w
    using lin_indep_def by blast
  then have "(- \<one>) = \<zero>" using w by (simp add: c_def)
  then show False
    using additive.commute_iff_inverse nontrivial by fastforce
qed

text \<open>Conversely, over a field, a finite set none of whose members lies in the span of the others is
  linearly independent.  Given a dependence @{term "lincomb c B = \<zero>\<^sub>V"} with some @{term "c w \<noteq> \<zero>"},
  solving for @{term w} exhibits @{term w} in the span of the rest.\<close>
lemma not_in_span_lin_indep:
  assumes finB: "finite B" and "B \<subseteq> V"
    and irred: "\<And>w. w \<in> B \<Longrightarrow> w \<notin> span (B \<setminus> {w})"
  shows "lin_indep B"
  unfolding lin_indep_def
proof (intro strip conjI assms)
  show "c v = \<zero>" if cPiE: "c \<in> B \<rightarrow>\<^sub>E R" and zero: "lincomb c B = \<zero>\<^sub>V" and v: "v \<in> B" for c v
  proof (rule ccontr)
    assume cwnz: "c v \<noteq> \<zero>" 
    define r where "r \<equiv> lincomb c (B \<setminus> {v})"
    have rspan: "r \<in> span (B \<setminus> {v})" using finB cPiE unfolding r_def span_def by blast
    have rV: "r \<in> V" using rspan \<open>B \<subseteq> V\<close> span_closed by blast
    have wV: "v \<in> V" using v \<open>B \<subseteq> V\<close> by blast
    have cwR: "c v \<in> R" using cPiE v by blast
        \<comment> \<open>Split off the @{term v}-term: @{term "\<zero>\<^sub>V = (c v \<odot> v) \<oplus> lincomb c (B \<setminus> {v})"}.\<close>
    have cww: "c v \<odot> v \<in> V" using cwR wV by (rule scale_closed)
    have "B = insert v (B \<setminus> {v})" using v by blast
    then have "lincomb c B = lincomb c (insert v (B \<setminus> {v}))" by simp
    also have "\<dots> = (c v \<odot> v) \<oplus> lincomb c (B \<setminus> {v})"
      unfolding lincomb_def using finB wV cwR cPiE \<open>B \<subseteq> V\<close>
      by (subst vadd.fincomp_insert) (auto intro!: scale_closed)
    finally have "c v \<odot> v = vadd.inverse r"
      using cww rV r_def vadd.commutative vadd.inverse_equality zero by metis
    have cwinv: "multiplicative.inverse (c v) \<in> R" using cwR cwnz field_inverse by simp
    have cwcw: "multiplicative.inverse (c v) \<cdot> c v = \<one>"
      using cwR cwnz field_inverse by (simp add: multiplicative.invertible_left_inverse)
    have "v = multiplicative.inverse (c v) \<odot> (c v \<odot> v)"
      using cwinv cwR wV by (simp add: scale_scale[symmetric] cwcw scale_one)
    also have "\<dots> = multiplicative.inverse (c v) \<odot> vadd.inverse r"
      using \<open>c v \<odot> v = vadd.inverse r\<close> by simp
    finally have "v = multiplicative.inverse (c v) \<odot> vadd.inverse r" .
    moreover have "multiplicative.inverse (c v) \<odot> vadd.inverse r \<in> span (B \<setminus> {v})"
      using \<open>B \<subseteq> V\<close> cwinv span_neg[OF _ rspan] by (auto intro: span_scale)
    ultimately have "v \<in> span (B \<setminus> {v})" by simp
    with irred[OF v] show False by simp
  qed
qed

text \<open>Adjoining a vector outside the span preserves linear independence.\<close>

lemma lin_indep_insert:
  assumes ind: "lin_indep A" and x: "x \<in> V" and outside: "x \<notin> span A"
  shows "lin_indep (insert x A)"
proof (rule not_in_span_lin_indep)
  show "finite (insert x A)" using ind by (simp add: lin_indep_def)
  show "insert x A \<subseteq> V" using ind x by (auto simp: lin_indep_def)
  fix w assume w: "w \<in> insert x A"
  have AV: "A \<subseteq> V" using ind by (simp add: lin_indep_def)
  have xA: "x \<notin> A"
    using AV outside span_incl by blast
  show "w \<notin> span (insert x A \<setminus> {w})"
  proof
    assume wsp: "w \<in> span (insert x A \<setminus> {w})"
    have wA: "w \<in> A" using w
      using insert_iff outside wsp by fastforce
    have w_outside: "w \<notin> span (A \<setminus> {w})"
      using ind wA by (rule lin_indep_not_in_span)
    have w_span: "w \<in> span (insert x (A \<setminus> {w}))"
      using wsp w_outside by (metis insert_Diff_if)
    have diffV: "A \<setminus> {w} \<subseteq> V" using AV by auto
    then show False
      using outside in_span_insert wA w_outside w_span x by (metis insert_Diff) 
  qed
qed

subsection \<open>Bases span and are independent\<close>

text \<open>A spanning set spans the whole space: every vector of @{term V} lies in its span.\<close>
lemma spanning_span_all:
  assumes "spanning B" "v \<in> V"
  shows "v \<in> span B"
  using assms mod.spanningD spanning_def spanning_iff_mod_spanning by meson

text \<open>A basis is linearly independent: the coordinate map is injective, and the zero vector is
  @{term "lincomb (\<lambda>_. \<zero>) B"}, so any coordinate vector mapping to @{term "\<zero>\<^sub>V"} must be the zero one.\<close>
lemma basis_lin_indep:
  assumes B: "basis B"
  shows "lin_indep B"
proof -
  have finB: "finite B" and "B \<subseteq> V" using B by (auto simp: basis_def)
  have inj: "inj_on (\<lambda>c. lincomb c B) (B \<rightarrow>\<^sub>E R)" using B by (simp add: basis_def bij_betw_def)
  have "c v = \<zero>" if  cPiE: "c \<in> B \<rightarrow>\<^sub>E R" and zero: "lincomb c B = \<zero>\<^sub>V" and "v\<in>B" for c v
  proof -
    define z where "z \<equiv> restrict (\<lambda>_. \<zero>) B"
    have zPiE: "z \<in> B \<rightarrow>\<^sub>E R" using additive.unit_closed by (auto simp: z_def)
    have "lincomb z B = lincomb (\<lambda>_. \<zero>) B" by (rule lincomb_cong) (use \<open>B \<subseteq> V\<close> in \<open>auto simp: z_def\<close>)
    also have "\<dots> = \<zero>\<^sub>V" by (simp add: \<open>B \<subseteq> V\<close>)
    finally have "lincomb z B = \<zero>\<^sub>V" .
    with zero inj cPiE zPiE have "c = z"
      by (metis inj_on_eq_iff)
    then show "c v = \<zero>"
      using \<open>v \<in> B\<close> z_def by force
  qed
  with finB \<open>B \<subseteq> V\<close> show ?thesis unfolding lin_indep_def by blast
qed

text \<open>A finite vector-space basis is also a basis in the underlying free-module sense.
  This bridge lets constructions defined by the universal property of free modules consume the
  coordinate-map basis used by the dimension theory.\<close>

lemma basis_module_basis:
  assumes B: "basis B"
  shows "mod.module_basis B"
proof (rule mod.module_basisI)
  have finB: "finite B" and BV: "B \<subseteq> V" using B by (auto simp: basis_def)
  show "mod.spanning B"
    using basis_spanning[OF B] spanning_iff_mod_spanning[OF finB BV] by simp
  show "mod.lin_indep B"
    using basis_lin_indep[OF B] lin_indep_iff_mod_lin_indep[OF finB BV] by simp
qed

text \<open>\<^emph>\<open>Spanning forces equality with a containing independent set.\<close>  If @{term "T \<subseteq> S"}, @{term S} is
  independent and @{term "S \<subseteq> span T"}, then @{term "S = T"}: any @{term "w \<in> S - T"} would lie in
  @{term "span T \<subseteq> span (S \<setminus> {w})"}, contradicting independence.\<close>
lemma spanning_subset_independent:
  assumes TS: "T \<subseteq> S" and iS: "lin_indep S" and SsT: "S \<subseteq> span T"
  shows "S = T"
proof (rule antisym[OF _ TS])
  show "S \<subseteq> T"
  proof (rule ccontr)
    assume "\<not> S \<subseteq> T"
    then obtain w where w: "w \<in> S" "w \<notin> T" "T \<subseteq> S \<setminus> {w}" using TS  by blast
    then have "w \<in> span (S \<setminus> {w})"
      using SsT span_mono by blast
    with lin_indep_not_in_span[OF iS w(1)] show False by simp
  qed
qed

subsection \<open>The Steinitz exchange lemma\<close>

text \<open>An independent set contained in the span of a set @{term T} is contained in the span of an
  equinumerous ``exchanged'' set drawn from @{term "S \<union> T"}: independent vectors are traded into
  @{term T} one at a time.  Induction on @{term "card (T \<setminus> S)"}, following Steinitz.\<close>
lemma exchange_lemma:
  assumes "finite T" and "lin_indep S" and "S \<subseteq> span T" and "T \<subseteq> V"
  shows "\<exists>T'. card T' = card T \<and> finite T' \<and> S \<subseteq> T' \<and> T' \<subseteq> S \<union> T \<and> S \<subseteq> span T'"
  using assms
proof (induct "card (T \<setminus> S)" arbitrary: S T rule: less_induct)
  case less
  note ft = \<open>finite T\<close> and iS = \<open>lin_indep S\<close> and spST = \<open>S \<subseteq> span T\<close> and TV = \<open>T \<subseteq> V\<close>
  have SV: "S \<subseteq> V" using iS by (simp add: lin_indep_def)
  have finS: "finite S" using iS by (simp add: lin_indep_def)
  let ?P = "\<lambda>T'. card T' = card T \<and> finite T' \<and> S \<subseteq> T' \<and> T' \<subseteq> S \<union> T \<and> S \<subseteq> span T'"
  show ?case
  proof (cases "S \<subseteq> T \<or> T \<subseteq> S")
    case True
    then show ?thesis
      using ft iS spST spanning_subset_independent by auto
  next
    case False
    then obtain b where  "\<not> S \<subseteq> T" and b: "b \<in> T" "b \<notin> S" "T \<setminus> {b} \<setminus> S \<subset> T \<setminus> S" by blast
    then have cardlt: "card (T \<setminus> {b} \<setminus> S) < card (T \<setminus> S)" 
      using ft by (auto intro: psubset_card_mono)
    from b ft have ct0: "card T \<noteq> 0" by auto
    show ?thesis
    proof (cases "S \<subseteq> span (T \<setminus> {b})")
      case True
      from ft have ftb: "finite (T \<setminus> {b})" by auto
      have TbV: "T \<setminus> {b} \<subseteq> V" using TV by blast
      from less(1)[OF cardlt ftb iS True TbV]
      obtain U where U: "card U = card (T \<setminus> {b})" "S \<subseteq> U" "U \<subseteq> S \<union> (T \<setminus> {b})" "S \<subseteq> span U"
        and fu: "finite U" by blast
      have bu: "b \<notin> U" using b U by blast
      then have th2: "card (insert b U) = card T" using card_insert_disjoint[OF fu bu] ct0
        using U(1) b(1) ft by (metis card.remove)
      have "S \<subseteq> span (insert b U)"
        using U(4) span_mono by blast
      then show ?thesis using U b th2 fu by blast
    next
      case False
      then obtain a where a: "a \<in> S" "a \<notin> span (T \<setminus> {b})" and aV: "a \<in> V" and ab: "a \<noteq> b"
        using SV b(2) by blast
      have at: "a \<notin> T"
        using a ab TV by (auto intro: span_incl)
      have ft': "finite (insert a (T \<setminus> {b}))" using ft by auto
      have insV: "insert a (T \<setminus> {b}) \<subseteq> V" using aV TV by blast
      \<comment> \<open>@{term b} may be exchanged for @{term a}, so @{term "S \<subseteq> span (insert a (T \<setminus> {b}))"}.\<close>
      have sp': "S \<subseteq> span (insert a (T \<setminus> {b}))"
      proof
        fix x assume xs: "x \<in> S"
        have TbV: "T \<setminus> {b} \<subseteq> V" using TV by blast
        have aspan: "a \<in> span (insert b (T \<setminus> {b}))"
          using a(1) spST b by (metis insert_Diff subsetD)
        have bV: "b \<in> V" using b TV by blast
        have bs: "b \<in> span (insert a (T \<setminus> {b}))"
          by (rule in_span_insert[OF TbV bV aspan a(2)])
        have xspanT: "x \<in> span T" using xs spST by blast
        have "T \<subseteq> insert a (insert b (T \<setminus> {b}))" using b by auto
        with xspanT have x: "x \<in> span (insert a (insert b (T \<setminus> {b})))"
          using span_mono by blast
        \<comment> \<open>Absorb @{term b} (which is spanned) into the generating set.\<close>
        show "x \<in> span (insert a (T \<setminus> {b}))"
          using span_trans_mem[OF insV bs] x by (simp add: insert_commute)
      qed
      have mlt: "card (insert a (T \<setminus> {b}) \<setminus> S) < card (T \<setminus> S)"
        using cardlt ft a b by (auto intro: psubset_card_mono)
      from less(1)[OF mlt ft' iS sp' insV] a b ft at ct0 ab show ?thesis by auto
    qed
  qed
qed

subsection \<open>The cardinality bound and uniqueness of dimension\<close>

text \<open>\<^emph>\<open>Steinitz bound.\<close>  A linearly independent set is no larger than any set whose span contains
  it --- in particular, than any spanning set.\<close>
theorem independent_le_span:
  assumes iS: "lin_indep S" and fT: "finite T" and TV: "T \<subseteq> V" and spST: "S \<subseteq> span T"
  shows "card S \<le> card T"
  by (metis exchange_lemma[OF fT iS spST TV] card_mono)

text \<open>\<^emph>\<open>Uniqueness of dimension over an arbitrary field.\<close>  Any two bases of @{term V} have the same
  cardinality: each is independent and spans, so each bounds the other by the Steinitz bound.  This
  generalises @{thm [source] basis_card_unique_finite}, dropping the finiteness of the base field.\<close>
theorem basis_card_unique:
  assumes B1: "basis B\<^sub>1" and B2: "basis B\<^sub>2"
  shows "card B\<^sub>1 = card B\<^sub>2"
proof -
  have sp1: "spanning B\<^sub>1" and sp2: "spanning B\<^sub>2" using B1 B2 by (auto intro: basis_spanning)
  have i1: "lin_indep B\<^sub>1" and i2: "lin_indep B\<^sub>2" using B1 B2 by (auto intro: basis_lin_indep)
  have "finite B\<^sub>1" "finite B\<^sub>2" and B1V: "B\<^sub>1 \<subseteq> V" and B2V: "B\<^sub>2 \<subseteq> V"
    using B1 B2 by (auto simp: basis_def)
  \<comment> \<open>Every basis vector lies in the span of the other basis (which spans @{term V}).\<close>
  moreover have "B\<^sub>1 \<subseteq> span B\<^sub>2" "B\<^sub>2 \<subseteq> span B\<^sub>1" 
    using sp2 B1V sp1 B2V by (auto intro: spanning_span_all)
  ultimately show ?thesis
    by (simp add: antisym i1 i2 independent_le_span)
qed

text \<open>Consequently the @{const dimension} is the size of \<^emph>\<open>any\<close> basis, over an arbitrary field ---
  the finite-field hypothesis of @{thm [source] dimension_eq} is no longer needed.\<close>
theorem dimension_eq_any_field:
  assumes B: "basis B" shows "dimension = card B"
  by (metis assms basis_card_unique dimension_def someI)


subsection \<open>Existence of a basis\<close>

text \<open>@{const basis} is defined as bijectivity of the coordinate map, and
  @{thm [source] basis_spanning} and @{thm [source] basis_lin_indep} take it apart.  The converse ---
  that spanning together with independence \<^emph>\<open>gives\<close> a basis --- is what one needs in order to
  \<^emph>\<open>build\<close> a basis, and it is the missing introduction rule: surjectivity of the coordinate map is
  spanning, and injectivity is independence, applied to the difference of two coordinate vectors.\<close>
lemma basisI:
  assumes sp: "spanning B" and ind: "lin_indep B"
  shows "basis B"
  unfolding basis_def
proof (intro conjI)
  show finB: "finite B" and BV: "B \<subseteq> V" using sp by (auto simp: spanning_def)
  show "bij_betw (\<lambda>c. lincomb c B) (B \<rightarrow>\<^sub>E R) V"
    unfolding bij_betw_def
  proof
    \<comment> \<open>Injectivity.  If two coordinate vectors give the same vector, their difference is a dependence,
      so independence makes it zero coefficientwise.\<close>
    show "inj_on (\<lambda>c. lincomb c B) (B \<rightarrow>\<^sub>E R)"
    proof (rule inj_onI)
      fix c d assume c: "c \<in> B \<rightarrow>\<^sub>E R" and d: "d \<in> B \<rightarrow>\<^sub>E R" and eq: "lincomb c B = lincomb d B"
      have cR: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> R" and dR: "\<And>v. v \<in> B \<Longrightarrow> d v \<in> R" using c d by auto
      \<comment> \<open>The coefficientwise difference.  Adding it to @{term d} recovers @{term c}, so by
        @{thm [source] lincomb_add} its combination is @{term "\<zero>\<^sub>V"}.\<close>
      define e where "e \<equiv> restrict (\<lambda>v. c v + additive.inverse (d v)) B"
      have eR: "\<And>v. v \<in> B \<Longrightarrow> e v \<in> R" using cR dR by (auto simp: e_def)
      have ePiE: "e \<in> B \<rightarrow>\<^sub>E R" using eR by (simp add: e_def)
      have sum_back: "\<And>v. v \<in> B \<Longrightarrow> e v + d v = c v"
        using cR dR by (simp add: e_def additive.associative additive.inverse_composition_commute)
      have "lincomb e B \<oplus> lincomb d B = lincomb (\<lambda>v. e v + d v) B"
        using BV finB eR dR by (rule lincomb_add)
      also have "\<dots> = lincomb c B" by (rule lincomb_cong) (use BV sum_back cR in auto)
      finally have "lincomb e B \<oplus> lincomb d B = lincomb d B" using eq by simp
      then have "lincomb e B = \<zero>\<^sub>V"
        using BV finB eR dR
        by (metis lincomb_closed vadd.invertible vadd.invertible_right_cancel vadd.left_unit
            vzero_closed)
      then have "\<And>v. v \<in> B \<Longrightarrow> e v = \<zero>" using ind ePiE by (simp add: lin_indep_def)
      then have "\<And>v. v \<in> B \<Longrightarrow> c v = d v"
        using cR dR sum_back by (metis additive.left_unit)
      then show "c = d" using c d by (blast intro: PiE_ext)
    qed
    \<comment> \<open>Surjectivity is spanning, in the coordinate form the definition uses.\<close>
    show "(\<lambda>c. lincomb c B) ` (B \<rightarrow>\<^sub>E R) = V"
    proof
      show "(\<lambda>c. lincomb c B) ` (B \<rightarrow>\<^sub>E R) \<subseteq> V"
        using finB BV by (auto intro: lincomb_closed)
      show "V \<subseteq> (\<lambda>c. lincomb c B) ` (B \<rightarrow>\<^sub>E R)"
        using sp by (auto simp: spanning_def)
    qed
  qed
qed

text \<open>The zero vector space has the empty basis.  This small introduction rule is useful when
  dimension arguments reduce a kernel or intersection to the trivial subspace.\<close>

lemma basis_empty_trivial:
  assumes triv: "V = {\<zero>\<^sub>V}"
  shows "basis {}"
proof (rule basisI)
  show "spanning {}"
    unfolding spanning_def
    using mod.lincomb_empty triv by auto
  show "lin_indep {}" by (simp add: lin_indep_def)
qed

text \<open>\<^emph>\<open>Basis extension.\<close>  Every finite independent set extends to a basis inside its
  union with any given basis.  At each step, a basis vector outside the current span is adjoined;
  the finite difference from the given basis is the termination measure.\<close>

theorem basis_extension:
  assumes ind: "lin_indep A" and B: "basis B"
  shows "\<exists>C. A \<subseteq> C \<and> C \<subseteq> A \<union> B \<and> basis C"
  using assms
proof (induction "card (B \<setminus> A)" arbitrary: A rule: less_induct)
  case less
  note ind = less.prems(1) and B = less.prems(2)
  have finA: "finite A" and AV: "A \<subseteq> V" using ind by (auto simp: lin_indep_def)
  show ?case
  proof (cases "spanning A")
    case True
    then show ?thesis
      using basisI ind by blast
  next
    case False
    have "\<not> B \<subseteq> span A"
    proof
      assume Bspan: "B \<subseteq> span A"
      have "\<And>v. v \<in> V \<Longrightarrow> v \<in> span A"
        using AV B Bspan basis_spanning span_trans spanning_span_all by blast
      with mod.spanningI[OF AV] have "spanning A"
        unfolding spanning_iff_mod_spanning[OF finA AV] .
      then show False using False by contradiction
    qed
    then obtain b where b: "b \<in> B" "b \<notin> span A" by blast
    have BV: "B \<subseteq> V" and finB: "finite B" using B by (auto simp: basis_def)
    have bV: "b \<in> V" using b BV by blast
    have bA: "b \<notin> A"
      using AV b(2) span_incl by blast
    have "0 < card (B \<setminus> A)"
      using finB b bA by (simp add: card_gt_0_iff) blast
    then have measure: "card (B \<setminus> insert b A) < card (B \<setminus> A)"
      by (simp add: b(1) bA)
    obtain C where C: "insert b A \<subseteq> C" "C \<subseteq> insert b A \<union> B" "basis C"
      using B b(2) bV ind less.hyps lin_indep_insert measure by meson
    have "A \<subseteq> C" using C(1) by blast
    moreover have "C \<subseteq> A \<union> B" using C b(1) by blast
    ultimately show ?thesis using C(3) by blast
  qed
qed

text \<open>\<^emph>\<open>Every finitely spanned space has a basis, extracted from any finite spanning set.\<close>  Discard
  redundant vectors one at a time: if some @{term "w \<in> B"} lies in the span of the others then
  @{term "B \<setminus> {w}"} still spans (by @{thm [source] span_trans_mem}), and it is strictly smaller, so
  the process terminates.  What it terminates at is a set no member of which is spanned by the rest,
  which by @{thm [source] not_in_span_lin_indep} is exactly independence.

  This is the result that turns ``finite-dimensional'' into ``has a basis'', and hence the one that
  lets the dimension theory above be applied to a space presented by generators.\<close>
theorem basis_exists_from_spanning:
  assumes "spanning B"
  shows "\<exists>B' \<subseteq> B. basis B'"
  using assms
proof (induction "card B" arbitrary: B rule: less_induct)
  case less
  have finB: "finite B" and BV: "B \<subseteq> V" using less.prems by (auto simp: spanning_def)
  show ?case
  proof (cases "\<exists>w \<in> B. w \<in> span (B \<setminus> {w})")
    case True
    \<comment> \<open>A redundant vector: drop it.  The smaller set still spans, since anything in the span of
      @{term B} is already in the span of @{term "B \<setminus> {w}"}.\<close>
    then obtain w where w: "w \<in> B" and wsp: "w \<in> span (B \<setminus> {w})" by blast
    have sub: "B \<setminus> {w} \<subseteq> V" using BV by blast
    have "spanning (B \<setminus> {w})"
      unfolding spanning_def
    proof (intro conjI ballI finB sub)
      show "finite (B \<setminus> {w})" using finB by blast
      fix v assume v: "v \<in> V"
      have "v \<in> span (B \<setminus> {w})" using sub wsp
        using less.prems span_trans_mem spanning_span_all v w by (metis insert_Diff)
      then show "\<exists>c \<in> (B \<setminus> {w}) \<rightarrow>\<^sub>E R. v = lincomb c (B \<setminus> {w})"
      proof -
        obtain c C where veq: "v = lincomb c C" and finC: "finite C" and CB: "C \<subseteq> B \<setminus> {w}"
          and cR: "\<And>u. u \<in> C \<Longrightarrow> c u \<in> R" using \<open>v \<in> span (B \<setminus> {w})\<close> unfolding span_def by blast
        define d where "d \<equiv> restrict (\<lambda>u. if u \<in> C then c u else \<zero>) (B \<setminus> {w})"
        have dR: "\<And>u. u \<in> B \<setminus> {w} \<Longrightarrow> d u \<in> R" using cR by (auto simp: d_def)
        have dPiE: "d \<in> (B \<setminus> {w}) \<rightarrow>\<^sub>E R" using dR by (simp add: d_def)
        \<comment> \<open>Note the orientation: the lemma reads @{text "lincomb c D = lincomb c B"} with
          @{text "B \<subseteq> D"}, so the \<^emph>\<open>small\<close> set @{term C} is its @{text B} and the big one its @{text D}.\<close>
        have "lincomb d (B \<setminus> {w}) = lincomb d C"
        proof (intro CB sub lincomb_zero_extend_eq)
          show "\<And>u. \<lbrakk> u \<in> B \<setminus> {w}; u \<notin> C \<rbrakk> \<Longrightarrow> d u = \<zero>" by (simp add: d_def)
        qed (use finB CB sub dR in auto)
        also have "\<dots> = lincomb c C" by (rule lincomb_cong) (use CB sub cR in \<open>auto simp: d_def\<close>)
        finally have "lincomb d (B \<setminus> {w}) = v" using veq by simp
        then show ?thesis using dPiE by blast
      qed
    qed
    moreover have "card (B \<setminus> {w}) < card B"
      by (meson finB w card_Diff1_less_iff)
    ultimately show ?thesis using less.hyps by blast
  next
    case False
    then show ?thesis
      using BV basisI finB less.prems not_in_span_lin_indep by auto
  qed
qed

text \<open>A finite vector space has cardinality @{term "card R ^ dimension"}.\<close>
theorem card_eq_card_base_pow_dimension:
  assumes finV: "finite V"
  shows "card V = card R ^ dimension"
proof -
  have spanV: "spanning V"
    using finV mod.spanning_whole spanning_iff_mod_spanning by blast
  obtain B where basis: "basis B"
    using basis_exists_from_spanning[OF spanV] by blast
  then show ?thesis
    using card_eq_card_base_pow_dim dimension_eq_any_field by presburger
qed

text \<open>A uniform finite bound on the cardinalities of independent sets already gives a basis.  Choose
  an independent set of maximum cardinality; if a vector lay outside its span, adjoining that vector
  would produce a strictly larger independent set.\<close>
theorem basis_exists_of_independent_card_bound:
  assumes bound: "\<And>A. lin_indep A \<Longrightarrow> card A \<le> n"
  shows "\<exists>A. basis A"
proof -
  define sizes where "sizes \<equiv> {card A | A. lin_indep A}"
  obtain sizes_nonempty: "sizes \<noteq> {}" and sizes_bounded: "sizes \<subseteq> {..n}"
    using assms unfolding sizes_def lin_indep_def by auto
  have finite_sizes: "finite sizes"
    using sizes_bounded by (rule finite_subset) simp
  have "Max sizes \<in> sizes" by (rule Max_in[OF finite_sizes sizes_nonempty])
  then obtain A where indA: "lin_indep A" and maxA: "Max sizes = card A"
    unfolding sizes_def by blast
  have finA: "finite A" and AV: "A \<subseteq> V" using indA by (auto simp: lin_indep_def)
  have "mod.spanning A"
  proof (rule mod.spanningI[OF AV])
    fix x assume xV: "x \<in> V"
    show "x \<in> span A"
    proof (rule ccontr)
      assume outside: "x \<notin> span A"
      have ind_insert: "lin_indep (insert x A)"
        by (rule lin_indep_insert[OF indA xV outside])
      have xA: "x \<notin> A"
        using AV outside span_incl by force
      have "card (insert x A) \<le> Max sizes"
        using Max_ge finite_sizes ind_insert sizes_def by blast 
      then show False
        using finA maxA xA by force
    qed
  qed
  then show ?thesis
    using basisI finA indA mod.spanning_def spanning_iff_mod_spanning by meson
qed

text \<open>Hence the dimension of a finitely spanned space is bounded by any spanning set.\<close>
corollary dimension_le_spanning:
  assumes "spanning B" shows "dimension \<le> card B"
proof -
  obtain B' where B'B: "B' \<subseteq> B" and B': "basis B'"
    using assms by (blast dest: basis_exists_from_spanning)
  then show ?thesis using dimension_eq_any_field
    using assms card_mono spanning_def by auto
qed

end

context vector_subspace
begin

text \<open>Linear combinations and spans do not depend on whether their vectors are viewed in the
  ambient space or in the subspace; only the carrier side-condition changes.\<close>

lemma sub_fincomp_eq:
  assumes finA: "finite A" and f: "f \<in> A \<rightarrow> W"
  shows "sub.vadd.fincomp f A = vadd.fincomp f A"
  using finA f
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x A)
  obtain fxV: "f x \<in> V" and fAV: "f \<in> A \<rightarrow> V"
    using Module.submodule_subset W_submodule insert.prems mod.Module_axioms by fastforce
  with insert show ?case
    by auto
qed

lemma sub_lincomb_eq:
  assumes finA: "finite A" and AW: "A \<subseteq> W"
    and c: "\<And>v. v \<in> A \<Longrightarrow> c v \<in> R"
  shows "sub.lincomb c A = lincomb c A"
  unfolding sub.lincomb_def lincomb_def
  using AW c by (auto intro!: sub_fincomp_eq[OF finA] sub.scale_closed)

lemma sub_span_eq:
  assumes AW: "A \<subseteq> W"
  shows "sub.span A = span A"
proof
  show "sub.span A \<subseteq> span A"
  proof
    fix x assume "x \<in> sub.span A"
    then obtain c C where C: "finite C" "C \<subseteq> A" "sub.mod.coeffs_on c C"
      "x = sub.lincomb c C" and CW: "C \<subseteq> W" using assms sub.mod.spanE by (metis subset_trans)
    have x_eq: "x = lincomb c C" using C sub_lincomb_eq[OF C(1) CW] sub.mod.coeffs_onD by simp
    show "x \<in> span A"
      using C mod.spanI x_eq by force
  qed
  show "span A \<subseteq> sub.span A"
  proof
    fix x assume "x \<in> span A"
    then obtain c C where C: "finite C" "C \<subseteq> A" "mod.coeffs_on c C" "x = lincomb c C" 
      and CW: "C \<subseteq> W" using assms mod.spanE by (metis subset_trans)
    have x_eq: "x = sub.lincomb c C" using C sub_lincomb_eq[OF C(1) CW] mod.coeffs_onD by simp
    show "x \<in> sub.span A"
      using C sub.mod.spanI x_eq by force
  qed
qed

lemma sub_lin_indep_iff:
  assumes AW: "A \<subseteq> W"
  shows "sub.lin_indep A \<longleftrightarrow> lin_indep A"
proof
  assume ind: "sub.lin_indep A"
  show "lin_indep A"
    unfolding lin_indep_def
  proof (intro conjI ballI impI)
    show finA: "finite A" 
      using ind by (simp add: sub.lin_indep_def)
    show "A \<subseteq> V" using AW W_submodule mod.submodule_subset by blast
    fix c v
    assume c: "c \<in> A \<rightarrow>\<^sub>E R" and zero: "lincomb c A = \<zero>\<^sub>V" and v: "v \<in> A"
    have coeff: "\<And>u. u \<in> A \<Longrightarrow> c u \<in> R" using c by auto
    have "sub.lincomb c A = \<zero>\<^sub>V" using zero sub_lincomb_eq[OF finA AW coeff] by simp
    then show "c v = \<zero>" using ind c v by (simp add: sub.lin_indep_def)
  qed
next
  assume ind: "lin_indep A"
  show "sub.lin_indep A"
    unfolding sub.lin_indep_def
  proof (intro conjI ballI impI AW)
    show finA: "finite A" 
      using ind by (simp add: lin_indep_def)
    fix c v
    assume c: "c \<in> A \<rightarrow>\<^sub>E R" and zero: "sub.lincomb c A = \<zero>\<^sub>V" and v: "v \<in> A"
    have coeff: "\<And>u. u \<in> A \<Longrightarrow> c u \<in> R" using c by auto
    have "lincomb c A = \<zero>\<^sub>V" using zero sub_lincomb_eq[OF finA AW coeff] by simp
    then show "c v = \<zero>" using ind c v by (simp add: lin_indep_def)
  qed
qed

text \<open>\<^emph>\<open>Subspaces of finite-dimensional spaces have bases.\<close>  The possible cardinalities of
  independent subsets of @{term W} are bounded by the size of an ambient basis.  Choose an
  independent set of maximum cardinality; adjoining any vector outside its span would contradict
  maximality, so it spans the subspace.\<close>

theorem subspace_basis_exists:
  assumes B: "basis B"
  shows "\<exists>A. sub.basis A"
proof -
  define sizes where "sizes \<equiv> {card A | A. sub.lin_indep A}"
  have finB: "finite B" and BV: "B \<subseteq> V" using B by (auto simp: basis_def)
  have sizes_nonempty: "sizes \<noteq> {}"
    unfolding sizes_def using sub.lin_indep_def by force
  have sizes_bounded: "sizes \<subseteq> {..card B}"
  proof
    fix n assume "n \<in> sizes"
    then obtain A where A: "sub.lin_indep A" "n = card A" and AW: "A \<subseteq> W"
      using sizes_def sub.lin_indep_def by auto
    then have indA: "lin_indep A" using sub_lin_indep_iff[OF AW] A by simp
    have "A \<subseteq> span B" using basis_spanning[OF B]
      using indA lin_indep_def spanning_span_all by blast
    then show "n \<in> {..card B}" using A
      by (simp add: BV finB indA independent_le_span)
  qed
  have finite_sizes: "finite sizes"
    using sizes_bounded by (rule finite_subset) simp
  have "Max sizes \<in> sizes" by (rule Max_in[OF finite_sizes sizes_nonempty])
  then obtain A where indA: "sub.lin_indep A" and maxA: "Max sizes = card A" 
       and finA: "finite A" and AW: "A \<subseteq> W"
    unfolding sizes_def using sub.lin_indep_def by auto
  have "sub.mod.spanning A"
  proof (rule sub.mod.spanningI[OF AW])
    fix x assume xW: "x \<in> W"
    show "x \<in> sub.span A"
    proof (rule ccontr)
      assume outside: "x \<notin> sub.span A"
      have ind_insert: "sub.lin_indep (insert x A)"
        by (rule sub.lin_indep_insert[OF indA xW outside])
      have insert_size: "card (insert x A) = Suc (card A)"
        by (meson AW finA outside sub.span_incl card_insert_disjoint)
      then show False 
        using insert_size maxA Max_ge finite_sizes ind_insert sizes_def by fastforce
    qed
  qed
  then have "sub.basis A" using indA
    by (simp add: AW finA sub.basisI sub.spanning_iff_mod_spanning)
  then show ?thesis by blast
qed

text \<open>A subspace of a finite-dimensional space cannot have larger dimension than the
  ambient space.  This is the set-based counterpart of the standard monotonicity theorem for
  dimension: a subspace basis is also ambiently independent, so Steinitz bounds it by any
  ambient basis.\<close>

theorem subspace_dimension_le:
  assumes B: "basis B"
  shows "sub.dimension \<le> dimension"
proof -
  obtain A where A: "sub.basis A" and AW: "A \<subseteq> W" and indA: "lin_indep A"
    using subspace_basis_exists[OF B] sub.basis_def sub.basis_lin_indep sub_lin_indep_iff by metis
  have finB: "finite B" and BV: "B \<subseteq> V" using B by (auto simp: basis_def)
  have AV: "A \<subseteq> V" using AW W_submodule mod.submodule_subset by blast
  have "A \<subseteq> span B"
    using basis_spanning[OF B] AV by (auto intro: spanning_span_all)
  then show ?thesis
    using sub.dimension_eq_any_field[OF A] dimension_eq_any_field[OF B]
    by (simp add: BV finB indA independent_le_span)
qed

text \<open>In finite dimension, a subspace has full dimension exactly when it is the whole
  ambient space.  For the non-trivial direction, extend a subspace basis to an ambient basis;
  equality of dimensions leaves no additional basis vectors.\<close>

theorem subspace_eq_ambient_iff_dimension_eq:
  assumes B: "basis B"
  shows "W = V \<longleftrightarrow> sub.dimension = dimension"
proof
  assume WV: "W = V"
  have subB: "sub.basis B" using B WV by simp
  show "sub.dimension = dimension"
    using sub.dimension_eq_any_field[OF subB] dimension_eq_any_field[OF B] by simp
next
  assume dim: "sub.dimension = dimension"
  obtain A where A: "sub.basis A"
    using subspace_basis_exists[OF B] by blast
  have AW: "A \<subseteq> W" using A by (simp add: sub.basis_def)
  have indA: "lin_indep A"
    using sub.basis_lin_indep[OF A] sub_lin_indep_iff[OF AW] by simp
  obtain C where AC: "A \<subseteq> C" and C: "basis C" and finC: "finite C"
    using basis_extension[OF indA B] basis_def by blast
  then have "A=C"
    using A card_subset_eq dim dimension_eq_any_field sub.dimension_eq_any_field by auto
  then have "V \<subseteq> W"
    using C basis_spanning spanning_span_all AW W_submodule mod.span_minimal by blast
  then show "W = V"
    using W_submodule mod.submodule_subset by blast
qed

text \<open>The only zero-dimensional subspace is the trivial one.  The ambient basis assumption
  supplies a basis of the subspace; dimension zero then forces that basis to be empty.\<close>

theorem subspace_dimension_eq_zero_iff:
  assumes B: "basis B"
  shows "sub.dimension = 0 \<longleftrightarrow> W = {\<zero>\<^sub>V}"
proof
  assume dim: "sub.dimension = 0"
  obtain A where A: "sub.basis A" "finite A"
    using subspace_basis_exists[OF B] sub.basis_def by blast
  then have "A = {}" using sub.dimension_eq_any_field dim by fastforce
  then have empty_spanning: "sub.spanning {}"
    using A sub.basis_spanning by blast
  then show "W = {\<zero>\<^sub>V}"
    unfolding sub.spanning_def by auto
next
  assume W: "W = {\<zero>\<^sub>V}"
  then show "sub.dimension = 0"
    using sub.dimension_eq_any_field sub.basis_empty_trivial by force
qed

end

end
