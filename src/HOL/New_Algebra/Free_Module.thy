section \<open>Generators, independence, bases and free modules\<close>

theory Free_Module
  imports Module_Basics
begin

text \<open>Over a ring the two halves of ``basis'' come apart.  A spanning set need not be linearly
  independent, a linearly independent set need not span, and --- unlike the vector-space case --- a
  linearly independent spanning set is genuinely stronger than either.  So \<open>spanning\<close> and
  \<open>lin_indep\<close> are defined separately, and a module is \<^emph>\<open>free\<close> when it has a basis, meaning a
  set that is both.

  \<^emph>\<open>These definitions are stated for arbitrary --- possibly infinite --- subsets.\<close>  Finiteness is
  not part of either concept; it enters only through the finite index sets inside \<open>lincomb\<close> and
  \<open>span\<close>.  This matters because \<open>madd.fincomp\<close> returns the unit on an infinite index set
  (\<open>fincomp_infinite\<close>), so a definition that applied \<open>lincomb\<close> directly to an
  infinite set would silently be talking about the zero of the module rather than about an
  infinite sum.
  Quantifying over finite subsets, as \<open>lin_indep\<close> does, avoids that trap; guarding the
  definition with \<open>finite\<close> would merely hide it.

  \<open>Vector_Space\<close> defines its own finite-dimensional \<open>basis\<close> as bijectivity of the coordinate map,
  which is the right packaging for the cardinality count there but presumes finiteness.  The
  bridging lemmas relating the two live in that theory, with \<open>finite\<close> as an explicit hypothesis
  where it does real work rather than baked into the concept.

  The uniqueness-of-coordinates theorem \<open>lin_indep_lincomb_unique\<close> below is the reason linear
  independence is worth isolating: it is what makes a free module the right domain for defining a
  homomorphism by prescribing values on a basis.\<close>

context Module
begin

subsection \<open>Coefficient functions\<close>

text \<open>A \<^emph>\<open>coefficient function on \<open>B\<close>\<close> assigns a ring element to each element of @{term B}.  We do
  not require extensionality: the linear combination @{term "lincomb c B"} only ever inspects
  @{term c} on @{term B}, so two coefficient functions agreeing on @{term B} give the same
  combination (\<open>lincomb_cong\<close> below).\<close>
definition coeffs_on :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "coeffs_on c B \<longleftrightarrow> (\<forall>v \<in> B. c v \<in> R)"

lemma coeffs_onI: "(\<And>v. v \<in> B \<Longrightarrow> c v \<in> R) \<Longrightarrow> coeffs_on c B"
  by (simp add: coeffs_on_def)

lemma coeffs_onD: "\<lbrakk> coeffs_on c B; v \<in> B \<rbrakk> \<Longrightarrow> c v \<in> R"
  by (simp add: coeffs_on_def)

lemma coeffs_on_subset: "\<lbrakk> coeffs_on c B; A \<subseteq> B \<rbrakk> \<Longrightarrow> coeffs_on c A"
  by (auto simp: coeffs_on_def)

text \<open>The zero coefficient function.\<close>
abbreviation zero_coeffs :: "'b \<Rightarrow> 'a"
  where "zero_coeffs \<equiv> (\<lambda>_. \<zero>)"

lemma coeffs_on_zero [simp, intro]: "coeffs_on zero_coeffs B"
  by (simp add: coeffs_on_def)

text \<open>A linear combination depends on the coefficients only through their values on the index set.\<close>
lemma lincomb_cong:
  assumes B: "B \<subseteq> M" and eq: "\<And>v. v \<in> B \<Longrightarrow> c v = d v" and d: "coeffs_on d B"
  shows "lincomb c B = lincomb d B"
  unfolding lincomb_def
proof (rule madd.fincomp_cong')
  show "B = B" ..
  show "(\<lambda>v. d v \<odot> v) \<in> B \<rightarrow> M" using B d by (auto intro: scale_closed coeffs_onD)
  show "\<And>v. v \<in> B \<Longrightarrow> c v \<odot> v = d v \<odot> v" using eq by simp
qed

text \<open>The zero combination.  Every term is @{term "\<zero> \<odot> v = \<zero>\<^sub>M"}.\<close>
lemma lincomb_zero_coeffs [simp]:
  assumes B: "B \<subseteq> M" shows "lincomb zero_coeffs B = \<zero>\<^sub>M"
  unfolding lincomb_def
  using B by (auto intro!: madd.fincomp_unit_eqI scale_zero_scalar)

text \<open>Scaling distributes over a finite module sum.  Proved by induction on the index set; kept as
  a named lemma because inline it is slow enough to hit the proof timeout.\<close>
lemma scale_fincomp:
  assumes a: "a \<in> R" and f: "f \<in> A \<rightarrow> M"
  shows "a \<odot> madd.fincomp f A = madd.fincomp (\<lambda>v. a \<odot> f v) A"
  using f
proof (induct A rule: infinite_finite_induct)
  case (infinite A) then show ?case using a by (simp add: scale_zero_elem)
next
  case empty then show ?case using a by (simp add: scale_zero_elem)
next
  case (insert v A)
  then have fv: "f v \<in> M" and fA: "f \<in> A \<rightarrow> M" by auto
  have sc: "(\<lambda>u. a \<odot> f u) \<in> A \<rightarrow> M" using a fA by (auto intro: scale_closed)
  have "a \<odot> madd.fincomp f (insert v A) = a \<odot> (f v \<oplus> madd.fincomp f A)"
    using insert fv fA by simp
  also have "\<dots> = (a \<odot> f v) \<oplus> (a \<odot> madd.fincomp f A)"
    using a fv fA by (auto intro!: scale_distrib_madd madd.fincomp_closed)
  also have "\<dots> = (a \<odot> f v) \<oplus> madd.fincomp (\<lambda>u. a \<odot> f u) A"
    using insert fA by simp
  also have "\<dots> = madd.fincomp (\<lambda>u. a \<odot> f u) (insert v A)"
    using insert a fv sc by (auto intro!: madd.fincomp_insert[symmetric] scale_closed)
  finally show ?case .
qed

text \<open>Enlarging the index set by elements whose coefficient is @{term \<zero>} does not change the
  combination: the extra terms are all @{term "\<zero> \<odot> v = \<zero>\<^sub>M"}.  This is what lets two combinations
  over different finite index sets be added on their union.\<close>
lemma lincomb_mono_zero:
  assumes B: "finite B" and AB: "A \<subseteq> B" and BM: "B \<subseteq> M"
    and zero: "\<And>v. v \<in> B - A \<Longrightarrow> c v = \<zero>" and c: "coeffs_on c B"
  shows "lincomb c A = lincomb c B"
  unfolding lincomb_def
proof (rule madd.fincomp_mono_neutral_cong_left)
  show "finite B" and "A \<subseteq> B" using B AB by simp_all
  show "\<And>v. v \<in> B - A \<Longrightarrow> c v \<odot> v = \<zero>\<^sub>M"
    using zero BM by (auto simp: scale_zero_scalar)
  show "\<And>v. v \<in> A \<Longrightarrow> c v \<odot> v = c v \<odot> v" by simp
  show "(\<lambda>v. c v \<odot> v) \<in> B \<rightarrow> M"
    using BM c by (auto intro!: scale_closed intro: coeffs_onD)
qed


subsection \<open>Membership in the span\<close>

text \<open>Introduction and elimination for @{const span}, in the form the proofs below want.\<close>
lemma spanI:
  assumes "finite A" and "A \<subseteq> S" and "coeffs_on c A" and "x = lincomb c A"
  shows "x \<in> span S"
  using assms unfolding span_def coeffs_on_def by blast

lemma spanE:
  assumes "x \<in> span S"
  obtains c A where "finite A" "A \<subseteq> S" "coeffs_on c A" "x = lincomb c A"
  using assms unfolding span_def coeffs_on_def by blast

text \<open>A combination over a singleton is just the scaling.  Kept separate: unfolding
  @{const lincomb} to @{const madd.fincomp} inline makes the simplifier work far harder than it
  needs to (it timed out at 12s in an earlier draft).\<close>
lemma lincomb_singleton [simp]:
  assumes v: "v \<in> M" and c: "c v \<in> R"
  shows "lincomb c {v} = c v \<odot> v"
  unfolding lincomb_def using v c by (simp add: scale_closed)

text \<open>Each element of a set lies in its span: take the singleton combination with coefficient
  @{term \<one>}.\<close>
lemma span_incl:
  assumes S: "S \<subseteq> M" shows "S \<subseteq> span S"
proof
  fix v assume v: "v \<in> S"
  then have vM: "v \<in> M" using S by blast
  have "lincomb (\<lambda>_. \<one>) {v} = \<one> \<odot> v" using vM by simp
  also have "\<dots> = v" using vM by (rule scale_one)
  finally have "v = lincomb (\<lambda>_. \<one>) {v}" ..
  then show "v \<in> span S" using v by (auto intro!: spanI[where A = "{v}"] coeffs_onI)
qed

text \<open>Adding coefficient functions pointwise adds the combinations.  Both the span-closure proof
  and the uniqueness proof need this; factored out so each does the @{const madd.fincomp}
  manipulation once.\<close>
lemma lincomb_add_coeffs:
  assumes AM: "A \<subseteq> M" and c: "coeffs_on c A" and d: "coeffs_on d A"
  shows "lincomb (\<lambda>v. c v + d v) A = lincomb c A \<oplus> lincomb d A"
  unfolding lincomb_def
proof (rule trans)
  show "madd.fincomp (\<lambda>v. (c v + d v) \<odot> v) A
      = madd.fincomp (\<lambda>v. (c v \<odot> v) \<oplus> (d v \<odot> v)) A"
    using AM c d
    by (intro madd.fincomp_cong')
       (auto intro!: scale_distrib_add scale_closed madd_closed intro: coeffs_onD)
  show "madd.fincomp (\<lambda>v. (c v \<odot> v) \<oplus> (d v \<odot> v)) A
      = madd.fincomp (\<lambda>v. c v \<odot> v) A \<oplus> madd.fincomp (\<lambda>v. d v \<odot> v) A"
    using AM c d
    by (intro madd.fincomp_comp) (auto intro!: scale_closed intro: coeffs_onD)
qed

text \<open>The span is a submodule.  Closure under addition merges two finite index sets; closure under
  scaling multiplies through the coefficients.\<close>
lemma span_zero [simp, intro]: "\<zero>\<^sub>M \<in> span S"
  by (rule spanI[where A = "{}" and c = zero_coeffs]) auto

lemma span_madd_closed:
  assumes S: "S \<subseteq> M" and x: "x \<in> span S" and y: "y \<in> span S"
  shows "x \<oplus> y \<in> span S"
proof -
  from x obtain c A where A: "finite A" "A \<subseteq> S" "coeffs_on c A" "x = lincomb c A"
    by (rule spanE)
  from y obtain d B where B: "finite B" "B \<subseteq> S" "coeffs_on d B" "y = lincomb d B"
    by (rule spanE)
  \<comment> \<open>Extend both coefficient functions by @{term \<zero>} off their own index sets and add them on the
    union; each combination is unchanged by @{thm [source] lincomb_mono_zero}.\<close>
  define c' where "c' = (\<lambda>v. if v \<in> A then c v else \<zero>)"
  define d' where "d' = (\<lambda>v. if v \<in> B then d v else \<zero>)"
  have UM: "A \<union> B \<subseteq> M" using A(2) B(2) S by blast
  have finU: "finite (A \<union> B)" using A(1) B(1) by simp
  have c'R: "coeffs_on c' (A \<union> B)"
  proof (rule coeffs_onI)
    fix v assume "v \<in> A \<union> B"
    show "c' v \<in> R" unfolding c'_def using coeffs_onD[OF A(3)] by simp
  qed
  have d'R: "coeffs_on d' (A \<union> B)"
  proof (rule coeffs_onI)
    fix v assume "v \<in> A \<union> B"
    show "d' v \<in> R" unfolding d'_def using coeffs_onD[OF B(3)] by simp
  qed
  \<comment> \<open>Each extended combination over the union agrees with the original over its own index set,
    because the added coefficients are @{term \<zero>}.\<close>
  have cA: "lincomb c' (A \<union> B) = lincomb c A"
  proof -
    have "lincomb c' A = lincomb c' (A \<union> B)"
    proof (rule lincomb_mono_zero[OF finU Un_upper1 UM])
      show "\<And>v. v \<in> A \<union> B - A \<Longrightarrow> c' v = \<zero>" unfolding c'_def by simp
      show "coeffs_on c' (A \<union> B)" by (rule c'R)
    qed
    moreover have "lincomb c' A = lincomb c A"
    proof (rule lincomb_cong)
      show "A \<subseteq> M" using A(2) S by blast
      show "\<And>v. v \<in> A \<Longrightarrow> c' v = c v" unfolding c'_def by simp
      show "coeffs_on c A" by (rule A(3))
    qed
    ultimately show ?thesis by simp
  qed
  have dB: "lincomb d' (A \<union> B) = lincomb d B"
  proof -
    have "lincomb d' B = lincomb d' (A \<union> B)"
    proof (rule lincomb_mono_zero[OF finU Un_upper2 UM])
      show "\<And>v. v \<in> A \<union> B - B \<Longrightarrow> d' v = \<zero>" unfolding d'_def by simp
      show "coeffs_on d' (A \<union> B)" by (rule d'R)
    qed
    moreover have "lincomb d' B = lincomb d B"
    proof (rule lincomb_cong)
      show "B \<subseteq> M" using B(2) S by blast
      show "\<And>v. v \<in> B \<Longrightarrow> d' v = d v" unfolding d'_def by simp
      show "coeffs_on d B" by (rule B(3))
    qed
    ultimately show ?thesis by simp
  qed
  have sum: "lincomb (\<lambda>v. c' v + d' v) (A \<union> B) = x \<oplus> y"
    using lincomb_add_coeffs[OF UM c'R d'R] cA dB A(4) B(4) by simp
  have sumR: "coeffs_on (\<lambda>v. c' v + d' v) (A \<union> B)"
    by (rule coeffs_onI) (use coeffs_onD[OF c'R] coeffs_onD[OF d'R] in simp)
  show ?thesis
    by (rule spanI[OF finU _ sumR sum[symmetric]]) (use A(2) B(2) in blast)
qed

lemma span_scale_closed:
  assumes S: "S \<subseteq> M" and a: "a \<in> R" and x: "x \<in> span S"
  shows "a \<odot> x \<in> span S"
proof -
  from x obtain c A where A: "finite A" "A \<subseteq> S" "coeffs_on c A" "x = lincomb c A"
    by (rule spanE)
  have AM: "A \<subseteq> M" using A(2) S by blast
  have pi: "(\<lambda>v. c v \<odot> v) \<in> A \<rightarrow> M"
    using AM A(3) by (auto intro!: scale_closed intro: coeffs_onD)
  have "a \<odot> lincomb c A = lincomb (\<lambda>v. a \<cdot> c v) A"
    unfolding lincomb_def
  proof (rule trans)
    show "a \<odot> madd.fincomp (\<lambda>v. c v \<odot> v) A = madd.fincomp (\<lambda>v. a \<odot> (c v \<odot> v)) A"
      using a pi by (rule scale_fincomp)
    \<comment> \<open>@{thm [source] scale_scale} is oriented @{term "(a \<cdot> b) \<odot> v = a \<odot> (b \<odot> v)"}, so each term is
      rewritten right-to-left, one element at a time.\<close>
    show "madd.fincomp (\<lambda>v. a \<odot> (c v \<odot> v)) A = madd.fincomp (\<lambda>v. (a \<cdot> c v) \<odot> v) A"
    proof (rule madd.fincomp_cong')
      show "A = A" ..
      show "(\<lambda>v. (a \<cdot> c v) \<odot> v) \<in> A \<rightarrow> M"
        using AM a coeffs_onD[OF A(3)] by (auto intro!: scale_closed)
      fix v assume v: "v \<in> A"
      then have vM: "v \<in> M" and cv: "c v \<in> R" using AM coeffs_onD[OF A(3)] by auto
      show "a \<odot> (c v \<odot> v) = (a \<cdot> c v) \<odot> v" by (rule scale_scale[OF a cv vM, symmetric])
    qed
  qed
  moreover have "coeffs_on (\<lambda>v. a \<cdot> c v) A"
    by (rule coeffs_onI) (use a coeffs_onD[OF A(3)] in simp)
  ultimately show ?thesis using A by (blast intro: spanI)
qed

theorem span_submodule:
  assumes S: "S \<subseteq> M" shows "submodule (span S)"
proof (rule submoduleI)
  show "span S \<subseteq> M" using S by (auto intro: span_closed)
  show "\<zero>\<^sub>M \<in> span S" by simp
  show "\<And>u v. \<lbrakk> u \<in> span S; v \<in> span S \<rbrakk> \<Longrightarrow> u \<oplus> v \<in> span S"
    using S by (rule span_madd_closed)
  show "\<And>a v. \<lbrakk> a \<in> R; v \<in> span S \<rbrakk> \<Longrightarrow> a \<odot> v \<in> span S"
    using S by (rule span_scale_closed)
qed

text \<open>The span is the least submodule containing its generators.  This elimination form
  complements @{thm [source] span_submodule}: any submodule containing @{term S} contains every
  finite linear combination of elements of @{term S}.\<close>

theorem span_minimal:
  assumes N: "submodule N" and SN: "S \<subseteq> N"
  shows "span S \<subseteq> N"
proof
  fix x assume "x \<in> span S"
  then obtain c A where A: "finite A" "A \<subseteq> S" "coeffs_on c A" "x = lincomb c A"
    by (rule spanE)
  have lincomb_in_N: "lincomb c A \<in> N"
    if "finite A" "A \<subseteq> N" "coeffs_on c A" for A c
    using that
  proof (induction A arbitrary: c rule: finite_induct)
    case empty
    then show ?case using submodule_zero[OF N] by simp
  next
    case (insert v A)
    have vN: "v \<in> N" and AN: "A \<subseteq> N" using insert.prems by auto
    have NM: "N \<subseteq> M" by (rule submodule_subset[OF N])
    have vM: "v \<in> M" and AM: "A \<subseteq> M" using vN AN NM by auto
    have cv: "c v \<in> R" by (rule coeffs_onD[OF insert.prems(2)]) simp
    have cA: "coeffs_on c A" by (rule coeffs_on_subset[OF insert.prems(2)]) blast
    have terms: "(\<lambda>u. c u \<odot> u) \<in> A \<rightarrow> M"
      using AM cA by (auto intro!: scale_closed intro: coeffs_onD)
    have eq: "lincomb c (insert v A) = (c v \<odot> v) \<oplus> lincomb c A"
      unfolding lincomb_def using insert.hyps terms cv vM by (simp add: scale_closed)
    have term_N: "c v \<odot> v \<in> N" by (rule submodule_scale[OF N cv vN])
    have rest_N: "lincomb c A \<in> N" by (rule insert.IH[OF AN cA])
    have "(c v \<odot> v) \<oplus> lincomb c A \<in> N"
      by (rule submodule_add[OF N term_N rest_N])
    then show ?case using eq by simp
  qed
  have "lincomb c A \<in> N"
    by (rule lincomb_in_N[OF A(1) _ A(3)]) (use A(2) SN in blast)
  then show "x \<in> N" using A(4) by simp
qed


subsection \<open>Generating sets, independence, bases\<close>

text \<open>@{term S} \<^emph>\<open>generates\<close> the module when its span is everything.\<close>
definition spanning :: "'b set \<Rightarrow> bool"
  where "spanning S \<longleftrightarrow> S \<subseteq> M \<and> span S = M"

lemma spanningI: "\<lbrakk> S \<subseteq> M; \<And>v. v \<in> M \<Longrightarrow> v \<in> span S \<rbrakk> \<Longrightarrow> spanning S"
  unfolding spanning_def using span_closed by blast

lemma spanningD: "\<lbrakk> spanning S; v \<in> M \<rbrakk> \<Longrightarrow> v \<in> span S"
  by (simp add: spanning_def)

text \<open>The whole module generates itself.\<close>
lemma spanning_whole: "spanning M"
  by (rule spanningI) (auto intro: span_incl[THEN subsetD])

text \<open>@{term S} is \<^emph>\<open>linearly independent\<close> when no non-trivial finite combination of \<^emph>\<open>distinct\<close> elements
  vanishes: whenever a finite @{term "A \<subseteq> S"} has @{term "lincomb c A = \<zero>\<^sub>M"}, all the coefficients
  on @{term A} are @{term \<zero>}.  Over a ring this is the right notion --- note it forbids torsion
  among the generators, which is why not every module is free.\<close>
definition lin_indep :: "'b set \<Rightarrow> bool"
  where "lin_indep S \<longleftrightarrow> S \<subseteq> M \<and>
    (\<forall>c A. finite A \<longrightarrow> A \<subseteq> S \<longrightarrow> coeffs_on c A \<longrightarrow> lincomb c A = \<zero>\<^sub>M \<longrightarrow> (\<forall>v \<in> A. c v = \<zero>))"

lemma lin_indepI:
  "\<lbrakk> S \<subseteq> M;
     \<And>c A v. \<lbrakk> finite A; A \<subseteq> S; coeffs_on c A; lincomb c A = \<zero>\<^sub>M; v \<in> A \<rbrakk> \<Longrightarrow> c v = \<zero> \<rbrakk>
   \<Longrightarrow> lin_indep S"
  unfolding lin_indep_def by blast

lemma lin_indepD:
  "\<lbrakk> lin_indep S; finite A; A \<subseteq> S; coeffs_on c A; lincomb c A = \<zero>\<^sub>M; v \<in> A \<rbrakk> \<Longrightarrow> c v = \<zero>"
  unfolding lin_indep_def by blast

lemma lin_indep_subset: "\<lbrakk> lin_indep S; T \<subseteq> S \<rbrakk> \<Longrightarrow> lin_indep T"
  unfolding lin_indep_def using subset_trans by blast

text \<open>The empty set is linearly independent.\<close>
lemma lin_indep_empty [simp, intro]: "lin_indep {}"
  by (rule lin_indepI) auto

text \<open>Independence rules out @{term "\<zero>\<^sub>M"} as a member --- the combination @{term "\<one> \<odot> \<zero>\<^sub>M"} vanishes
  with coefficient @{term \<one>} --- but \<^emph>\<open>only over a non-trivial ring\<close>.  The hypothesis
  @{term "\<one> \<noteq> \<zero>"} is genuinely needed: @{locale Module} extends @{locale Ring}, which does not
  assume it, and over the trivial ring @{term "\<one> = \<zero>"} makes every coefficient zero, so
  @{term "{\<zero>\<^sub>M}"} counts as \<open>lin_indep\<close>.\<close>
lemma lin_indep_not_mzero:
  assumes S: "lin_indep S" and nz: "\<one> \<noteq> \<zero>" shows "\<zero>\<^sub>M \<notin> S"
proof
  assume z: "\<zero>\<^sub>M \<in> S"
  have "lincomb (\<lambda>_. \<one>) {\<zero>\<^sub>M} = \<one> \<odot> \<zero>\<^sub>M" by simp
  also have "\<dots> = \<zero>\<^sub>M" by (rule scale_one) simp
  finally have lc: "lincomb (\<lambda>_. \<one>) {\<zero>\<^sub>M} = \<zero>\<^sub>M" .
  have "(\<lambda>_. \<one>) \<zero>\<^sub>M = \<zero>"
    by (rule lin_indepD[OF S _ _ _ lc]) (use z in \<open>auto intro!: coeffs_onI\<close>)
  then have "\<one> = \<zero>" by simp
  then show False using nz by simp
qed

text \<open>A \<^emph>\<open>basis\<close> is a linearly independent spanning set; a module is \<^emph>\<open>free\<close> when it has one.\<close>
definition module_basis :: "'b set \<Rightarrow> bool"
  where "module_basis B \<longleftrightarrow> spanning B \<and> lin_indep B"

definition free :: bool
  where "free \<longleftrightarrow> (\<exists>B. module_basis B)"

lemma module_basisI: "\<lbrakk> spanning B; lin_indep B \<rbrakk> \<Longrightarrow> module_basis B"
  by (simp add: module_basis_def)

lemma module_basis_spanning: "module_basis B \<Longrightarrow> spanning B"
  by (simp add: module_basis_def)

lemma module_basis_lin_indep: "module_basis B \<Longrightarrow> lin_indep B"
  by (simp add: module_basis_def)

lemma freeI: "module_basis B \<Longrightarrow> free"
  unfolding free_def by blast

text \<open>The trivial module is free, on the empty basis: its only element @{term "\<zero>\<^sub>M"} is the empty
  linear combination, which lies in @{term "span {}"}.\<close>
lemma module_basis_empty_trivial:
  assumes triv: "M = {\<zero>\<^sub>M}" shows "module_basis {}"
proof (rule module_basisI)
  show "spanning {}"
  proof (rule spanningI)
    show "{} \<subseteq> M" by simp
    fix v assume "v \<in> M"
    then have "v = \<zero>\<^sub>M" using triv by blast
    then show "v \<in> span {}" by simp
  qed
qed auto

lemma free_trivial:
  assumes "M = {\<zero>\<^sub>M}" shows free
  using module_basis_empty_trivial[OF assms] by (rule freeI)


subsection \<open>Uniqueness of coordinates\<close>

text \<open>\<^emph>\<open>The point of independence.\<close>  Over a linearly independent set the coefficients of a linear
  combination are determined by its value.  Stated for a common finite index set @{term A}: if two
  coefficient functions give the same combination, they agree on @{term A}.

  The proof forms the difference of the two coefficient functions.  Its combination is
  @{term "\<zero>\<^sub>M"}, so independence forces every difference to vanish, hence
  @{term "c v = d v"} by cancellation in the ring's additive group.\<close>
theorem lin_indep_lincomb_unique:
  assumes S: "lin_indep S" and A: "finite A" "A \<subseteq> S"
    and c: "coeffs_on c A" and d: "coeffs_on d A"
    and eq: "lincomb c A = lincomb d A"
    and v: "v \<in> A"
  shows "c v = d v"
proof -
  have AM: "A \<subseteq> M" using A(2) S unfolding lin_indep_def by blast
  \<comment> \<open>The difference function, and the observation that its combination is the difference of the
    combinations --- so it vanishes.\<close>
  define e where "e = (\<lambda>u. c u + (- d u))"
  have negd: "coeffs_on (\<lambda>u. - d u) A"
    by (rule coeffs_onI) (use coeffs_onD[OF d] in simp)
  have eR: "coeffs_on e A"
    unfolding e_def
    by (rule coeffs_onI)
       (use coeffs_onD[OF c] coeffs_onD[OF negd] in simp)
  have "lincomb e A = lincomb c A \<oplus> madd.inverse (lincomb d A)"
  proof -
    have "lincomb e A = lincomb c A \<oplus> lincomb (\<lambda>u. - d u) A"
      unfolding e_def by (rule lincomb_add_coeffs[OF AM c negd])
    also have "lincomb (\<lambda>u. - d u) A = madd.inverse (lincomb d A)"
      unfolding lincomb_def
    proof (rule trans)
      show "madd.fincomp (\<lambda>u. (- d u) \<odot> u) A = madd.fincomp (\<lambda>u. madd.inverse (d u \<odot> u)) A"
      proof (rule madd.fincomp_cong')
        show "A = A" ..
        show "(\<lambda>u. madd.inverse (d u \<odot> u)) \<in> A \<rightarrow> M"
          using AM coeffs_onD[OF d] by (auto intro!: scale_closed)
        fix u assume u: "u \<in> A"
        then have uM: "u \<in> M" and du: "d u \<in> R" using AM coeffs_onD[OF d] by auto
        show "(- d u) \<odot> u = madd.inverse (d u \<odot> u)" by (rule scale_neg_scalar[OF du uM])
      qed
      show "madd.fincomp (\<lambda>u. madd.inverse (d u \<odot> u)) A = madd.inverse (madd.fincomp (\<lambda>u. d u \<odot> u) A)"
        using AM d by (intro madd.fincomp_inverse) (auto intro!: scale_closed intro: coeffs_onD)
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = \<zero>\<^sub>M"
    using eq lincomb_closed[OF AM] d c
    by (simp add: madd.invertible_right_inverse coeffs_on_def)
  finally have "lincomb e A = \<zero>\<^sub>M" .
  \<comment> \<open>Independence kills every coefficient of the difference.\<close>
  then have "e v = \<zero>" using S A eR v by (rule_tac lin_indepD) auto
  then have cd: "c v + (- d v) = \<zero>" unfolding e_def .
  \<comment> \<open>Cancel the common summand @{term "- d v"}: both @{term "c v"} and @{term "d v"} added to it
    give @{term \<zero>}.  (Stated by explicit cancellation rather than left to @{method metis}, which
    on goals of this shape tends not to terminate.)\<close>
  have cvR: "c v \<in> R" and dvR: "d v \<in> R" using coeffs_onD[OF c v] coeffs_onD[OF d v] by simp_all
  have ndvR: "- d v \<in> R" using dvR by simp
  have "d v + (- d v) = \<zero>" using dvR by simp
  with cd have eq2: "c v + (- d v) = d v + (- d v)" by simp
  show "c v = d v"
    by (rule additive.invertible_right_cancel
              [OF additive.invertible[OF ndvR] ndvR cvR dvR, THEN iffD1, OF eq2])
qed

text \<open>Consequently, for a basis every module element has \<^emph>\<open>unique\<close> coordinates on any finite
  index set: existence from generation, uniqueness from independence.\<close>
corollary module_basis_coords_unique:
  assumes B: "module_basis B" and A: "finite A" "A \<subseteq> B"
    and c: "coeffs_on c A" and d: "coeffs_on d A"
    and eq: "lincomb c A = lincomb d A"
  shows "\<forall>v \<in> A. c v = d v"
  using lin_indep_lincomb_unique[OF module_basis_lin_indep[OF B] A c d eq] by blast


subsection \<open>Coordinates over a basis\<close>

text \<open>For the universal property below we need uniqueness across \<^emph>\<open>different\<close> index sets, not just a
  common one: two representations of the same element, over possibly different finite subsets of an
  independent set, must agree once each coefficient function is extended by @{term \<zero>} outside its own
  index set.  The proof pushes both representations onto the union of the two index sets --- which
  changes neither combination, by @{thm [source] lincomb_mono_zero} --- and then applies
  @{thm [source] lin_indep_lincomb_unique} there.\<close>
theorem lin_indep_lincomb_unique_gen:
  assumes S: "lin_indep S"
    and A: "finite A" "A \<subseteq> S" and A': "finite A'" "A' \<subseteq> S"
    and c: "coeffs_on c A" and d: "coeffs_on d A'"
    and eq: "lincomb c A = lincomb d A'"
  shows "(if v \<in> A then c v else \<zero>) = (if v \<in> A' then d v else \<zero>)"
proof -
  have SM: "S \<subseteq> M" using S unfolding lin_indep_def by blast
  have UM: "A \<union> A' \<subseteq> M" using A(2) A'(2) SM by blast
  have finU: "finite (A \<union> A')" using A(1) A'(1) by simp
  have US: "A \<union> A' \<subseteq> S" using A(2) A'(2) by blast
  define c' where "c' = (\<lambda>u. if u \<in> A then c u else \<zero>)"
  define d' where "d' = (\<lambda>u. if u \<in> A' then d u else \<zero>)"
  have c'R: "coeffs_on c' (A \<union> A')"
    by (rule coeffs_onI) (use coeffs_onD[OF c] in \<open>simp add: c'_def\<close>)
  have d'R: "coeffs_on d' (A \<union> A')"
    by (rule coeffs_onI) (use coeffs_onD[OF d] in \<open>simp add: d'_def\<close>)
  \<comment> \<open>Each extended combination over the union agrees with the original over its own index set.\<close>
  have cU: "lincomb c' (A \<union> A') = lincomb c A"
  proof -
    have "lincomb c' A = lincomb c' (A \<union> A')"
    proof (rule lincomb_mono_zero[OF finU Un_upper1 UM])
      show "\<And>u. u \<in> A \<union> A' - A \<Longrightarrow> c' u = \<zero>" unfolding c'_def by simp
      show "coeffs_on c' (A \<union> A')" by (rule c'R)
    qed
    moreover have "lincomb c' A = lincomb c A"
    proof (rule lincomb_cong)
      show "A \<subseteq> M" using A(2) SM by blast
      show "\<And>u. u \<in> A \<Longrightarrow> c' u = c u" unfolding c'_def by simp
      show "coeffs_on c A" by (rule c)
    qed
    ultimately show ?thesis by simp
  qed
  have dU: "lincomb d' (A \<union> A') = lincomb d A'"
  proof -
    have "lincomb d' A' = lincomb d' (A \<union> A')"
    proof (rule lincomb_mono_zero[OF finU Un_upper2 UM])
      show "\<And>u. u \<in> A \<union> A' - A' \<Longrightarrow> d' u = \<zero>" unfolding d'_def by simp
      show "coeffs_on d' (A \<union> A')" by (rule d'R)
    qed
    moreover have "lincomb d' A' = lincomb d A'"
    proof (rule lincomb_cong)
      show "A' \<subseteq> M" using A'(2) SM by blast
      show "\<And>u. u \<in> A' \<Longrightarrow> d' u = d u" unfolding d'_def by simp
      show "coeffs_on d A'" by (rule d)
    qed
    ultimately show ?thesis by simp
  qed
  from eq cU dU have eqU: "lincomb c' (A \<union> A') = lincomb d' (A \<union> A')" by simp
  show ?thesis
  proof (cases "v \<in> A \<union> A'")
    case True
    then have "c' v = d' v"
      by (rule lin_indep_lincomb_unique[OF S finU US c'R d'R eqU])
    then show ?thesis unfolding c'_def d'_def .
  next
    case False
    then show ?thesis by simp
  qed
qed

text \<open>Spans generated by disjoint parts of one independent set meet only at zero.  The
  generating sets themselves need not be finite: span membership supplies the two finite supports
  on which uniqueness of coordinates is applied.\<close>
theorem span_inter_eq_trivial:
  assumes S: "lin_indep S" and AS: "A \<subseteq> S" and BS: "B \<subseteq> S"
    and disjoint: "A \<inter> B = {}"
  shows "span A \<inter> span B = {\<zero>\<^sub>M}"
proof
  show "span A \<inter> span B \<subseteq> {\<zero>\<^sub>M}"
  proof
    fix x assume x: "x \<in> span A \<inter> span B"
    have xA: "x \<in> span A" and xB: "x \<in> span B" using x by simp_all
    from xA obtain c C where C: "finite C" "C \<subseteq> A" "coeffs_on c C"
      "x = lincomb c C"
      by (rule spanE)
    from xB obtain d D where D: "finite D" "D \<subseteq> B" "coeffs_on d D"
      "x = lincomb d D"
      by (rule spanE)
    have CS: "C \<subseteq> S" using C(2) AS by blast
    have DS: "D \<subseteq> S" using D(2) BS by blast
    have eq: "lincomb c C = lincomb d D" using C(4) D(4) by simp
    have c_zero: "c v = \<zero>" if v: "v \<in> C" for v
    proof -
      have "v \<notin> D" using v C(2) D(2) disjoint by blast
      moreover have "(if v \<in> C then c v else \<zero>) =
          (if v \<in> D then d v else \<zero>)"
        by (rule lin_indep_lincomb_unique_gen[OF S C(1) CS D(1) DS C(3) D(3) eq])
      ultimately show ?thesis using v by simp
    qed
    have CM: "C \<subseteq> M" using CS S unfolding lin_indep_def by blast
    have "x = lincomb c C" by (rule C(4))
    also have "\<dots> = lincomb zero_coeffs C"
      by (rule lincomb_cong[OF CM c_zero coeffs_on_zero])
    also have "\<dots> = \<zero>\<^sub>M" using CM by simp
    finally show "x \<in> {\<zero>\<^sub>M}" by simp
  qed
  show "{\<zero>\<^sub>M} \<subseteq> span A \<inter> span B" by simp
qed

text \<open>Every element of a module with a basis has a representation over some finite subset of it.\<close>
lemma module_basis_repr_exists:
  assumes B: "module_basis B" and x: "x \<in> M"
  obtains A c where "finite A" "A \<subseteq> B" "coeffs_on c A" "x = lincomb c A"
proof -
  have "x \<in> span B" by (rule spanningD[OF module_basis_spanning[OF B] x])
  then show thesis using that by (rule spanE)
qed

text \<open>And that representation is unique in the sense of
  @{thm [source] lin_indep_lincomb_unique_gen}: the coefficients, extended by @{term \<zero>}, are
  determined by the element.\<close>
corollary module_basis_repr_unique:
  assumes B: "module_basis B"
    and A: "finite A" "A \<subseteq> B" and A': "finite A'" "A' \<subseteq> B"
    and c: "coeffs_on c A" and d: "coeffs_on d A'"
    and eq: "lincomb c A = lincomb d A'"
  shows "(if v \<in> A then c v else \<zero>) = (if v \<in> A' then d v else \<zero>)"
  by (rule lin_indep_lincomb_unique_gen
            [OF module_basis_lin_indep[OF B] A A' c d eq])

end (* context module *)

end
