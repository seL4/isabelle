section \<open>The universal property of a free module\<close>

theory Free_Module_Universal
  imports Free_Module Module_Homomorphism
begin

text \<open>As in \<open>Module_Homomorphism\<close>: the import of \<open>FiniteProduct\<close> (through \<open>Module\<close>) re-merges HOL's
  @{text "+"}/@{text "-"} concrete syntax alongside the ring locale's.  That is harmless in term
  positions but ambiguous in the locale-header instantiation arguments below, so we remove the HOL
  syntax again.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A free module is free in the sense of a universal property: a homomorphism out of it may be
  prescribed \<^emph>\<open>arbitrarily\<close> on a basis, and is then determined.  Precisely: if @{term B} is a basis
  of the @{term R}-module @{term M} and @{term f} maps @{term B} into an @{term R}-module
  @{term M'}, then there is exactly one module homomorphism @{text "M \<rightarrow> M'"} extending @{term f}.

  This is what the uniqueness-of-coordinates results in \<open>Free_Module\<close> were for.  Existence needs
  coordinates to be \<^emph>\<open>readable\<close> --- every element has a representation over a finite subset of the
  basis --- and well-definedness needs them to be \<^emph>\<open>unique\<close> in the strong sense of
  \<open>lin_indep_lincomb_unique_gen\<close>, across different index sets, since nothing fixes an index set in
  advance.

  The locale below fixes the ring once in the \<open>for\<close> clause and shares it between the two modules,
  exactly as @{locale module_homomorphism} does; writing the two module interpretations with
  separate ring parameters would make the \<open>+\<close> token ambiguous.\<close>

locale free_module_ext =
  source: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" +
  target: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)"
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>) and scale (infixr \<open>\<odot>\<close> 75)
    and M' and madd' (infixl \<open>\<oplus>\<^sub>2\<close> 65) and mzero' (\<open>\<zero>\<^sub>2\<close>) and scale' (infixr \<open>\<odot>\<^sub>2\<close> 75)
    and B and f +
  assumes basis: "source.module_basis B"
    and f_closed: "v \<in> B \<Longrightarrow> f v \<in> M'"
begin

text \<open>The basis lies in the source module, and is independent and spanning.\<close>
lemma B_subset: "B \<subseteq> M"
  using basis source.module_basis_spanning unfolding source.spanning_def by blast

lemma B_lin_indep: "source.lin_indep B"
  by (rule source.module_basis_lin_indep[OF basis])


subsection \<open>The twisted sum\<close>

text \<open>The image of a linear combination must be @{text "\<Oplus>\<^bsub>v\<in>A\<^esub> c v \<odot>\<^sub>2 f v"} --- a sum in the
  \<^emph>\<open>target\<close> indexed by elements of the source.  We give this ``twisted'' sum a name and prove for it
  the three facts the homomorphism obligations need: it is closed, it is unchanged by padding the
  index set with zero coefficients, and it is additive and homogeneous in the coefficients.\<close>
definition tsum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'c"
  where "tsum c A = target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 f v) A"

lemma tsum_Pi:
  assumes A: "A \<subseteq> B" and c: "source.coeffs_on c A"
  shows "(\<lambda>v. c v \<odot>\<^sub>2 f v) \<in> A \<rightarrow> M'"
  using A c f_closed by (auto intro!: target.scale_closed intro: source.coeffs_onD)

lemma tsum_closed [intro, simp]:
  assumes A: "A \<subseteq> B" and c: "source.coeffs_on c A"
  shows "tsum c A \<in> M'"
  unfolding tsum_def using tsum_Pi[OF A c] by (rule target.madd.fincomp_closed)

lemma tsum_empty [simp]: "tsum c {} = \<zero>\<^sub>2"
  by (simp add: tsum_def)

text \<open>Only the values on the index set matter.\<close>
lemma tsum_cong:
  assumes A: "A \<subseteq> B" and eq: "\<And>v. v \<in> A \<Longrightarrow> c v = d v" and d: "source.coeffs_on d A"
  shows "tsum c A = tsum d A"
  unfolding tsum_def
proof (rule target.madd.fincomp_cong')
  show "A = A" ..
  show "(\<lambda>v. d v \<odot>\<^sub>2 f v) \<in> A \<rightarrow> M'" by (rule tsum_Pi[OF A d])
  show "\<And>v. v \<in> A \<Longrightarrow> c v \<odot>\<^sub>2 f v = d v \<odot>\<^sub>2 f v" using eq by simp
qed

text \<open>Padding the index set with zero coefficients does not change the sum: the extra terms are
  @{term "\<zero> \<odot>\<^sub>2 f v = \<zero>\<^sub>2"}.\<close>
lemma tsum_mono_zero:
  assumes finA': "finite A'" and AA': "A \<subseteq> A'" and A'B: "A' \<subseteq> B"
    and zero: "\<And>v. v \<in> A' \<setminus> A \<Longrightarrow> c v = \<zero>" and c: "source.coeffs_on c A'"
  shows "tsum c A = tsum c A'"
  unfolding tsum_def
proof (rule target.madd.fincomp_mono_neutral_cong_left)
  show "finite A'" and "A \<subseteq> A'" using finA' AA' by simp_all
  show "\<And>v. v \<in> A' \<setminus> A \<Longrightarrow> c v \<odot>\<^sub>2 f v = \<zero>\<^sub>2"
    using zero A'B f_closed by (auto simp: target.scale_zero_scalar)
  show "\<And>v. v \<in> A \<Longrightarrow> c v \<odot>\<^sub>2 f v = c v \<odot>\<^sub>2 f v" by simp
  show "(\<lambda>v. c v \<odot>\<^sub>2 f v) \<in> A' \<rightarrow> M'" by (rule tsum_Pi[OF A'B c])
qed

text \<open>Additivity in the coefficients.\<close>
lemma tsum_add_coeffs:
  assumes A: "A \<subseteq> B" and c: "source.coeffs_on c A" and d: "source.coeffs_on d A"
  shows "tsum (\<lambda>v. c v + d v) A = tsum c A \<oplus>\<^sub>2 tsum d A"
  unfolding tsum_def
proof (rule trans)
  show "target.madd.fincomp (\<lambda>v. (c v + d v) \<odot>\<^sub>2 f v) A
      = target.madd.fincomp (\<lambda>v. (c v \<odot>\<^sub>2 f v) \<oplus>\<^sub>2 (d v \<odot>\<^sub>2 f v)) A"
  proof (rule target.madd.fincomp_cong')
    show "A = A" ..
    show "(\<lambda>v. (c v \<odot>\<^sub>2 f v) \<oplus>\<^sub>2 (d v \<odot>\<^sub>2 f v)) \<in> A \<rightarrow> M'"
      using tsum_Pi[OF A c] tsum_Pi[OF A d] by auto
    fix v assume v: "v \<in> A"
    then have "c v \<in> R" and "d v \<in> R" and "f v \<in> M'"
      using source.coeffs_onD[OF c] source.coeffs_onD[OF d] A f_closed by auto
    then show "(c v + d v) \<odot>\<^sub>2 f v = (c v \<odot>\<^sub>2 f v) \<oplus>\<^sub>2 (d v \<odot>\<^sub>2 f v)"
      by (rule target.scale_distrib_add)
  qed
  show "target.madd.fincomp (\<lambda>v. (c v \<odot>\<^sub>2 f v) \<oplus>\<^sub>2 (d v \<odot>\<^sub>2 f v)) A
      = target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 f v) A \<oplus>\<^sub>2 target.madd.fincomp (\<lambda>v. d v \<odot>\<^sub>2 f v) A"
    using tsum_Pi[OF A c] tsum_Pi[OF A d] by (rule target.madd.fincomp_comp)
qed

text \<open>Homogeneity in the coefficients.\<close>
lemma tsum_scale_coeffs:
  assumes A: "A \<subseteq> B" and a: "a \<in> R" and c: "source.coeffs_on c A"
  shows "tsum (\<lambda>v. a \<cdot> c v) A = a \<odot>\<^sub>2 tsum c A"
  unfolding tsum_def
proof (rule trans)
  show "target.madd.fincomp (\<lambda>v. (a \<cdot> c v) \<odot>\<^sub>2 f v) A
      = target.madd.fincomp (\<lambda>v. a \<odot>\<^sub>2 (c v \<odot>\<^sub>2 f v)) A"
  proof (rule target.madd.fincomp_cong')
    show "A = A" ..
    show "(\<lambda>v. a \<odot>\<^sub>2 (c v \<odot>\<^sub>2 f v)) \<in> A \<rightarrow> M'"
      using a tsum_Pi[OF A c] by (auto intro: target.scale_closed)
    fix v assume v: "v \<in> A"
    then have cv: "c v \<in> R" and fv: "f v \<in> M'"
      using source.coeffs_onD[OF c] A f_closed by auto
    show "(a \<cdot> c v) \<odot>\<^sub>2 f v = a \<odot>\<^sub>2 (c v \<odot>\<^sub>2 f v)"
      by (rule target.scale_scale[OF a cv fv])
  qed
  show "target.madd.fincomp (\<lambda>v. a \<odot>\<^sub>2 (c v \<odot>\<^sub>2 f v)) A
      = a \<odot>\<^sub>2 target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 f v) A"
    using a tsum_Pi[OF A c] by (rule target.scale_fincomp[symmetric])
qed


subsection \<open>The extension is well defined\<close>

text \<open>Two representations of the same element give the same twisted sum.  This is where
  \<open>lin_indep_lincomb_unique_gen\<close> is used: the coefficient functions, extended by @{term \<zero>}, agree,
  and each twisted sum equals the one over the union of the two index sets.\<close>
lemma tsum_well_defined:
  assumes A: "finite A" "A \<subseteq> B" and A': "finite A'" "A' \<subseteq> B"
    and c: "source.coeffs_on c A" and d: "source.coeffs_on d A'"
    and eq: "source.lincomb c A = source.lincomb d A'"
  shows "tsum c A = tsum d A'"
proof -
  define c' where "c' = (\<lambda>u. if u \<in> A then c u else \<zero>)"
  define d' where "d' = (\<lambda>u. if u \<in> A' then d u else \<zero>)"
  have finU: "finite (A \<union> A')" using A(1) A'(1) by simp
  have UB: "A \<union> A' \<subseteq> B" using A(2) A'(2) by blast
  have c'R: "source.coeffs_on c' (A \<union> A')"
    by (rule source.coeffs_onI) (use source.coeffs_onD[OF c] in \<open>simp add: c'_def\<close>)
  have d'R: "source.coeffs_on d' (A \<union> A')"
    by (rule source.coeffs_onI) (use source.coeffs_onD[OF d] in \<open>simp add: d'_def\<close>)
  \<comment> \<open>The extended coefficient functions agree, by uniqueness of coordinates.\<close>
  have agree: "\<And>v. c' v = d' v"
    unfolding c'_def d'_def
    by (rule source.lin_indep_lincomb_unique_gen[OF B_lin_indep A A' c d eq])
  \<comment> \<open>Each twisted sum is unchanged by padding to the union.\<close>
  have "tsum c A = tsum c' A"
    by (rule tsum_cong[OF A(2)]) (use c in \<open>auto simp: c'_def source.coeffs_on_def\<close>)
  also have "\<dots> = tsum c' (A \<union> A')"
  proof (rule tsum_mono_zero[OF finU Un_upper1 UB])
    show "\<And>v. v \<in> A \<union> A' \<setminus> A \<Longrightarrow> c' v = \<zero>" unfolding c'_def by simp
    show "source.coeffs_on c' (A \<union> A')" by (rule c'R)
  qed
  also have "\<dots> = tsum d' (A \<union> A')"
    by (rule tsum_cong[OF UB]) (use agree d'R in auto)
  also have "\<dots> = tsum d' A'"
  proof (rule sym, rule tsum_mono_zero[OF finU Un_upper2 UB])
    show "\<And>v. v \<in> A \<union> A' \<setminus> A' \<Longrightarrow> d' v = \<zero>" unfolding d'_def by simp
    show "source.coeffs_on d' (A \<union> A')" by (rule d'R)
  qed
  also have "\<dots> = tsum d A'"
    by (rule tsum_cong[OF A'(2)]) (use d in \<open>auto simp: d'_def source.coeffs_on_def\<close>)
  finally show ?thesis .
qed


subsection \<open>The extension\<close>

text \<open>The extension of @{term f} to all of @{term M}: read off any representation over the basis and
  take the twisted sum.  Made extensional on @{term M} so that it satisfies the @{term map}
  obligation of @{locale module_homomorphism} directly.\<close>
definition free_ext :: "'b \<Rightarrow> 'c"
  where "free_ext =
    (\<lambda>x \<in> M. THE y. \<exists>A c. finite A \<and> A \<subseteq> B \<and> source.coeffs_on c A
                          \<and> x = source.lincomb c A \<and> y = tsum c A)"

text \<open>On a representation, the extension is the twisted sum.\<close>
lemma free_ext_repr:
  assumes A: "finite A" "A \<subseteq> B" and c: "source.coeffs_on c A" and x: "x = source.lincomb c A"
  shows "free_ext x = tsum c A"
proof -
  have xM: "x \<in> M"
    using x A c source.lincomb_closed[of A c] B_subset source.coeffs_onD by blast
  have "(THE y. \<exists>A' c'. finite A' \<and> A' \<subseteq> B \<and> source.coeffs_on c' A'
                        \<and> x = source.lincomb c' A' \<and> y = tsum c' A') = tsum c A"
  proof (rule the_equality)
    show "\<exists>A' c'. finite A' \<and> A' \<subseteq> B \<and> source.coeffs_on c' A'
                  \<and> x = source.lincomb c' A' \<and> tsum c A = tsum c' A'"
      using A c x by blast
  next
    fix y assume "\<exists>A' c'. finite A' \<and> A' \<subseteq> B \<and> source.coeffs_on c' A'
                          \<and> x = source.lincomb c' A' \<and> y = tsum c' A'"
    then obtain A' c' where y: "finite A'" "A' \<subseteq> B" "source.coeffs_on c' A'"
      "x = source.lincomb c' A'" "y = tsum c' A'" by blast
    have "source.lincomb c A = source.lincomb c' A'" using x y(4) by simp
    then have "tsum c A = tsum c' A'"
      by (rule tsum_well_defined[OF A y(1,2) c y(3)])
    then show "y = tsum c A" using y(5) by simp
  qed
  then show ?thesis unfolding free_ext_def using xM by simp
qed

text \<open>The extension agrees with @{term f} on the basis: a basis element is its own singleton
  combination with coefficient @{term \<one>}.\<close>
theorem free_ext_extends:
  assumes v: "v \<in> B" shows "free_ext v = f v"
proof -
  have vM: "v \<in> M" using v B_subset by blast
  have c1: "source.coeffs_on (\<lambda>_. \<one>) {v}" by (rule source.coeffs_onI) simp
  have "source.lincomb (\<lambda>_. \<one>) {v} = v"
    using vM by (simp add: source.scale_one)
  then have "free_ext v = tsum (\<lambda>_. \<one>) {v}"
    using v c1 by (auto intro: free_ext_repr[where A = "{v}"])
  also have "\<dots> = \<one> \<odot>\<^sub>2 f v"
    unfolding tsum_def using f_closed[OF v]
    by (simp add: target.scale_one)
  also have "\<dots> = f v" using f_closed[OF v] by (rule target.scale_one)
  finally show ?thesis .
qed

text \<open>\<^emph>\<open>Existence.\<close>  The extension is a module homomorphism.\<close>
theorem free_ext_hom:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) free_ext"
proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)" by (rule source.Module_axioms)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2)" by (rule target.Module_axioms)
  show "free_ext \<in> M \<rightarrow>\<^sub>E M'"
  proof (rule PiE_I)
    fix x assume x: "x \<in> M"
    obtain A c where A: "finite A" "A \<subseteq> B" "source.coeffs_on c A" "x = source.lincomb c A"
      by (rule source.module_basis_repr_exists[OF basis x])
    then show "free_ext x \<in> M'" using free_ext_repr[OF A] by simp
  qed (simp add: free_ext_def)
next
  fix x y assume x: "x \<in> M" and y: "y \<in> M"
  obtain A c where A: "finite A" "A \<subseteq> B" "source.coeffs_on c A" "x = source.lincomb c A"
    by (rule source.module_basis_repr_exists[OF basis x])
  obtain A' d where A': "finite A'" "A' \<subseteq> B" "source.coeffs_on d A'" "y = source.lincomb d A'"
    by (rule source.module_basis_repr_exists[OF basis y])
  \<comment> \<open>Pad both representations to the union, add coefficients there, and use additivity of the
    twisted sum.\<close>
  define c' where "c' = (\<lambda>u. if u \<in> A then c u else \<zero>)"
  define d' where "d' = (\<lambda>u. if u \<in> A' then d u else \<zero>)"
  have finU: "finite (A \<union> A')" using A(1) A'(1) by simp
  have UB: "A \<union> A' \<subseteq> B" using A(2) A'(2) by blast
  have UM: "A \<union> A' \<subseteq> M" using UB B_subset by blast
  have c'R: "source.coeffs_on c' (A \<union> A')"
    by (rule source.coeffs_onI) (use source.coeffs_onD[OF A(3)] in \<open>simp add: c'_def\<close>)
  have d'R: "source.coeffs_on d' (A \<union> A')"
    by (rule source.coeffs_onI) (use source.coeffs_onD[OF A'(3)] in \<open>simp add: d'_def\<close>)
  \<comment> \<open>Source side: the padded combinations are unchanged, so their sum represents \<open>x \<oplus> y\<close>.\<close>
  have cU: "source.lincomb c' (A \<union> A') = x"
  proof -
    have "source.lincomb c' A = source.lincomb c' (A \<union> A')"
      by (rule source.lincomb_mono_zero[OF finU Un_upper1 UM])
         (use c'R in \<open>simp_all add: c'_def\<close>)
    moreover have "source.lincomb c' A = source.lincomb c A"
      by (rule source.lincomb_cong)
         (use A(2) A(3) B_subset in \<open>auto simp: c'_def\<close>)
    ultimately show ?thesis using A(4) by simp
  qed
  have dU: "source.lincomb d' (A \<union> A') = y"
  proof -
    have "source.lincomb d' A' = source.lincomb d' (A \<union> A')"
      by (rule source.lincomb_mono_zero[OF finU Un_upper2 UM])
         (use d'R in \<open>simp_all add: d'_def\<close>)
    moreover have "source.lincomb d' A' = source.lincomb d A'"
      by (rule source.lincomb_cong)
         (use A'(2) A'(3) B_subset in \<open>auto simp: d'_def\<close>)
    ultimately show ?thesis using A'(4) by simp
  qed
  have sumR: "source.coeffs_on (\<lambda>u. c' u + d' u) (A \<union> A')"
    by (rule source.coeffs_onI)
       (use source.coeffs_onD[OF c'R] source.coeffs_onD[OF d'R] in simp)
  have "x \<oplus> y = source.lincomb (\<lambda>u. c' u + d' u) (A \<union> A')"
    using source.lincomb_add_coeffs[OF UM c'R d'R] cU dU by simp
  then have "free_ext (x \<oplus> y) = tsum (\<lambda>u. c' u + d' u) (A \<union> A')"
    by (rule free_ext_repr[OF finU UB sumR])
  also have "\<dots> = tsum c' (A \<union> A') \<oplus>\<^sub>2 tsum d' (A \<union> A')"
    by (rule tsum_add_coeffs[OF UB c'R d'R])
  also have "tsum c' (A \<union> A') = free_ext x"
    using free_ext_repr[OF finU UB c'R cU[symmetric]] by simp
  also have "tsum d' (A \<union> A') = free_ext y"
    using free_ext_repr[OF finU UB d'R dU[symmetric]] by simp
  finally show "free_ext (x \<oplus> y) = free_ext x \<oplus>\<^sub>2 free_ext y" .
next
  fix a x assume a: "a \<in> R" and x: "x \<in> M"
  obtain A c where A: "finite A" "A \<subseteq> B" "source.coeffs_on c A" "x = source.lincomb c A"
    by (rule source.module_basis_repr_exists[OF basis x])
  have AM: "A \<subseteq> M" using A(2) B_subset by blast
  have scR: "source.coeffs_on (\<lambda>u. a \<cdot> c u) A"
    by (rule source.coeffs_onI) (use a source.coeffs_onD[OF A(3)] in simp)
  \<comment> \<open>Scaling a combination scales its coefficients (the computation inside
    \<open>span_scale_closed\<close>, reused here).\<close>
  have "a \<odot> x = source.lincomb (\<lambda>u. a \<cdot> c u) A"
  proof -
    have pi: "(\<lambda>v. c v \<odot> v) \<in> A \<rightarrow> M"
      using AM source.coeffs_onD[OF A(3)] by (auto intro!: source.scale_closed)
    have "a \<odot> source.lincomb c A
        = source.madd.fincomp (\<lambda>v. a \<odot> (c v \<odot> v)) A"
      unfolding source.lincomb_def using a pi by (rule source.scale_fincomp)
    also have "\<dots> = source.madd.fincomp (\<lambda>v. (a \<cdot> c v) \<odot> v) A"
    proof (rule source.madd.fincomp_cong')
      show "A = A" ..
      show "(\<lambda>v. (a \<cdot> c v) \<odot> v) \<in> A \<rightarrow> M"
        using AM a source.coeffs_onD[OF A(3)] by (auto intro!: source.scale_closed)
      fix v assume v: "v \<in> A"
      then have vM: "v \<in> M" and cv: "c v \<in> R"
        using AM source.coeffs_onD[OF A(3)] by auto
      show "a \<odot> (c v \<odot> v) = (a \<cdot> c v) \<odot> v" by (rule source.scale_scale[OF a cv vM, symmetric])
    qed
    finally show ?thesis
      by (simp add: A(4) source.lincomb_def) 
  qed
  then have "free_ext (a \<odot> x) = tsum (\<lambda>u. a \<cdot> c u) A"
    by (rule free_ext_repr[OF A(1,2) scR])
  also have "\<dots> = a \<odot>\<^sub>2 tsum c A" by (rule tsum_scale_coeffs[OF A(2) a A(3)])
  also have "tsum c A = free_ext x" using free_ext_repr[OF A] by simp
  finally show "free_ext (a \<odot> x) = a \<odot>\<^sub>2 free_ext x" .
qed

text \<open>\<^emph>\<open>Uniqueness.\<close>  Any homomorphism agreeing with @{term f} on the basis equals the extension:
  two homomorphisms agreeing on a spanning set agree everywhere, because each element is a finite
  combination of basis elements and both maps commute with the combination.\<close>
theorem free_ext_unique:
  assumes \<eta>: "module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
    and agree: "\<And>v. v \<in> B \<Longrightarrow> \<eta> v = f v"
    and x: "x \<in> M"
  shows "\<eta> x = free_ext x"
proof -
  interpret H: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one> M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<eta>
    by (rule \<eta>)
  obtain A c where A: "finite A" "A \<subseteq> B" "source.coeffs_on c A" "x = source.lincomb c A"
    by (rule source.module_basis_repr_exists[OF basis x])
  have AM: "A \<subseteq> M" using A(2) B_subset by blast
  \<comment> \<open>A homomorphism carries a linear combination to the twisted sum of the images.\<close>
  have "\<eta> (source.lincomb c A) = target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) A"
    by (rule H.hom_lincomb[OF A(1) AM]) (use A(3) in \<open>auto intro: source.coeffs_onD\<close>)
  \<comment> \<open>On the basis the images agree with @{term f}, so that sum is exactly the twisted sum.\<close>
  also have "target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) A = tsum c A"
    unfolding tsum_def
  proof (rule target.madd.fincomp_cong')
    show "A = A" ..
    show "(\<lambda>v. c v \<odot>\<^sub>2 f v) \<in> A \<rightarrow> M'" by (rule tsum_Pi[OF A(2) A(3)])
    show "\<And>v. v \<in> A \<Longrightarrow> c v \<odot>\<^sub>2 \<eta> v = c v \<odot>\<^sub>2 f v" using agree A(2) by auto
  qed
  finally show ?thesis using A(4) free_ext_repr[OF A] by simp
qed

text \<open>\<^emph>\<open>The universal property.\<close>  There is exactly one homomorphism extending @{term f}.\<close>
theorem free_module_universal:
  "\<exists>!\<eta>. module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
        \<and> (\<forall>v \<in> B. \<eta> v = f v) \<and> \<eta> \<in> M \<rightarrow>\<^sub>E M'"
proof
  show "module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) free_ext
      \<and> (\<forall>v \<in> B. free_ext v = f v) \<and> free_ext \<in> M \<rightarrow>\<^sub>E M'"
  proof (intro conjI ballI free_ext_hom)
    show "\<And>v. v \<in> B \<Longrightarrow> free_ext v = f v" by (rule free_ext_extends)
    show "free_ext \<in> M \<rightarrow>\<^sub>E M'"
      using module_homomorphism.axioms(3)[OF free_ext_hom] map.graph by blast
  qed
next
  fix \<eta>
  assume "module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
          \<and> (\<forall>v \<in> B. \<eta> v = f v) \<and> \<eta> \<in> M \<rightarrow>\<^sub>E M'"
  then have H: "module_homomorphism R (+) (\<cdot>) \<zero> \<one> M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
    and ag: "\<And>v. v \<in> B \<Longrightarrow> \<eta> v = f v" and ext: "\<eta> \<in> M \<rightarrow>\<^sub>E M'" by auto
  show "\<eta> = free_ext"
  proof (rule extensionalityI)
    show "\<eta> \<in> extensional M" using ext by (simp add: PiE_iff)
    show "free_ext \<in> extensional M" unfolding free_ext_def by simp
    fix x assume "x \<in> M"
    then show "\<eta> x = free_ext x"
      using H ag free_ext_unique by blast
  qed
qed

end (* free_module_ext *)

end
