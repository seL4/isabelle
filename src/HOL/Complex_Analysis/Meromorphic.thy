(*
  Authors:    Manuel Eberl, University of Innsbruck
              Wenda Li, University of Edinburgh
*)
theory Meromorphic imports
  Laurent_Convergence
  Cauchy_Integral_Formula
  "HOL-Analysis.Sparse_In"
begin

subsection \<open>Remove singular points\<close>

text \<open>
  This function takes a complex function and returns a version of it where all removable
  singularities have been removed and all other singularities (to be more precise,
  unremovable discontinuities) are set to 0.

  This is very useful since it is sometimes difficult to avoid introducing removable singularities.
  For example, consider the meromorphic functions $f(z) = z$ and $g(z) = 1/z$.
  Then a mathematician would write $f(z)g(z) = 1$, but in Isabelle of course this is not so.

  Using the \<open>remove_sings\<close> function, we indeed have \<open>remove_sings (\<lambda>z. f z * g z) = (\<lambda>_. 1)\<close>.
\<close>
definition%important remove_sings :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "remove_sings f z = (if \<exists>c. f \<midarrow>z\<rightarrow> c then Lim (at z) f else 0)"

lemma remove_sings_eqI [intro]:
  assumes "f \<midarrow>z\<rightarrow> c"
  shows   "remove_sings f z = c"
  using assms unfolding remove_sings_def by (auto simp: tendsto_Lim)

lemma remove_sings_at_analytic [simp]:
  assumes "f analytic_on {z}"
  shows   "remove_sings f z = f z"
  using assms by (intro remove_sings_eqI) (simp add: analytic_at_imp_isCont isContD)

lemma remove_sings_at_pole [simp]:
  assumes "is_pole f z"
  shows   "remove_sings f z = 0"
  using assms unfolding remove_sings_def is_pole_def
  by (meson at_neq_bot not_tendsto_and_filterlim_at_infinity)

lemma eventually_remove_sings_eq_at:
  assumes "isolated_singularity_at f z"
  shows   "eventually (\<lambda>w. remove_sings f w = f w) (at z)"
proof -
  from assms obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    by (auto simp: isolated_singularity_at_def)
  hence *: "f analytic_on {w}" if "w \<in> ball z r - {z}" for w
    using r that by (auto intro: analytic_on_subset)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r by (intro eventually_at_in_open) auto
  thus ?thesis
    by eventually_elim (auto simp: remove_sings_at_analytic * )
qed

lemma eventually_remove_sings_eq_nhds:
  assumes "f analytic_on {z}"
  shows   "eventually (\<lambda>w. remove_sings f w = f w) (nhds z)"
proof -
  from assms obtain A where A: "open A" "z \<in> A" "f holomorphic_on A"
    by (auto simp: analytic_at)
  have "eventually (\<lambda>z. z \<in> A) (nhds z)"
    by (intro eventually_nhds_in_open A)
  thus ?thesis
  proof eventually_elim
    case (elim w)
    from elim have "f analytic_on {w}"
      using A analytic_at by blast
    thus ?case by auto
  qed
qed

lemma remove_sings_compose:
  assumes "filtermap g (at z) = at z'"
  shows   "remove_sings (f \<circ> g) z = remove_sings f z'"
proof (cases "\<exists>c. f \<midarrow>z'\<rightarrow> c")
  case True
  then obtain c where c: "f \<midarrow>z'\<rightarrow> c"
    by auto
  from c have "remove_sings f z' = c"
    by blast
  moreover from c have "remove_sings (f \<circ> g) z = c"
    using c by (intro remove_sings_eqI) (auto simp: filterlim_def filtermap_compose assms)
  ultimately show ?thesis
    by simp
next
  case False
  hence "\<not>(\<exists>c. (f \<circ> g) \<midarrow>z\<rightarrow> c)"
    by (auto simp: filterlim_def filtermap_compose assms)
  with False show ?thesis
    by (auto simp: remove_sings_def)
qed

lemma remove_sings_cong:
  assumes "eventually (\<lambda>x. f x = g x) (at z)" "z = z'"
  shows   "remove_sings f z = remove_sings g z'"
proof (cases "\<exists>c. f \<midarrow>z\<rightarrow> c")
  case True
  then obtain c where c: "f \<midarrow>z\<rightarrow> c" by blast
  hence "remove_sings f z = c"
    by blast
  moreover have "f \<midarrow>z\<rightarrow> c \<longleftrightarrow> g \<midarrow>z'\<rightarrow> c"
    using assms by (intro filterlim_cong refl) auto
  with c have "remove_sings g z' = c"
    by (intro remove_sings_eqI) auto
  ultimately show ?thesis
    by simp
next
  case False
  have "f \<midarrow>z\<rightarrow> c \<longleftrightarrow> g \<midarrow>z'\<rightarrow> c" for c
    using assms by (intro filterlim_cong) auto
  with False show ?thesis
    by (auto simp: remove_sings_def)
qed


lemma deriv_remove_sings_at_analytic [simp]:
  assumes "f analytic_on {z}"
  shows   "deriv (remove_sings f) z = deriv f z"
  apply (rule deriv_cong_ev)
  apply (rule eventually_remove_sings_eq_nhds)
  using assms by auto

lemma isolated_singularity_at_remove_sings [simp, intro]:
  assumes "isolated_singularity_at f z"
  shows   "isolated_singularity_at (remove_sings f) z"
  using isolated_singularity_at_cong[OF eventually_remove_sings_eq_at[OF assms] refl] assms
  by simp

lemma not_essential_remove_sings_iff [simp]:
  assumes "isolated_singularity_at f z"
  shows   "not_essential (remove_sings f) z \<longleftrightarrow> not_essential f z"
  using not_essential_cong[OF eventually_remove_sings_eq_at[OF assms(1)] refl]
  by simp

lemma not_essential_remove_sings [intro]:
  assumes "isolated_singularity_at f z" "not_essential f z"
  shows   "not_essential (remove_sings f) z"
  by (subst not_essential_remove_sings_iff) (use assms in auto)

lemma
  assumes "isolated_singularity_at f z"
  shows is_pole_remove_sings_iff [simp]:
        "is_pole (remove_sings f) z \<longleftrightarrow> is_pole f z"
  and zorder_remove_sings [simp]:
        "zorder (remove_sings f) z = zorder f z"
  and zor_poly_remove_sings [simp]:
        "zor_poly (remove_sings f) z = zor_poly f z"
  and has_laurent_expansion_remove_sings_iff [simp]:
        "(\<lambda>w. remove_sings f (z + w)) has_laurent_expansion F \<longleftrightarrow>
         (\<lambda>w. f (z + w)) has_laurent_expansion F"
  and tendsto_remove_sings_iff [simp]:
        "remove_sings f \<midarrow>z\<rightarrow> c \<longleftrightarrow> f \<midarrow>z\<rightarrow> c"
  by (intro is_pole_cong eventually_remove_sings_eq_at refl zorder_cong
            zor_poly_cong has_laurent_expansion_cong' tendsto_cong assms)+

lemma get_all_poles_from_remove_sings:
  fixes f:: "complex \<Rightarrow> complex"
  defines "ff\<equiv>remove_sings f"
  assumes f_holo:"f holomorphic_on s - pts" and "finite pts" 
    "pts\<subseteq>s" "open s" and not_ess:"\<forall>x\<in>pts. not_essential f x"
  obtains pts' where 
    "pts' \<subseteq> pts" "finite pts'" "ff holomorphic_on s - pts'" "\<forall>x\<in>pts'. is_pole ff x"
proof -
  define pts' where "pts' = {x\<in>pts. is_pole f x}"

  have "pts' \<subseteq> pts" unfolding pts'_def by auto
  then have "finite pts'" using \<open>finite pts\<close> 
    using rev_finite_subset by blast
  then have "open (s - pts')" using \<open>open s\<close>
    by (simp add: finite_imp_closed open_Diff)

  have isolated:"isolated_singularity_at f z" if "z\<in>pts" for z
  proof (rule isolated_singularity_at_holomorphic)
    show "f holomorphic_on (s-(pts-{z})) - {z}" 
      by (metis Diff_insert f_holo insert_Diff that)
    show " open (s - (pts - {z}))" 
      by (meson assms(3) assms(5) finite_Diff finite_imp_closed open_Diff)
    show "z \<in> s - (pts - {z})" 
      using assms(4) that by auto
  qed

  have "ff holomorphic_on s - pts'"
  proof (rule no_isolated_singularity')
    show "(ff \<longlongrightarrow> ff z) (at z within s - pts')" if "z \<in> pts-pts'" for z
    proof -
      have "at z within s - pts' = at z"
        apply (rule at_within_open)
        using \<open>open (s - pts')\<close> that \<open>pts\<subseteq>s\<close>  by auto
      moreover have "ff \<midarrow>z\<rightarrow> ff z"
        unfolding ff_def
      proof (subst tendsto_remove_sings_iff)
        show "isolated_singularity_at f z"
          apply (rule isolated)
          using that by auto
        have "not_essential f z" 
          using not_ess that by auto
        moreover have "\<not>is_pole f z"
          using that unfolding pts'_def by auto
        ultimately have "\<exists>c. f \<midarrow>z\<rightarrow> c" 
          unfolding not_essential_def by auto
        then show "f \<midarrow>z\<rightarrow> remove_sings f z"
          using remove_sings_eqI by blast
      qed
      ultimately show ?thesis by auto
    qed
    have "ff holomorphic_on s - pts"
      using f_holo 
    proof (elim holomorphic_transform)
      fix x assume "x \<in> s - pts"
      then have "f analytic_on {x}" 
        using assms(3) assms(5) f_holo
        by (meson finite_imp_closed 
            holomorphic_on_imp_analytic_at open_Diff) 
      from remove_sings_at_analytic[OF this]
      show "f x = ff x" unfolding ff_def by auto 
    qed
    then show "ff holomorphic_on s - pts' - (pts - pts')"
      apply (elim holomorphic_on_subset)
      by blast
    show "open (s - pts')" 
      by (simp add: \<open>open (s - pts')\<close>)
    show "finite (pts - pts')" 
      by (simp add: assms(3))
  qed
  moreover have "\<forall>x\<in>pts'. is_pole ff x"
    unfolding pts'_def 
    using ff_def is_pole_remove_sings_iff isolated by blast
  moreover note \<open>pts' \<subseteq> pts\<close> \<open>finite pts'\<close> 
  ultimately show ?thesis using that by auto
qed

lemma remove_sings_eq_0_iff:
  assumes "not_essential f w"
  shows "remove_sings f w = 0 \<longleftrightarrow> is_pole f w \<or> f \<midarrow>w\<rightarrow> 0"
proof (cases "is_pole f w")
  case False
  then obtain c where c:"f \<midarrow>w\<rightarrow> c"
    using \<open>not_essential f w\<close> unfolding not_essential_def by auto
  then show ?thesis 
    using False remove_sings_eqI by auto
qed simp


subsection \<open>Meromorphicity\<close>

text \<open>
  We define meromorphicity in terms of Laurent series expansions. This has the advantage of
  giving us a particularly simple definition that makes many of the lemmas below trivial because
  they reduce to similar statements about Laurent series that are already in the library.

  On open domains, this definition coincides with the usual one from the literature, namely that
  the function be holomorphic on its domain except for a set of non-essential singularities that
  is \<^emph>\<open>sparse\<close>, i.e.\ that has no limit point inside the domain.
  
  However, unlike the definitions found in the literature, our definition also makes sense for
  non-open domains: similarly to \<^const>\<open>analytic_on\<close>, we consider a function meromorphic on a
  non-open domain if it is meromorphic on some open superset of that domain.

  We will prove all of this below.
\<close>
definition%important meromorphic_on :: "(complex \<Rightarrow> complex) \<Rightarrow> complex set \<Rightarrow> bool"
  (infixl \<open>(meromorphic'_on)\<close> 50) where
  "f meromorphic_on A \<longleftrightarrow> (\<forall>z\<in>A. \<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F)"

lemma meromorphic_at_iff: "f meromorphic_on {z} \<longleftrightarrow> isolated_singularity_at f z \<and> not_essential f z"
  unfolding meromorphic_on_def
  by (metis has_laurent_expansion_isolated has_laurent_expansion_not_essential
            insertI1 singletonD not_essential_has_laurent_expansion)

named_theorems meromorphic_intros

lemma meromorphic_on_empty [simp, intro]: "f meromorphic_on {}"
  by (auto simp: meromorphic_on_def)

lemma meromorphic_on_def':
  "f meromorphic_on A \<longleftrightarrow> (\<forall>z\<in>A. (\<lambda>w. f (z + w)) has_laurent_expansion laurent_expansion f z)"
  unfolding meromorphic_on_def using laurent_expansion_eqI by blast

lemma meromorphic_on_meromorphic_at: "f meromorphic_on A \<longleftrightarrow> (\<forall>x\<in>A. f meromorphic_on {x})"
  by (auto simp: meromorphic_on_def)

lemma meromorphic_on_altdef:
  "f meromorphic_on A \<longleftrightarrow> (\<forall>z\<in>A. isolated_singularity_at f z \<and> not_essential f z)"
  by (subst meromorphic_on_meromorphic_at) (auto simp: meromorphic_at_iff)

lemma meromorphic_on_cong:
  assumes "\<And>z. z \<in> A \<Longrightarrow> eventually (\<lambda>w. f w = g w) (at z)" "A = B"
  shows   "f meromorphic_on A \<longleftrightarrow> g meromorphic_on B"
  unfolding meromorphic_on_def using assms
  by (intro ball_cong refl arg_cong[of _ _ Ex] has_laurent_expansion_cong ext)
     (simp_all add: at_to_0' eventually_filtermap add_ac)

lemma meromorphic_on_subset: "f meromorphic_on A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> f meromorphic_on B"
  by (auto simp: meromorphic_on_def)

lemma meromorphic_on_Un:
  assumes "f meromorphic_on A" "f meromorphic_on B"
  shows   "f meromorphic_on (A \<union> B)"
  using assms unfolding meromorphic_on_def by blast

lemma meromorphic_on_Union:
  assumes "\<And>A. A \<in> B \<Longrightarrow> f meromorphic_on A"
  shows   "f meromorphic_on (\<Union>B)"
  using assms unfolding meromorphic_on_def by blast

lemma meromorphic_on_UN:
  assumes "\<And>x. x \<in> X \<Longrightarrow> f meromorphic_on (A x)"
  shows   "f meromorphic_on (\<Union>x\<in>X. A x)"
  using assms unfolding meromorphic_on_def by blast

lemma meromorphic_on_imp_has_laurent_expansion:
  assumes "f meromorphic_on A" "z \<in> A"
  shows   "(\<lambda>w. f (z + w)) has_laurent_expansion laurent_expansion f z"
  using assms laurent_expansion_eqI unfolding meromorphic_on_def by blast

lemma meromorphic_on_open_nhd:
  assumes "f meromorphic_on A"
  obtains B where "open B" "A \<subseteq> B" "f meromorphic_on B"
proof -
  obtain F where F: "\<And>z. z \<in> A \<Longrightarrow> (\<lambda>w. f (z + w)) has_laurent_expansion F z"
    using assms unfolding meromorphic_on_def by metis
  have "\<exists>Z. open Z \<and> z \<in> Z \<and> (\<forall>w\<in>Z-{z}. eval_fls (F z) (w - z) = f w)" if z: "z \<in> A" for z
  proof -
    obtain Z where Z: "open Z" "0 \<in> Z" "\<And>w. w \<in> Z - {0} \<Longrightarrow> eval_fls (F z) w = f (z + w)"
      using F[OF z] unfolding has_laurent_expansion_def eventually_at_topological by blast
    hence "open ((+) z ` Z)" and "z \<in> (+) z ` Z"
      using open_translation by auto
    moreover have "eval_fls (F z) (w - z) = f w" if "w \<in> (+) z ` Z - {z}" for w
      using Z(3)[of "w - z"] that by auto
    ultimately show ?thesis by blast
  qed
  then obtain Z where Z:
    "\<And>z. z \<in> A \<Longrightarrow> open (Z z) \<and> z \<in> Z z \<and> (\<forall>w\<in>Z z-{z}. eval_fls (F z) (w - z) = f w)"
    by metis

  define B where "B = (\<Union>z\<in>A. Z z \<inter> eball z (fls_conv_radius (F z)))"
  show ?thesis
  proof (rule that[of B])
    show "open B"
      using Z unfolding B_def by auto
    show "A \<subseteq> B"
      unfolding B_def using F Z by (auto simp: has_laurent_expansion_def zero_ereal_def)
    show "f meromorphic_on B"
      unfolding meromorphic_on_def
    proof
      fix z assume z: "z \<in> B"
      show "\<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F"
      proof (cases "z \<in> A")
        case True
        thus ?thesis using F by blast
      next
        case False
        then obtain z0 where z0: "z0 \<in> A" "z \<in> Z z0 - {z0}" "dist z0 z < fls_conv_radius (F z0)"
          using z False Z unfolding B_def by auto
        hence "(\<lambda>w. eval_fls (F z0) (w - z0)) analytic_on {z}"
          by (intro analytic_on_eval_fls' analytic_intros) (auto simp: dist_norm)
        also have "?this \<longleftrightarrow> f analytic_on {z}"
        proof (intro analytic_at_cong refl)
          have "eventually (\<lambda>w. w \<in> Z z0 - {z0}) (nhds z)"
            using Z[of z0] z0 by (intro eventually_nhds_in_open) auto
          thus "\<forall>\<^sub>F x in nhds z. eval_fls (F z0) (x - z0) = f x"
            by eventually_elim (use Z[of z0] z0 in auto)
        qed
        finally show ?thesis
          using analytic_at_imp_has_fps_expansion has_fps_expansion_to_laurent by blast
      qed
    qed
  qed
qed

lemma meromorphic_on_not_essential:
  assumes "f meromorphic_on {z}"
  shows   "not_essential f z"
  using assms has_laurent_expansion_not_essential unfolding meromorphic_on_def by blast

lemma meromorphic_on_isolated_singularity:
  assumes "f meromorphic_on {z}"
  shows   "isolated_singularity_at f z"
  using assms has_laurent_expansion_isolated unfolding meromorphic_on_def by blast

lemma meromorphic_on_imp_not_islimpt_singularities:
  assumes "f meromorphic_on A" "z \<in> A"
  shows   "\<not>z islimpt {w. \<not>f analytic_on {w}}"
proof -
  obtain B where B: "open B" "A \<subseteq> B" "f meromorphic_on B"
    using assms meromorphic_on_open_nhd by blast
  obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    using B assms(2) unfolding meromorphic_on_def by blast
  from F have "isolated_singularity_at f z"
    using has_laurent_expansion_isolated assms(2) by blast
  then obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    unfolding isolated_singularity_at_def by blast
  have "f analytic_on {w}" if "w \<in> ball z r - {z}" for w
    by (rule analytic_on_subset[OF r(2)]) (use that in auto)
  hence "eventually (\<lambda>w. f analytic_on {w}) (at z)"
    using eventually_at_in_open[of "ball z r" z] \<open>r > 0\<close> by (auto elim!: eventually_mono)
  thus "\<not>z islimpt {w. \<not>f analytic_on {w}}"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
qed

lemma meromorphic_on_imp_sparse_singularities:
  assumes "f meromorphic_on A"
  shows   "{w. \<not>f analytic_on {w}} sparse_in A"
  by (metis assms meromorphic_on_imp_not_islimpt_singularities 
        meromorphic_on_open_nhd sparse_in_open sparse_in_subset)

lemma meromorphic_on_imp_sparse_singularities':
  assumes "f meromorphic_on A"
  shows   "{w\<in>A. \<not>f analytic_on {w}} sparse_in A"
  using meromorphic_on_imp_sparse_singularities[OF assms]
  by (rule sparse_in_subset2) auto

lemma meromorphic_onE:
  assumes "f meromorphic_on A"
  obtains pts where "pts \<subseteq> A" "pts sparse_in A" "f analytic_on A - pts"
    "\<And>z. z \<in> A \<Longrightarrow> not_essential f z" "\<And>z. z \<in> A \<Longrightarrow> isolated_singularity_at f z"
proof (rule that)
  show "{z \<in> A. \<not> f analytic_on {z}} sparse_in A"
    using assms by (rule meromorphic_on_imp_sparse_singularities')
  show "f analytic_on A - {z \<in> A. \<not> f analytic_on {z}}"
    by (subst analytic_on_analytic_at) auto
qed (use assms in \<open>auto intro: meromorphic_on_isolated_singularity meromorphic_on_not_essential meromorphic_on_subset\<close>)

lemma meromorphic_onI_weak:
  assumes "f analytic_on A - pts" "\<And>z. z \<in> pts \<Longrightarrow> not_essential f z" "pts sparse_in A"
          "pts \<inter> frontier A = {}"
  shows   "f meromorphic_on A"
  unfolding meromorphic_on_def
proof
  fix z assume z: "z \<in> A"                                    
  show "(\<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F)"
  proof (cases "z \<in> pts")
    case False
    have "f analytic_on {z}"
      using assms(1) by (rule analytic_on_subset) (use False z in auto)
    thus ?thesis
      using isolated_singularity_at_analytic not_essential_analytic 
            not_essential_has_laurent_expansion by blast
  next
    case True
    show ?thesis
    proof (rule exI, rule not_essential_has_laurent_expansion)
      show "not_essential f z"
        using assms(2) True by blast
    next
      show "isolated_singularity_at f z"
      proof (rule isolated_singularity_at_holomorphic)
        show "open (interior A - (pts - {z}))"
        proof (rule open_diff_sparse_pts)
          show "pts - {z} sparse_in interior A"
            using sparse_in_subset sparse_in_subset2 assms interior_subset Diff_subset by metis
        qed auto
      next
        have "f analytic_on interior A - (pts - {z}) - {z}"
          using assms(1) by (rule analytic_on_subset) (use interior_subset in blast)
        thus "f holomorphic_on interior A - (pts - {z}) - {z}"
          by (rule analytic_imp_holomorphic)
      next
        from assms(4) and True have "z \<in> interior A"
          unfolding frontier_def using closure_subset z by blast
        thus "z \<in> interior A - (pts - {z})"
          by blast
      qed
    qed
  qed
qed

lemma meromorphic_onI_open:
  assumes "open A" "f analytic_on A - pts" "\<And>z. z \<in> pts \<Longrightarrow> not_essential f z"
  assumes "\<And>z. z \<in> A \<Longrightarrow> \<not>z islimpt pts \<inter> A"
  shows   "f meromorphic_on A"
proof (rule meromorphic_onI_weak)
  have *: "A - pts \<inter> A = A - pts"
    by blast
  show "f analytic_on A - pts \<inter> A"
    unfolding * by fact
  show "pts \<inter> A sparse_in A"
    using assms(1,4) by (subst sparse_in_open) auto
  show "not_essential f z" if "z \<in> pts \<inter> A" for z
    using assms(3) that by blast
  show "pts \<inter> A \<inter> frontier A = {}"
    using \<open>open A\<close> frontier_disjoint_eq by blast
qed

lemma meromorphic_at_isCont_imp_analytic:
  assumes "f meromorphic_on {z}" "isCont f z"
  shows   "f analytic_on {z}"
proof -
  have *: "(\<lambda>w. f (z + w)) has_laurent_expansion laurent_expansion f z"
    using assms by (auto intro: meromorphic_on_imp_has_laurent_expansion)
  from assms have "\<not>is_pole f z"
    using is_pole_def not_tendsto_and_filterlim_at_infinity trivial_limit_at by (metis isContD)
  with * have "fls_subdegree (laurent_expansion f z) \<ge> 0"
    using has_laurent_expansion_imp_is_pole linorder_not_le by blast
  hence **: "(\<lambda>w. eval_fls (laurent_expansion f z) (w - z)) analytic_on {z}"
    by (intro analytic_intros)+ (use * in \<open>auto simp: has_laurent_expansion_def zero_ereal_def\<close>)
  have "(\<lambda>w. eval_fls (laurent_expansion f z) (w - z)) \<midarrow>z\<rightarrow> eval_fls (laurent_expansion f z) (z - z)"
    by (intro isContD analytic_at_imp_isCont **)
  also have "?this \<longleftrightarrow> f \<midarrow>z\<rightarrow> eval_fls (laurent_expansion f z) (z - z)"
    by (intro filterlim_cong refl)
       (use * in \<open>auto simp: has_laurent_expansion_def at_to_0' eventually_filtermap add_ac\<close>)
  finally have "f \<midarrow>z\<rightarrow> eval_fls (laurent_expansion f z) 0"
    by simp
  moreover from assms have "f \<midarrow>z\<rightarrow> f z"
    by (auto intro: isContD)
  ultimately have ***: "eval_fls (laurent_expansion f z) 0 = f z"
    by (rule LIM_unique)

  have "eventually (\<lambda>w. f w = eval_fls (laurent_expansion f z) (w - z)) (at z)"
    using * by (simp add: has_laurent_expansion_def at_to_0' eventually_filtermap add_ac eq_commute)
  hence "eventually (\<lambda>w. f w = eval_fls (laurent_expansion f z) (w - z)) (nhds z)"
    unfolding eventually_at_filter by eventually_elim (use *** in auto)
  hence "f analytic_on {z} \<longleftrightarrow> (\<lambda>w. eval_fls (laurent_expansion f z) (w - z)) analytic_on {z}"
    by (intro analytic_at_cong refl)
  with ** show ?thesis
    by simp
qed

lemma analytic_on_imp_meromorphic_on:
  assumes "f analytic_on A"
  shows   "f meromorphic_on A"
  by (rule meromorphic_onI_weak[of _ _ "{}"]) (use assms in auto)

lemma meromorphic_on_compose:
  assumes "g meromorphic_on A" "f analytic_on B" "f ` B \<subseteq> A"
  shows   "(\<lambda>w. g (f w)) meromorphic_on B"
  unfolding meromorphic_on_def
proof safe
  fix z assume z: "z \<in> B"
  have "f analytic_on {z}"
    using assms(2) by (rule analytic_on_subset) (use assms(3) z in auto)
  hence "(\<lambda>w. f w - f z) analytic_on {z}"
    by (intro analytic_intros)
  then obtain F where F: "(\<lambda>w. f (z + w) - f z) has_fps_expansion F"
    using analytic_at_imp_has_fps_expansion by blast

  from assms(3) and z have "f z \<in> A"
    by auto
  with assms(1) obtain G where G: "(\<lambda>w. g (f z + w)) has_laurent_expansion G"
    using z by (auto simp: meromorphic_on_def)

  have "\<exists>H. ((\<lambda>w. g (f z + w)) \<circ> (\<lambda>w. f (z + w) - f z)) has_laurent_expansion H"
  proof (cases "F = 0")
    case False
    show ?thesis
    proof (rule exI, rule has_laurent_expansion_compose)
      show "(\<lambda>w. f (z + w) - f z) has_laurent_expansion fps_to_fls F"
        using F by (rule has_laurent_expansion_fps)
      show "fps_nth F 0 = 0"
        using has_fps_expansion_imp_0_eq_fps_nth_0[OF F] by simp
    qed fact+
  next
    case True
    have "(\<lambda>w. g (f z)) has_laurent_expansion fls_const (g (f z))"
      by auto
    also have "?this \<longleftrightarrow> (\<lambda>w. ((\<lambda>w. g (f z + w)) \<circ> (\<lambda>w. f (z + w) - f z)) w) 
                           has_laurent_expansion fls_const (g (f z))"
    proof (rule has_laurent_expansion_cong, goal_cases)
      case 1
      from F and True have "eventually (\<lambda>w. f (z + w) - f z = 0) (nhds 0)"
        by (simp add: has_fps_expansion_0_iff)
      hence "eventually (\<lambda>w. f (z + w) - f z = 0) (at 0)"
        by (simp add: eventually_nhds_conv_at)
      thus ?case
        by eventually_elim auto
    qed auto
    finally show ?thesis
      by blast
  qed
  thus "\<exists>H. (\<lambda>w. g (f (z + w))) has_laurent_expansion H"
    by (simp add: o_def)
qed

lemma constant_on_imp_meromorphic_on:
  assumes "f constant_on A" "open A"
  shows "f meromorphic_on A"
  using assms analytic_on_imp_meromorphic_on 
    constant_on_imp_analytic_on 
  by blast

subsection \<open>Nice meromorphicity\<close>

text \<open>
  This is probably very non-standard, but we call a function ``nicely meromorphic'' if it is
  meromorphic and has no removable singularities. That means that the only singularities are
  poles. We furthermore require that the function return 0 at any pole, for convenience.
\<close>
definition nicely_meromorphic_on :: "(complex \<Rightarrow> complex) \<Rightarrow> complex set \<Rightarrow> bool"
    (infixl \<open>(nicely'_meromorphic'_on)\<close> 50)
    where "f nicely_meromorphic_on A \<longleftrightarrow> f meromorphic_on A 
        \<and> (\<forall>z\<in>A. (is_pole f z \<and> f z=0) \<or> f \<midarrow>z\<rightarrow> f z)"

lemma nicely_meromorphic_on_subset:
  "f nicely_meromorphic_on A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> f nicely_meromorphic_on B"
  using meromorphic_on_subset unfolding nicely_meromorphic_on_def by blast

lemma constant_on_imp_nicely_meromorphic_on:
  assumes "f constant_on A" "open A"
  shows "f nicely_meromorphic_on A"
  by (meson analytic_at_imp_isCont assms
      constant_on_imp_holomorphic_on 
      constant_on_imp_meromorphic_on 
      holomorphic_on_imp_analytic_at isCont_def 
      nicely_meromorphic_on_def)

lemma nicely_meromorphic_on_imp_analytic_at:
  assumes "f nicely_meromorphic_on A" "z \<in> A" "\<not>is_pole f z"
  shows   "f analytic_on {z}"
proof (rule meromorphic_at_isCont_imp_analytic)
  show "f meromorphic_on {z}"
    by (rule meromorphic_on_subset[of _ A]) (use assms in \<open>auto simp: nicely_meromorphic_on_def\<close>)
next
  from assms have "f \<midarrow>z\<rightarrow> f z"
    by (auto simp: nicely_meromorphic_on_def)
  thus "isCont f z"
    by (auto simp: isCont_def)
qed
  
lemma analytic_on_imp_nicely_meromorphic_on:
  "f analytic_on A \<Longrightarrow> f nicely_meromorphic_on A"
  by (meson analytic_at_imp_isCont analytic_on_analytic_at
            analytic_on_imp_meromorphic_on isContD nicely_meromorphic_on_def)

lemma remove_sings_meromorphic [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "remove_sings f meromorphic_on A"
  unfolding meromorphic_on_def
proof safe
  fix z assume z: "z \<in> A"
  show "\<exists>F. (\<lambda>w. remove_sings f (z + w)) has_laurent_expansion F"
    using assms meromorphic_on_isolated_singularity meromorphic_on_not_essential
          not_essential_has_laurent_expansion z meromorphic_on_subset by blast
qed

lemma remove_sings_nicely_meromorphic:
  assumes "f meromorphic_on A"
  shows   "remove_sings f nicely_meromorphic_on A"
proof -
  have "remove_sings f meromorphic_on A"
    by (simp add: assms remove_sings_meromorphic)
  moreover have "is_pole (remove_sings f) z 
        \<and> remove_sings f z = 0 \<or>
            remove_sings f \<midarrow>z\<rightarrow> remove_sings f z"
    if "z\<in>A" for z
  proof (cases "\<exists>c. f \<midarrow>z\<rightarrow> c")
    case True
    then have "remove_sings f \<midarrow>z\<rightarrow> remove_sings f z"
      by (metis remove_sings_eqI tendsto_remove_sings_iff
          assms meromorphic_onE that)
    then show ?thesis by simp
  next
    case False
    then have "is_pole (remove_sings f) z 
        \<and> remove_sings f z = 0"
      by (meson is_pole_remove_sings_iff remove_sings_def 
            remove_sings_eq_0_iff assms meromorphic_onE that)
    then show ?thesis by simp
  qed
  ultimately show ?thesis 
    unfolding nicely_meromorphic_on_def by simp
qed

text \<open>
  A nicely meromorphic function that frequently takes the same value in the neighbourhood of some
  point is constant.
\<close>
lemma frequently_eq_meromorphic_imp_constant:
  assumes "frequently (\<lambda>z. f z = c) (at z)"
  assumes "f nicely_meromorphic_on A" "open A" "connected A" "z \<in> A"
  shows   "\<And>w. w \<in> A \<Longrightarrow> f w = c"
proof -
  from assms(2) have mero: "f meromorphic_on A"
    by (auto simp: nicely_meromorphic_on_def)
  have sparse: "{z. is_pole f z} sparse_in A"
    using assms(2) mero
    by (meson assms(3) meromorphic_on_isolated_singularity meromorphic_on_meromorphic_at not_islimpt_poles sparse_in_open)

  have eq: "f w = c" if w: "w \<in> A" "\<not>is_pole f w" for w
  proof -
    have "f w - c = 0"
    proof (rule analytic_continuation[of "\<lambda>w. f w - c"])
      show "(\<lambda>w. f w - c) holomorphic_on {z\<in>A. \<not>is_pole f z}" using assms(2)
        by (intro holomorphic_intros)
           (metis (mono_tags, lifting) analytic_imp_holomorphic analytic_on_analytic_at 
              mem_Collect_eq nicely_meromorphic_on_imp_analytic_at)
    next
      from sparse and assms(3) have "open (A - {z. is_pole f z})"
        by (simp add: open_diff_sparse_pts)
      also have "A - {z. is_pole f z} = {z\<in>A. \<not>is_pole f z}"
        by blast
      finally show "open \<dots>" .
    next
      from sparse have "connected (A - {z. is_pole f z})"
        using assms(3,4) by (intro sparse_imp_connected) auto
      also have "A - {z. is_pole f z} = {z\<in>A. \<not>is_pole f z}"
        by blast
      finally show "connected \<dots>" .
    next
      have "eventually (\<lambda>w. w \<in> A) (at z)"
        using assms by (intro eventually_at_in_open') auto
      moreover have "eventually (\<lambda>w. \<not>is_pole f w) (at z)" using mero
        by (metis assms(5) eventually_not_pole meromorphic_onE)
      ultimately have ev: "eventually (\<lambda>w. w \<in> A \<and> \<not>is_pole f w) (at z)"
        by eventually_elim auto
      show "z islimpt {z\<in>A. \<not>is_pole f z \<and> f z = c}"
        using frequently_eventually_frequently[OF assms(1) ev]
        unfolding islimpt_conv_frequently_at by (rule frequently_elim1) auto
    next
      from assms(1) have "\<not>is_pole f z"
        by (simp add: frequently_const_imp_not_is_pole)
      with \<open>z \<in> A\<close> show "z \<in> {z \<in> A. \<not> is_pole f z}"
        by auto
    qed (use w in auto)
    thus "f w = c"
      by simp
  qed

  have not_pole: "\<not>is_pole f w" if w: "w \<in> A" for w
  proof -
    have "eventually (\<lambda>w. \<not>is_pole f w) (at w)"
      using mero by (metis eventually_not_pole meromorphic_onE that)
    moreover have "eventually (\<lambda>w. w \<in> A) (at w)"
      using w \<open>open A\<close> by (intro eventually_at_in_open')
    ultimately have "eventually (\<lambda>w. f w = c) (at w)"
      by eventually_elim (auto simp: eq)
    hence "is_pole f w \<longleftrightarrow> is_pole (\<lambda>_. c) w"
      by (intro is_pole_cong refl)
    thus ?thesis
      by simp
  qed

  show "f w = c" if w: "w \<in> A" for w
    using eq[OF w not_pole[OF w]] .
qed

subsection \<open>Closure properties and proofs for individual functions\<close>

lemma meromorphic_on_const [intro, meromorphic_intros]: "(\<lambda>_. c) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) auto

lemma meromorphic_on_id [intro, meromorphic_intros]: "(\<lambda>w. w) meromorphic_on A"
  by (auto simp: meromorphic_on_def intro!: exI laurent_expansion_intros)

lemma meromorphic_on_id' [intro, meromorphic_intros]: "id meromorphic_on A"
  by (auto simp: meromorphic_on_def intro!: exI laurent_expansion_intros)

lemma meromorphic_on_add [meromorphic_intros]:
  assumes "f meromorphic_on A" "g meromorphic_on A"
  shows   "(\<lambda>w. f w + g w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_uminus [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>w. -f w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_diff [meromorphic_intros]:
  assumes "f meromorphic_on A" "g meromorphic_on A"
  shows   "(\<lambda>w. f w - g w) meromorphic_on A"
  using meromorphic_on_add[OF assms(1) meromorphic_on_uminus[OF assms(2)]] by simp

lemma meromorphic_on_mult [meromorphic_intros]:
  assumes "f meromorphic_on A" "g meromorphic_on A"
  shows   "(\<lambda>w. f w * g w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_power [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>w. f w ^ n) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_powi [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>w. f w powi n) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_scaleR [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>w. scaleR x (f w)) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_inverse [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>w. inverse (f w)) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_divide [meromorphic_intros]:
  assumes "f meromorphic_on A" "g meromorphic_on A"
  shows   "(\<lambda>w. f w / g w) meromorphic_on A"
  using meromorphic_on_mult[OF assms(1) meromorphic_on_inverse[OF assms(2)]]
  by (simp add: field_simps)

lemma meromorphic_on_sum [meromorphic_intros]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Sum>i\<in>I. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_sum_list [meromorphic_intros]:
  assumes "\<And>i. i \<in> set fs \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Sum>i\<leftarrow>fs. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_sum_mset [meromorphic_intros]:
  assumes "\<And>i. i \<in># I \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Sum>i\<in>#I. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_prod [meromorphic_intros]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Prod>i\<in>I. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_prod_list [meromorphic_intros]:
  assumes "\<And>i. i \<in> set fs \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Prod>i\<leftarrow>fs. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_prod_mset [meromorphic_intros]:
  assumes "\<And>i. i \<in># I \<Longrightarrow> f i meromorphic_on A"
  shows   "(\<lambda>w. \<Prod>i\<in>#I. f i w) meromorphic_on A"
  unfolding meromorphic_on_def
  by (rule laurent_expansion_intros exI ballI
           assms[THEN meromorphic_on_imp_has_laurent_expansion] | assumption)+

lemma meromorphic_on_If [meromorphic_intros]:
  assumes "f meromorphic_on A" "g meromorphic_on B"
  assumes "\<And>z. z \<in> A \<Longrightarrow> z \<in> B \<Longrightarrow> f z = g z" "open A" "open B" "C \<subseteq> A \<union> B"
  shows   "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on C"
proof (rule meromorphic_on_subset)
  show "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on (A \<union> B)"
  proof (rule meromorphic_on_Un)
    have "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on A \<longleftrightarrow> f meromorphic_on A"
    proof (rule meromorphic_on_cong)
      fix z assume "z \<in> A"
      hence "eventually (\<lambda>z. z \<in> A) (at z)"
        using \<open>open A\<close> by (intro eventually_at_in_open') auto
      thus "\<forall>\<^sub>F w in at z. (if w \<in> A then f w else g w) = f w"
        by eventually_elim auto
    qed auto
    with assms(1) show "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on A"
      by blast
  next
    have "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on B \<longleftrightarrow> g meromorphic_on B"
    proof (rule meromorphic_on_cong)
      fix z assume "z \<in> B"
      hence "eventually (\<lambda>z. z \<in> B) (at z)"
        using \<open>open B\<close> by (intro eventually_at_in_open') auto
      thus "\<forall>\<^sub>F w in at z. (if w \<in> A then f w else g w) = g w"
        by eventually_elim (use assms(3) in auto)
    qed auto
    with assms(2) show "(\<lambda>z. if z \<in> A then f z else g z) meromorphic_on B"
      by blast
  qed
qed fact

lemma meromorphic_on_deriv [meromorphic_intros]:
  "f meromorphic_on A \<Longrightarrow> deriv f meromorphic_on A"
  by (metis meromorphic_on_def isolated_singularity_at_deriv meromorphic_on_isolated_singularity 
            meromorphic_on_meromorphic_at meromorphic_on_not_essential not_essential_deriv
            not_essential_has_laurent_expansion)

lemma meromorphic_on_higher_deriv [meromorphic_intros]:
  "f meromorphic_on A \<Longrightarrow> (deriv ^^ n) f meromorphic_on A"
  by (induction n) (auto intro!: meromorphic_intros)

lemma analytic_on_eval_fps [analytic_intros]:
  assumes "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < fps_conv_radius F"
  shows   "(\<lambda>w. eval_fps F (f w)) analytic_on A"
  by (rule analytic_on_compose[OF assms(1) analytic_on_eval_fps, unfolded o_def])
     (use assms(2) in auto)

lemma meromorphic_on_eval_fps [meromorphic_intros]:
  assumes "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < fps_conv_radius F"
  shows   "(\<lambda>w. eval_fps F (f w)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on analytic_intros analytic_on_eval_fps assms)+

lemma meromorphic_on_eval_fls [meromorphic_intros]:
  assumes "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < fls_conv_radius F"
  shows   "(\<lambda>w. eval_fls F (f w)) meromorphic_on A"
proof (cases "fls_conv_radius F > 0")
  case False
  with assms(2) have "A = {}"
    by (metis all_not_in_conv ereal_less(2) norm_eq_zero order.strict_trans 
              zero_ereal_def zero_less_norm_iff)
  thus ?thesis
    by auto
next
  case True
  have F: "eval_fls F has_laurent_expansion F"
    using True by (rule eval_fls_has_laurent_expansion)
  show ?thesis
  proof (rule meromorphic_on_compose[OF _ assms(1)])
    show "eval_fls F meromorphic_on eball 0 (fls_conv_radius F)"
    proof (rule meromorphic_onI_open)
      show "eval_fls F analytic_on eball 0 (fls_conv_radius F) - {0}"
        by (rule analytic_on_eval_fls) auto
      show "not_essential (eval_fls F) z" if "z \<in> {0}" for z
        using that F has_laurent_expansion_not_essential_0 by blast
    qed (auto simp: islimpt_finite)
  qed (use assms(2) in auto)
qed

lemma meromorphic_on_imp_analytic_cosparse:
  assumes "f meromorphic_on A"
  shows   "eventually (\<lambda>z. f analytic_on {z}) (cosparse A)"
  unfolding eventually_cosparse using assms meromorphic_on_imp_sparse_singularities by auto

lemma meromorphic_on_imp_not_pole_cosparse:
  assumes "f meromorphic_on A"
  shows   "eventually (\<lambda>z. \<not>is_pole f z) (cosparse A)"
proof -
  have "eventually (\<lambda>z. f analytic_on {z}) (cosparse A)"
    by (rule meromorphic_on_imp_analytic_cosparse) fact
  thus ?thesis
    by eventually_elim (blast dest: analytic_at_imp_no_pole)
qed

lemma eventually_remove_sings_eq:
  assumes "f meromorphic_on A"
  shows   "eventually (\<lambda>z. remove_sings f z = f z) (cosparse A)"
proof -
  have "eventually (\<lambda>z. f analytic_on {z}) (cosparse A)"
    using assms by (rule meromorphic_on_imp_analytic_cosparse)
  thus ?thesis
    by eventually_elim auto
qed


text \<open>
  A meromorphic function on a connected domain takes any given value either almost everywhere
  or almost nowhere.
\<close>
lemma meromorphic_imp_constant_or_avoid:
  assumes mero: "f meromorphic_on A" and A: "open A" "connected A"
  shows   "eventually (\<lambda>z. f z = c) (cosparse A) \<or> eventually (\<lambda>z. f z \<noteq> c) (cosparse A)"
proof -
  have "eventually (\<lambda>z. f z = c) (cosparse A)" if freq: "frequently (\<lambda>z. f z = c) (cosparse A)"
  proof -
  let ?f = "remove_sings f"
    have ev: "eventually (\<lambda>z. ?f z = f z) (cosparse A)"
      by (rule eventually_remove_sings_eq) fact
    have "frequently (\<lambda>z. ?f z = c) (cosparse A)"
      using frequently_eventually_frequently[OF freq ev] by (rule frequently_elim1) auto
    then obtain z0 where z0: "z0 \<in> A" "frequently (\<lambda>z. ?f z = c) (at z0)"
      using A by (auto simp: eventually_cosparse_open_eq frequently_def)
    have mero': "?f nicely_meromorphic_on A"
      using mero remove_sings_nicely_meromorphic by blast
    have eq: "?f w = c" if w: "w \<in> A" for w
      using frequently_eq_meromorphic_imp_constant[OF z0(2) mero'] A z0(1) w by blast
    have "eventually (\<lambda>z. z \<in> A) (cosparse A)"
      by (rule eventually_in_cosparse) (use A in auto)
    thus "eventually (\<lambda>z. f z = c) (cosparse A)"
      using ev by eventually_elim (use eq in auto)
  qed
  thus ?thesis
    by (auto simp: frequently_def)
qed

lemma nicely_meromorphic_imp_constant_or_avoid:
  assumes "f nicely_meromorphic_on A" "open A" "connected A"
  shows "(\<forall>x\<in>A. f x = c) \<or> (\<forall>\<^sub>\<approx>x\<in>A. f x \<noteq> c)"
proof -
  have "(\<forall>\<^sub>\<approx>x\<in>A. f x = c) \<or> (\<forall>\<^sub>\<approx>x\<in>A. f x \<noteq> c)"
    by (intro meromorphic_imp_constant_or_avoid)
       (use assms in \<open>auto simp: nicely_meromorphic_on_def\<close>)
  thus ?thesis
  proof
    assume ev: "\<forall>\<^sub>\<approx>x\<in>A. f x = c"
    have "\<forall>x\<in>A. f x = c "
    proof
      fix x assume x: "x \<in> A"
      have "not_essential f x"
        using assms x unfolding nicely_meromorphic_on_def by blast
      moreover have "is_pole f x \<longleftrightarrow> is_pole (\<lambda>_. c) x"
        by (intro is_pole_cong) (use ev x in \<open>auto simp: eventually_cosparse_open_eq assms\<close>)
      hence "\<not>is_pole f x"
        by auto
      ultimately have "f analytic_on {x}"
        using assms(1) nicely_meromorphic_on_imp_analytic_at x by blast
      hence "f \<midarrow>x\<rightarrow> f x"
        by (intro isContD analytic_at_imp_isCont)
      also have "?this \<longleftrightarrow> (\<lambda>_. c) \<midarrow>x\<rightarrow> f x"
        by (intro tendsto_cong) (use ev x in \<open>auto simp: eventually_cosparse_open_eq assms\<close>)
      finally have "(\<lambda>_. c) \<midarrow>x\<rightarrow> f x" .
      moreover have "(\<lambda>_. c) \<midarrow>x\<rightarrow> c"
        by simp
      ultimately show "f x = c"
        using LIM_unique by blast
    qed
    thus ?thesis
      by blast
  qed blast
qed

lemma nicely_meromorphic_onE:
  assumes "f nicely_meromorphic_on A"
  obtains pts where "pts \<subseteq> A" "pts sparse_in A" 
    "f analytic_on A - pts"
    "\<And>z. z \<in> pts \<Longrightarrow> is_pole f z \<and> f z=0"
proof -
  define pts where "pts = {z \<in> A. \<not> f analytic_on {z}}"
  have "pts \<subseteq> A" "pts sparse_in A" 
    using assms unfolding pts_def nicely_meromorphic_on_def
    by (auto intro:meromorphic_on_imp_sparse_singularities')
  moreover have "f analytic_on A - pts" unfolding pts_def
    by (subst analytic_on_analytic_at) auto
  moreover have "\<And>z. z \<in> pts \<Longrightarrow> is_pole f z \<and> f z=0"
    by (metis (no_types, lifting) remove_sings_eqI 
        remove_sings_eq_0_iff assms is_pole_imp_not_essential 
        mem_Collect_eq nicely_meromorphic_on_def 
        nicely_meromorphic_on_imp_analytic_at pts_def)
  ultimately show ?thesis using that by auto
qed

lemma nicely_meromorphic_onI_open:
  assumes "open A" and
    analytic:"f analytic_on A - pts" and
    pole:"\<And>x. x\<in>pts \<Longrightarrow> is_pole f x \<and> f x = 0" and 
    isolated:"\<And>x. x\<in>A \<Longrightarrow> isolated_singularity_at f x"
  shows "f nicely_meromorphic_on A"
proof -
  have "f meromorphic_on A"
  proof (rule meromorphic_onI_open)
    show "\<And>z. z \<in> pts \<Longrightarrow> not_essential f z"
      using pole unfolding not_essential_def by auto
    show "\<And>z. z \<in> A \<Longrightarrow> \<not> z islimpt pts \<inter> A"
      by (metis assms(3) assms(4) inf_commute inf_le2
            islimpt_subset mem_Collect_eq not_islimpt_poles subsetI)
  qed fact+ 
  moreover have "(\<forall>z\<in>A. (is_pole f z \<and> f z=0) \<or> f \<midarrow>z\<rightarrow> f z)"
    by (meson DiffI analytic analytic_at_imp_isCont 
        analytic_on_analytic_at assms(3) isContD)
  ultimately show ?thesis unfolding nicely_meromorphic_on_def
    by auto
qed

lemma nicely_meromorphic_without_singularities:
  assumes "f nicely_meromorphic_on A" "\<forall>z\<in>A. \<not> is_pole f z"
  shows "f analytic_on A"
  by (meson analytic_on_analytic_at assms
        nicely_meromorphic_on_imp_analytic_at)

lemma meromorphic_on_cong':
  assumes "eventually (\<lambda>z. f z = g z) (cosparse A)" "A = B"
  shows   "f meromorphic_on A \<longleftrightarrow> g meromorphic_on B"
  unfolding assms(2)[symmetric]
  by (rule meromorphic_on_cong eventually_cosparse_imp_eventually_at assms)+ auto


subsection \<open>Meromorphic functions and zorder\<close>

lemma zorder_power_int:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. f z powi n) z = n * zorder f z"
proof -
  from assms(1) obtain L where L: "(\<lambda>w. f (z + w)) has_laurent_expansion L"
    by (auto simp: meromorphic_on_def)
  from assms(2) and L have [simp]: "L \<noteq> 0"
    by (metis assms(1) has_laurent_expansion_eventually_nonzero_iff meromorphic_at_iff
          not_essential_frequently_0_imp_eventually_0 not_eventually not_frequently)
  from L have L': "(\<lambda>w. f (z + w) powi n) has_laurent_expansion L powi n"
    by (intro laurent_expansion_intros)
  have "zorder f z = fls_subdegree L"
    using L assms(2) \<open>L \<noteq> 0\<close> by (simp add: has_laurent_expansion_zorder)
  moreover have "zorder (\<lambda>z. f z powi n) z = fls_subdegree (L powi n)"
    using L' assms(2) \<open>L \<noteq> 0\<close> by (simp add: has_laurent_expansion_zorder)
  moreover have "fls_subdegree (L powi n) = n * fls_subdegree L"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma zorder_power:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. f z ^ n) z = n * zorder f z"
  using zorder_power_int[OF assms, of "int n"] by simp

lemma zorder_add1:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "zorder f z < zorder g z"
  shows   "zorder (\<lambda>z. f z + g z) z = zorder f z"
proof -
  from assms(1) obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  from assms(3) obtain G where G: "(\<lambda>w. g (z + w)) has_laurent_expansion G"
    by (auto simp: meromorphic_on_def)
  have [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by (metis assms has_laurent_expansion_eventually_nonzero_iff meromorphic_at_iff
          not_essential_frequently_0_imp_eventually_0 not_eventually not_frequently F G)+
  have *: "zorder f z = fls_subdegree F" "zorder g z = fls_subdegree G"
    using F G assms by (simp_all add: has_laurent_expansion_zorder)
  from assms * have "F \<noteq> -G"
    by auto
  hence [simp]: "F + G \<noteq> 0"
    by (simp add: add_eq_0_iff2)
  moreover have "zorder (\<lambda>z. f z + g z) z = fls_subdegree (F + G)"
    using has_laurent_expansion_zorder[OF has_laurent_expansion_add[OF F G]] \<open>F \<noteq> -G\<close> by simp
  moreover have "fls_subdegree (F + G) = fls_subdegree F"
    using assms by (simp add: * fls_subdegree_add_eq1)
  ultimately show ?thesis
    by (simp add: *)
qed

lemma zorder_add2:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "zorder f z > zorder g z"
  shows   "zorder (\<lambda>z. f z + g z) z = zorder g z"
  using zorder_add1[OF assms(3,4) assms(1,2)] assms(5-) by (simp add: add.commute)


lemma zorder_add_ge:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "frequently (\<lambda>z. f z + g z \<noteq> 0) (at z)" "zorder f z \<ge> c" "zorder g z \<ge> c"
  shows   "zorder (\<lambda>z. f z + g z) z \<ge> c"
proof -
  from assms(1) obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  from assms(3) obtain G where G: "(\<lambda>w. g (z + w)) has_laurent_expansion G"
    by (auto simp: meromorphic_on_def)
  have [simp]: "F \<noteq> 0" "G \<noteq> 0"
    using assms F G has_laurent_expansion_frequently_nonzero_iff by blast+
  have FG: "(\<lambda>w. f (z + w) + g (z + w)) has_laurent_expansion F + G"
    by (intro laurent_expansion_intros F G)
  have [simp]: "F + G \<noteq> 0"
    using assms(5) has_laurent_expansion_frequently_nonzero_iff[OF FG] by blast    

  have *: "zorder f z = fls_subdegree F" "zorder g z = fls_subdegree G"
          "zorder (\<lambda>z. f z + g z) z = fls_subdegree (F + G)"
    using F G FG has_laurent_expansion_zorder by simp_all
  moreover have "zorder (\<lambda>z. f z + g z) z = fls_subdegree (F + G)"
    using has_laurent_expansion_zorder[OF has_laurent_expansion_add[OF F G]] by simp
  moreover have "fls_subdegree (F + G) \<ge> min (fls_subdegree F) (fls_subdegree G)"
    by (intro fls_plus_subdegree) simp
  ultimately show ?thesis
    using assms(6,7) unfolding * by linarith
qed

lemma zorder_diff_ge:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "frequently (\<lambda>z. f z \<noteq> g z) (at z)" "zorder f z \<ge> c" "zorder g z \<ge> c"
  shows   "zorder (\<lambda>z. f z - g z) z \<ge> c"
proof  -
  have "(\<lambda>z. - g z) meromorphic_on {z}"
    by (auto intro: meromorphic_intros assms)
  thus ?thesis
    using zorder_add_ge[of f z "\<lambda>z. -g z" c] assms by simp
qed

lemma zorder_diff1:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "zorder f z < zorder g z"
  shows   "zorder (\<lambda>z. f z - g z) z = zorder f z"
proof -
  have "zorder (\<lambda>z. f z + (-g z)) z = zorder f z"
    by (intro zorder_add1 meromorphic_intros assms) (use assms in auto)
  thus ?thesis
    by simp
qed

lemma zorder_diff2:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  assumes "zorder f z > zorder g z"
  shows   "zorder (\<lambda>z. f z - g z) z = zorder g z"
proof -
  have "zorder (\<lambda>z. f z + (-g z)) z = zorder (\<lambda>z. -g z) z"
    by (intro zorder_add2 meromorphic_intros assms) (use assms in auto)
  thus ?thesis
    by simp
qed

lemma zorder_mult:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. f z * g z) z = zorder f z + zorder g z"
proof -
  from assms(1) obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  from assms(3) obtain G where G: "(\<lambda>w. g (z + w)) has_laurent_expansion G"
    by (auto simp: meromorphic_on_def)
  have [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by (metis assms has_laurent_expansion_eventually_nonzero_iff meromorphic_at_iff
          not_essential_frequently_0_imp_eventually_0 not_eventually not_frequently F G)+
  have *: "zorder f z = fls_subdegree F" "zorder g z = fls_subdegree G"
    using F G assms by (simp_all add: has_laurent_expansion_zorder)
  moreover have "zorder (\<lambda>z. f z * g z) z = fls_subdegree (F * G)"
    using has_laurent_expansion_zorder[OF has_laurent_expansion_mult[OF F G]] by simp
  moreover have "fls_subdegree (F * G) = fls_subdegree F + fls_subdegree G"
    using assms by simp
  ultimately show ?thesis
    by (simp add: *)
qed

lemma zorder_divide:
  assumes "f meromorphic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  assumes "g meromorphic_on {z}" "frequently (\<lambda>z. g z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. f z / g z) z = zorder f z - zorder g z"
proof -
  from assms(1) obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  from assms(3) obtain G where G: "(\<lambda>w. g (z + w)) has_laurent_expansion G"
    by (auto simp: meromorphic_on_def)
  have [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by (metis assms has_laurent_expansion_eventually_nonzero_iff meromorphic_at_iff
          not_essential_frequently_0_imp_eventually_0 not_eventually not_frequently F G)+
  have *: "zorder f z = fls_subdegree F" "zorder g z = fls_subdegree G"
    using F G assms by (simp_all add: has_laurent_expansion_zorder)
  moreover have "zorder (\<lambda>z. f z / g z) z = fls_subdegree (F / G)"
    using has_laurent_expansion_zorder[OF has_laurent_expansion_divide[OF F G]] by simp
  moreover have "fls_subdegree (F / G) = fls_subdegree F - fls_subdegree G"
    using assms by (simp add: fls_divide_subdegree)
  ultimately show ?thesis
    by (simp add: *)
qed

lemma constant_on_extend_nicely_meromorphic_on:
  assumes "f nicely_meromorphic_on B" "f constant_on A" 
  assumes "open A" "open B" "connected B" "A \<noteq> {}" "A \<subseteq> B"
  shows   "f constant_on B"
proof -
  from assms obtain c where c: "\<And>z. z \<in> A \<Longrightarrow> f z = c"
    by (auto simp: constant_on_def)
  have "eventually (\<lambda>z. z \<in> A) (cosparse A)"
    by (intro eventually_in_cosparse assms order.refl)
  hence "eventually (\<lambda>z. f z = c) (cosparse A)"
    by eventually_elim (use c in auto)
  hence freq: "frequently (\<lambda>z. f z = c) (cosparse A)"
    by (intro eventually_frequently) (use assms in auto)
  then obtain z0 where z0: "z0 \<in> A" "frequently (\<lambda>z. f z = c) (at z0)"
    using assms by (auto simp: frequently_def eventually_cosparse_open_eq)

  have "f z = c" if "z \<in> B" for z
  proof (rule frequently_eq_meromorphic_imp_constant[OF _ assms(1)])
    show "z0 \<in> B" "frequently (\<lambda>z. f z = c) (at z0)"
      using z0 assms by auto
  qed (use assms that in auto)
  thus "f constant_on B"
    by (auto simp: constant_on_def)
qed

end
