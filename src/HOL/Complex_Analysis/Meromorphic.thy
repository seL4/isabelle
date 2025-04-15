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

lemma remove_sings_analytic_on:
  assumes "isolated_singularity_at f z" "f \<midarrow>z\<rightarrow> c"
  shows   "remove_sings f analytic_on {z}"
proof -
  from assms(1) obtain A where A: "open A" "z \<in> A" "f holomorphic_on (A - {z})"
    using analytic_imp_holomorphic isolated_singularity_at_iff_analytic_nhd by auto
  have ana: "f analytic_on (A - {z})"
    by (subst analytic_on_open) (use A in auto)

  have "remove_sings f holomorphic_on A"
  proof (rule no_isolated_singularity)
    have "f holomorphic_on (A - {z})"
      by fact
    moreover have "remove_sings f holomorphic_on (A - {z}) \<longleftrightarrow> f holomorphic_on (A - {z})"
      by (intro holomorphic_cong remove_sings_at_analytic) (auto intro!: analytic_on_subset[OF ana])
    ultimately show "remove_sings f holomorphic_on (A - {z})"
      by blast
    hence "continuous_on (A-{z}) (remove_sings f)"
      by (intro holomorphic_on_imp_continuous_on)
    moreover have "isCont (remove_sings f) z"
      using assms isCont_def remove_sings_eqI tendsto_remove_sings_iff by blast
    ultimately show "continuous_on A (remove_sings f)"
      by (metis A(1) DiffI closed_singleton continuous_on_eq_continuous_at open_Diff singletonD)
  qed (use A(1) in auto)
  thus ?thesis
    using A(1,2) analytic_at by blast
qed

lemma residue_remove_sings [simp]:
  assumes "isolated_singularity_at f z"
  shows   "residue (remove_sings f) z = residue f z"
proof -
  from assms have "eventually (\<lambda>w. remove_sings f w = f w) (at z)"
    using eventually_remove_sings_eq_at by blast
  then obtain A where A: "open A" "z \<in> A" "\<And>w. w \<in> A - {z} \<Longrightarrow> remove_sings f w = f w"
    by (subst (asm) eventually_at_topological) blast
  from A(1,2) obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "cball z \<epsilon> \<subseteq> A"
    using open_contains_cball_eq by blast
  hence eq: "remove_sings f w = f w" if "w \<in> cball z \<epsilon> - {z}" for w
    using that A \<epsilon> by blast

  define P where "P = (\<lambda>f c \<epsilon>. (f has_contour_integral of_real (2 * pi) * \<i> * c) (circlepath z \<epsilon>))"
  have "P (remove_sings f) c \<delta> \<longleftrightarrow> P f c \<delta>" if "0 < \<delta>" "\<delta> < \<epsilon>" for c \<delta>
    unfolding P_def using \<open>\<epsilon> > 0\<close> that by (intro has_contour_integral_cong) (auto simp: eq)
  hence *: "(\<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P (remove_sings f) c \<epsilon>) \<longleftrightarrow> (\<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P f c \<epsilon>)" if "e \<le> \<epsilon>" for c e
    using that by force
  have **: "(\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P (remove_sings f) c \<epsilon>) \<longleftrightarrow> (\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P f c \<epsilon>)" for c
  proof
    assume "(\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P (remove_sings f) c \<epsilon>)"
    then obtain e where "e > 0" "\<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P (remove_sings f) c \<epsilon>"
      by blast
    thus "(\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P f c \<epsilon>)"
      by (intro exI[of _ "min e \<epsilon>"]) (use *[of "min e \<epsilon>" c] \<epsilon>(1) in auto)
  next
    assume "(\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P f c \<epsilon>)"
    then obtain e where "e > 0" "\<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P f c \<epsilon>"
      by blast
    thus "(\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> P (remove_sings f) c \<epsilon>)"
      by (intro exI[of _ "min e \<epsilon>"]) (use *[of "min e \<epsilon>" c] \<epsilon>(1) in auto)
  qed
  show ?thesis
    unfolding residue_def by (intro arg_cong[of _ _ Eps] ext **[unfolded P_def])
qed    

lemma remove_sings_shift_0:
  "remove_sings f z = remove_sings (\<lambda>w. f (z + w)) 0"
proof (cases "\<exists>c. f \<midarrow>z\<rightarrow> c")
  case True
  then obtain c where c: "f \<midarrow>z\<rightarrow> c"
    by blast
  from c have "remove_sings f z = c"
    by (rule remove_sings_eqI)
  moreover have "remove_sings (\<lambda>w. f (z + w)) 0 = c"
    by (rule remove_sings_eqI) (use c in \<open>simp_all add: at_to_0' filterlim_filtermap add_ac\<close>)
  ultimately show ?thesis
    by simp
next
  case False
  hence "\<not>(\<exists>c. (\<lambda>w. f (z + w)) \<midarrow>0\<rightarrow> c)"
    by (simp add: at_to_0' filterlim_filtermap add_ac)
  with False show ?thesis
    by (simp add: remove_sings_def)
qed

lemma remove_sings_shift_0':
  "NO_MATCH 0 z \<Longrightarrow> remove_sings f z = remove_sings (\<lambda>w. f (z + w)) 0"
  by (rule remove_sings_shift_0)


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

lemma nicely_meromorphic_on_unop:
  assumes "f nicely_meromorphic_on A"
  assumes "f meromorphic_on A \<Longrightarrow> (\<lambda>z. h (f z)) meromorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> is_pole f z \<Longrightarrow> is_pole (\<lambda>z. h (f z)) z"
  assumes "\<And>z. z \<in> f ` A \<Longrightarrow> isCont h z"
  assumes "h 0 = 0"
  shows   "(\<lambda>z. h (f z)) nicely_meromorphic_on A"
  unfolding nicely_meromorphic_on_def
proof (intro conjI ballI)
  show "(\<lambda>z. h (f z)) meromorphic_on A"
    using assms(1,2) by (auto simp: nicely_meromorphic_on_def)
next
  fix z assume z: "z \<in> A"
  hence "is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z"
    using assms by (auto simp: nicely_meromorphic_on_def)
  thus "is_pole (\<lambda>z. h (f z)) z \<and> h (f z) = 0 \<or> (\<lambda>z. h (f z)) \<midarrow>z\<rightarrow> h (f z)"
  proof (rule disj_forward)
    assume "is_pole f z \<and> f z = 0"
    thus "is_pole (\<lambda>z. h (f z)) z \<and> h (f z) = 0"
      using assms z by auto
  next
    assume *: "f \<midarrow>z\<rightarrow> f z"
    from z assms have "isCont h (f z)"
      by auto
    with * show "(\<lambda>z. h (f z)) \<midarrow>z\<rightarrow> h (f z)"
      using continuous_within continuous_within_compose3 by blast
  qed
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

lemma nicely_meromorphic_on_const [intro]: "(\<lambda>_. c) nicely_meromorphic_on A"
  unfolding nicely_meromorphic_on_def by auto

lemma nicely_meromorphic_on_cmult_left [intro]:
  assumes "f nicely_meromorphic_on A"
  shows   "(\<lambda>z. c * f z) nicely_meromorphic_on A"
proof (cases "c = 0")
  case [simp]: False
  show ?thesis
    using assms by (rule nicely_meromorphic_on_unop) (auto intro!: meromorphic_intros)
qed (auto intro!: nicely_meromorphic_on_const)

lemma nicely_meromorphic_on_cmult_right [intro]:
  assumes "f nicely_meromorphic_on A"
  shows   "(\<lambda>z. f z * c) nicely_meromorphic_on A"
  using nicely_meromorphic_on_cmult_left[OF assms, of c] by (simp add: mult.commute)

lemma nicely_meromorphic_on_scaleR [intro]:
  assumes "f nicely_meromorphic_on A"
  shows   "(\<lambda>z. c *\<^sub>R f z) nicely_meromorphic_on A"
  using assms by (auto simp: scaleR_conv_of_real)

lemma nicely_meromorphic_on_uminus [intro]:
  assumes "f nicely_meromorphic_on A"
  shows   "(\<lambda>z. -f z) nicely_meromorphic_on A"
  using nicely_meromorphic_on_cmult_left[OF assms, of "-1"] by simp

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

lemma remove_sings_constant_on_open_iff:
  assumes "f meromorphic_on A" "open A"
  shows   "remove_sings f constant_on A \<longleftrightarrow> (\<exists>c. \<forall>\<^sub>\<approx>x\<in>A. f x = c)"
proof
  assume "remove_sings f constant_on A"
  then obtain c where c: "remove_sings f z = c" if "z \<in> A" for z
    using that by (auto simp: constant_on_def)
  have "\<forall>\<^sub>\<approx>x\<in>A. x \<in> A"
    using \<open>open A\<close> by (simp add: eventually_in_cosparse)
  hence "\<forall>\<^sub>\<approx>x\<in>A. f x = c"
    using eventually_remove_sings_eq[OF assms(1)] by eventually_elim (use c in auto)
  thus "\<exists>c. \<forall>\<^sub>\<approx>x\<in>A. f x = c"
    by blast
next
  assume "\<exists>c. \<forall>\<^sub>\<approx>x\<in>A. f x = c"
  then obtain c where c: "\<forall>\<^sub>\<approx>x\<in>A. f x = c"
    by blast
  have "\<forall>\<^sub>\<approx>x\<in>A. remove_sings f x = c"
    using eventually_remove_sings_eq[OF assms(1)] c by eventually_elim auto
  hence "remove_sings f z = c" if "z \<in> A" for z using that 
    by (meson assms(2) c eventually_cosparse_open_eq remove_sings_eqI tendsto_eventually)
  thus "remove_sings f constant_on A"
    unfolding constant_on_def by blast
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


subsection \<open>More on poles and zeros\<close>

lemma zorder_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x meromorphic_on {z}"
  assumes "eventually (\<lambda>z. (\<Prod>x\<in>A. f x z) \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z = (\<Sum>x\<in>A. zorder (f x) z)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  have "zorder (\<lambda>z. \<Prod>x\<in>insert a A. f x z) z = zorder (\<lambda>z. f a z * (\<Prod>x\<in>A. f x z)) z"
    using insert.hyps by simp
  also have "\<dots> = zorder (f a) z + zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z"
  proof (subst zorder_mult)
    have "\<forall>\<^sub>F z in at z. f a z \<noteq> 0"
      using insert.prems(2) by eventually_elim (use insert.hyps in auto)
    thus "\<exists>\<^sub>F z in at z. f a z \<noteq> 0"
      using eventually_frequently at_neq_bot by blast
  next
    have "\<forall>\<^sub>F z in at z. (\<Prod>x\<in>A. f x z) \<noteq> 0"
      using insert.prems(2) by eventually_elim (use insert.hyps in auto)
    thus "\<exists>\<^sub>F z in at z. (\<Prod>x\<in>A. f x z) \<noteq> 0"
      using eventually_frequently at_neq_bot by blast
  qed (use insert.prems in \<open>auto intro!: meromorphic_intros\<close>)
  also have "zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z = (\<Sum>x\<in>A. zorder (f x) z)"
    by (intro insert.IH) (use insert.prems insert.hyps in \<open>auto elim!: eventually_mono\<close>)
  also have "zorder (f a) z + \<dots> = (\<Sum>x\<in>insert a A. zorder (f x) z)"
    using insert.hyps by simp
  finally show ?case .
qed auto

lemma zorder_scale:
  assumes "f meromorphic_on {a * z}" "a \<noteq> 0"
  shows "zorder (\<lambda>w. f (a * w)) z = zorder f (a * z)"
proof (cases "eventually (\<lambda>z. f z = 0) (at (a * z))")
  case True
  hence ev: "eventually (\<lambda>z. f (a * z) = 0) (at z)"
  proof (rule eventually_compose_filterlim)
    show "filterlim ((*) a) (at (a * z)) (at z)"
    proof (rule filterlim_atI)
      show "\<forall>\<^sub>F x in at z. a * x \<noteq> a * z"
        using eventually_neq_at_within[of z z] by eventually_elim (use \<open>a \<noteq> 0\<close> in auto)
    qed (auto intro!: tendsto_intros)
  qed

  have "zorder (\<lambda>w. f (a * w)) z = zorder (\<lambda>_. 0) z"
    by (rule zorder_cong) (use ev in auto)
  also have "\<dots> = zorder (\<lambda>_. 0) (a * z)"
    by (simp add: zorder_shift')
  also have "\<dots> = zorder f (a * z)"
    by (rule zorder_cong) (use True in auto)
  finally show ?thesis .
next
  case False
  define G where "G = fps_const a * fps_X"
  have "zorder (f \<circ> (\<lambda>z. a * z)) z = zorder f (a * z) * int (subdegree G)"
  proof (rule zorder_compose)
    show "isolated_singularity_at f (a * z)" "not_essential f (a * z)"
      using assms(1) by (auto simp: meromorphic_on_altdef)
  next
    have "(\<lambda>x. a * x) has_fps_expansion G"
      unfolding G_def by (intro fps_expansion_intros)
    thus "(\<lambda>x. a * (z + x) - a * z) has_fps_expansion G"
      by (simp add: algebra_simps)
  next
    show "\<forall>\<^sub>F w in at (a * z). f w \<noteq> 0" using False 
      by (metis assms(1) has_laurent_expansion_isolated has_laurent_expansion_not_essential
             meromorphic_on_def non_zero_neighbour not_eventually singletonI)
  qed (use \<open>a \<noteq> 0\<close> in \<open>auto simp: G_def\<close>)
  also have "subdegree G = 1"
    using \<open>a \<noteq> 0\<close> by (simp add: G_def)
  finally show ?thesis
    by (simp add: o_def)
qed

lemma zorder_uminus:
  assumes "f meromorphic_on {-z}"
  shows "zorder (\<lambda>w. f (-w)) z = zorder f (-z)"
  using assms zorder_scale[of f "-1" z] by simp

lemma is_pole_deriv_iff:
  assumes "f meromorphic_on {z}"
  shows   "is_pole (deriv f) z \<longleftrightarrow> is_pole f z"
proof -
  from assms obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  have "deriv (\<lambda>w. f (z + w)) has_laurent_expansion fls_deriv F"
    using F by (rule has_laurent_expansion_deriv)
  also have "deriv (\<lambda>w. f (z + w)) = (\<lambda>w. deriv f (z + w))"
    by (simp add: deriv_shift_0' add_ac o_def fun_eq_iff)
  finally have F': "(\<lambda>w. deriv f (z + w)) has_laurent_expansion fls_deriv F" .
  have "is_pole (deriv f) z \<longleftrightarrow> fls_subdegree (fls_deriv F) < 0"
    using is_pole_fls_subdegree_iff[OF F'] by simp
  also have "\<dots> \<longleftrightarrow> fls_subdegree F < 0"
    using fls_deriv_subdegree0 fls_subdegree_deriv linorder_less_linear by fastforce
  also have "\<dots> \<longleftrightarrow> is_pole f z"
    using F by (simp add: has_laurent_expansion_imp_is_pole_iff)
  finally show ?thesis .
qed

lemma isolated_zero_remove_sings_iff [simp]:
  assumes "isolated_singularity_at f z"
  shows   "isolated_zero (remove_sings f) z \<longleftrightarrow> isolated_zero f z"
proof -
  have *: "(\<forall>\<^sub>F x in at z. remove_sings f x \<noteq> 0) \<longleftrightarrow> (\<forall>\<^sub>F x in at z. f x \<noteq> 0)"
  proof
    assume "(\<forall>\<^sub>F x in at z. f x \<noteq> 0)"
    thus "(\<forall>\<^sub>F x in at z. remove_sings f x \<noteq> 0)"
      using eventually_remove_sings_eq_at[OF assms]
      by eventually_elim auto
  next
    assume "(\<forall>\<^sub>F x in at z. remove_sings f x \<noteq> 0)"
    thus "(\<forall>\<^sub>F x in at z. f x \<noteq> 0)"
      using eventually_remove_sings_eq_at[OF assms]
      by eventually_elim auto
  qed
  show ?thesis
    unfolding isolated_zero_def using assms * by simp
qed

lemma zorder_isolated_zero_pos:
  assumes "isolated_zero f z" "f analytic_on {z}"
  shows   "zorder f z > 0"
proof (subst zorder_pos_iff' [OF assms(2)])
  show "f z = 0"
    using assms by (simp add: zero_isolated_zero_analytic)
next
  have "\<forall>\<^sub>F z in at z. f z \<noteq> 0"
    using assms by (auto simp: isolated_zero_def)
  thus "\<exists>\<^sub>F z in at z. f z \<noteq> 0"
    by (simp add: eventually_frequently)
qed

lemma zorder_isolated_zero_pos':
  assumes "isolated_zero f z" "isolated_singularity_at f z"
  shows   "zorder f z > 0"
proof -
  from assms(1) have "f \<midarrow>z\<rightarrow> 0"
    by (simp add: isolated_zero_def)
  with assms(2) have "remove_sings f analytic_on {z}"
    by (intro remove_sings_analytic_on)
  hence "zorder (remove_sings f) z > 0"
    using assms by (intro zorder_isolated_zero_pos) auto
  thus ?thesis
    using assms by simp
qed

lemma zero_isolated_zero_nicely_meromorphic:
  assumes "isolated_zero f z" "f nicely_meromorphic_on {z}"
  shows "f z = 0"
proof -
  have "\<not>is_pole f z"
    using assms pole_is_not_zero by blast
  with assms(2) have "f analytic_on {z}"
    by (simp add: nicely_meromorphic_on_imp_analytic_at)
  with zero_isolated_zero_analytic assms(1) show ?thesis
    by blast
qed

lemma meromorphic_on_imp_not_zero_cosparse:
  assumes "f meromorphic_on A"
  shows   "eventually (\<lambda>z. \<not>isolated_zero f z) (cosparse A)"
proof -
  have "eventually (\<lambda>z. \<not>is_pole (\<lambda>z. inverse (f z)) z) (cosparse A)"
    by (intro meromorphic_on_imp_not_pole_cosparse meromorphic_intros assms)
  thus ?thesis
    by (simp add: is_pole_inverse_iff)
qed

lemma nicely_meromorphic_on_inverse [meromorphic_intros]:
  assumes "f nicely_meromorphic_on A"
  shows   "(\<lambda>x. inverse (f x)) nicely_meromorphic_on A"
  unfolding nicely_meromorphic_on_def
proof (intro conjI ballI)
  fix z assume z: "z \<in> A"
  have "is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z"
    using assms z by (auto simp: nicely_meromorphic_on_def)
  thus "is_pole (\<lambda>x. inverse (f x)) z \<and> inverse (f z) = 0 \<or>
        (\<lambda>x. inverse (f x)) \<midarrow>z\<rightarrow> inverse (f z)"
  proof
    assume "is_pole f z \<and> f z = 0"
    hence "isolated_zero (\<lambda>z. inverse (f z)) z \<and> inverse (f z) = 0"
      by (auto simp: isolated_zero_inverse_iff)
    hence "(\<lambda>x. inverse (f x)) \<midarrow>z\<rightarrow> inverse (f z)"
      by (simp add: isolated_zero_def)
    thus ?thesis ..
  next
    assume lim: "f \<midarrow>z\<rightarrow> f z"
    hence ana: "f analytic_on {z}"
      using assms is_pole_def nicely_meromorphic_on_imp_analytic_at
            not_tendsto_and_filterlim_at_infinity trivial_limit_at z by blast
    show ?thesis
    proof (cases "isolated_zero f z")
      case True
      with lim have "f z = 0"
        using continuous_within zero_isolated_zero by blast
      with True have "is_pole (\<lambda>z. inverse (f z)) z \<and> inverse (f z) = 0"
        by (auto simp: is_pole_inverse_iff)
      thus ?thesis ..
    next
      case False
      hence "f z \<noteq> 0 \<or> (f z = 0 \<and> eventually (\<lambda>z. f z = 0) (at z))"
        using non_isolated_zero_imp_eventually_zero[OF ana] by blast
      thus ?thesis
      proof (elim disjE conjE)
        assume "f z \<noteq> 0"
        hence "(\<lambda>z. inverse (f z)) \<midarrow>z\<rightarrow> inverse (f z)"
          by (intro tendsto_intros lim)
        thus ?thesis ..
      next
        assume *: "f z = 0" "eventually (\<lambda>z. f z = 0) (at z)"
        have "eventually (\<lambda>z. inverse (f z) = 0) (at z)"
          using *(2) by eventually_elim auto
        hence "(\<lambda>z. inverse (f z)) \<midarrow>z\<rightarrow> 0"
          by (simp add: tendsto_eventually)
        with *(1) show ?thesis
          by auto
      qed
    qed
  qed
qed (use assms in \<open>auto simp: nicely_meromorphic_on_def intro!: meromorphic_intros\<close>)

lemma is_pole_zero_at_nicely_mero:
  assumes "f nicely_meromorphic_on A" "is_pole f z" "z \<in> A"
  shows "f z = 0"
  by (meson assms at_neq_bot 
      is_pole_def nicely_meromorphic_on_def 
      not_tendsto_and_filterlim_at_infinity)

lemma zero_or_pole:
  assumes mero: "f nicely_meromorphic_on A" 
    and "z \<in> A" "f z = 0" and event: "\<forall>\<^sub>F x in at z. f x \<noteq> 0"
  shows "isolated_zero f z \<or> is_pole f z"
proof -
  from mero \<open>z\<in>A\<close>
  have "(is_pole f z \<and> f z=0) \<or> f \<midarrow>z\<rightarrow> f z"
    unfolding nicely_meromorphic_on_def by simp
  moreover have "isolated_zero f z" if "f \<midarrow>z\<rightarrow> f z" 
    unfolding isolated_zero_def
    using \<open>f z=0\<close> that event tendsto_nhds_iff by auto
  ultimately show ?thesis by auto
qed

lemma isolated_zero_fls_subdegree_iff:
  assumes "(\<lambda>x. f (z + x)) has_laurent_expansion F"
  shows "isolated_zero f z \<longleftrightarrow> fls_subdegree F > 0"
  using assms unfolding isolated_zero_def
  by (metis Lim_at_zero fls_zero_subdegree has_laurent_expansion_eventually_nonzero_iff not_le
        order.refl tendsto_0_subdegree_iff_0)

lemma zorder_pos_imp_isolated_zero:
  assumes "f meromorphic_on {z}" "eventually (\<lambda>z. f z \<noteq> 0) (at z)" "zorder f z > 0"
  shows   "isolated_zero f z"
  using assms isolated_zero_fls_subdegree_iff
  by (metis has_laurent_expansion_eventually_nonzero_iff
      has_laurent_expansion_zorder insertI1
      meromorphic_on_def)

lemma zorder_neg_imp_is_pole:
  assumes "f meromorphic_on {z}" "eventually (\<lambda>z. f z \<noteq> 0) (at z)" "zorder f z < 0"
  shows   "is_pole f z"
  using assms is_pole_fls_subdegree_iff at_neq_bot eventually_frequently meromorphic_at_iff
        neg_zorder_imp_is_pole by blast

lemma not_pole_not_isolated_zero_imp_zorder_eq_0:
  assumes "f meromorphic_on {z}" "\<not>is_pole f z" "\<not>isolated_zero f z" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder f z = 0"
proof -
  have "remove_sings f analytic_on {z}"
    using assms meromorphic_at_iff not_essential_def remove_sings_analytic_on by blast
  moreover from this and assms have "remove_sings f z \<noteq> 0"
    using isolated_zero_def meromorphic_at_iff non_zero_neighbour remove_sings_eq_0_iff by blast
  moreover have "frequently (\<lambda>z. remove_sings f z \<noteq> 0) (at z)"
    using assms analytic_at_neq_imp_eventually_neq calculation(1,2)
      eventually_frequently trivial_limit_at by blast
  ultimately have "zorder (remove_sings f) z = 0"
    using zorder_eq_0_iff by blast
  thus ?thesis
    using assms(1) meromorphic_at_iff by auto
qed

lemma not_essential_compose:
  assumes "not_essential f (g z)" "g analytic_on {z}"
  shows   "not_essential (\<lambda>x. f (g x)) z"
proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
  case False
  hence "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
    by (intro non_isolated_zero_imp_eventually_zero' analytic_intros assms) auto
  hence "not_essential (\<lambda>x. f (g x)) z \<longleftrightarrow> not_essential (\<lambda>_. f (g z)) z"
    by (intro not_essential_cong refl)
       (auto elim!: eventually_mono simp: eventually_at_filter)
  thus ?thesis
    by (simp add: not_essential_const)
next
  case True
  hence ev: "eventually (\<lambda>w. g w \<noteq> g z) (at z)"
    by (auto simp: isolated_zero_def)
  from assms consider c where "f \<midarrow>g z\<rightarrow> c" | "is_pole f (g z)"
    by (auto simp: not_essential_def)  
  have "isCont g z"
    by (rule analytic_at_imp_isCont) fact
  hence lim: "g \<midarrow>z\<rightarrow> g z"
    using isContD by blast

  from assms(1) consider c where "f \<midarrow>g z\<rightarrow> c" | "is_pole f (g z)"
    unfolding not_essential_def by blast
  thus ?thesis
  proof cases
    fix c assume "f \<midarrow>g z\<rightarrow> c"
    hence "(\<lambda>x. f (g x)) \<midarrow>z\<rightarrow> c"
      by (rule filterlim_compose) (use lim ev in \<open>auto simp: filterlim_at\<close>)
    thus ?thesis
      by (auto simp: not_essential_def)
  next
    assume "is_pole f (g z)"
    hence "is_pole (\<lambda>x. f (g x)) z"
      by (rule is_pole_compose) fact+
    thus ?thesis
      by (auto simp: not_essential_def)
  qed
qed


lemma isolated_singularity_at_compose:
  assumes "isolated_singularity_at f (g z)" "g analytic_on {z}"
  shows   "isolated_singularity_at (\<lambda>x. f (g x)) z"
proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
  case False
  hence "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
    by (intro non_isolated_zero_imp_eventually_zero') (use assms in \<open>auto intro!: analytic_intros\<close>)
  hence "isolated_singularity_at (\<lambda>x. f (g x)) z \<longleftrightarrow> isolated_singularity_at (\<lambda>_. f (g z)) z"
    by (intro isolated_singularity_at_cong refl)
       (auto elim!: eventually_mono simp: eventually_at_filter)
  thus ?thesis
    by (simp add: isolated_singularity_at_const)
next
  case True
  from assms(1) obtain r where r: "r > 0" "f analytic_on ball (g z) r - {g z}"
    by (auto simp: isolated_singularity_at_def)
  hence holo_f: "f holomorphic_on ball (g z) r - {g z}"
    by (subst (asm) analytic_on_open) auto
  from assms(2) obtain r' where r': "r' > 0" "g holomorphic_on ball z r'"
    by (auto simp: analytic_on_def)

  have "continuous_on (ball z r') g"
    using holomorphic_on_imp_continuous_on r' by blast
  hence "isCont g z"
    using r' by (subst (asm) continuous_on_eq_continuous_at) auto
  hence "g \<midarrow>z\<rightarrow> g z"
    using isContD by blast
  hence "eventually (\<lambda>w. g w \<in> ball (g z) r) (at z)"
    using \<open>r > 0\<close> unfolding tendsto_def by force
  moreover have "eventually (\<lambda>w. g w \<noteq> g z) (at z)" using True
    by (auto simp: isolated_zero_def elim!: eventually_mono)
  ultimately have "eventually (\<lambda>w. g w \<in> ball (g z) r - {g z}) (at z)"
    by eventually_elim auto
  then obtain r'' where r'': "r'' > 0" "\<forall>w\<in>ball z r''-{z}. g w \<in> ball (g z) r - {g z}"
    unfolding eventually_at_filter eventually_nhds_metric ball_def
    by (auto simp: dist_commute)
  have "f \<circ> g holomorphic_on ball z (min r' r'') - {z}"
  proof (rule holomorphic_on_compose_gen)
    show "g holomorphic_on ball z (min r' r'') - {z}"
      by (rule holomorphic_on_subset[OF r'(2)]) auto
    show "f holomorphic_on ball (g z) r - {g z}"
      by fact
    show "g ` (ball z (min r' r'') - {z}) \<subseteq> ball (g z) r - {g z}"
      using r'' by force
  qed
  hence "f \<circ> g analytic_on ball z (min r' r'') - {z}"
    by (subst analytic_on_open) auto
  thus ?thesis using \<open>r' > 0\<close> \<open>r'' > 0\<close>
    by (auto simp: isolated_singularity_at_def o_def intro!: exI[of _ "min r' r''"])
qed

lemma is_pole_power_int_0:
  assumes "f analytic_on {x}" "isolated_zero f x" "n < 0"
  shows   "is_pole (\<lambda>x. f x powi n) x"
proof -
  have "f \<midarrow>x\<rightarrow> f x"
    using assms(1) by (simp add: analytic_at_imp_isCont isContD)
  with assms show ?thesis
    unfolding is_pole_def
    by (intro filterlim_power_int_neg_at_infinity) (auto simp: isolated_zero_def)
qed

lemma isolated_zero_imp_not_constant_on:
  fixes f :: "'a :: perfect_space \<Rightarrow> 'b :: real_normed_div_algebra"
  assumes "isolated_zero f x" "x \<in> A" "open A"
  shows   "\<not>f constant_on A"
proof
  assume "f constant_on A"
  then obtain c where c: "\<And>x. x \<in> A \<Longrightarrow> f x = c"
    by (auto simp: constant_on_def)
  have "eventually (\<lambda>z. z \<in> A - {x}) (at x)"
    by (intro eventually_at_in_open assms)
  hence "eventually (\<lambda>z. f z = c) (at x)"
    by eventually_elim (use c in auto)
  hence "f \<midarrow>x\<rightarrow> c"
    using tendsto_eventually by blast
  moreover from assms have "f \<midarrow>x\<rightarrow> 0"
    by (simp add: isolated_zero_def)
  ultimately have [simp]: "c = 0"
    using tendsto_unique[of "at x" f c 0] by (simp add: at_neq_bot)

  have "eventually (\<lambda>x. f x \<noteq> 0) (at x)"
    using assms by (auto simp: isolated_zero_def)
  moreover have "eventually (\<lambda>x. x \<in> A) (at x)"
    using assms by (intro eventually_at_in_open') auto
  ultimately have "eventually (\<lambda>x. False) (at x)"
    by eventually_elim (use c in auto)
  thus False
    by simp
qed

end
