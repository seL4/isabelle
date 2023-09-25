theory Meromorphic
  imports Laurent_Convergence Riemann_Mapping
begin

definition remove_sings :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
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
    by eventually_elim (auto simp: remove_sings_at_analytic *)
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
  case True
  then show ?thesis by simp
next
  case False
  then obtain c where c:"f \<midarrow>w\<rightarrow> c"
    using \<open>not_essential f w\<close> unfolding not_essential_def by auto
  then show ?thesis 
    using False remove_sings_eqI by auto
qed

definition meromorphic_on:: "[complex \<Rightarrow> complex, complex set, complex set] \<Rightarrow> bool" 
  ("_ (meromorphic'_on) _ _" [50,50,50]50) where 
  "f meromorphic_on D pts \<equiv> 
     open D \<and> pts \<subseteq> D \<and> (\<forall>z\<in>pts. isolated_singularity_at f z \<and> not_essential f z) \<and>
     (\<forall>z\<in>D. \<not>(z islimpt pts)) \<and> (f holomorphic_on D-pts)"

lemma meromorphic_imp_holomorphic: "f meromorphic_on D pts \<Longrightarrow> f holomorphic_on (D - pts)"
  unfolding meromorphic_on_def by auto

lemma meromorphic_imp_closedin_pts:
  assumes "f meromorphic_on D pts"
  shows "closedin (top_of_set D) pts"
  by (meson assms closedin_limpt meromorphic_on_def)

lemma meromorphic_imp_open_diff':
  assumes "f meromorphic_on D pts" "pts' \<subseteq> pts"
  shows "open (D - pts')"
proof -
  have "D - pts' = D - closure pts'"
  proof safe
    fix x assume x: "x \<in> D" "x \<in> closure pts'" "x \<notin> pts'"
    hence "x islimpt pts'"
      by (subst islimpt_in_closure) auto
    hence "x islimpt pts"
      by (rule islimpt_subset) fact
    with assms x show False
      by (auto simp: meromorphic_on_def)
  qed (use closure_subset in auto)
  then show ?thesis
    using assms meromorphic_on_def by auto
qed

lemma meromorphic_imp_open_diff: "f meromorphic_on D pts \<Longrightarrow> open (D - pts)"
  by (erule meromorphic_imp_open_diff') auto

lemma meromorphic_pole_subset:
  assumes merf: "f meromorphic_on D pts" 
  shows "{x\<in>D. is_pole f x} \<subseteq> pts"
  by (smt (verit) Diff_iff assms mem_Collect_eq meromorphic_imp_open_diff 
      meromorphic_on_def not_is_pole_holomorphic subsetI)

named_theorems meromorphic_intros

lemma meromorphic_on_subset:
  assumes "f meromorphic_on A pts" "open B" "B \<subseteq> A" "pts' = pts \<inter> B"
  shows   "f meromorphic_on B pts'"
  unfolding meromorphic_on_def
proof (intro ballI conjI)
  fix z assume "z \<in> B"
  show "\<not>z islimpt pts'"
  proof
    assume "z islimpt pts'"
    hence "z islimpt pts"
      by (rule islimpt_subset) (use \<open>pts' = _\<close> in auto)
    thus False using \<open>z \<in> B\<close> \<open>B \<subseteq> A\<close> assms(1)
      by (auto simp: meromorphic_on_def)
  qed
qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

lemma meromorphic_on_superset_pts:
  assumes "f meromorphic_on A pts" "pts \<subseteq> pts'" "pts' \<subseteq> A" "\<forall>x\<in>A. \<not>x islimpt pts'"
  shows   "f meromorphic_on A pts'"
  unfolding meromorphic_on_def
proof (intro conjI ballI impI)
  fix z assume "z \<in> pts'"
  from assms(1) have holo: "f holomorphic_on A - pts" and "open A"
    unfolding meromorphic_on_def by blast+
  have "open (A - pts)"
    by (intro meromorphic_imp_open_diff[OF assms(1)])

  show "isolated_singularity_at f z"
  proof (cases "z \<in> pts")
    case False
    thus ?thesis
      using \<open>open (A - pts)\<close> assms \<open>z \<in> pts'\<close>
      by (intro isolated_singularity_at_holomorphic[of _ "A - pts"] holomorphic_on_subset[OF holo])
         auto
  qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

  show "not_essential f z"
  proof (cases "z \<in> pts")
    case False
    thus ?thesis
      using \<open>open (A - pts)\<close> assms \<open>z \<in> pts'\<close>
      by (intro not_essential_holomorphic[of _ "A - pts"] holomorphic_on_subset[OF holo])
         auto
  qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)
qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

lemma meromorphic_on_no_singularities: "f meromorphic_on A {} \<longleftrightarrow> f holomorphic_on A \<and> open A"
  by (auto simp: meromorphic_on_def)

lemma holomorphic_on_imp_meromorphic_on:
  "f holomorphic_on A \<Longrightarrow> pts \<subseteq> A \<Longrightarrow> open A \<Longrightarrow> \<forall>x\<in>A. \<not>x islimpt pts \<Longrightarrow> f meromorphic_on A pts"
  by (rule meromorphic_on_superset_pts[where pts = "{}"])
     (auto simp: meromorphic_on_no_singularities)

lemma meromorphic_on_const [meromorphic_intros]: 
  assumes "open A" "\<forall>x\<in>A. \<not>x islimpt pts" "pts \<subseteq> A"
  shows   "(\<lambda>_. c) meromorphic_on A pts"
  by (rule holomorphic_on_imp_meromorphic_on) (use assms in auto)

lemma meromorphic_on_ident [meromorphic_intros]:
  assumes "open A" "\<forall>x\<in>A. \<not>x islimpt pts" "pts \<subseteq> A"
  shows   "(\<lambda>x. x) meromorphic_on A pts"
  by (rule holomorphic_on_imp_meromorphic_on) (use assms in auto)

lemma meromorphic_on_id [meromorphic_intros]:
  assumes "open A" "\<forall>x\<in>A. \<not>x islimpt pts" "pts \<subseteq> A"
  shows   "id meromorphic_on A pts"
  using meromorphic_on_ident assms unfolding id_def .

lemma not_essential_add [singularity_intros]:
  assumes f_ness: "not_essential f z" and g_ness: "not_essential g z"
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
  shows "not_essential (\<lambda>w. f w + g w) z"
proof -
  have "(\<lambda>w. f (z + w) + g (z + w)) has_laurent_expansion laurent_expansion f z + laurent_expansion g z"
    by (intro not_essential_has_laurent_expansion laurent_expansion_intros assms)
  hence "not_essential (\<lambda>w. f (z + w) + g (z + w)) 0"
    using has_laurent_expansion_not_essential_0 by blast
  thus ?thesis
    by (simp add: not_essential_shift_0)
qed

lemma meromorphic_on_uminus [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>z. -f z) meromorphic_on A pts"
  unfolding meromorphic_on_def
  by (use assms in \<open>auto simp: meromorphic_on_def intro!: holomorphic_intros singularity_intros\<close>)

lemma meromorphic_on_add [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "g meromorphic_on A pts"
  shows   "(\<lambda>z. f z + g z) meromorphic_on A pts"
  unfolding meromorphic_on_def
  by (use assms in \<open>auto simp: meromorphic_on_def intro!: holomorphic_intros singularity_intros\<close>)

lemma meromorphic_on_add':
  assumes "f meromorphic_on A pts1" "g meromorphic_on A pts2"
  shows   "(\<lambda>z. f z + g z) meromorphic_on A (pts1 \<union> pts2)"
proof (rule meromorphic_intros)
  show "f meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(1)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
  show "g meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(2)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
qed

lemma meromorphic_on_add_const [meromorphic_intros]:
  assumes "f meromorphic_on A pts" 
  shows   "(\<lambda>z. f z + c) meromorphic_on A pts"
  unfolding meromorphic_on_def
  by (use assms in \<open>auto simp: meromorphic_on_def intro!: holomorphic_intros singularity_intros\<close>)

lemma meromorphic_on_minus_const [meromorphic_intros]:
  assumes "f meromorphic_on A pts" 
  shows   "(\<lambda>z. f z - c) meromorphic_on A pts"
  using meromorphic_on_add_const[OF assms,of "-c"] by simp

lemma meromorphic_on_diff [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "g meromorphic_on A pts"
  shows   "(\<lambda>z. f z - g z) meromorphic_on A pts"
  using meromorphic_on_add[OF assms(1) meromorphic_on_uminus[OF assms(2)]] by simp

lemma meromorphic_on_diff':
  assumes "f meromorphic_on A pts1" "g meromorphic_on A pts2"
  shows   "(\<lambda>z. f z - g z) meromorphic_on A (pts1 \<union> pts2)"
proof (rule meromorphic_intros)
  show "f meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(1)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
  show "g meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(2)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
qed

lemma meromorphic_on_mult [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "g meromorphic_on A pts"
  shows   "(\<lambda>z. f z * g z) meromorphic_on A pts"
  unfolding meromorphic_on_def
  by (use assms in \<open>auto simp: meromorphic_on_def intro!: holomorphic_intros singularity_intros\<close>)

lemma meromorphic_on_mult':
  assumes "f meromorphic_on A pts1" "g meromorphic_on A pts2"
  shows   "(\<lambda>z. f z * g z) meromorphic_on A (pts1 \<union> pts2)"
proof (rule meromorphic_intros)
  show "f meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(1)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
  show "g meromorphic_on A (pts1 \<union> pts2)"
    by (rule meromorphic_on_superset_pts[OF assms(2)])
       (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)
qed



lemma meromorphic_on_imp_not_essential:
  assumes "f meromorphic_on A pts" "z \<in> A"
  shows   "not_essential f z"
proof (cases "z \<in> pts")
  case False
  thus ?thesis
    using not_essential_holomorphic[of f "A - pts" z] meromorphic_imp_open_diff[OF assms(1)] assms
    by (auto simp: meromorphic_on_def)
qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

lemma meromorphic_imp_analytic: "f meromorphic_on D pts \<Longrightarrow> f analytic_on (D - pts)"
  unfolding meromorphic_on_def 
  apply (subst analytic_on_open)
  using meromorphic_imp_open_diff meromorphic_on_id apply blast
  apply auto
  done

lemma not_islimpt_isolated_zeros:
  assumes mero: "f meromorphic_on A pts" and "z \<in> A"
  shows "\<not>z islimpt {w\<in>A. isolated_zero f w}"
proof
  assume islimpt: "z islimpt {w\<in>A. isolated_zero f w}"
  have holo: "f holomorphic_on A - pts" and "open A"
    using assms by (auto simp: meromorphic_on_def)
  have open': "open (A - (pts - {z}))"
    by (intro meromorphic_imp_open_diff'[OF mero]) auto
  then obtain r where r: "r > 0" "ball z r \<subseteq> A - (pts - {z})"
    using meromorphic_imp_open_diff[OF mero] \<open>z \<in> A\<close> openE by blast

  have "not_essential f z"
    using assms by (rule meromorphic_on_imp_not_essential)
  then consider c where "f \<midarrow>z\<rightarrow> c" | "is_pole f z"
    unfolding not_essential_def by blast
  thus False
  proof cases
    assume "is_pole f z"
    hence "eventually (\<lambda>w. f w \<noteq> 0) (at z)"
      by (rule non_zero_neighbour_pole)
    hence "\<not>z islimpt {w. f w = 0}"
      by (simp add: islimpt_conv_frequently_at frequently_def)
    moreover have "z islimpt {w. f w = 0}"
      using islimpt by (rule islimpt_subset) (auto simp: isolated_zero_def)
    ultimately show False by contradiction
  next
    fix c assume c: "f \<midarrow>z\<rightarrow> c"
    define g where "g = (\<lambda>w. if w = z then c else f w)"
    have holo': "g holomorphic_on A - (pts - {z})" unfolding g_def
      by (intro removable_singularity holomorphic_on_subset[OF holo] open' c) auto

    have eq_zero: "g w = 0" if "w \<in> ball z r" for w
    proof (rule analytic_continuation[where f = g])
      show "open (ball z r)" "connected (ball z r)" "{w\<in>ball z r. isolated_zero f w} \<subseteq> ball z r"
        by auto
      have "z islimpt {w\<in>A. isolated_zero f w} \<inter> ball z r"
        using islimpt \<open>r > 0\<close> by (intro islimpt_Int_eventually eventually_at_in_open') auto
      also have "\<dots> = {w\<in>ball z r. isolated_zero f w}"
        using r by auto
      finally show "z islimpt {w\<in>ball z r. isolated_zero f w}"
        by simp
    next
      fix w assume w: "w \<in> {w\<in>ball z r. isolated_zero f w}"
      show "g w = 0"
      proof (cases "w = z")
        case False
        thus ?thesis using w by (auto simp: g_def isolated_zero_def)
      next
        case True
        have "z islimpt {z. f z = 0}"
          using islimpt by (rule islimpt_subset) (auto simp: isolated_zero_def)
        thus ?thesis
          using w by (simp add: isolated_zero_altdef True)
      qed
    qed (use r that in \<open>auto intro!: holomorphic_on_subset[OF holo'] simp: isolated_zero_def\<close>)

    have "infinite ({w\<in>A. isolated_zero f w} \<inter> ball z r)"
      using islimpt \<open>r > 0\<close> unfolding islimpt_eq_infinite_ball by blast
    hence "{w\<in>A. isolated_zero f w} \<inter> ball z r \<noteq> {}"
      by force
    then obtain z0 where z0: "z0 \<in> A" "isolated_zero f z0" "z0 \<in> ball z r"
      by blast
    have "\<forall>\<^sub>F y in at z0. y \<in> ball z r - (if z = z0 then {} else {z}) - {z0}"
      using r z0 by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>w. f w = 0) (at z0)"
    proof eventually_elim
      case (elim w)
      show ?case
        using eq_zero[of w] elim by (auto simp: g_def split: if_splits)
    qed
    hence "eventually (\<lambda>w. f w = 0) (at z0)"
      by (auto simp: g_def eventually_at_filter elim!: eventually_mono split: if_splits)
    moreover from z0 have "eventually (\<lambda>w. f w \<noteq> 0) (at z0)"
      by (simp add: isolated_zero_def)
    ultimately have "eventually (\<lambda>_. False) (at z0)"
      by eventually_elim auto
    thus False
      by simp
  qed
qed
  
lemma closedin_isolated_zeros:
  assumes "f meromorphic_on A pts"
  shows   "closedin (top_of_set A) {z\<in>A. isolated_zero f z}"
  unfolding closedin_limpt using not_islimpt_isolated_zeros[OF assms] by auto

lemma meromorphic_on_deriv':
  assumes "f meromorphic_on A pts" "open A"
  assumes "\<And>x. x \<in> A - pts \<Longrightarrow> (f has_field_derivative f' x) (at x)"
  shows   "f' meromorphic_on A pts"
  unfolding meromorphic_on_def
proof (intro conjI ballI)
  have "open (A - pts)"
    by (intro meromorphic_imp_open_diff[OF assms(1)])
  thus "f' holomorphic_on A - pts"
    by (rule derivative_is_holomorphic) (use assms in auto)
next
  fix z assume "z \<in> pts"
  hence "z \<in> A"
    using assms(1) by (auto simp: meromorphic_on_def)
  from \<open>z \<in> pts\<close> obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    using assms(1) by (auto simp: meromorphic_on_def isolated_singularity_at_def)

  have "open (ball z r \<inter> (A - (pts - {z})))"
    by (intro open_Int assms meromorphic_imp_open_diff'[OF assms(1)]) auto
  then obtain r' where r': "r' > 0" "ball z r' \<subseteq> ball z r \<inter> (A - (pts - {z}))"
    using r \<open>z \<in> A\<close> by (subst (asm) open_contains_ball) fastforce

  have "open (ball z r' - {z})"
    by auto
  hence "f' holomorphic_on ball z r' - {z}"
    by (rule derivative_is_holomorphic[of _ f]) (use r' in \<open>auto intro!: assms(3)\<close>)
  moreover have "open (ball z r' - {z})"
    by auto
  ultimately show "isolated_singularity_at f' z"
    unfolding isolated_singularity_at_def using \<open>r' > 0\<close>
    by (auto simp: analytic_on_open intro!: exI[of _ r'])
next
  fix z assume z: "z \<in> pts"
  hence z': "not_essential f z" "z \<in> A"
    using assms by (auto simp: meromorphic_on_def)
  from z'(1) show "not_essential f' z"
  proof (rule not_essential_deriv')
    show "z \<in> A - (pts - {z})"
      using \<open>z \<in> A\<close> by blast
    show "open (A - (pts - {z}))"
      by (intro meromorphic_imp_open_diff'[OF assms(1)]) auto
  qed (use assms in auto)
qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

lemma meromorphic_on_deriv [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "open A"
  shows   "deriv f meromorphic_on A pts"
proof (intro meromorphic_on_deriv'[OF assms(1)])
  have *: "open (A - pts)"
    by (intro meromorphic_imp_open_diff[OF assms(1)])
  show "(f has_field_derivative deriv f x) (at x)" if "x \<in> A - pts" for x
    using assms(1) by (intro holomorphic_derivI[OF _ * that]) (auto simp: meromorphic_on_def)
qed fact

lemma meromorphic_on_imp_analytic_at:
  assumes "f meromorphic_on A pts" "z \<in> A - pts"
  shows   "f analytic_on {z}"
  using assms by (metis analytic_at meromorphic_imp_open_diff meromorphic_on_def)

lemma meromorphic_compact_finite_pts:
  assumes "f meromorphic_on D pts" "compact S" "S \<subseteq> D"
  shows "finite (S \<inter> pts)"
proof -
  { assume "infinite (S \<inter> pts)"
    then obtain z where "z \<in> S" and z: "z islimpt (S \<inter> pts)"
      using assms by (metis compact_eq_Bolzano_Weierstrass inf_le1) 
    then have False
        using assms by (meson in_mono inf_le2 islimpt_subset meromorphic_on_def) }
  then show ?thesis by metis
qed

lemma meromorphic_imp_countable:
  assumes "f meromorphic_on D pts" 
  shows "countable pts"
proof -
  obtain K :: "nat \<Rightarrow> complex set" where K: "D = (\<Union>n. K n)" "\<And>n. compact (K n)"
    using assms unfolding meromorphic_on_def by (metis open_Union_compact_subsets)
  then have "pts = (\<Union>n. K n \<inter> pts)"
    using assms meromorphic_on_def by auto
  moreover have "\<And>n. finite (K n \<inter> pts)"
    by (metis K(1) K(2) UN_I assms image_iff meromorphic_compact_finite_pts rangeI subset_eq)
  ultimately show ?thesis
    by (metis countableI_type countable_UN countable_finite)
qed

lemma meromorphic_imp_connected_diff':
  assumes "f meromorphic_on D pts" "connected D" "pts' \<subseteq> pts"
  shows "connected (D - pts')"
proof (rule connected_open_diff_countable)
  show "countable pts'"
    by (rule countable_subset [OF assms(3)]) (use assms(1) in \<open>auto simp: meromorphic_imp_countable\<close>)
qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)

lemma meromorphic_imp_connected_diff:
  assumes "f meromorphic_on D pts" "connected D"
  shows "connected (D - pts)"
  using meromorphic_imp_connected_diff'[OF assms order.refl] .

lemma meromorphic_on_compose [meromorphic_intros]:
  assumes f: "f meromorphic_on A pts" and g: "g holomorphic_on B"
  assumes "open B" and "g ` B \<subseteq> A"
  shows   "(\<lambda>x. f (g x)) meromorphic_on B (isolated_points_of (g -` pts \<inter> B))"
  unfolding meromorphic_on_def
proof (intro ballI conjI)
  fix z assume z: "z \<in> isolated_points_of (g -` pts \<inter> B)"
  hence z': "z \<in> B" "g z \<in> pts"
    using isolated_points_of_subset by blast+
  have g': "g analytic_on {z}"
    using g z' \<open>open B\<close> analytic_at by blast

  show "isolated_singularity_at (\<lambda>x. f (g x)) z"
    by (rule isolated_singularity_at_compose[OF _ g']) (use f z' in \<open>auto simp: meromorphic_on_def\<close>)
  show "not_essential (\<lambda>x. f (g x)) z"
    by (rule not_essential_compose[OF _ g']) (use f z' in \<open>auto simp: meromorphic_on_def\<close>)
next
  fix z assume z: "z \<in> B"
  hence "g z \<in> A"
    using assms by auto
  hence "\<not>g z islimpt pts"
    using f by (auto simp: meromorphic_on_def)
  hence ev: "eventually (\<lambda>w. w \<notin> pts) (at (g z))"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
  have g': "g analytic_on {z}"
    by (rule holomorphic_on_imp_analytic_at[OF g]) (use assms z in auto)

  (* TODO: There's probably a useful lemma somewhere in here to extract... *)
  have "eventually (\<lambda>w. w \<notin> isolated_points_of (g -` pts \<inter> B)) (at z)"
  proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
    case True
    have "eventually (\<lambda>w. w \<notin> pts) (at (g z))"
      using ev by (auto simp: islimpt_conv_frequently_at frequently_def)
    moreover have "g \<midarrow>z\<rightarrow> g z"
      using analytic_at_imp_isCont[OF g'] isContD by blast
    hence lim: "filterlim g (at (g z)) (at z)"
      using True by (auto simp: filterlim_at isolated_zero_def)
    have "eventually (\<lambda>w. g w \<notin> pts) (at z)"
      using ev lim by (rule eventually_compose_filterlim)
    thus ?thesis
      by eventually_elim (auto simp: isolated_points_of_def)
  next
    case False
    have "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
      using False by (rule non_isolated_zero) (auto intro!: analytic_intros g')
    hence "eventually (\<lambda>w. g w = g z \<and> w \<in> B) (nhds z)"
      using eventually_nhds_in_open[OF \<open>open B\<close> \<open>z \<in> B\<close>]
      by eventually_elim auto
    then obtain X where X: "open X" "z \<in> X" "X \<subseteq> B" "\<forall>x\<in>X. g x = g z"
      unfolding eventually_nhds by blast

    have "z0 \<notin> isolated_points_of (g -` pts \<inter> B)" if "z0 \<in> X" for z0
    proof (cases "g z \<in> pts")
      case False
      with that have "g z0 \<notin> pts"
        using X by metis
      thus ?thesis
        by (auto simp: isolated_points_of_def)
    next
      case True
      have "eventually (\<lambda>w. w \<in> X) (at z0)"
        by (intro eventually_at_in_open') fact+
      hence "eventually (\<lambda>w. w \<in> g -` pts \<inter> B) (at z0)"
        by eventually_elim (use X True in fastforce)
      hence "frequently (\<lambda>w. w \<in> g -` pts \<inter> B) (at z0)"
        by (meson at_neq_bot eventually_frequently)
      thus "z0 \<notin> isolated_points_of (g -` pts \<inter> B)"
        unfolding isolated_points_of_def by (auto simp: frequently_def)
    qed
    moreover have "eventually (\<lambda>x. x \<in> X) (at z)"
      by (intro eventually_at_in_open') fact+
    ultimately show ?thesis
      by (auto elim!: eventually_mono)
  qed
  thus "\<not>z islimpt isolated_points_of (g -` pts \<inter> B)"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
next
  have "f \<circ> g analytic_on (\<Union>z\<in>B - isolated_points_of (g -` pts \<inter> B). {z})"
    unfolding analytic_on_UN
  proof
    fix z assume z: "z \<in> B - isolated_points_of (g -` pts \<inter> B)"
    hence "z \<in> B" by blast
    have g': "g analytic_on {z}"
      by (rule holomorphic_on_imp_analytic_at[OF g]) (use assms z in auto)
    show "f \<circ> g analytic_on {z}"
    proof (cases "g z \<in> pts")
      case False
      show ?thesis
      proof (rule analytic_on_compose)
        show "f analytic_on g ` {z}" using False z assms
          by (auto intro!: meromorphic_on_imp_analytic_at[OF f])
      qed fact
    next
      case True
      show ?thesis
      proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
        case False
        hence "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
          by (rule non_isolated_zero) (auto intro!: analytic_intros g')
        hence "f \<circ> g analytic_on {z} \<longleftrightarrow> (\<lambda>_. f (g z)) analytic_on {z}"
          by (intro analytic_at_cong) (auto elim!: eventually_mono)
        thus ?thesis
          by simp
      next
        case True
        hence ev: "eventually (\<lambda>w. g w \<noteq> g z) (at z)"
          by (auto simp: isolated_zero_def)
  
        have "\<not>g z islimpt pts"
          using \<open>g z \<in> pts\<close> f by (auto simp: meromorphic_on_def)
        hence "eventually (\<lambda>w. w \<notin> pts) (at (g z))"
          by (auto simp: islimpt_conv_frequently_at frequently_def)
        moreover have "g \<midarrow>z\<rightarrow> g z"
          using analytic_at_imp_isCont[OF g'] isContD by blast
        with ev have "filterlim g (at (g z)) (at z)"
          by (auto simp: filterlim_at)
        ultimately have "eventually (\<lambda>w. g w \<notin> pts) (at z)"
          using eventually_compose_filterlim by blast
        hence "z \<in> isolated_points_of (g -` pts \<inter> B)"
          using \<open>g z \<in> pts\<close> \<open>z \<in> B\<close>
          by (auto simp: isolated_points_of_def elim!: eventually_mono)
        with z show ?thesis by simp
      qed
    qed
  qed
  also have "\<dots> = B - isolated_points_of (g -` pts \<inter> B)"
    by blast
  finally show "(\<lambda>x. f (g x)) holomorphic_on B - isolated_points_of (g -` pts \<inter> B)"
    unfolding o_def using analytic_imp_holomorphic by blast
qed (auto simp: isolated_points_of_def \<open>open B\<close>)

lemma meromorphic_on_compose':
  assumes f: "f meromorphic_on A pts" and g: "g holomorphic_on B"
  assumes "open B" and "g ` B \<subseteq> A" and "pts' = (isolated_points_of (g -` pts \<inter> B))"
  shows   "(\<lambda>x. f (g x)) meromorphic_on B pts'"
  using meromorphic_on_compose[OF assms(1-4)] assms(5) by simp

lemma meromorphic_on_inverse': "inverse meromorphic_on UNIV 0"
  unfolding meromorphic_on_def
  by (auto intro!: holomorphic_intros singularity_intros not_essential_inverse 
                   isolated_singularity_at_inverse simp: islimpt_finite)

lemma meromorphic_on_inverse [meromorphic_intros]:
  assumes mero: "f meromorphic_on A pts"
  shows   "(\<lambda>z. inverse (f z)) meromorphic_on A (pts \<union> {z\<in>A. isolated_zero f z})"
proof -
  have "open A"
    using mero by (auto simp: meromorphic_on_def)
  have open': "open (A - pts)"
    by (intro meromorphic_imp_open_diff[OF mero])
  have holo: "f holomorphic_on A - pts"
    using assms by (auto simp: meromorphic_on_def)
  have ana: "f analytic_on A - pts"
    using open' holo by (simp add: analytic_on_open)

  show ?thesis
    unfolding meromorphic_on_def
  proof (intro conjI ballI)
    fix z assume z: "z \<in> pts \<union> {z\<in>A. isolated_zero f z}"
    have "isolated_singularity_at f z \<and> not_essential f z"
    proof (cases "z \<in> pts")
      case False
      have "f holomorphic_on A - pts - {z}"
        by (intro holomorphic_on_subset[OF holo]) auto
      hence "isolated_singularity_at f z"
        by (rule isolated_singularity_at_holomorphic)
           (use z False in \<open>auto intro!: meromorphic_imp_open_diff[OF mero]\<close>)
      moreover have "not_essential f z"
        using z False
        by (intro not_essential_holomorphic[OF holo] meromorphic_imp_open_diff[OF mero]) auto
      ultimately show ?thesis by blast
    qed (use assms in \<open>auto simp: meromorphic_on_def\<close>)
    thus "isolated_singularity_at (\<lambda>z. inverse (f z)) z" "not_essential (\<lambda>z. inverse (f z)) z"
      by (auto intro!: isolated_singularity_at_inverse not_essential_inverse)
  next
    fix z assume "z \<in> A"
    hence "\<not> z islimpt {z\<in>A. isolated_zero f z}"
      by (rule not_islimpt_isolated_zeros[OF mero])
    thus "\<not> z islimpt pts \<union> {z \<in> A. isolated_zero f z}" using \<open>z \<in> A\<close>
      using mero by (auto simp: islimpt_Un meromorphic_on_def)
  next
    show "pts \<union> {z \<in> A. isolated_zero f z} \<subseteq> A"
      using mero by (auto simp: meromorphic_on_def)
  next
    have "(\<lambda>z. inverse (f z)) analytic_on (\<Union>w\<in>A - (pts \<union> {z \<in> A. isolated_zero f z}) . {w})"
      unfolding analytic_on_UN
    proof (intro ballI)
      fix w assume w: "w \<in> A - (pts \<union> {z \<in> A. isolated_zero f z})"
      show "(\<lambda>z. inverse (f z)) analytic_on {w}"
      proof (cases "f w = 0")
        case False
        thus ?thesis using w
          by (intro analytic_intros analytic_on_subset[OF ana]) auto
      next
        case True
        have "eventually (\<lambda>w. f w = 0) (nhds w)"
          using True w by (intro non_isolated_zero analytic_on_subset[OF ana]) auto
        hence "(\<lambda>z. inverse (f z)) analytic_on {w} \<longleftrightarrow> (\<lambda>_. 0) analytic_on {w}"
          using w by (intro analytic_at_cong refl) auto
        thus ?thesis
          by simp
      qed
    qed
    also have "\<dots> = A - (pts \<union> {z \<in> A. isolated_zero f z})"
      by blast
    finally have "(\<lambda>z. inverse (f z)) analytic_on \<dots>" .
    moreover have "open (A - (pts \<union> {z \<in> A. isolated_zero f z}))"
      using closedin_isolated_zeros[OF mero] open' \<open>open A\<close>
      by (metis (no_types, lifting) Diff_Diff_Int Diff_Un closedin_closed open_Diff open_Int)
    ultimately show "(\<lambda>z. inverse (f z)) holomorphic_on A - (pts \<union> {z \<in> A. isolated_zero f z})"
      by (subst (asm) analytic_on_open) auto
  qed (use assms in \<open>auto simp: meromorphic_on_def islimpt_Un 
                          intro!: holomorphic_intros singularity_intros\<close>)
qed

lemma meromorphic_on_inverse'' [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "{z\<in>A. f z = 0} \<subseteq> pts"
  shows   "(\<lambda>z. inverse (f z)) meromorphic_on A pts"
proof -
  have "(\<lambda>z. inverse (f z)) meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
    by (intro meromorphic_on_inverse assms)
  also have "(pts \<union> {z \<in> A. isolated_zero f z}) = pts"
    using assms(2) by (auto simp: isolated_zero_def)
  finally show ?thesis .
qed

lemma meromorphic_on_divide [meromorphic_intros]:
  assumes "f meromorphic_on A pts" and "g meromorphic_on A pts"
  shows   "(\<lambda>z. f z / g z) meromorphic_on A (pts \<union> {z\<in>A. isolated_zero g z})"
proof -
  have mero1: "(\<lambda>z. inverse (g z)) meromorphic_on A (pts \<union> {z\<in>A. isolated_zero g z})"
    by (intro meromorphic_intros assms)
  have sparse: "\<forall>x\<in>A. \<not> x islimpt pts \<union> {z\<in>A. isolated_zero g z}" and "pts \<subseteq> A"
    using mero1 by (auto simp: meromorphic_on_def)
  have mero2: "f meromorphic_on A (pts \<union> {z\<in>A. isolated_zero g z})"
    by (rule meromorphic_on_superset_pts[OF assms(1)]) (use sparse \<open>pts \<subseteq> A\<close> in auto)
  have "(\<lambda>z. f z * inverse (g z)) meromorphic_on A (pts \<union> {z\<in>A. isolated_zero g z})"
    by (intro meromorphic_on_mult mero1 mero2)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma meromorphic_on_divide' [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "g meromorphic_on A pts" "{z\<in>A. g z = 0} \<subseteq> pts"
  shows   "(\<lambda>z. f z / g z) meromorphic_on A pts"
proof -
  have "(\<lambda>z. f z * inverse (g z)) meromorphic_on A pts"
    by (intro meromorphic_intros assms)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma meromorphic_on_cmult_left [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>x. c * f x) meromorphic_on A pts"
  using assms by (intro meromorphic_intros) (auto simp: meromorphic_on_def)

lemma meromorphic_on_cmult_right [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>x. f x * c) meromorphic_on A pts"
  using assms by (intro meromorphic_intros) (auto simp: meromorphic_on_def)

lemma meromorphic_on_scaleR [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>x. c *\<^sub>R f x) meromorphic_on A pts"
  using assms unfolding scaleR_conv_of_real
  by (intro meromorphic_intros) (auto simp: meromorphic_on_def)

lemma meromorphic_on_sum [meromorphic_intros]:
  assumes "\<And>y. y \<in> I \<Longrightarrow> f y meromorphic_on A pts"
  assumes "I \<noteq> {} \<or> open A \<and> pts \<subseteq> A \<and> (\<forall>x\<in>A. \<not>x islimpt pts)"
  shows   "(\<lambda>x. \<Sum>y\<in>I. f y x) meromorphic_on A pts"
proof -
  have *: "open A \<and> pts \<subseteq> A \<and> (\<forall>x\<in>A. \<not>x islimpt pts)"
    using assms(2)
  proof
    assume "I \<noteq> {}"
    then obtain x where "x \<in> I"
      by blast
    from assms(1)[OF this] show ?thesis
      by (auto simp: meromorphic_on_def)
  qed auto
  show ?thesis
    using assms(1)
    by (induction I rule: infinite_finite_induct) (use * in \<open>auto intro!: meromorphic_intros\<close>)
qed

lemma meromorphic_on_prod [meromorphic_intros]:
  assumes "\<And>y. y \<in> I \<Longrightarrow> f y meromorphic_on A pts"
  assumes "I \<noteq> {} \<or> open A \<and> pts \<subseteq> A \<and> (\<forall>x\<in>A. \<not>x islimpt pts)"
  shows   "(\<lambda>x. \<Prod>y\<in>I. f y x) meromorphic_on A pts"
proof -
  have *: "open A \<and> pts \<subseteq> A \<and> (\<forall>x\<in>A. \<not>x islimpt pts)"
    using assms(2)
  proof
    assume "I \<noteq> {}"
    then obtain x where "x \<in> I"
      by blast
    from assms(1)[OF this] show ?thesis
      by (auto simp: meromorphic_on_def)
  qed auto
  show ?thesis
    using assms(1)
    by (induction I rule: infinite_finite_induct) (use * in \<open>auto intro!: meromorphic_intros\<close>)
qed

lemma meromorphic_on_power [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>x. f x ^ n) meromorphic_on A pts"
proof -
  have "(\<lambda>x. \<Prod>i\<in>{..<n}. f x) meromorphic_on A pts"
    by (intro meromorphic_intros assms(1)) (use assms in \<open>auto simp: meromorphic_on_def\<close>)
  thus ?thesis
    by simp
qed

lemma meromorphic_on_power_int [meromorphic_intros]:
  assumes "f meromorphic_on A pts"
  shows   "(\<lambda>z. f z powi n) meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
proof -
  have inv: "(\<lambda>x. inverse (f x)) meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
    by (intro meromorphic_intros assms)
  have *: "f meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
    by (intro meromorphic_on_superset_pts [OF assms(1)])
       (use inv in \<open>auto simp: meromorphic_on_def\<close>)
  show ?thesis
  proof (cases "n \<ge> 0")
    case True   
    have "(\<lambda>x. f x ^ nat n) meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
      by (intro meromorphic_intros *)
    thus ?thesis
      using True by (simp add: power_int_def)
  next
    case False
    have "(\<lambda>x. inverse (f x) ^ nat (-n)) meromorphic_on A (pts \<union> {z \<in> A. isolated_zero f z})"
      by (intro meromorphic_intros assms)
    thus ?thesis
      using False by (simp add: power_int_def)
  qed
qed

lemma meromorphic_on_power_int' [meromorphic_intros]:
  assumes "f meromorphic_on A pts" "n \<ge> 0 \<or> (\<forall>z\<in>A. isolated_zero f z \<longrightarrow> z \<in> pts)"
  shows   "(\<lambda>z. f z powi n) meromorphic_on A pts"
proof (cases "n \<ge> 0")
  case True
  have "(\<lambda>z. f z ^ nat n) meromorphic_on A pts"
    by (intro meromorphic_intros assms)
  thus ?thesis
    using True by (simp add: power_int_def)
next
  case False
  have "(\<lambda>z. f z powi n) meromorphic_on A (pts \<union> {z\<in>A. isolated_zero f z})"
    by (rule meromorphic_on_power_int) fact
  also from assms(2) False have "pts \<union> {z\<in>A. isolated_zero f z} = pts"
    by auto
  finally show ?thesis .
qed

lemma has_laurent_expansion_on_imp_meromorphic_on:
  assumes "open A" 
  assumes laurent: "\<And>z. z \<in> A \<Longrightarrow> \<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F"
  shows   "f meromorphic_on A {z\<in>A. \<not>f analytic_on {z}}"
  unfolding meromorphic_on_def
proof (intro conjI ballI)
  fix z assume "z \<in> {z\<in>A. \<not>f analytic_on {z}}"
  then obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    using laurent[of z] by blast
  from F show "not_essential f z" "isolated_singularity_at f z"
    using has_laurent_expansion_not_essential has_laurent_expansion_isolated by blast+
next
  fix z assume z: "z \<in> A"
  obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    using laurent[of z] \<open>z \<in> A\<close> by blast
  from F have "isolated_singularity_at f z"
    using has_laurent_expansion_isolated z by blast
  then obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    unfolding isolated_singularity_at_def by blast
  have "f analytic_on {w}" if "w \<in> ball z r - {z}" for w
    by (rule analytic_on_subset[OF r(2)]) (use that in auto)
  hence "eventually (\<lambda>w. f analytic_on {w}) (at z)"
    using eventually_at_in_open[of "ball z r" z] \<open>r > 0\<close> by (auto elim!: eventually_mono)
  hence "\<not>z islimpt {w. \<not>f analytic_on {w}}"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
  thus "\<not>z islimpt {w\<in>A. \<not>f analytic_on {w}}"
    using islimpt_subset[of z "{w\<in>A. \<not>f analytic_on {w}}" "{w. \<not>f analytic_on {w}}"] by blast
next
  have "f analytic_on A - {w\<in>A. \<not>f analytic_on {w}}"
    by (subst analytic_on_analytic_at) auto
  thus "f holomorphic_on A - {w\<in>A. \<not>f analytic_on {w}}"
    by (meson analytic_imp_holomorphic)
qed (use assms in auto)

lemma meromorphic_on_imp_has_laurent_expansion:
  assumes "f meromorphic_on A pts" "z \<in> A"
  shows   "(\<lambda>w. f (z + w)) has_laurent_expansion laurent_expansion f z"
proof (cases "z \<in> pts")
  case True
  thus ?thesis
    using assms by (intro not_essential_has_laurent_expansion) (auto simp: meromorphic_on_def)
next
  case False
  have "f holomorphic_on (A - pts)"
    using assms by (auto simp: meromorphic_on_def)
  moreover have "z \<in> A - pts" "open (A - pts)"
    using assms(2) False by (auto intro!: meromorphic_imp_open_diff[OF assms(1)])
  ultimately have "f analytic_on {z}"
    unfolding analytic_at by blast
  thus ?thesis
    using isolated_singularity_at_analytic not_essential_analytic
          not_essential_has_laurent_expansion by blast
qed    

lemma
  assumes "isolated_singularity_at f z" "f \<midarrow>z\<rightarrow> c"
  shows   eventually_remove_sings_eq_nhds':
            "eventually (\<lambda>w. remove_sings f w = (if w = z then c else f w)) (nhds z)"
    and   remove_sings_analytic_at_singularity: "remove_sings f analytic_on {z}"
proof -
  have "eventually (\<lambda>w. w \<noteq> z) (at z)"
    by (auto simp: eventually_at_filter)
  hence "eventually (\<lambda>w. remove_sings f w = (if w = z then c else f w)) (at z)"
    using eventually_remove_sings_eq_at[OF assms(1)]
    by eventually_elim auto
  moreover have "remove_sings f z = c"
    using assms by auto
  ultimately show ev: "eventually (\<lambda>w. remove_sings f w = (if w = z then c else f w)) (nhds z)"
    by (simp add: eventually_at_filter)

  have "(\<lambda>w. if w = z then c else f w) analytic_on {z}"
    by (intro removable_singularity' assms)
  also have "?this \<longleftrightarrow> remove_sings f analytic_on {z}"
    using ev by (intro analytic_at_cong) (auto simp: eq_commute)
  finally show \<dots> .
qed

lemma remove_sings_meromorphic_on:
  assumes "f meromorphic_on A pts" "\<And>z. z \<in> pts - pts' \<Longrightarrow> \<not>is_pole f z" "pts' \<subseteq> pts"
  shows   "remove_sings f meromorphic_on A pts'"
  unfolding meromorphic_on_def
proof safe
  have "remove_sings f analytic_on {z}" if "z \<in> A - pts'" for z
  proof (cases "z \<in> pts")
    case False
    hence *: "f analytic_on {z}"
      using assms meromorphic_imp_open_diff[OF assms(1)] that
      by (force simp: meromorphic_on_def analytic_at) 
    have "remove_sings f analytic_on {z} \<longleftrightarrow> f analytic_on {z}"
      by (intro analytic_at_cong eventually_remove_sings_eq_nhds * refl)
    thus ?thesis using * by simp
  next
    case True
    have isol: "isolated_singularity_at f z"
      using True using assms by (auto simp: meromorphic_on_def)
    from assms(1) have "not_essential f z"
      using True by (auto simp: meromorphic_on_def)
    with assms(2) True that obtain c where "f \<midarrow>z\<rightarrow> c"
      by (auto simp: not_essential_def)
    thus "remove_sings f analytic_on {z}"
      by (intro remove_sings_analytic_at_singularity isol)
  qed
  hence "remove_sings f analytic_on A - pts'"
    by (subst analytic_on_analytic_at) auto
  thus "remove_sings f holomorphic_on A - pts'"
    using meromorphic_imp_open_diff'[OF assms(1,3)] by (subst (asm) analytic_on_open)
qed (use assms islimpt_subset[OF _ assms(3)] in \<open>auto simp: meromorphic_on_def\<close>)

lemma remove_sings_holomorphic_on:
  assumes "f meromorphic_on A pts" "\<And>z. z \<in> pts \<Longrightarrow> \<not>is_pole f z"
  shows   "remove_sings f holomorphic_on A"
  using remove_sings_meromorphic_on[OF assms(1), of "{}"] assms(2)
  by (auto simp: meromorphic_on_no_singularities)

lemma meromorphic_on_Ex_iff:
  "(\<exists>pts. f meromorphic_on A pts) \<longleftrightarrow>
     open A \<and> (\<forall>z\<in>A. \<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F)"
proof safe
  fix pts assume *: "f meromorphic_on A pts"
  from * show "open A"
    by (auto simp: meromorphic_on_def)
  show "\<exists>F. (\<lambda>w. f (z + w)) has_laurent_expansion F" if "z \<in> A" for z
    using that *
    by (intro exI[of _ "laurent_expansion f z"] meromorphic_on_imp_has_laurent_expansion)
qed (blast intro!: has_laurent_expansion_on_imp_meromorphic_on)

lemma is_pole_inverse_holomorphic_pts:
  fixes pts::"complex set" and f::"complex \<Rightarrow> complex"
  defines "g \<equiv> \<lambda>x. (if x\<in>pts then 0 else inverse (f x))"
  assumes mer: "f meromorphic_on D pts"
    and non_z: "\<And>z. z \<in> D - pts \<Longrightarrow> f z \<noteq> 0"
    and all_poles:"\<forall>x. is_pole f x \<longleftrightarrow> x\<in>pts"
  shows "g holomorphic_on D"
proof -
  have "open D" and f_holo: "f holomorphic_on (D-pts)" 
    using mer by (auto simp: meromorphic_on_def)
  have "\<exists>r. r>0 \<and> f analytic_on ball z r - {z} 
            \<and> (\<forall>x \<in> ball z r - {z}. f x\<noteq>0)" if "z\<in>pts" for z 
  proof -
    have "isolated_singularity_at f z" "is_pole f z"
      using mer meromorphic_on_def that all_poles by blast+
    then obtain r1 where "r1>0" and fan: "f analytic_on ball z r1 - {z}"
      by (meson isolated_singularity_at_def)
    obtain r2 where "r2>0" "\<forall>x \<in> ball z r2 - {z}. f x\<noteq>0"
      using non_zero_neighbour_pole[OF \<open>is_pole f z\<close>] 
      unfolding eventually_at by (metis Diff_iff UNIV_I dist_commute insertI1 mem_ball)
    define r where "r = min r1 r2"
    have "r>0" by (simp add: \<open>0 < r2\<close> \<open>r1>0\<close> r_def)
    moreover have "f analytic_on ball z r - {z}"
      using r_def by (force intro: analytic_on_subset [OF fan])
    moreover have "\<forall>x \<in> ball z r - {z}. f x\<noteq>0"
      by (simp add: \<open>\<forall>x\<in>ball z r2 - {z}. f x \<noteq> 0\<close> r_def)
    ultimately show ?thesis by auto
  qed
  then obtain get_r where r_pos:"get_r z>0" 
      and r_ana:"f analytic_on ball z (get_r z) - {z}"
      and r_nz:"\<forall>x \<in> ball z (get_r z) - {z}. f x\<noteq>0"
    if "z\<in>pts" for z
    by metis
  define p_balls where "p_balls \<equiv> \<Union>z\<in>pts. ball z (get_r z)"
  have g_ball:"g holomorphic_on ball z (get_r z)" if "z\<in>pts" for z
  proof -
    have "(\<lambda>x. if x = z then 0 else inverse (f x)) holomorphic_on ball z (get_r z)"
    proof (rule is_pole_inverse_holomorphic)
      show "f holomorphic_on ball z (get_r z) - {z}"
        using analytic_imp_holomorphic r_ana that by blast
      show "is_pole f z"
        using mer meromorphic_on_def that all_poles by force
      show "\<forall>x\<in>ball z (get_r z) - {z}. f x \<noteq> 0"
        using r_nz that by metis
    qed auto
    then show ?thesis unfolding g_def
      by (smt (verit, ccfv_SIG) Diff_iff Elementary_Metric_Spaces.open_ball
          all_poles analytic_imp_holomorphic empty_iff 
          holomorphic_transform insert_iff not_is_pole_holomorphic 
          open_delete r_ana that)
  qed
  then have "g holomorphic_on p_balls" 
  proof -
    have "g analytic_on p_balls"
      unfolding p_balls_def analytic_on_UN
      using g_ball by (simp add: analytic_on_open)
    moreover have "open p_balls" using p_balls_def by blast
    ultimately show ?thesis 
      by (simp add: analytic_imp_holomorphic)
  qed
  moreover have "g holomorphic_on D-pts" 
  proof -
    have "(\<lambda>z. inverse (f z)) holomorphic_on D - pts"
      using f_holo holomorphic_on_inverse non_z by blast
    then show ?thesis
      by (metis DiffD2 g_def holomorphic_transform) 
  qed
  moreover have "open p_balls" 
    using p_balls_def by blast
  ultimately have "g holomorphic_on (p_balls \<union> (D-pts))"
    by (simp add: holomorphic_on_Un meromorphic_imp_open_diff[OF mer])
  moreover have "D \<subseteq> p_balls \<union> (D-pts)"
    unfolding p_balls_def using \<open>\<And>z. z \<in> pts \<Longrightarrow> 0 < get_r z\<close> by force
  ultimately show "g holomorphic_on D" by (meson holomorphic_on_subset)
qed

lemma meromorphic_imp_analytic_on:
  assumes "f meromorphic_on D pts"
  shows "f analytic_on (D - pts)"
  by (metis assms analytic_on_open meromorphic_imp_open_diff meromorphic_on_def)

lemma meromorphic_imp_constant_on:
  assumes merf: "f meromorphic_on D pts" 
      and "f constant_on (D - pts)"
      and "\<forall>x\<in>pts. is_pole f x"
    shows "f constant_on D"
proof -
  obtain c where c:"\<And>z. z \<in> D-pts \<Longrightarrow> f z = c"
    by (meson assms constant_on_def)

  have "f z = c" if "z \<in> D" for z
  proof (cases "is_pole f z")
    case True
    then obtain r0 where "r0 > 0" and r0: "f analytic_on ball z r0 - {z}" and pol: "is_pole f z"
      using merf unfolding meromorphic_on_def isolated_singularity_at_def 
      by (metis \<open>z \<in> D\<close> insert_Diff insert_Diff_if insert_iff merf 
          meromorphic_imp_open_diff not_is_pole_holomorphic)
    have "open D"
      using merf meromorphic_on_def by auto
    then obtain r where "r > 0" "ball z r \<subseteq> D" "r \<le> r0"
      by (smt (verit, best) \<open>0 < r0\<close> \<open>z \<in> D\<close> openE order_subst2 subset_ball)
    have r: "f analytic_on ball z r - {z}"
      by (meson Diff_mono \<open>r \<le> r0\<close> analytic_on_subset order_refl r0 subset_ball)
    have "ball z r - {z} \<subseteq> -pts"
      using merf r unfolding meromorphic_on_def
      by (meson ComplI Elementary_Metric_Spaces.open_ball 
          analytic_imp_holomorphic assms(3) not_is_pole_holomorphic open_delete subsetI)
    with \<open>ball z r \<subseteq> D\<close> have "ball z r - {z} \<subseteq> D-pts"
      by fastforce
    with c have c': "\<And>u. u \<in> ball z r - {z} \<Longrightarrow> f u = c"
      by blast    
    have False if "\<forall>\<^sub>F x in at z. cmod c + 1 \<le> cmod (f x)"
    proof -
      have "\<forall>\<^sub>F x in at z within ball z r - {z}. cmod c + 1 \<le> cmod (f x)"
        by (smt (verit, best) Diff_UNIV Diff_eq_empty_iff eventually_at_topological insert_subset that)
      with \<open>r > 0\<close> show ?thesis
        apply (simp add: c' eventually_at_filter topological_space_class.eventually_nhds open_dist)
        by (metis dist_commute min_less_iff_conj perfect_choose_dist)
    qed
    with pol show ?thesis
      by (auto simp: is_pole_def filterlim_at_infinity_conv_norm_at_top filterlim_at_top)
  next
    case False
    then show ?thesis by (meson DiffI assms(3) c that)
  qed 
  then show ?thesis
    by (simp add: constant_on_def)
qed


lemma meromorphic_isolated:
  assumes merf: "f meromorphic_on D pts" and "p\<in>pts"
  obtains r where "r>0" "ball p r \<subseteq> D" "ball p r \<inter> pts = {p}"
proof -
  have "\<forall>z\<in>D. \<exists>e>0. finite (pts \<inter> ball z e)" 
    using merf unfolding meromorphic_on_def islimpt_eq_infinite_ball
    by auto
  then obtain r0 where r0:"r0>0" "finite (pts \<inter> ball p r0)"
    by (metis assms(2) in_mono merf meromorphic_on_def)
  moreover define pts' where "pts' = pts \<inter> ball p r0 - {p}"
  ultimately have "finite pts'"
    by simp
  
  define r1 where "r1=(if pts'={} then r0 else 
                          min (Min {dist p' p |p'. p'\<in>pts'}/2) r0)"
  have "r1>0 \<and> pts \<inter> ball p r1 - {p} = {}"
  proof (cases "pts'={}")
    case True
    then show ?thesis 
      using pts'_def r0(1) r1_def by presburger
  next
    case False
    define S where "S={dist p' p |p'. p'\<in>pts'}"

    have nempty:"S \<noteq> {}"
      using False S_def by blast
    have finite:"finite S"
      using \<open>finite pts'\<close> S_def by simp

    have "r1>0"
    proof -
      have "r1=min (Min S/2) r0"
        using False unfolding S_def r1_def by auto
      moreover have "Min S\<in>S"
        using \<open>S\<noteq>{}\<close> \<open>finite S\<close>  Min_in by auto
      then have "Min S>0" unfolding S_def 
        using pts'_def by force
      ultimately show ?thesis using \<open>r0>0\<close> by auto
    qed
    moreover have "pts \<inter> ball p r1 - {p} = {}"
    proof (rule ccontr)
      assume "pts \<inter> ball p r1 - {p} \<noteq> {}"
      then obtain p' where "p'\<in>pts \<inter> ball p r1 - {p}" by blast
      moreover have "r1\<le>r0" using r1_def by auto
      ultimately have "p'\<in>pts'" unfolding pts'_def 
        by auto
      then have "dist p' p\<ge>Min S" 
        using S_def eq_Min_iff local.finite by blast
      moreover have "dist p' p < Min S"
        using \<open>p'\<in>pts \<inter> ball p r1 - {p}\<close> False unfolding r1_def
        apply (fold S_def)
        by (smt (verit, ccfv_threshold) DiffD1 Int_iff dist_commute 
            dist_triangle_half_l mem_ball)
      ultimately show False by auto
    qed
    ultimately show ?thesis by auto
  qed
  then have "r1>0" and r1_pts:"pts \<inter> ball p r1 - {p} = {}" by auto

  obtain r2 where "r2>0" "ball p r2 \<subseteq> D"
    by (metis assms(2) merf meromorphic_on_def openE subset_eq)
  define r where "r=min r1 r2"
  have "r > 0" unfolding r_def 
    by (simp add: \<open>0 < r1\<close> \<open>0 < r2\<close>)
  moreover have "ball p r \<subseteq> D" 
    using \<open>ball p r2 \<subseteq> D\<close> r_def by auto
  moreover have "ball p r \<inter> pts = {p}"
    using assms(2) \<open>r>0\<close> r1_pts
    unfolding r_def by auto
  ultimately show ?thesis using that by auto
qed

lemma meromorphic_pts_closure:
  assumes merf: "f meromorphic_on D pts" 
  shows "pts \<subseteq> closure (D - pts)"
proof -
  have "p islimpt (D - pts)" if "p\<in>pts" for p 
  proof -
    obtain r where "r>0" "ball p r \<subseteq> D" "ball p r \<inter> pts = {p}"
      using meromorphic_isolated[OF merf \<open>p\<in>pts\<close>] by auto
    from \<open>r>0\<close>
    have "p islimpt ball p r - {p}"
      by (meson open_ball ball_subset_cball in_mono islimpt_ball 
          islimpt_punctured le_less open_contains_ball_eq)
    moreover have " ball p r - {p} \<subseteq> D - pts"
      using \<open>ball p r \<inter> pts = {p}\<close> \<open>ball p r \<subseteq> D\<close> by fastforce
    ultimately show ?thesis 
      using islimpt_subset by auto
  qed
  then show ?thesis by (simp add: islimpt_in_closure subset_eq)
qed

lemma nconst_imp_nzero_neighbour:
  assumes merf: "f meromorphic_on D pts" 
    and f_nconst:"\<not>(\<forall>w\<in>D-pts. f w=0)"
    and "z\<in>D" and "connected D"
  shows "(\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w \<in> D - pts)"
proof -
  obtain \<beta> where \<beta>:"\<beta> \<in> D - pts" "f \<beta>\<noteq>0"
    using f_nconst by auto

  have ?thesis if "z\<notin>pts" 
  proof -
    have "\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w \<in> D - pts"
      apply (rule non_zero_neighbour_alt[of f "D-pts" z  \<beta>])
      subgoal using merf meromorphic_on_def by blast
      subgoal using merf meromorphic_imp_open_diff by auto
      subgoal using assms(4) merf meromorphic_imp_connected_diff by blast
      subgoal by (simp add: assms(3) that)
      using \<beta> by auto
    then show ?thesis by (auto elim:eventually_mono)
  qed
  moreover have ?thesis if "z\<in>pts" "\<not> f \<midarrow>z\<rightarrow> 0" 
  proof -
    have "\<forall>\<^sub>F w in at z. w \<in> D - pts"
      using merf[unfolded meromorphic_on_def islimpt_iff_eventually] \<open>z\<in>D\<close>
      using eventually_at_in_open' eventually_elim2 by fastforce
    moreover have "\<forall>\<^sub>F w in at z. f w \<noteq> 0" 
    proof (cases  "is_pole f z")
      case True
      then show ?thesis using non_zero_neighbour_pole by auto
    next
      case False
      moreover have "not_essential f z"
        using merf meromorphic_on_def that(1) by fastforce
      ultimately obtain c where "c\<noteq>0" "f \<midarrow>z\<rightarrow> c"
        by (metis \<open>\<not> f \<midarrow>z\<rightarrow> 0\<close> not_essential_def)
      then show ?thesis 
        using tendsto_imp_eventually_ne by auto
    qed
    ultimately show ?thesis by eventually_elim auto
  qed
  moreover have ?thesis if "z\<in>pts" "f \<midarrow>z\<rightarrow> 0" 
  proof -
    define ff where "ff=(\<lambda>x. if x=z then 0 else f x)"
    define A where "A=D - (pts - {z})"

    have "f holomorphic_on A - {z}"
      by (metis A_def Diff_insert analytic_imp_holomorphic 
            insert_Diff merf meromorphic_imp_analytic_on that(1))
    moreover have "open A"  
      using A_def merf meromorphic_imp_open_diff' by force
    ultimately have "ff holomorphic_on A" 
      using \<open>f \<midarrow>z\<rightarrow> 0\<close> unfolding ff_def
      by (rule removable_singularity)
    moreover have "connected A"
    proof -
      have "connected (D - pts)" 
        using assms(4) merf meromorphic_imp_connected_diff by auto
      moreover have "D - pts \<subseteq> A"
        unfolding A_def by auto
      moreover have "A \<subseteq> closure (D - pts)" unfolding A_def
        by (smt (verit, ccfv_SIG) Diff_empty Diff_insert 
            closure_subset insert_Diff_single insert_absorb 
            insert_subset merf meromorphic_pts_closure that(1))
      ultimately show ?thesis using connected_intermediate_closure 
        by auto
    qed
    moreover have "z \<in> A" using A_def assms(3) by blast
    moreover have "ff z = 0" unfolding ff_def by auto
    moreover have "\<beta> \<in> A " using A_def \<beta>(1) by blast
    moreover have "ff \<beta> \<noteq> 0" using \<beta>(1) \<beta>(2) ff_def that(1) by auto
    ultimately obtain r where "0 < r" 
        "ball z r \<subseteq> A" "\<And>x. x \<in> ball z r - {z} \<Longrightarrow> ff x \<noteq> 0"
      using \<open>open A\<close> isolated_zeros[of ff A z \<beta>] by auto
    then show ?thesis unfolding eventually_at ff_def
      by (intro exI[of _ r]) (auto simp: A_def dist_commute ball_def)
  qed
  ultimately show ?thesis by auto
qed

lemma nconst_imp_nzero_neighbour':
  assumes merf: "f meromorphic_on D pts" 
    and f_nconst:"\<not>(\<forall>w\<in>D-pts. f w=0)"
    and "z\<in>D" and "connected D"
  shows "\<forall>\<^sub>F w in at z. f w \<noteq> 0"
  using nconst_imp_nzero_neighbour[OF assms]
  by (auto elim:eventually_mono)

lemma meromorphic_compact_finite_zeros:
  assumes merf:"f meromorphic_on D pts" 
    and "compact S" "S \<subseteq> D" "connected D"
    and f_nconst:"\<not>(\<forall>w\<in>D-pts. f w=0)"
  shows "finite ({x\<in>S. f x=0})"
proof -
  have "finite ({x\<in>S. f x=0 \<and> x \<notin> pts})" 
  proof (rule ccontr)
    assume "infinite {x \<in> S. f x = 0 \<and> x \<notin> pts}"
    then obtain z where "z\<in>S" and z_lim:"z islimpt {x \<in> S. f x = 0
                                              \<and> x \<notin> pts}"
      using \<open>compact S\<close> unfolding compact_eq_Bolzano_Weierstrass
      by auto
  
    from z_lim
    have "\<exists>\<^sub>F x in at z. f x = 0 \<and> x \<in> S \<and> x \<notin> pts"
      unfolding islimpt_iff_eventually not_eventually by simp
    moreover have "\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w \<in> D - pts"
      using nconst_imp_nzero_neighbour[OF merf f_nconst _ \<open>connected D\<close>]
        \<open>z\<in>S\<close> \<open>S \<subseteq> D\<close>
      by auto
    ultimately have "\<exists>\<^sub>F x in at z. False"
      by (simp add: eventually_mono frequently_def)
    then show False by auto
  qed
  moreover have "finite (S \<inter> pts)" 
    using meromorphic_compact_finite_pts[OF merf \<open>compact S\<close> \<open>S \<subseteq> D\<close>] .
  ultimately have "finite ({x\<in>S. f x=0 \<and> x \<notin> pts} \<union> (S \<inter> pts))"
    unfolding finite_Un by auto 
  then show ?thesis by (elim rev_finite_subset) auto
qed

lemma meromorphic_onI [intro?]:
  assumes "open A" "pts \<subseteq> A"
  assumes "f holomorphic_on A - pts" "\<And>z. z \<in> A \<Longrightarrow> \<not>z islimpt pts"
  assumes "\<And>z. z \<in> pts \<Longrightarrow> isolated_singularity_at f z"
  assumes "\<And>z. z \<in> pts \<Longrightarrow> not_essential f z"
  shows   "f meromorphic_on A pts"
  using assms unfolding meromorphic_on_def by blast

lemma Polygamma_plus_of_nat:
  assumes "\<forall>k<m. z \<noteq> -of_nat k"
  shows   "Polygamma n (z + of_nat m) =
             Polygamma n z + (-1) ^ n * fact n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n)"
  using assms
proof (induction m)
  case (Suc m)
  have "Polygamma n (z + of_nat (Suc m)) = Polygamma n (z + of_nat m + 1)"
    by (simp add: add_ac)
  also have "\<dots> = Polygamma n (z + of_nat m) + (-1) ^ n * fact n * (1 / ((z + of_nat m) ^ Suc n))"
    using Suc.prems by (subst Polygamma_plus1) (auto simp: add_eq_0_iff2)
  also have "Polygamma n (z + of_nat m) =
               Polygamma n z + (-1) ^ n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n) * fact n"
    using Suc.prems by (subst Suc.IH) auto
  finally show ?case
    by (simp add: algebra_simps)
qed auto

lemma tendsto_Gamma [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma (f z)) \<longlongrightarrow> Gamma c) F"
  by (intro isCont_tendsto_compose[OF _ assms(1)] continuous_intros assms)

lemma tendsto_Polygamma [tendsto_intros]:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field,euclidean_space}"
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Polygamma n (f z)) \<longlongrightarrow> Polygamma n c) F"
  by (intro isCont_tendsto_compose[OF _ assms(1)] continuous_intros assms)

lemma analytic_on_Gamma' [analytic_intros]:
  assumes "f analytic_on A" "\<forall>x\<in>A. f x \<notin> \<int>\<^sub>\<le>\<^sub>0" 
  shows   "(\<lambda>z. Gamma (f z)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_Gamma[of "f ` A"]] assms(2)
  by (auto simp: o_def)

lemma analytic_on_Polygamma' [analytic_intros]:
  assumes "f analytic_on A" "\<forall>x\<in>A. f x \<notin> \<int>\<^sub>\<le>\<^sub>0" 
  shows   "(\<lambda>z. Polygamma n (f z)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_on_Polygamma[of "f ` A" n]] assms(2)
  by (auto simp: o_def)

lemma
  shows is_pole_Polygamma: "is_pole (Polygamma n) (-of_nat m :: complex)"
  and   zorder_Polygamma:  "zorder (Polygamma n) (-of_nat m) = -int (Suc n)"
  and   residue_Polygamma: "residue (Polygamma n) (-of_nat m) = (if n = 0 then -1 else 0)"
proof -
  define g1 :: "complex \<Rightarrow> complex" where
    "g1 = (\<lambda>z. Polygamma n (z + of_nat (Suc m)) +
              (-1) ^ Suc n * fact n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n))"
  define g :: "complex \<Rightarrow> complex" where
    "g = (\<lambda>z. g1 z + (-1) ^ Suc n * fact n / (z + of_nat m) ^ Suc n)"
  define F where "F = fps_to_fls (fps_expansion g1 (-of_nat m)) + fls_const ((-1) ^ Suc n * fact n) / fls_X ^ Suc n"
  have F_altdef: "F = fps_to_fls (fps_expansion g1 (-of_nat m)) + fls_shift (n+1) (fls_const ((-1) ^ Suc n * fact n))"
    by (simp add: F_def del: power_Suc)

  have "\<not>(-of_nat m) islimpt (\<int>\<^sub>\<le>\<^sub>0 :: complex set)"
    by (intro discrete_imp_not_islimpt[where e = 1])
       (auto elim!: nonpos_Ints_cases simp: dist_of_int)
  hence "eventually (\<lambda>z::complex. z \<notin> \<int>\<^sub>\<le>\<^sub>0) (at (-of_nat m))"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
  hence ev: "eventually (\<lambda>z. Polygamma n z = g z) (at (-of_nat m))"
  proof eventually_elim
    case (elim z)
    hence *: "\<forall>k<Suc m. z \<noteq> - of_nat k"
      by auto
    thus ?case
      using Polygamma_plus_of_nat[of "Suc m" z n, OF *]
      by (auto simp: g_def g1_def algebra_simps)
  qed

  have "(\<lambda>w. g (-of_nat m + w)) has_laurent_expansion F"
    unfolding g_def F_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps analytic_at_imp_has_fps_expansion)
       (auto simp: g1_def intro!: laurent_expansion_intros analytic_intros)
  also have "?this \<longleftrightarrow> (\<lambda>w. Polygamma n (-of_nat m + w)) has_laurent_expansion F"
    using ev by (intro has_laurent_expansion_cong refl)
                (simp_all add: eq_commute at_to_0' eventually_filtermap)
  finally have *: "(\<lambda>w. Polygamma n (-of_nat m + w)) has_laurent_expansion F" .

  have subdegree: "fls_subdegree F = -int (Suc n)" unfolding F_def
    by (subst fls_subdegree_add_eq2) (simp_all add: fls_subdegree_fls_to_fps fls_divide_subdegree)
  have [simp]: "F \<noteq> 0"
    using subdegree by auto
  
  show "is_pole (Polygamma n) (-of_nat m :: complex)"
    using * by (rule has_laurent_expansion_imp_is_pole) (auto simp: subdegree)
  show "zorder (Polygamma n) (-of_nat m :: complex) = -int (Suc n)"
    by (subst has_laurent_expansion_zorder[OF *]) (auto simp: subdegree)
  show "residue (Polygamma n) (-of_nat m :: complex) = (if n = 0 then -1 else 0)"
    by (subst has_laurent_expansion_residue[OF *]) (auto simp: F_altdef)
qed

lemma Gamma_meromorphic_on [meromorphic_intros]: "Gamma meromorphic_on UNIV \<int>\<^sub>\<le>\<^sub>0"
proof
  show "\<not>z islimpt \<int>\<^sub>\<le>\<^sub>0" for z :: complex
    by (intro discrete_imp_not_islimpt[of 1]) (auto elim!: nonpos_Ints_cases simp: dist_of_int)
next
  fix z :: complex assume z: "z \<in> \<int>\<^sub>\<le>\<^sub>0"
  then obtain n where n: "z = -of_nat n"
    by (elim nonpos_Ints_cases')
  show "not_essential Gamma z"
    by (auto simp: n intro!: is_pole_imp_not_essential is_pole_Gamma)
  have *: "open (-(\<int>\<^sub>\<le>\<^sub>0 - {z}))"
    by (intro open_Compl discrete_imp_closed[of 1]) (auto elim!: nonpos_Ints_cases simp: dist_of_int)
  have "Gamma holomorphic_on -(\<int>\<^sub>\<le>\<^sub>0 - {z}) - {z}"
    by (intro holomorphic_intros) auto
  thus "isolated_singularity_at Gamma z"
    by (rule isolated_singularity_at_holomorphic) (use z * in auto)
qed (auto intro!: holomorphic_intros)

lemma Polygamma_meromorphic_on [meromorphic_intros]: "Polygamma n meromorphic_on UNIV \<int>\<^sub>\<le>\<^sub>0"
proof
  show "\<not>z islimpt \<int>\<^sub>\<le>\<^sub>0" for z :: complex
    by (intro discrete_imp_not_islimpt[of 1]) (auto elim!: nonpos_Ints_cases simp: dist_of_int)
next
  fix z :: complex assume z: "z \<in> \<int>\<^sub>\<le>\<^sub>0"
  then obtain m where n: "z = -of_nat m"
    by (elim nonpos_Ints_cases')
  show "not_essential (Polygamma n) z"
    by (auto simp: n intro!: is_pole_imp_not_essential is_pole_Polygamma)
  have *: "open (-(\<int>\<^sub>\<le>\<^sub>0 - {z}))"
    by (intro open_Compl discrete_imp_closed[of 1]) (auto elim!: nonpos_Ints_cases simp: dist_of_int)
  have "Polygamma n holomorphic_on -(\<int>\<^sub>\<le>\<^sub>0 - {z}) - {z}"
    by (intro holomorphic_intros) auto
  thus "isolated_singularity_at (Polygamma n) z"
    by (rule isolated_singularity_at_holomorphic) (use z * in auto)
qed (auto intro!: holomorphic_intros)


theorem argument_principle':
  fixes f::"complex \<Rightarrow> complex" and poles s:: "complex set"
  \<comment> \<open>\<^term>\<open>pz\<close> is the set of non-essential singularities and zeros\<close>
  defines "pz \<equiv> {w\<in>s. f w = 0 \<or> w \<in> poles}"
  assumes "open s" and
          "connected s" and
          f_holo:"f holomorphic_on s-poles" and
          h_holo:"h holomorphic_on s" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          path_img:"path_image g \<subseteq> s - pz" and
          homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number g z = 0" and
          finite:"finite pz" and
          poles:"\<forall>p\<in>s\<inter>poles. not_essential f p"
  shows "contour_integral g (\<lambda>x. deriv f x * h x / f x) = 2 * pi * \<i> *
          (\<Sum>p\<in>pz. winding_number g p * h p * zorder f p)"
proof -
  define ff where "ff = remove_sings f"

  have finite':"finite (s \<inter> poles)"  
    using finite unfolding pz_def by (auto elim:rev_finite_subset)

  have isolated:"isolated_singularity_at f z" if "z\<in>s" for z 
  proof (rule isolated_singularity_at_holomorphic)
    show "f holomorphic_on (s-(poles-{z})) - {z}" 
      by (metis Diff_empty Diff_insert Diff_insert0 Diff_subset 
          f_holo holomorphic_on_subset insert_Diff)
    show "open (s - (poles - {z}))" 
      by (metis Diff_Diff_Int Int_Diff assms(2) finite' finite_Diff 
          finite_imp_closed inf.idem open_Diff)
    show "z \<in> s - (poles - {z})" 
      using assms(4) that by auto
  qed

  have not_ess:"not_essential f w" if "w\<in>s" for w 
    by (metis Diff_Diff_Int Diff_iff Int_Diff Int_absorb assms(2) 
        f_holo finite' finite_imp_closed not_essential_holomorphic 
        open_Diff poles that)

  have nzero:"\<forall>\<^sub>F x in at w. f x \<noteq> 0" if "w\<in>s" for w
  proof (rule ccontr) 
    assume "\<not> (\<forall>\<^sub>F x in at w. f x \<noteq> 0)"
    then have "\<exists>\<^sub>F x in at w. f x = 0" 
      unfolding not_eventually by simp
    moreover have "\<forall>\<^sub>F x in at w. x\<in>s" 
      by (simp add: assms(2) eventually_at_in_open' that)
    ultimately have "\<exists>\<^sub>F x in at w. x\<in>{w\<in>s. f w = 0}" 
      apply (elim frequently_rev_mp)
      by (auto elim:eventually_mono)
    from frequently_at_imp_islimpt[OF this] 
    have "w islimpt {w \<in> s. f w = 0}" .
    then have "infinite({w \<in> s. f w = 0} \<inter> ball w 1)"
      unfolding islimpt_eq_infinite_ball by auto
    then have "infinite({w \<in> s. f w = 0})"
      by auto
    then have "infinite pz" unfolding pz_def 
      by (smt (verit) Collect_mono_iff rev_finite_subset)
    then show False using finite by auto
  qed

  obtain pts' where pts':"pts' \<subseteq> s \<inter> poles" 
    "finite pts'" "ff holomorphic_on s - pts'" "\<forall>x\<in>pts'. is_pole ff x"
    apply (elim get_all_poles_from_remove_sings
        [of f,folded ff_def,rotated -1])
    subgoal using f_holo by fastforce
    using \<open>open s\<close> poles finite' by auto

  have pts'_sub_pz:"{w \<in> s. ff w = 0 \<or> w \<in> pts'} \<subseteq> pz"
  proof -
    have "w\<in>poles" if "w\<in>s" "w\<in>pts'" for w 
      by (meson in_mono le_infE pts'(1) that(2))
    moreover have "f w=0" if" w\<in>s" "w\<notin>poles" "ff w=0" for w
    proof -
      have "\<not> is_pole f w"
        by (metis DiffI Diff_Diff_Int Diff_subset assms(2) f_holo 
            finite' finite_imp_closed inf.absorb_iff2 
            not_is_pole_holomorphic open_Diff that(1) that(2))
      then have "f \<midarrow>w\<rightarrow> 0" 
        using remove_sings_eq_0_iff[OF not_ess[OF \<open>w\<in>s\<close>]] \<open>ff w=0\<close>
        unfolding ff_def by auto
      moreover have "f analytic_on {w}" 
        using that(1,2) finite' f_holo assms(2)
        by (metis Diff_Diff_Int Diff_empty Diff_iff Diff_subset 
            double_diff finite_imp_closed 
            holomorphic_on_imp_analytic_at open_Diff)
      ultimately show ?thesis 
        using ff_def remove_sings_at_analytic that(3) by presburger
    qed
    ultimately show ?thesis unfolding pz_def by auto
  qed


  have "contour_integral g (\<lambda>x. deriv f x * h x / f x)
          = contour_integral g (\<lambda>x. deriv ff x * h x / ff x)"
  proof (rule contour_integral_eq)
    fix x assume "x \<in> path_image g" 
    have "f analytic_on {x}"
    proof (rule holomorphic_on_imp_analytic_at[of _ "s-poles"])
      from finite' 
      show "open (s - poles)" 
        using \<open>open s\<close> 
        by (metis Diff_Compl Diff_Diff_Int Diff_eq finite_imp_closed 
            open_Diff)
      show "x \<in> s - poles"
        using path_img \<open>x \<in> path_image g\<close> unfolding pz_def by auto
    qed (use f_holo in simp)
    then show "deriv f x * h x / f x = deriv ff x * h x / ff x"
      unfolding ff_def by auto
  qed
  also have "... = complex_of_real (2 * pi) * \<i> *
                      (\<Sum>p\<in>{w \<in> s. ff w = 0 \<or> w \<in> pts'}. 
                        winding_number g p * h p * of_int (zorder ff p))"
  proof (rule argument_principle[OF \<open>open s\<close> \<open>connected s\<close>, of ff pts' h g])
    show "path_image g \<subseteq> s - {w \<in> s. ff w = 0 \<or> w \<in> pts'}"
      using path_img pts'_sub_pz  by auto
    show "finite {w \<in> s. ff w = 0 \<or> w \<in> pts'}" 
      using pts'_sub_pz finite 
      using rev_finite_subset by blast  
  qed (use pts' assms in auto)
  also have "... = 2 * pi * \<i> *
          (\<Sum>p\<in>pz. winding_number g p * h p * zorder f p)"
  proof -
    have "(\<Sum>p\<in>{w \<in> s. ff w = 0 \<or> w \<in> pts'}.
       winding_number g p * h p * of_int (zorder ff p)) =
      (\<Sum>p\<in>pz. winding_number g p * h p * of_int (zorder f p))"
    proof (rule sum.mono_neutral_cong_left)
      have "zorder f w = 0" 
        if "w\<in>s" " f w = 0 \<or> w \<in> poles" "ff w \<noteq> 0" " w \<notin> pts'"
        for w
      proof -
        define F where "F=laurent_expansion f w"
        have has_l:"(\<lambda>x. f (w + x)) has_laurent_expansion F"
          unfolding F_def
          apply (rule not_essential_has_laurent_expansion)
          using isolated not_ess \<open>w\<in>s\<close> by auto
        from has_laurent_expansion_eventually_nonzero_iff[OF this]
        have "F \<noteq>0"
          using nzero \<open>w\<in>s\<close> by auto
        from tendsto_0_subdegree_iff[OF has_l this] 
        have "f \<midarrow>w\<rightarrow> 0 = (0 < fls_subdegree F)" .
        moreover have "\<not> (is_pole f w \<or> f \<midarrow>w\<rightarrow> 0)"
          using remove_sings_eq_0_iff[OF not_ess[OF \<open>w\<in>s\<close>]] \<open>ff w \<noteq> 0\<close>
          unfolding ff_def by auto
        moreover have "is_pole f w = (fls_subdegree F < 0)"
          using is_pole_fls_subdegree_iff[OF has_l] .
        ultimately have "fls_subdegree F = 0" by auto
        then show ?thesis
          using has_laurent_expansion_zorder[OF has_l \<open>F\<noteq>0\<close>] by auto
      qed
      then show "\<forall>i\<in>pz - {w \<in> s. ff w = 0 \<or> w \<in> pts'}.
        winding_number g i * h i * of_int (zorder f i) = 0" 
        unfolding pz_def by auto
      show "\<And>x. x \<in> {w \<in> s. ff w = 0 \<or> w \<in> pts'} \<Longrightarrow>
         winding_number g x * h x * of_int (zorder ff x) =
         winding_number g x * h x * of_int (zorder f x)"
        using isolated zorder_remove_sings[of f,folded ff_def] by auto
    qed (use pts'_sub_pz finite in auto)
    then show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma meromorphic_on_imp_isolated_singularity:
  assumes "f meromorphic_on D pts" "z \<in> D"
  shows   "isolated_singularity_at f z"
  by (meson DiffI assms(1) assms(2) holomorphic_on_imp_analytic_at isolated_singularity_at_analytic 
        meromorphic_imp_open_diff meromorphic_on_def)

lemma meromorphic_imp_not_is_pole:
  assumes "f meromorphic_on D pts" "z \<in> D - pts"
  shows   "\<not>is_pole f z"
proof -
  from assms have "f analytic_on {z}"
    using meromorphic_on_imp_analytic_at by blast
  thus ?thesis
    using analytic_at not_is_pole_holomorphic by blast
qed

lemma meromorphic_all_poles_iff_empty [simp]: "f meromorphic_on pts pts \<longleftrightarrow> pts = {}"
  by (auto simp: meromorphic_on_def holomorphic_on_def open_imp_islimpt)

lemma meromorphic_imp_nonsingular_point_exists:
  assumes "f meromorphic_on A pts" "A \<noteq> {}"
  obtains x where "x \<in> A - pts"
proof -
  have "A \<noteq> pts"
    using assms by auto
  moreover have "pts \<subseteq> A"
    using assms by (auto simp: meromorphic_on_def)
  ultimately show ?thesis
    using that by blast
qed

lemma meromorphic_frequently_const_imp_const:
  assumes "f meromorphic_on A pts" "connected A"
  assumes "frequently (\<lambda>w. f w = c) (at z)"
  assumes "z \<in> A - pts"
  assumes "w \<in> A - pts"
  shows   "f w = c"
proof -
  have "f w - c = 0"
  proof (rule analytic_continuation[where f = "\<lambda>z. f z - c"])
    show "(\<lambda>z. f z - c) holomorphic_on (A - pts)"
      by (intro holomorphic_intros meromorphic_imp_holomorphic[OF assms(1)])
    show [intro]: "open (A - pts)"
      using assms meromorphic_imp_open_diff by blast
    show "connected (A - pts)"
      using assms meromorphic_imp_connected_diff by blast
    show "{z\<in>A-pts. f z = c} \<subseteq> A - pts"
      by blast
    have "eventually (\<lambda>z. z \<in> A - pts) (at z)"
      using assms by (intro eventually_at_in_open') auto
    hence "frequently (\<lambda>z. f z = c \<and> z \<in> A - pts) (at z)"
      by (intro frequently_eventually_frequently assms)
    thus "z islimpt {z\<in>A-pts. f z = c}"
      by (simp add: islimpt_conv_frequently_at conj_commute)
  qed (use assms in auto)
  thus ?thesis
    by simp
qed

lemma meromorphic_imp_eventually_neq:
  assumes "f meromorphic_on A pts" "connected A" "\<not>f constant_on A - pts"
  assumes "z \<in> A - pts"
  shows   "eventually (\<lambda>z. f z \<noteq> c) (at z)"
proof (rule ccontr)
  assume "\<not>eventually (\<lambda>z. f z \<noteq> c) (at z)"
  hence *: "frequently (\<lambda>z. f z = c) (at z)"
    by (auto simp: frequently_def)
  have "\<forall>w\<in>A-pts. f w = c"
    using meromorphic_frequently_const_imp_const [OF assms(1,2) * assms(4)] by blast
  hence "f constant_on A - pts"
    by (auto simp: constant_on_def)
  thus False
    using assms(3) by contradiction
qed

lemma meromorphic_frequently_const_imp_const':
  assumes "f meromorphic_on A pts" "connected A" "\<forall>w\<in>pts. is_pole f w"
  assumes "frequently (\<lambda>w. f w = c) (at z)"
  assumes "z \<in> A"
  assumes "w \<in> A"
  shows   "f w = c"
proof -
  have "\<not>is_pole f z"
    using frequently_const_imp_not_is_pole[OF assms(4)] .
  with assms have z: "z \<in> A - pts"
    by auto
  have *: "f w = c" if "w \<in> A - pts" for w
    using that meromorphic_frequently_const_imp_const [OF assms(1,2,4) z] by auto
  have "\<not>is_pole f u" if "u \<in> A" for u
  proof -
    have "is_pole f u \<longleftrightarrow> is_pole (\<lambda>_. c) u"
    proof (rule is_pole_cong)
      have "eventually (\<lambda>w. w \<in> A - (pts - {u}) - {u}) (at u)"
        by (intro eventually_at_in_open meromorphic_imp_open_diff' [OF assms(1)]) (use that in auto)
      thus "eventually (\<lambda>w. f w = c) (at u)"
        by eventually_elim (use * in auto)
    qed auto
    thus ?thesis
      by auto
  qed
  moreover have "pts \<subseteq> A"
    using assms(1) by (simp add: meromorphic_on_def)
  ultimately have "pts = {}"
    using assms(3) by auto
  with * and \<open>w \<in> A\<close> show ?thesis
    by blast
qed

lemma meromorphic_imp_eventually_neq':
  assumes "f meromorphic_on A pts" "connected A" "\<forall>w\<in>pts. is_pole f w" "\<not>f constant_on A"
  assumes "z \<in> A"
  shows   "eventually (\<lambda>z. f z \<noteq> c) (at z)"
proof (rule ccontr)
  assume "\<not>eventually (\<lambda>z. f z \<noteq> c) (at z)"
  hence *: "frequently (\<lambda>z. f z = c) (at z)"
    by (auto simp: frequently_def)
  have "\<forall>w\<in>A. f w = c"
    using meromorphic_frequently_const_imp_const' [OF assms(1,2,3) * assms(5)] by blast
  hence "f constant_on A"
    by (auto simp: constant_on_def)
  thus False
    using assms(4) by contradiction
qed

lemma zorder_eq_0_iff_meromorphic:
  assumes "f meromorphic_on A pts" "\<forall>z\<in>pts. is_pole f z" "z \<in> A"
  assumes "eventually (\<lambda>x. f x \<noteq> 0) (at z)"
  shows   "zorder f z = 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z \<noteq> 0"
proof (cases "z \<in> pts")
  case True
  from assms obtain F where F: "(\<lambda>x. f (z + x)) has_laurent_expansion F"
    by (metis True meromorphic_on_def not_essential_has_laurent_expansion) (* TODO: better lemmas *)
  from F and assms(4) have [simp]: "F \<noteq> 0"
    using has_laurent_expansion_eventually_nonzero_iff by blast
  show ?thesis using True assms(2)
    using is_pole_fls_subdegree_iff [OF F] has_laurent_expansion_zorder [OF F]
    by auto
next
  case False
  have ana: "f analytic_on {z}"
    using meromorphic_on_imp_analytic_at False assms by blast
  hence "\<not>is_pole f z"
    using analytic_at not_is_pole_holomorphic by blast
  moreover have "frequently (\<lambda>w. f w \<noteq> 0) (at z)"
    using assms(4) by (intro eventually_frequently) auto
  ultimately show ?thesis using zorder_eq_0_iff[OF ana] False
    by auto
qed

lemma zorder_pos_iff_meromorphic:
  assumes "f meromorphic_on A pts" "\<forall>z\<in>pts. is_pole f z" "z \<in> A"
  assumes "eventually (\<lambda>x. f x \<noteq> 0) (at z)"
  shows   "zorder f z > 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
proof (cases "z \<in> pts")
  case True
  from assms obtain F where F: "(\<lambda>x. f (z + x)) has_laurent_expansion F"
    by (metis True meromorphic_on_def not_essential_has_laurent_expansion) (* TODO: better lemmas *)
  from F and assms(4) have [simp]: "F \<noteq> 0"
    using has_laurent_expansion_eventually_nonzero_iff by blast
  show ?thesis using True assms(2)
    using is_pole_fls_subdegree_iff [OF F] has_laurent_expansion_zorder [OF F]
    by auto
next
  case False
  have ana: "f analytic_on {z}"
    using meromorphic_on_imp_analytic_at False assms by blast
  hence "\<not>is_pole f z"
    using analytic_at not_is_pole_holomorphic by blast
  moreover have "frequently (\<lambda>w. f w \<noteq> 0) (at z)"
    using assms(4) by (intro eventually_frequently) auto
  ultimately show ?thesis using zorder_pos_iff'[OF ana] False
    by auto
qed

lemma zorder_neg_iff_meromorphic:
  assumes "f meromorphic_on A pts" "\<forall>z\<in>pts. is_pole f z" "z \<in> A"
  assumes "eventually (\<lambda>x. f x \<noteq> 0) (at z)"
  shows   "zorder f z < 0 \<longleftrightarrow> is_pole f z"
proof -
  have "frequently (\<lambda>x. f x \<noteq> 0) (at z)"
    using assms by (intro eventually_frequently) auto
  moreover from assms have "isolated_singularity_at f z" "not_essential f z"
    using meromorphic_on_imp_isolated_singularity meromorphic_on_imp_not_essential by blast+
  ultimately show ?thesis
    using isolated_pole_imp_neg_zorder neg_zorder_imp_is_pole by blast
qed

lemma meromorphic_on_imp_discrete:
  assumes mero:"f meromorphic_on S pts" and "connected S" 
    and nconst:"\<not> (\<forall>w\<in>S - pts. f w = c)"
  shows "discrete {x\<in>S. f x=c}" 
proof -
  define g where "g=(\<lambda>x. f x - c)"
  have "\<forall>\<^sub>F w in at z. g w \<noteq> 0" if "z \<in> S" for z
  proof (rule nconst_imp_nzero_neighbour'[of g S pts z])
    show "g meromorphic_on S pts" using mero unfolding g_def
      by (auto intro:meromorphic_intros)
    show "\<not> (\<forall>w\<in>S - pts. g w = 0)" using nconst unfolding g_def by auto
  qed fact+
  then show ?thesis 
    unfolding discrete_altdef g_def 
    using eventually_mono by fastforce
qed

lemma meromorphic_isolated_in:
  assumes merf: "f meromorphic_on D pts" "p\<in>pts"
  shows "p isolated_in pts"
  by (meson assms isolated_in_islimpt_iff meromorphic_on_def subsetD)

lemma remove_sings_constant_on:
  assumes merf: "f meromorphic_on D pts" and "connected D"
      and const:"f constant_on (D - pts)"
    shows "(remove_sings f) constant_on D"
proof -
  have remove_sings_const: "remove_sings f constant_on D - pts" 
    using const
    by (metis constant_onE merf meromorphic_on_imp_analytic_at remove_sings_at_analytic)

  have ?thesis if "D = {}"
    using that unfolding constant_on_def by auto
  moreover have ?thesis if "D\<noteq>{}" "{x\<in>pts. is_pole f x} = {}"
  proof -
    obtain \<xi> where "\<xi> \<in> (D - pts)" "\<xi> islimpt (D - pts)"
    proof -
      have "open (D - pts)"
        using meromorphic_imp_open_diff[OF merf] .
      moreover have "(D - pts) \<noteq> {}" using \<open>D\<noteq>{}\<close>
        by (metis Diff_empty closure_empty merf 
            meromorphic_pts_closure subset_empty)
      ultimately show ?thesis using open_imp_islimpt that by auto
    qed
    moreover have "remove_sings f holomorphic_on D"
      using remove_sings_holomorphic_on[OF merf] that by auto
    moreover note remove_sings_const
    moreover have "open D" 
      using assms(1) meromorphic_on_def by blast
    ultimately show ?thesis
      using Conformal_Mappings.analytic_continuation'
              [of "remove_sings f" D "D-pts" \<xi>] \<open>connected D\<close>
      by auto
  qed
  moreover have ?thesis if "D\<noteq>{}" "{x\<in>pts. is_pole f x} \<noteq> {}"
  proof -
    define PP where "PP={x\<in>D. is_pole f x}"
    have "remove_sings f meromorphic_on D PP"
      using merf unfolding PP_def
      apply (elim remove_sings_meromorphic_on)
      subgoal using assms(1) meromorphic_on_def by force
      subgoal using meromorphic_pole_subset merf by auto
      done
    moreover have "remove_sings f constant_on D - PP"
    proof -
      obtain \<xi> where "\<xi> \<in> f ` (D - pts)" 
        by (metis Diff_empty Diff_eq_empty_iff \<open>D \<noteq> {}\<close> assms(1) 
            closure_empty ex_in_conv imageI meromorphic_pts_closure)
      have \<xi>:"\<forall>x\<in>D - pts. f x = \<xi>"    
        by (metis \<open>\<xi> \<in> f ` (D - pts)\<close> assms(3) constant_on_def image_iff)

      have "remove_sings f x = \<xi>" if "x\<in>D - PP" for x
      proof (cases "x\<in>pts")
        case True
        then have"x isolated_in pts" 
          using meromorphic_isolated_in[OF merf] by auto
        then obtain T0 where T0:"open T0" "T0 \<inter> pts = {x}"
          unfolding isolated_in_def by auto
        obtain T1 where T1:"open T1" "x\<in>T1" "T1 \<subseteq> D"
          using merf unfolding meromorphic_on_def 
          using True by blast
        define T2 where "T2 = T1 \<inter> T0"
        have "open T2" "x\<in>T2" "T2 - {x} \<subseteq> D - pts"
          using T0 T1 unfolding T2_def by auto
        then have "\<forall>w\<in>T2. w\<noteq>x \<longrightarrow> f w =\<xi>"
          using \<xi> by auto
        then have "\<forall>\<^sub>F x in at x. f x = \<xi>" 
          unfolding eventually_at_topological
          using \<open>open T2\<close> \<open>x\<in>T2\<close> by auto
        then have "f \<midarrow>x\<rightarrow> \<xi>" 
          using tendsto_eventually by auto
        then show ?thesis by blast
      next
        case False
        then show ?thesis 
          using \<open>\<forall>x\<in>D - pts. f x = \<xi>\<close> assms(1) 
            meromorphic_on_imp_analytic_at that by auto
      qed

      then show ?thesis unfolding constant_on_def by auto
    qed

    moreover have "is_pole (remove_sings f) x" if "x\<in>PP" for x
    proof -
      have "isolated_singularity_at f x"
        by (metis (mono_tags, lifting) DiffI PP_def assms(1) 
            isolated_singularity_at_analytic mem_Collect_eq 
            meromorphic_on_def meromorphic_on_imp_analytic_at that)
      then show ?thesis using that unfolding PP_def by simp
    qed
    ultimately show ?thesis
      using meromorphic_imp_constant_on
            [of "remove_sings f" D PP]
      by auto
  qed
  ultimately show ?thesis by auto
qed

lemma meromorphic_eq_meromorphic_extend:
  assumes "f meromorphic_on A pts1" "g meromorphic_on A pts1" "\<not>z islimpt pts2"
  assumes "\<And>z. z \<in> A - pts2 \<Longrightarrow> f z = g z" "pts1 \<subseteq> pts2" "z \<in> A - pts1"
  shows   "f z = g z"
proof -
  have "g analytic_on {z}"
    using assms by (intro meromorphic_on_imp_analytic_at[OF assms(2)]) auto
  hence "g \<midarrow>z\<rightarrow> g z"
    using analytic_at_imp_isCont isContD by blast
  also have "?this \<longleftrightarrow> f \<midarrow>z\<rightarrow> g z"
  proof (intro filterlim_cong)
    have "eventually (\<lambda>w. w \<notin> pts2) (at z)"
      using assms by (auto simp: islimpt_conv_frequently_at frequently_def)
    moreover have "eventually (\<lambda>w. w \<in> A) (at z)"
      using assms by (intro eventually_at_in_open') (auto simp: meromorphic_on_def)
    ultimately show "\<forall>\<^sub>F x in at z. g x = f x"
      by eventually_elim (use assms in auto)
  qed auto
  finally have "f \<midarrow>z\<rightarrow> g z" .
  moreover have "f analytic_on {z}"
    using assms by (intro meromorphic_on_imp_analytic_at[OF assms(1)]) auto
  hence "f \<midarrow>z\<rightarrow> f z"
    using analytic_at_imp_isCont isContD by blast
  ultimately show ?thesis
    using tendsto_unique by force
qed

lemma meromorphic_constant_on_extend:
  assumes "f constant_on A - pts1" "f meromorphic_on A pts1" "f meromorphic_on A pts2" "pts2 \<subseteq> pts1"
  shows   "f constant_on A - pts2"
proof -
  from assms(1) obtain c where c: "\<And>z. z \<in> A - pts1 \<Longrightarrow> f z = c"
    unfolding constant_on_def by auto
  have "f z = c" if "z \<in> A - pts2" for z
    using assms(3)
  proof (rule meromorphic_eq_meromorphic_extend[where z = z])
    show "(\<lambda>a. c) meromorphic_on A pts2"
      by (intro meromorphic_on_const) (use assms in \<open>auto simp: meromorphic_on_def\<close>)
    show "\<not>z islimpt pts1"
      using that assms by (auto simp: meromorphic_on_def)
  qed (use assms c that in auto)
  thus ?thesis
    by (auto simp: constant_on_def)
qed

lemma meromorphic_remove_sings_constant_on_imp_constant_on:
  assumes "f meromorphic_on A pts"
  assumes "remove_sings f constant_on A"
  shows   "f constant_on A - pts"
proof -
  from assms(2) obtain c where c: "\<And>z. z \<in> A \<Longrightarrow> remove_sings f z = c"
    by (auto simp: constant_on_def)
  have "f z = c" if "z \<in> A - pts" for z
    using meromorphic_on_imp_analytic_at[OF assms(1) that] c[of z] that
    by auto
  thus ?thesis
    by (auto simp: constant_on_def)
qed




definition singularities_on :: "complex set \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex set" where
  "singularities_on A f =
     {z\<in>A. isolated_singularity_at f z \<and> not_essential f z \<and> \<not>f analytic_on {z}}"

lemma singularities_on_subset: "singularities_on A f \<subseteq> A"
  by (auto simp: singularities_on_def)

lemma pole_in_singularities_on:
  assumes "f meromorphic_on A pts" "z \<in> A" "is_pole f z"
  shows   "z \<in> singularities_on A f"
  unfolding singularities_on_def not_essential_def using assms
  using analytic_at_imp_no_pole meromorphic_on_imp_isolated_singularity by force


lemma meromorphic_on_subset_pts:
  assumes "f meromorphic_on A pts" "pts' \<subseteq> pts" "f analytic_on pts - pts'"
  shows   "f meromorphic_on A pts'"
proof
  show "open A" "pts' \<subseteq> A"
    using assms by (auto simp: meromorphic_on_def)
  show "isolated_singularity_at f z" "not_essential f z" if "z \<in> pts'" for z
    using assms that by (auto simp: meromorphic_on_def)
  show "\<not>z islimpt pts'" if "z \<in> A" for z
    using assms that islimpt_subset unfolding meromorphic_on_def by blast
  have "f analytic_on A - pts"
    using assms(1) meromorphic_imp_analytic by blast
  with assms have "f analytic_on (A - pts) \<union> (pts - pts')"
    by (subst analytic_on_Un) auto
  also have "(A - pts) \<union> (pts - pts') = A - pts'"
    using assms by (auto simp: meromorphic_on_def)
  finally show "f holomorphic_on A - pts'"
    using analytic_imp_holomorphic by blast
qed

lemma meromorphic_on_imp_superset_singularities_on:
  assumes "f meromorphic_on A pts"
  shows   "singularities_on A f \<subseteq> pts"
proof
  fix z assume "z \<in> singularities_on A f"
  hence "z \<in> A" "\<not>f analytic_on {z}"
    by (auto simp: singularities_on_def)
  with assms show "z \<in> pts"
    by (meson DiffI meromorphic_on_imp_analytic_at)
qed  

lemma meromorphic_on_singularities_on:
  assumes "f meromorphic_on A pts"
  shows   "f meromorphic_on A (singularities_on A f)"
  using assms meromorphic_on_imp_superset_singularities_on[OF assms]
proof (rule meromorphic_on_subset_pts)
  have "f analytic_on {z}" if "z \<in> pts - singularities_on A f" for z
    using that assms by (auto simp: singularities_on_def meromorphic_on_def)
  thus "f analytic_on pts - singularities_on A f"
    using analytic_on_analytic_at by blast
qed

theorem Residue_theorem_inside:
  assumes f: "f meromorphic_on s pts"
             "simply_connected s"
  assumes g: "valid_path g"
             "pathfinish g = pathstart g"
             "path_image g \<subseteq> s - pts"
  defines "pts1 \<equiv> pts \<inter> inside (path_image g)"
  shows "finite pts1"
    and "contour_integral g f = 2 * pi * \<i> * (\<Sum>p\<in>pts1. winding_number g p * residue f p)"
proof - 
  note [dest] = valid_path_imp_path
  have cl_g [intro]: "closed (path_image g)"
    using g by (auto intro!: closed_path_image)
  have "open s"
    using f(1) by (auto simp: meromorphic_on_def)
  define pts2 where "pts2 = pts - pts1"

  define A where "A = path_image g \<union> inside (path_image g)"
  have "closed A"
    unfolding A_def using g by (intro closed_path_image_Un_inside) auto
  moreover have "bounded A"
    unfolding A_def using g by (auto intro!: bounded_path_image bounded_inside)
  ultimately have 1: "compact A"
    using compact_eq_bounded_closed by blast
  have 2: "open (s - pts2)"
    using f by (auto intro!: meromorphic_imp_open_diff' [OF f(1)] simp: pts2_def)
  have 3: "A \<subseteq> s - pts2"
    unfolding A_def pts2_def pts1_def
    using f(2) g(3) 2 subset_simply_connected_imp_inside_subset[of s "path_image g"] \<open>open s\<close>
    by auto

  obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "(\<Union>x\<in>A. ball x \<epsilon>) \<subseteq> s - pts2"
    using compact_subset_open_imp_ball_epsilon_subset[OF 1 2 3] by blast
  define B where "B = (\<Union>x\<in>A. ball x \<epsilon>)"

  have "finite (A \<inter> pts)"
    using 1 3 by (intro meromorphic_compact_finite_pts[OF f(1)]) auto
  also have "A \<inter> pts = pts1"
    unfolding pts1_def using g by (auto simp: A_def)
  finally show fin: "finite pts1" .

  show "contour_integral g f = 2 * pi * \<i> * (\<Sum>p\<in>pts1. winding_number g p * residue f p)"
  proof (rule Residue_theorem)
    show "open B"
      by (auto simp: B_def)
  next
    have "connected A"
      unfolding A_def using g
      by (intro connected_with_inside closed_path_image connected_path_image) auto
    hence "connected (A \<union> B)"
      unfolding B_def using g \<open>\<epsilon> > 0\<close> f(2)
      by (intro connected_Un_UN connected_path_image valid_path_imp_path)
         (auto simp: simply_connected_imp_connected)
    also have "A \<union> B = B"
      using \<epsilon>(1) by (auto simp: B_def)
    finally show "connected B" .
  next
    have "f holomorphic_on (s - pts)"
      by (intro meromorphic_imp_holomorphic f)
    moreover have "B - pts1 \<subseteq> s - pts"
      using \<epsilon> unfolding B_def by (auto simp: pts1_def pts2_def)
    ultimately show "f holomorphic_on (B - pts1)"
      by (rule holomorphic_on_subset)
  next
    have "path_image g \<subseteq> A - pts1"
      using g unfolding pts1_def by (auto simp: A_def)
    also have "\<dots> \<subseteq> B - pts1"
      unfolding B_def using \<epsilon>(1) by auto
    finally show "path_image g \<subseteq> B - pts1" .
  next
    show "\<forall>z. z \<notin> B \<longrightarrow> winding_number g z = 0"
    proof safe
      fix z assume z: "z \<notin> B"
      hence "z \<notin> A"
        using \<epsilon>(1) by (auto simp: B_def)
      hence "z \<in> outside (path_image g)"
        unfolding A_def by (simp add: union_with_inside)
      thus "winding_number g z = 0"
        using g by (intro winding_number_zero_in_outside) auto
    qed
  qed (use g fin in auto)
qed

theorem Residue_theorem':
  assumes f: "f meromorphic_on s pts"
             "simply_connected s"
  assumes g: "valid_path g" 
             "pathfinish g = pathstart g"
             "path_image g \<subseteq> s - pts"
  assumes pts': "finite pts'"
                "pts' \<subseteq> s"
                "\<And>z. z \<in> pts - pts' \<Longrightarrow> winding_number g z = 0"
  shows "contour_integral g f = 2 * pi * \<i> * (\<Sum>p\<in>pts'. winding_number g p * residue f p)"
proof -
  note [dest] = valid_path_imp_path
  define pts1 where "pts1 = pts \<inter> inside (path_image g)"

  have "contour_integral g f = 2 * pi * \<i> * (\<Sum>p\<in>pts1. winding_number g p * residue f p)"
    unfolding pts1_def by (intro Residue_theorem_inside[OF f g])
  also have "(\<Sum>p\<in>pts1. winding_number g p * residue f p) =
             (\<Sum>p\<in>pts'. winding_number g p * residue f p)"
  proof (intro sum.mono_neutral_cong refl)
    show "finite pts1"
      unfolding pts1_def by (intro Residue_theorem_inside[OF f g])
    show "finite pts'"
      by fact
  next
    fix z assume z: "z \<in> pts' - pts1"
    show "winding_number g z * residue f z = 0"
    proof (cases "z \<in> pts")
      case True
      with z have "z \<notin> path_image g \<union> inside (path_image g)"
        using g(3) by (auto simp: pts1_def)
      hence "z \<in> outside (path_image g)"
        by (simp add: union_with_inside)
      hence "winding_number g z = 0"
        using g by (intro winding_number_zero_in_outside) auto
      thus ?thesis
        by simp
    next
      case False
      with z pts' have "z \<in> s - pts"
        by auto
      with f(1) have "f analytic_on {z}"
        by (intro meromorphic_on_imp_analytic_at)
      hence "residue f z = 0"
        using analytic_at residue_holo by blast
      thus ?thesis
        by simp
    qed
  next
    fix z assume z: "z \<in> pts1 - pts'"
    hence "winding_number g z = 0"
      using pts' by (auto simp: pts1_def)
    thus "winding_number g z * residue f z = 0"
      by simp
  qed
  finally show ?thesis .
qed

end
