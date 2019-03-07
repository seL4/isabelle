theory Abstract_Limits
  imports
    Abstract_Topology
begin

subsection\<open>nhdsin and atin\<close>

definition nhdsin :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a filter"
  where "nhdsin X a =
           (if a \<in> topspace X then (INF S:{S. openin X S \<and> a \<in> S}. principal S) else bot)"

definition atin :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a filter"
  where "atin X a \<equiv> inf (nhdsin X a) (principal (topspace X - {a}))"


lemma nhdsin_degenerate [simp]: "a \<notin> topspace X \<Longrightarrow> nhdsin X a = bot"
  and atin_degenerate [simp]: "a \<notin> topspace X \<Longrightarrow> atin X a = bot"
  by (simp_all add: nhdsin_def atin_def)

lemma eventually_nhdsin:
  "eventually P (nhdsin X a) \<longleftrightarrow> a \<notin> topspace X \<or> (\<exists>S. openin X S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"
proof (cases "a \<in> topspace X")
  case True
  hence "nhdsin X a = (INF S:{S. openin X S \<and> a \<in> S}. principal S)"
    by (simp add: nhdsin_def)
  also have "eventually P \<dots> \<longleftrightarrow> (\<exists>S. openin X S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"
    using True by (subst eventually_INF_base) (auto simp: eventually_principal)
  finally show ?thesis using True by simp
qed auto

lemma eventually_atin:
  "eventually P (atin X a) \<longleftrightarrow> a \<notin> topspace X \<or>
             (\<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x \<in> U - {a}. P x))"
proof (cases "a \<in> topspace X")
  case True
  hence "eventually P (atin X a) \<longleftrightarrow> (\<exists>S. openin X S \<and>
           a \<in> S \<and> (\<forall>x\<in>S. x \<in> topspace X \<and> x \<noteq> a \<longrightarrow> P x))"
    by (simp add: atin_def eventually_inf_principal eventually_nhdsin)
  also have "\<dots> \<longleftrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x \<in> U - {a}. P x))"
    using openin_subset by (intro ex_cong) auto
  finally show ?thesis by (simp add: True)
qed auto


subsection\<open>Limits in a topological space\<close>

definition limit :: "'a topology \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" where
  "limit X f l F \<equiv> l \<in> topspace X \<and> (\<forall>U. openin X U \<and> l \<in> U \<longrightarrow> eventually (\<lambda>x. f x \<in> U) F)"

lemma limit_euclideanreal_iff [simp]: "limit euclideanreal f l F \<longleftrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: limit_def tendsto_def)

lemma limit_in_topspace: "limit X f l F \<Longrightarrow> l \<in> topspace X"
  by (simp add: limit_def)

lemma limit_const: "limit X (\<lambda>a. l) l F \<longleftrightarrow> l \<in> topspace X"
  by (simp add: limit_def)

lemma limit_real_const: "limit euclideanreal (\<lambda>a. l) l F"
  by (simp add: limit_def)

lemma limit_eventually:
   "\<lbrakk>l \<in> topspace X; eventually (\<lambda>x. f x = l) F\<rbrakk> \<Longrightarrow> limit X f l F"
  by (auto simp: limit_def eventually_mono)

lemma limit_subsequence:
   "\<lbrakk>strict_mono r; limit X f l sequentially\<rbrakk> \<Longrightarrow> limit X (f \<circ> r) l sequentially"
  unfolding limit_def using eventually_subseq by fastforce

lemma limit_subtopology:
  "limit (subtopology X S) f l F
   \<longleftrightarrow> l \<in> S \<and> eventually (\<lambda>a. f a \<in> S) F \<and> limit X f l F"  (is "?lhs = ?rhs")
proof (cases "l \<in> S \<inter> topspace X")
  case True
  show ?thesis
  proof
    assume L: ?lhs
    with True
    have "\<forall>\<^sub>F b in F. f b \<in> topspace X \<inter> S"
      by (metis (no_types) limit_def openin_topspace topspace_subtopology)
    with L show ?rhs
      apply (clarsimp simp add: limit_def eventually_mono topspace_subtopology openin_subtopology_alt)
      apply (drule_tac x="S \<inter> U" in spec, force simp: elim: eventually_mono)
      done
  next
    assume ?rhs
    then show ?lhs
      using eventually_elim2
      by (fastforce simp add: limit_def topspace_subtopology openin_subtopology_alt)
  qed
qed (auto simp: limit_def topspace_subtopology)


lemma limit_sequentially:
   "limit X S l sequentially \<longleftrightarrow>
     l \<in> topspace X \<and> (\<forall>U. openin X U \<and> l \<in> U \<longrightarrow> (\<exists>N. \<forall>n. N \<le> n \<longrightarrow> S n \<in> U))"
  by (simp add: limit_def eventually_sequentially)

lemma limit_sequentially_offset:
   "limit X f l sequentially \<Longrightarrow> limit X (\<lambda>i. f (i + k)) l sequentially"
  unfolding limit_sequentially
  by (metis add.commute le_add2 order_trans)

lemma limit_sequentially_offset_rev:
  assumes "limit X (\<lambda>i. f (i + k)) l sequentially"
  shows "limit X f l sequentially"
proof -
  have "\<exists>N. \<forall>n\<ge>N. f n \<in> U" if U: "openin X U" "l \<in> U" for U
  proof -
    obtain N where "\<And>n. n\<ge>N \<Longrightarrow> f (n + k) \<in> U"
      using assms U unfolding limit_sequentially by blast
    then have "\<forall>n\<ge>N+k. f n \<in> U"
      by (metis add_leD2 le_add_diff_inverse ordered_cancel_comm_monoid_diff_class.le_diff_conv2 add.commute)
    then show ?thesis ..
  qed
  with assms show ?thesis
    unfolding limit_sequentially
    by simp
qed

lemma limit_atin:
   "limit Y f y (atin X x) \<longleftrightarrow>
        y \<in> topspace Y \<and>
        (x \<in> topspace X
        \<longrightarrow> (\<forall>V. openin Y V \<and> y \<in> V
                 \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> f ` (U - {x}) \<subseteq> V)))"
  by (auto simp: limit_def eventually_atin image_subset_iff)

lemma limit_atin_self:
   "limit Y f (f a) (atin X a) \<longleftrightarrow>
        f a \<in> topspace Y \<and>
        (a \<in> topspace X
         \<longrightarrow> (\<forall>V. openin Y V \<and> f a \<in> V
                  \<longrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> f ` U \<subseteq> V)))"
  unfolding limit_atin by fastforce

lemma limit_trivial:
   "\<lbrakk>trivial_limit F; y \<in> topspace X\<rbrakk> \<Longrightarrow> limit X f y F"
  by (simp add: limit_def)

lemma limit_transform_eventually:
   "\<lbrakk>eventually (\<lambda>x. f x = g x) F; limit X f l F\<rbrakk> \<Longrightarrow> limit X g l F"
  unfolding limit_def using eventually_elim2 by fastforce

lemma continuous_map_limit:
  assumes "continuous_map X Y g" and f: "limit X f l F"
  shows "limit Y (g \<circ> f) (g l) F"
proof -
  have "g l \<in> topspace Y"
    by (meson assms continuous_map_def limit_in_topspace)
  moreover
  have "\<And>U. \<lbrakk>\<forall>V. openin X V \<and> l \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V); openin Y U; g l \<in> U\<rbrakk>
            \<Longrightarrow> \<forall>\<^sub>F x in F. g (f x) \<in> U"
    using assms eventually_mono
    by (fastforce simp: limit_def dest!: openin_continuous_map_preimage)
  ultimately show ?thesis
    using f by (fastforce simp add: limit_def)
qed


subsection\<open>Pointwise continuity in topological spaces\<close>

definition topcontinuous_at where
  "topcontinuous_at X Y f x \<longleftrightarrow>
     x \<in> topspace X \<and>
     (\<forall>x \<in> topspace X. f x \<in> topspace Y) \<and>
     (\<forall>V. openin Y V \<and> f x \<in> V
          \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y \<in> U. f y \<in> V)))"

lemma topcontinuous_at_atin:
   "topcontinuous_at X Y f x \<longleftrightarrow>
        x \<in> topspace X \<and>
        (\<forall>x \<in> topspace X. f x \<in> topspace Y) \<and>
        limit Y f (f x) (atin X x)"
  unfolding topcontinuous_at_def
  by (fastforce simp add: limit_atin)+

lemma continuous_map_eq_topcontinuous_at:
   "continuous_map X Y f \<longleftrightarrow> (\<forall>x \<in> topspace X. topcontinuous_at X Y f x)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: continuous_map_def topcontinuous_at_def)
next
  assume R: ?rhs
  then show ?lhs
    apply (auto simp: continuous_map_def topcontinuous_at_def)
    apply (subst openin_subopen, safe)
    apply (drule bspec, assumption)
    using openin_subset[of X] apply (auto simp: subset_iff dest!: spec)
    done
qed

lemma continuous_map_atin:
   "continuous_map X Y f \<longleftrightarrow> (\<forall>x \<in> topspace X. limit Y f (f x) (atin X x))"
  by (auto simp: limit_def topcontinuous_at_atin continuous_map_eq_topcontinuous_at)

lemma limit_continuous_map:
   "\<lbrakk>continuous_map X Y f; a \<in> topspace X; f a = b\<rbrakk> \<Longrightarrow> limit Y f b (atin X a)"
  by (auto simp: continuous_map_atin)


subsection\<open>Combining theorems for continuous functions into the reals\<close>

lemma continuous_map_real_const [simp,continuous_intros]:
   "continuous_map X euclideanreal (\<lambda>x. c)"
  by simp

lemma continuous_map_real_mult [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x * g x)"
  by (simp add: continuous_map_atin tendsto_mult)

lemma continuous_map_real_pow [continuous_intros]:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x ^ n)"
  by (induction n) (auto simp: continuous_map_real_mult)

lemma continuous_map_real_mult_left:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. c * f x)"
  by (simp add: continuous_map_atin tendsto_mult)

lemma continuous_map_real_mult_left_eq:
   "continuous_map X euclideanreal (\<lambda>x. c * f x) \<longleftrightarrow> c = 0 \<or> continuous_map X euclideanreal f"
proof (cases "c = 0")
  case False
  have "continuous_map X euclideanreal (\<lambda>x. c * f x) \<Longrightarrow> continuous_map X euclideanreal f"
    apply (frule continuous_map_real_mult_left [where c="inverse c"])
    apply (simp add: field_simps False)
    done
  with False show ?thesis
    using continuous_map_real_mult_left by blast
qed simp

lemma continuous_map_real_mult_right:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x * c)"
  by (simp add: continuous_map_atin tendsto_mult)

lemma continuous_map_real_mult_right_eq:
   "continuous_map X euclideanreal (\<lambda>x. f x * c) \<longleftrightarrow> c = 0 \<or> continuous_map X euclideanreal f"
  by (simp add: mult.commute flip: continuous_map_real_mult_left_eq)

lemma continuous_map_real_minus [continuous_intros]:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. - f x)"
  by (simp add: continuous_map_atin tendsto_minus)

lemma continuous_map_real_minus_eq:
   "continuous_map X euclideanreal (\<lambda>x. - f x) \<longleftrightarrow> continuous_map X euclideanreal f"
  using continuous_map_real_mult_left_eq [where c = "-1"] by auto

lemma continuous_map_real_add [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x + g x)"
  by (simp add: continuous_map_atin tendsto_add)

lemma continuous_map_real_diff [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x - g x)"
  by (simp add: continuous_map_atin tendsto_diff)

lemma continuous_map_real_abs [continuous_intros]:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. abs(f x))"
  by (simp add: continuous_map_atin tendsto_rabs)

lemma continuous_map_real_max [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. max (f x) (g x))"
  by (simp add: continuous_map_atin tendsto_max)

lemma continuous_map_real_min [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. min (f x) (g x))"
  by (simp add: continuous_map_atin tendsto_min)

lemma continuous_map_sum [continuous_intros]:
   "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x i)\<rbrakk>
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. sum (f x) I)"
  by (simp add: continuous_map_atin tendsto_sum)

lemma continuous_map_prod [continuous_intros]:
   "\<lbrakk>finite I;
         \<And>i. i \<in> I \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x i)\<rbrakk>
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. prod (f x) I)"
  by (simp add: continuous_map_atin tendsto_prod)

lemma continuous_map_real_inverse [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; \<And>x. x \<in> topspace X \<Longrightarrow> f x \<noteq> 0\<rbrakk>
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. inverse(f x))"
  by (simp add: continuous_map_atin tendsto_inverse)

lemma continuous_map_real_divide [continuous_intros]:
   "\<lbrakk>continuous_map X euclideanreal f; continuous_map X euclideanreal g; \<And>x. x \<in> topspace X \<Longrightarrow> g x \<noteq> 0\<rbrakk>
   \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x / g x)"
  by (simp add: continuous_map_atin tendsto_divide)

end
