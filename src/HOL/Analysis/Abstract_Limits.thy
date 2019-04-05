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

definition limitin :: "'a topology \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" where
  "limitin X f l F \<equiv> l \<in> topspace X \<and> (\<forall>U. openin X U \<and> l \<in> U \<longrightarrow> eventually (\<lambda>x. f x \<in> U) F)"

lemma limitin_canonical_iff [simp]: "limitin euclidean f l F \<longleftrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: limitin_def tendsto_def)

lemma limitin_topspace: "limitin X f l F \<Longrightarrow> l \<in> topspace X"
  by (simp add: limitin_def)

lemma limitin_const_iff [simp]: "limitin X (\<lambda>a. l) l F \<longleftrightarrow> l \<in> topspace X"
  by (simp add: limitin_def)

lemma limitin_const: "limitin euclidean (\<lambda>a. l) l F"
  by simp

lemma limitin_eventually:
   "\<lbrakk>l \<in> topspace X; eventually (\<lambda>x. f x = l) F\<rbrakk> \<Longrightarrow> limitin X f l F"
  by (auto simp: limitin_def eventually_mono)

lemma limitin_subsequence:
   "\<lbrakk>strict_mono r; limitin X f l sequentially\<rbrakk> \<Longrightarrow> limitin X (f \<circ> r) l sequentially"
  unfolding limitin_def using eventually_subseq by fastforce

lemma limitin_subtopology:
  "limitin (subtopology X S) f l F
   \<longleftrightarrow> l \<in> S \<and> eventually (\<lambda>a. f a \<in> S) F \<and> limitin X f l F"  (is "?lhs = ?rhs")
proof (cases "l \<in> S \<inter> topspace X")
  case True
  show ?thesis
  proof
    assume L: ?lhs
    with True
    have "\<forall>\<^sub>F b in F. f b \<in> topspace X \<inter> S"
      by (metis (no_types) limitin_def openin_topspace topspace_subtopology)
    with L show ?rhs
      apply (clarsimp simp add: limitin_def eventually_mono topspace_subtopology openin_subtopology_alt)
      apply (drule_tac x="S \<inter> U" in spec, force simp: elim: eventually_mono)
      done
  next
    assume ?rhs
    then show ?lhs
      using eventually_elim2
      by (fastforce simp add: limitin_def topspace_subtopology openin_subtopology_alt)
  qed
qed (auto simp: limitin_def topspace_subtopology)


lemma limitin_canonical_iff_gen [simp]:
  assumes "open S"
  shows "limitin (top_of_set S) f l F \<longleftrightarrow> (f \<longlongrightarrow> l) F \<and> l \<in> S"
  using assms by (auto simp: limitin_subtopology tendsto_def)

lemma limitin_sequentially:
   "limitin X S l sequentially \<longleftrightarrow>
     l \<in> topspace X \<and> (\<forall>U. openin X U \<and> l \<in> U \<longrightarrow> (\<exists>N. \<forall>n. N \<le> n \<longrightarrow> S n \<in> U))"
  by (simp add: limitin_def eventually_sequentially)

lemma limitin_sequentially_offset:
   "limitin X f l sequentially \<Longrightarrow> limitin X (\<lambda>i. f (i + k)) l sequentially"
  unfolding limitin_sequentially
  by (metis add.commute le_add2 order_trans)

lemma limitin_sequentially_offset_rev:
  assumes "limitin X (\<lambda>i. f (i + k)) l sequentially"
  shows "limitin X f l sequentially"
proof -
  have "\<exists>N. \<forall>n\<ge>N. f n \<in> U" if U: "openin X U" "l \<in> U" for U
  proof -
    obtain N where "\<And>n. n\<ge>N \<Longrightarrow> f (n + k) \<in> U"
      using assms U unfolding limitin_sequentially by blast
    then have "\<forall>n\<ge>N+k. f n \<in> U"
      by (metis add_leD2 le_add_diff_inverse ordered_cancel_comm_monoid_diff_class.le_diff_conv2 add.commute)
    then show ?thesis ..
  qed
  with assms show ?thesis
    unfolding limitin_sequentially
    by simp
qed

lemma limitin_atin:
   "limitin Y f y (atin X x) \<longleftrightarrow>
        y \<in> topspace Y \<and>
        (x \<in> topspace X
        \<longrightarrow> (\<forall>V. openin Y V \<and> y \<in> V
                 \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> f ` (U - {x}) \<subseteq> V)))"
  by (auto simp: limitin_def eventually_atin image_subset_iff)

lemma limitin_atin_self:
   "limitin Y f (f a) (atin X a) \<longleftrightarrow>
        f a \<in> topspace Y \<and>
        (a \<in> topspace X
         \<longrightarrow> (\<forall>V. openin Y V \<and> f a \<in> V
                  \<longrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> f ` U \<subseteq> V)))"
  unfolding limitin_atin by fastforce

lemma limitin_trivial:
   "\<lbrakk>trivial_limit F; y \<in> topspace X\<rbrakk> \<Longrightarrow> limitin X f y F"
  by (simp add: limitin_def)

lemma limitin_transform_eventually:
   "\<lbrakk>eventually (\<lambda>x. f x = g x) F; limitin X f l F\<rbrakk> \<Longrightarrow> limitin X g l F"
  unfolding limitin_def using eventually_elim2 by fastforce

lemma continuous_map_limit:
  assumes "continuous_map X Y g" and f: "limitin X f l F"
  shows "limitin Y (g \<circ> f) (g l) F"
proof -
  have "g l \<in> topspace Y"
    by (meson assms continuous_map_def limitin_topspace)
  moreover
  have "\<And>U. \<lbrakk>\<forall>V. openin X V \<and> l \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V); openin Y U; g l \<in> U\<rbrakk>
            \<Longrightarrow> \<forall>\<^sub>F x in F. g (f x) \<in> U"
    using assms eventually_mono
    by (fastforce simp: limitin_def dest!: openin_continuous_map_preimage)
  ultimately show ?thesis
    using f by (fastforce simp add: limitin_def)
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
        limitin Y f (f x) (atin X x)"
  unfolding topcontinuous_at_def
  by (fastforce simp add: limitin_atin)+

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
   "continuous_map X Y f \<longleftrightarrow> (\<forall>x \<in> topspace X. limitin Y f (f x) (atin X x))"
  by (auto simp: limitin_def topcontinuous_at_atin continuous_map_eq_topcontinuous_at)

lemma limitin_continuous_map:
   "\<lbrakk>continuous_map X Y f; a \<in> topspace X; f a = b\<rbrakk> \<Longrightarrow> limitin Y f b (atin X a)"
  by (auto simp: continuous_map_atin)


subsection\<open>Combining theorems for continuous functions into the reals\<close>

lemma continuous_map_canonical_const [continuous_intros]:
   "continuous_map X euclidean (\<lambda>x. c)"
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

lemma continuous_map_minus [continuous_intros]:
  fixes f :: "'a\<Rightarrow>'b::real_normed_vector"
  shows "continuous_map X euclidean f \<Longrightarrow> continuous_map X euclidean (\<lambda>x. - f x)"
  by (simp add: continuous_map_atin tendsto_minus)

lemma continuous_map_minus_eq [simp]:
  fixes f :: "'a\<Rightarrow>'b::real_normed_vector"
  shows "continuous_map X euclidean (\<lambda>x. - f x) \<longleftrightarrow> continuous_map X euclidean f"
  using continuous_map_minus add.inverse_inverse continuous_map_eq by fastforce

lemma continuous_map_add [continuous_intros]:
  fixes f :: "'a\<Rightarrow>'b::real_normed_vector"
  shows "\<lbrakk>continuous_map X euclidean f; continuous_map X euclidean g\<rbrakk> \<Longrightarrow> continuous_map X euclidean (\<lambda>x. f x + g x)"
  by (simp add: continuous_map_atin tendsto_add)

lemma continuous_map_diff [continuous_intros]:
  fixes f :: "'a\<Rightarrow>'b::real_normed_vector"
  shows "\<lbrakk>continuous_map X euclidean f; continuous_map X euclidean g\<rbrakk> \<Longrightarrow> continuous_map X euclidean (\<lambda>x. f x - g x)"
  by (simp add: continuous_map_atin tendsto_diff)

lemma continuous_map_norm [continuous_intros]:
  fixes f :: "'a\<Rightarrow>'b::real_normed_vector"
  shows "continuous_map X euclidean f \<Longrightarrow> continuous_map X euclidean (\<lambda>x. norm(f x))"
  by (simp add: continuous_map_atin tendsto_norm)

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
  fixes f :: "'a\<Rightarrow>'b\<Rightarrow>'c::real_normed_vector"
  shows "\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> continuous_map X euclidean (\<lambda>x. f x i)\<rbrakk>
         \<Longrightarrow> continuous_map X euclidean (\<lambda>x. sum (f x) I)"
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
