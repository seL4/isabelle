section \<open>Faces, Extreme Points, Polytopes, Polyhedra etc\<close>

text\<open>Ported from HOL Light by L C Paulson\<close>

theory Polytope
imports Cartesian_Euclidean_Space Path_Connected
begin

subsection \<open>Faces of a (usually convex) set\<close>

definition\<^marker>\<open>tag important\<close> face_of :: "['a::real_vector set, 'a set] \<Rightarrow> bool" (infixr "(face'_of)" 50)
  where
  "T face_of S \<longleftrightarrow>
        T \<subseteq> S \<and> convex T \<and>
        (\<forall>a \<in> S. \<forall>b \<in> S. \<forall>x \<in> T. x \<in> open_segment a b \<longrightarrow> a \<in> T \<and> b \<in> T)"

lemma face_ofD: "\<lbrakk>T face_of S; x \<in> open_segment a b; a \<in> S; b \<in> S; x \<in> T\<rbrakk> \<Longrightarrow> a \<in> T \<and> b \<in> T"
  unfolding face_of_def by blast

lemma face_of_translation_eq [simp]:
    "((+) a ` T face_of (+) a ` S) \<longleftrightarrow> T face_of S"
proof -
  have *: "\<And>a T S. T face_of S \<Longrightarrow> ((+) a ` T face_of (+) a ` S)"
    by (simp add: face_of_def)
  show ?thesis
    by (force simp: image_comp o_def dest: * [where a = "-a"] intro: *)
qed

lemma face_of_linear_image:
  assumes "linear f" "inj f"
    shows "(f ` c face_of f ` S) \<longleftrightarrow> c face_of S"
by (simp add: face_of_def inj_image_subset_iff inj_image_mem_iff open_segment_linear_image assms)

lemma face_of_refl: "convex S \<Longrightarrow> S face_of S"
  by (auto simp: face_of_def)

lemma face_of_refl_eq: "S face_of S \<longleftrightarrow> convex S"
  by (auto simp: face_of_def)

lemma empty_face_of [iff]: "{} face_of S"
  by (simp add: face_of_def)

lemma face_of_empty [simp]: "S face_of {} \<longleftrightarrow> S = {}"
  by (meson empty_face_of face_of_def subset_empty)

lemma face_of_trans [trans]: "\<lbrakk>S face_of T; T face_of u\<rbrakk> \<Longrightarrow> S face_of u"
  unfolding face_of_def by (safe; blast)

lemma face_of_face: "T face_of S \<Longrightarrow> (f face_of T \<longleftrightarrow> f face_of S \<and> f \<subseteq> T)"
  unfolding face_of_def by (safe; blast)

lemma face_of_subset: "\<lbrakk>F face_of S; F \<subseteq> T; T \<subseteq> S\<rbrakk> \<Longrightarrow> F face_of T"
  unfolding face_of_def by (safe; blast)

lemma face_of_slice: "\<lbrakk>F face_of S; convex T\<rbrakk> \<Longrightarrow> (F \<inter> T) face_of (S \<inter> T)"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_Int: "\<lbrakk>t1 face_of S; t2 face_of S\<rbrakk> \<Longrightarrow> (t1 \<inter> t2) face_of S"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_Inter: "\<lbrakk>A \<noteq> {}; \<And>T. T \<in> A \<Longrightarrow> T face_of S\<rbrakk> \<Longrightarrow> (\<Inter> A) face_of S"
  unfolding face_of_def by (blast intro: convex_Inter)

lemma face_of_Int_Int: "\<lbrakk>F face_of T; F' face_of t'\<rbrakk> \<Longrightarrow> (F \<inter> F') face_of (T \<inter> t')"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_imp_subset: "T face_of S \<Longrightarrow> T \<subseteq> S"
  unfolding face_of_def by blast

proposition face_of_imp_eq_affine_Int:
  fixes S :: "'a::euclidean_space set"
  assumes S: "convex S"  and T: "T face_of S"
  shows "T = (affine hull T) \<inter> S"
proof -
  have "convex T" using T by (simp add: face_of_def)
  have *: False if x: "x \<in> affine hull T" and "x \<in> S" "x \<notin> T" and y: "y \<in> rel_interior T" for x y
  proof -
    obtain e where "e>0" and e: "cball y e \<inter> affine hull T \<subseteq> T"
      using y by (auto simp: rel_interior_cball)
    have "y \<noteq> x" "y \<in> S" "y \<in> T"
      using face_of_imp_subset rel_interior_subset T that by blast+
    then have zne: "\<And>u. \<lbrakk>u \<in> {0<..<1}; (1 - u) *\<^sub>R y + u *\<^sub>R x \<in> T\<rbrakk> \<Longrightarrow> False"
      using \<open>x \<in> S\<close> \<open>x \<notin> T\<close> \<open>T face_of S\<close> unfolding face_of_def
      by (meson greaterThanLessThan_iff in_segment(2))
    have in01: "min (1/2) (e / norm (x - y)) \<in> {0<..<1}"
      using \<open>y \<noteq> x\<close> \<open>e > 0\<close> by simp
    have \<section>: "norm (min (1/2) (e / norm (x - y)) *\<^sub>R y - min (1/2) (e / norm (x - y)) *\<^sub>R x) \<le> e"
      using \<open>e > 0\<close>
        by (simp add: scaleR_diff_right [symmetric] norm_minus_commute min_mult_distrib_right)
    show False
      apply (rule zne [OF in01 e [THEN subsetD]])
      using \<open>y \<in> T\<close>
        apply (simp add: hull_inc mem_affine x)
        by (simp add: dist_norm algebra_simps \<section>)
  qed
  show ?thesis
  proof (rule subset_antisym)
    show "T \<subseteq> affine hull T \<inter> S"
      using assms by (simp add: hull_subset face_of_imp_subset)
    show "affine hull T \<inter> S \<subseteq> T"
      using "*" \<open>convex T\<close> rel_interior_eq_empty by fastforce
  qed
qed

lemma face_of_imp_closed:
     fixes S :: "'a::euclidean_space set"
     assumes "convex S" "closed S" "T face_of S" shows "closed T"
  by (metis affine_affine_hull affine_closed closed_Int face_of_imp_eq_affine_Int assms)

lemma face_of_Int_supporting_hyperplane_le_strong:
    assumes "convex(S \<inter> {x. a \<bullet> x = b})" and aleb: "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b"
      shows "(S \<inter> {x. a \<bullet> x = b}) face_of S"
proof -
  have *: "a \<bullet> u = a \<bullet> x" if "x \<in> open_segment u v" "u \<in> S" "v \<in> S" and b: "b = a \<bullet> x"
          for u v x
  proof (rule antisym)
    show "a \<bullet> u \<le> a \<bullet> x"
      using aleb \<open>u \<in> S\<close> \<open>b = a \<bullet> x\<close> by blast
  next
    obtain \<xi> where "b = a \<bullet> ((1 - \<xi>) *\<^sub>R u + \<xi> *\<^sub>R v)" "0 < \<xi>" "\<xi> < 1"
      using \<open>b = a \<bullet> x\<close> \<open>x \<in> open_segment u v\<close> in_segment
      by (auto simp: open_segment_image_interval split: if_split_asm)
    then have "b + \<xi> * (a \<bullet> u) \<le> a \<bullet> u + \<xi> * b"
      using aleb [OF \<open>v \<in> S\<close>] by (simp add: algebra_simps)
    then have "(1 - \<xi>) * b \<le> (1 - \<xi>) * (a \<bullet> u)"
      by (simp add: algebra_simps)
    then have "b \<le> a \<bullet> u"
      using \<open>\<xi> < 1\<close> by auto
    with b show "a \<bullet> x \<le> a \<bullet> u" by simp
  qed
  show ?thesis
    using "*" open_segment_commute by (fastforce simp add: face_of_def assms)
qed

lemma face_of_Int_supporting_hyperplane_ge_strong:
   "\<lbrakk>convex(S \<inter> {x. a \<bullet> x = b}); \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk>
    \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  using face_of_Int_supporting_hyperplane_le_strong [of S "-a" "-b"] by simp

lemma face_of_Int_supporting_hyperplane_le:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  by (simp add: convex_Int convex_hyperplane face_of_Int_supporting_hyperplane_le_strong)

lemma face_of_Int_supporting_hyperplane_ge:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  by (simp add: convex_Int convex_hyperplane face_of_Int_supporting_hyperplane_ge_strong)

lemma face_of_imp_convex: "T face_of S \<Longrightarrow> convex T"
  using face_of_def by blast

lemma face_of_imp_compact:
    fixes S :: "'a::euclidean_space set"
    shows "\<lbrakk>convex S; compact S; T face_of S\<rbrakk> \<Longrightarrow> compact T"
  by (meson bounded_subset compact_eq_bounded_closed face_of_imp_closed face_of_imp_subset)

lemma face_of_Int_subface:
     "\<lbrakk>A \<inter> B face_of A; A \<inter> B face_of B; C face_of A; D face_of B\<rbrakk>
      \<Longrightarrow> (C \<inter> D) face_of C \<and> (C \<inter> D) face_of D"
  by (meson face_of_Int_Int face_of_face inf_le1 inf_le2)

lemma subset_of_face_of:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "u \<subseteq> S" "T \<inter> (rel_interior u) \<noteq> {}"
      shows "u \<subseteq> T"
proof
  fix c
  assume "c \<in> u"
  obtain b where "b \<in> T" "b \<in> rel_interior u" using assms by auto
  then obtain e where "e>0" "b \<in> u" and e: "cball b e \<inter> affine hull u \<subseteq> u"
    by (auto simp: rel_interior_cball)
  show "c \<in> T"
  proof (cases "b=c")
    case True with \<open>b \<in> T\<close> show ?thesis by blast
  next
    case False
    define d where "d = b + (e / norm(b - c)) *\<^sub>R (b - c)"
    have "d \<in> cball b e \<inter> affine hull u"
      using \<open>e > 0\<close> \<open>b \<in> u\<close> \<open>c \<in> u\<close>
      by (simp add: d_def dist_norm hull_inc mem_affine_3_minus False)
    with e have "d \<in> u" by blast
    have nbc: "norm (b - c) + e > 0" using \<open>e > 0\<close>
      by (metis add.commute le_less_trans less_add_same_cancel2 norm_ge_zero)
    then have [simp]: "d \<noteq> c" using False scaleR_cancel_left [of "1 + (e / norm (b - c))" b c]
      by (simp add: algebra_simps d_def) (simp add: field_split_simps)
    have [simp]: "((e - e * e / (e + norm (b - c))) / norm (b - c)) = (e / (e + norm (b - c)))"
      using False nbc
      by (simp add: divide_simps) (simp add: algebra_simps)
    have "b \<in> open_segment d c"
      apply (simp add: open_segment_image_interval)
      apply (simp add: d_def algebra_simps image_def)
      apply (rule_tac x="e / (e + norm (b - c))" in bexI)
      using False nbc \<open>0 < e\<close> by (auto simp: algebra_simps)
    then have "d \<in> T \<and> c \<in> T"
      by (meson \<open>b \<in> T\<close> \<open>c \<in> u\<close> \<open>d \<in> u\<close> assms face_ofD subset_iff)
    then show ?thesis ..
  qed
qed

lemma face_of_eq:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "U face_of S" "(rel_interior T) \<inter> (rel_interior U) \<noteq> {}"
    shows "T = U"
  using assms
  unfolding disjoint_iff_not_equal
  by (metis IntI empty_iff face_of_imp_subset mem_rel_interior_ball subset_antisym subset_of_face_of)

lemma face_of_disjoint_rel_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> rel_interior S = {}"
  by (meson assms subset_of_face_of face_of_imp_subset order_refl subset_antisym)

lemma face_of_disjoint_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> interior S = {}"
proof -
  have "T \<inter> interior S \<subseteq> rel_interior S"
    by (meson inf_sup_ord(2) interior_subset_rel_interior order.trans)
  thus ?thesis
    by (metis (no_types) Int_greatest assms face_of_disjoint_rel_interior inf_sup_ord(1) subset_empty)
qed

lemma face_of_subset_rel_boundary:
  fixes S :: "'a::real_normed_vector set"
  assumes "T face_of S" "T \<noteq> S"
    shows "T \<subseteq> (S - rel_interior S)"
by (meson DiffI assms disjoint_iff_not_equal face_of_disjoint_rel_interior face_of_imp_subset rev_subsetD subsetI)

lemma face_of_subset_rel_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "T \<noteq> S"
      shows "T \<subseteq> rel_frontier S"
  using assms closure_subset face_of_disjoint_rel_interior face_of_imp_subset rel_frontier_def by fastforce

lemma face_of_aff_dim_lt:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "T face_of S" "T \<noteq> S"
    shows "aff_dim T < aff_dim S"
proof -
  have "aff_dim T \<le> aff_dim S"
    by (simp add: face_of_imp_subset aff_dim_subset assms)
  moreover have "aff_dim T \<noteq> aff_dim S"
  proof (cases "T = {}")
    case True then show ?thesis
      by (metis aff_dim_empty \<open>T \<noteq> S\<close>)
  next case False then show ?thesis
    by (metis Set.set_insert assms convex_rel_frontier_aff_dim dual_order.irrefl face_of_imp_convex face_of_subset_rel_frontier insert_not_empty subsetI)
  qed
  ultimately show ?thesis
    by simp
qed

lemma subset_of_face_of_affine_hull:
    fixes S :: "'a::euclidean_space set"
  assumes T: "T face_of S" and "convex S" "U \<subseteq> S" and dis: "\<not> disjnt (affine hull T) (rel_interior U)"
  shows "U \<subseteq> T"
proof (rule subset_of_face_of [OF T \<open>U \<subseteq> S\<close>])
  show "T \<inter> rel_interior U \<noteq> {}"
    using face_of_imp_eq_affine_Int [OF \<open>convex S\<close> T] rel_interior_subset [of U] dis \<open>U \<subseteq> S\<close> disjnt_def 
    by fastforce
qed

lemma affine_hull_face_of_disjoint_rel_interior:
    fixes S :: "'a::euclidean_space set"
  assumes "convex S" "F face_of S" "F \<noteq> S"
  shows "affine hull F \<inter> rel_interior S = {}"
  by (metis assms disjnt_def face_of_imp_subset order_refl subset_antisym subset_of_face_of_affine_hull)

lemma affine_diff_divide:
    assumes "affine S" "k \<noteq> 0" "k \<noteq> 1" and xy: "x \<in> S" "y /\<^sub>R (1 - k) \<in> S"
      shows "(x - y) /\<^sub>R k \<in> S"
proof -
  have "inverse(k) *\<^sub>R (x - y) = (1 - inverse k) *\<^sub>R inverse(1 - k) *\<^sub>R y + inverse(k) *\<^sub>R x"
    using assms
    by (simp add: algebra_simps) (simp add: scaleR_left_distrib [symmetric] field_split_simps)
  then show ?thesis
    using \<open>affine S\<close> xy by (auto simp: affine_alt)
qed

proposition face_of_convex_hulls:
      assumes S: "finite S" "T \<subseteq> S" and disj: "affine hull T \<inter> convex hull (S - T) = {}"
      shows  "(convex hull T) face_of (convex hull S)"
proof -
  have fin: "finite T" "finite (S - T)" using assms
    by (auto simp: finite_subset)
  have *: "x \<in> convex hull T"
          if x: "x \<in> convex hull S" and y: "y \<in> convex hull S" and w: "w \<in> convex hull T" "w \<in> open_segment x y"
          for x y w
  proof -
    have waff: "w \<in> affine hull T"
      using convex_hull_subset_affine_hull w by blast
    obtain a b where a: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> a i" and asum: "sum a S = 1" and aeqx: "(\<Sum>i\<in>S. a i *\<^sub>R i) = x"
                 and b: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> b i" and bsum: "sum b S = 1" and beqy: "(\<Sum>i\<in>S. b i *\<^sub>R i) = y"
      using x y by (auto simp: assms convex_hull_finite)
    obtain u where "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> convex hull T" "x \<noteq> y" and weq: "w = (1 - u) *\<^sub>R x + u *\<^sub>R y"
               and u01: "0 < u" "u < 1"
      using w by (auto simp: open_segment_image_interval split: if_split_asm)
    define c where "c i = (1 - u) * a i + u * b i" for i
    have cge0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> c i"
      using a b u01 by (simp add: c_def)
    have sumc1: "sum c S = 1"
      by (simp add: c_def sum.distrib sum_distrib_left [symmetric] asum bsum)
    have sumci_xy: "(\<Sum>i\<in>S. c i *\<^sub>R i) = (1 - u) *\<^sub>R x + u *\<^sub>R y"
      apply (simp add: c_def sum.distrib scaleR_left_distrib)
      by (simp only: scaleR_scaleR [symmetric] Real_Vector_Spaces.scaleR_right.sum [symmetric] aeqx beqy)
    show ?thesis
    proof (cases "sum c (S - T) = 0")
      case True
      have ci0: "\<And>i. i \<in> (S - T) \<Longrightarrow> c i = 0"
        using True cge0 fin(2) sum_nonneg_eq_0_iff by auto
      have a0: "a i = 0" if "i \<in> (S - T)" for i
        using ci0 [OF that] u01 a [of i] b [of i] that
        by (simp add: c_def Groups.ordered_comm_monoid_add_class.add_nonneg_eq_0_iff)
      have [simp]: "sum a T = 1"
        using assms by (metis sum.mono_neutral_cong_right a0 asum)
      show ?thesis
        apply (simp add: convex_hull_finite \<open>finite T\<close>)
        apply (rule_tac x=a in exI)
        using a0 assms
        apply (auto simp: cge0 a aeqx [symmetric] sum.mono_neutral_right)
        done
    next
      case False
      define k where "k = sum c (S - T)"
      have "k > 0" using False
        unfolding k_def by (metis DiffD1 antisym_conv cge0 sum_nonneg not_less)
      have weq_sumsum: "w = sum (\<lambda>x. c x *\<^sub>R x) T + sum (\<lambda>x. c x *\<^sub>R x) (S - T)"
        by (metis (no_types) add.commute S(1) S(2) sum.subset_diff sumci_xy weq)
      show ?thesis
      proof (cases "k = 1")
        case True
        then have "sum c T = 0"
          by (simp add: S k_def sum_diff sumc1)
        then have [simp]: "sum c (S - T) = 1"
          by (simp add: S sum_diff sumc1)
        have ci0: "\<And>i. i \<in> T \<Longrightarrow> c i = 0"
          by (meson \<open>finite T\<close> \<open>sum c T = 0\<close> \<open>T \<subseteq> S\<close> cge0 sum_nonneg_eq_0_iff subsetCE)
        then have [simp]: "(\<Sum>i\<in>S-T. c i *\<^sub>R i) = w"
          by (simp add: weq_sumsum)
        have "w \<in> convex hull (S - T)"
          apply (simp add: convex_hull_finite fin)
          apply (rule_tac x=c in exI)
          apply (auto simp: cge0 weq True k_def)
          done
        then show ?thesis
          using disj waff by blast
      next
        case False
        then have sumcf: "sum c T = 1 - k"
          by (simp add: S k_def sum_diff sumc1)
        have ge0: "\<And>x. x \<in> T \<Longrightarrow> 0 \<le> inverse (1 - k) * c x"
          by (metis \<open>T \<subseteq> S\<close> cge0 inverse_nonnegative_iff_nonnegative mult_nonneg_nonneg subsetD sum_nonneg sumcf)
        have eq1: "(\<Sum>x\<in>T. inverse (1 - k) * c x) = 1"
          by (metis False eq_iff_diff_eq_0 mult.commute right_inverse sum_distrib_left sumcf)
        have "(\<Sum>i\<in>T. c i *\<^sub>R i) /\<^sub>R (1 - k) \<in> convex hull T"
          apply (simp add: convex_hull_finite fin)
          apply (rule_tac x="\<lambda>i. inverse (1-k) * c i" in exI)
          by (metis (mono_tags, lifting) eq1 ge0 scaleR_scaleR scale_sum_right sum.cong)
        with \<open>0 < k\<close>  have "inverse(k) *\<^sub>R (w - sum (\<lambda>i. c i *\<^sub>R i) T) \<in> affine hull T"
          by (simp add: affine_diff_divide [OF affine_affine_hull] False waff convex_hull_subset_affine_hull [THEN subsetD])
        moreover have "inverse(k) *\<^sub>R (w - sum (\<lambda>x. c x *\<^sub>R x) T) \<in> convex hull (S - T)"
          apply (simp add: weq_sumsum convex_hull_finite fin)
          apply (rule_tac x="\<lambda>i. inverse k * c i" in exI)
          using \<open>k > 0\<close> cge0
          apply (auto simp: scaleR_right.sum sum_distrib_left [symmetric] k_def [symmetric])
          done
        ultimately show ?thesis
          using disj by blast
      qed
    qed
  qed
  have [simp]: "convex hull T \<subseteq> convex hull S"
    by (simp add: \<open>T \<subseteq> S\<close> hull_mono)
  show ?thesis
    using open_segment_commute by (auto simp: face_of_def intro: *)
qed

proposition face_of_convex_hull_insert:
  assumes "finite S" "a \<notin> affine hull S" and T: "T face_of convex hull S"
  shows "T face_of convex hull insert a S"
proof -
  have "convex hull S face_of convex hull insert a S"
    by (simp add: assms face_of_convex_hulls insert_Diff_if subset_insertI)
  then show ?thesis
    using T face_of_trans by blast
qed

proposition face_of_affine_trivial:
    assumes "affine S" "T face_of S"
    shows "T = {} \<or> T = S"
proof (rule ccontr, clarsimp)
  assume "T \<noteq> {}" "T \<noteq> S"
  then obtain a where "a \<in> T" by auto
  then have "a \<in> S"
    using \<open>T face_of S\<close> face_of_imp_subset by blast
  have "S \<subseteq> T"
  proof
    fix b  assume "b \<in> S"
    show "b \<in> T"
    proof (cases "a = b")
      case True with \<open>a \<in> T\<close> show ?thesis by auto
    next
      case False
      then have "a \<noteq> 2 *\<^sub>R a - b"
        by (simp add: scaleR_2)
        with False have "a \<in> open_segment (2 *\<^sub>R a - b) b"
        apply (clarsimp simp: open_segment_def closed_segment_def)
        apply (rule_tac x="1/2" in exI)
          by (simp add: algebra_simps)
      moreover have "2 *\<^sub>R a - b \<in> S"
        by (rule mem_affine [OF \<open>affine S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close>, of 2 "-1", simplified])
      moreover note \<open>b \<in> S\<close> \<open>a \<in> T\<close>
      ultimately show ?thesis
        by (rule face_ofD [OF \<open>T face_of S\<close>, THEN conjunct2])
    qed
  qed
  then show False
    using \<open>T \<noteq> S\<close> \<open>T face_of S\<close> face_of_imp_subset by blast
qed


lemma face_of_affine_eq:
   "affine S \<Longrightarrow> (T face_of S \<longleftrightarrow> T = {} \<or> T = S)"
using affine_imp_convex face_of_affine_trivial face_of_refl by auto


proposition Inter_faces_finite_altbound:
    fixes T :: "'a::euclidean_space set set"
    assumes cfaI: "\<And>c. c \<in> T \<Longrightarrow> c face_of S"
    shows "\<exists>F'. finite F' \<and> F' \<subseteq> T \<and> card F' \<le> DIM('a) + 2 \<and> \<Inter>F' = \<Inter>T"
proof (cases "\<forall>F'. finite F' \<and> F' \<subseteq> T \<and> card F' \<le> DIM('a) + 2 \<longrightarrow> (\<exists>c. c \<in> T \<and> c \<inter> (\<Inter>F') \<subset> (\<Inter>F'))")
  case True
  then obtain c where c:
       "\<And>F'. \<lbrakk>finite F'; F' \<subseteq> T; card F' \<le> DIM('a) + 2\<rbrakk> \<Longrightarrow> c F' \<in> T \<and> c F' \<inter> (\<Inter>F') \<subset> (\<Inter>F')"
    by metis
  define d where "d = rec_nat {c{}} (\<lambda>n r. insert (c r) r)"
  have [simp]: "d 0 = {c {}}"
    by (simp add: d_def)
  have dSuc [simp]: "\<And>n. d (Suc n) = insert (c (d n)) (d n)"
    by (simp add: d_def)
  have dn_notempty: "d n \<noteq> {}" for n
    by (induction n) auto
  have dn_le_Suc: "d n \<subseteq> T \<and> finite(d n) \<and> card(d n) \<le> Suc n" if "n \<le> DIM('a) + 2" for n
  using that
  proof (induction n)
    case 0
    then show ?case by (simp add: c)
  next
    case (Suc n)
    then show ?case by (auto simp: c card_insert_if)
  qed
  have aff_dim_le: "aff_dim(\<Inter>(d n)) \<le> DIM('a) - int n" if "n \<le> DIM('a) + 2" for n
  using that
  proof (induction n)
    case 0
    then show ?case
      by (simp add: aff_dim_le_DIM)
  next
    case (Suc n)
    have fs: "\<Inter>(d (Suc n)) face_of S"
      by (meson Suc.prems cfaI dn_le_Suc dn_notempty face_of_Inter subsetCE)
    have condn: "convex (\<Inter>(d n))"
      using Suc.prems nat_le_linear not_less_eq_eq
      by (blast intro: face_of_imp_convex cfaI convex_Inter dest: dn_le_Suc)
    have fdn: "\<Inter>(d (Suc n)) face_of \<Inter>(d n)"
      by (metis (no_types, lifting) Inter_anti_mono Suc.prems dSuc cfaI dn_le_Suc dn_notempty face_of_Inter face_of_imp_subset face_of_subset subset_iff subset_insertI)
    have ne: "\<Inter>(d (Suc n)) \<noteq> \<Inter>(d n)"
      by (metis (no_types, lifting) Suc.prems Suc_leD c complete_lattice_class.Inf_insert dSuc dn_le_Suc less_irrefl order.trans)
    have *: "\<And>m::int. \<And>d. \<And>d'::int. d < d' \<and> d' \<le> m - n \<Longrightarrow> d \<le> m - of_nat(n+1)"
      by arith
    have "aff_dim (\<Inter>(d (Suc n))) < aff_dim (\<Inter>(d n))"
      by (rule face_of_aff_dim_lt [OF condn fdn ne])
    moreover have "aff_dim (\<Inter>(d n)) \<le> int (DIM('a)) - int n"
      using Suc by auto
    ultimately
    have "aff_dim (\<Inter>(d (Suc n))) \<le> int (DIM('a)) - (n+1)" by arith
    then show ?case by linarith
  qed
  have "aff_dim (\<Inter>(d (DIM('a) + 2))) \<le> -2"
      using aff_dim_le [OF order_refl] by simp
  with aff_dim_geq [of "\<Inter>(d (DIM('a) + 2))"] show ?thesis
    using order.trans by fastforce
next
  case False
  then show ?thesis
    apply simp
    apply (erule ex_forward)
    by blast
qed

lemma faces_of_translation:
   "{F. F face_of image (\<lambda>x. a + x) S} = image (image (\<lambda>x. a + x)) {F. F face_of S}"
proof -
  have "\<And>F. F face_of (+) a ` S \<Longrightarrow> \<exists>G. G face_of S \<and> F = (+) a ` G"
    by (metis face_of_imp_subset face_of_translation_eq subset_imageE)
  then show ?thesis
    by (auto simp: image_iff)
qed

proposition face_of_Times:
  assumes "F face_of S" and "F' face_of S'"
    shows "(F \<times> F') face_of (S \<times> S')"
proof -
  have "F \<times> F' \<subseteq> S \<times> S'"
    using assms [unfolded face_of_def] by blast
  moreover
  have "convex (F \<times> F')"
    using assms [unfolded face_of_def] by (blast intro: convex_Times)
  moreover
    have "a \<in> F \<and> a' \<in> F' \<and> b \<in> F \<and> b' \<in> F'"
       if "a \<in> S" "b \<in> S" "a' \<in> S'" "b' \<in> S'" "x \<in> F \<times> F'" "x \<in> open_segment (a,a') (b,b')"
       for a b a' b' x
  proof (cases "b=a \<or> b'=a'")
    case True with that show ?thesis
      using assms
      by (force simp: in_segment dest: face_ofD)
  next
    case False with assms [unfolded face_of_def] that show ?thesis
      by (blast dest!: open_segment_PairD)
  qed
  ultimately show ?thesis
    unfolding face_of_def by blast
qed

corollary face_of_Times_decomp:
    fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
    shows "C face_of (S \<times> S') \<longleftrightarrow> (\<exists>F F'. F face_of S \<and> F' face_of S' \<and> C = F \<times> F')"
     (is "?lhs = ?rhs")
proof
  assume C: ?lhs
  show ?rhs
  proof (cases "C = {}")
    case True then show ?thesis by auto
  next
    case False
    have 1: "fst ` C \<subseteq> S" "snd ` C \<subseteq> S'"
      using C face_of_imp_subset by fastforce+
    have "convex C"
      using C by (metis face_of_imp_convex)
    have conv: "convex (fst ` C)" "convex (snd ` C)"
      by (simp_all add: \<open>convex C\<close> convex_linear_image linear_fst linear_snd)
    have fstab: "a \<in> fst ` C \<and> b \<in> fst ` C"
            if "a \<in> S" "b \<in> S" "x \<in> open_segment a b" "(x,x') \<in> C" for a b x x'
    proof -
      have *: "(x,x') \<in> open_segment (a,x') (b,x')"
        using that by (auto simp: in_segment)
      show ?thesis
        using face_ofD [OF C *] that face_of_imp_subset [OF C] by force
    qed
    have fst: "fst ` C face_of S"
      by (force simp: face_of_def 1 conv fstab)
    have sndab: "a' \<in> snd ` C \<and> b' \<in> snd ` C"
      if "a' \<in> S'" "b' \<in> S'" "x' \<in> open_segment a' b'" "(x,x') \<in> C" for a' b' x x'
    proof -
      have *: "(x,x') \<in> open_segment (x,a') (x,b')"
        using that by (auto simp: in_segment)
      show ?thesis
        using face_ofD [OF C *] that face_of_imp_subset [OF C] by force
    qed
    have snd: "snd ` C face_of S'"
      by (force simp: face_of_def 1 conv sndab)
    have cc: "rel_interior C \<subseteq> rel_interior (fst ` C) \<times> rel_interior (snd ` C)"
      by (force simp: face_of_Times rel_interior_Times conv fst snd \<open>convex C\<close> linear_fst linear_snd rel_interior_convex_linear_image [symmetric])
    have "C = fst ` C \<times> snd ` C"
    proof (rule face_of_eq [OF C])
      show "fst ` C \<times> snd ` C face_of S \<times> S'"
        by (simp add: face_of_Times rel_interior_Times conv fst snd)
      show "rel_interior C \<inter> rel_interior (fst ` C \<times> snd ` C) \<noteq> {}"
        using False rel_interior_eq_empty \<open>convex C\<close> cc
        by (auto simp: face_of_Times rel_interior_Times conv fst)
    qed
    with fst snd show ?thesis by metis
  qed
next
  assume ?rhs with face_of_Times show ?lhs by auto
qed

lemma face_of_Times_eq:
    fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
    shows "(F \<times> F') face_of (S \<times> S') \<longleftrightarrow>
           F = {} \<or> F' = {} \<or> F face_of S \<and> F' face_of S'"
by (auto simp: face_of_Times_decomp times_eq_iff)

lemma hyperplane_face_of_halfspace_le: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<le> b}"
proof -
  have "{x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x = b} = {x. a \<bullet> x = b}"
    by auto
  with face_of_Int_supporting_hyperplane_le [OF convex_halfspace_le [of a b], of a b]
  show ?thesis by auto
qed

lemma hyperplane_face_of_halfspace_ge: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<ge> b}"
proof -
  have "{x. a \<bullet> x \<ge> b} \<inter> {x. a \<bullet> x = b} = {x. a \<bullet> x = b}"
    by auto
  with face_of_Int_supporting_hyperplane_ge [OF convex_halfspace_ge [of b a], of b a]
  show ?thesis by auto
qed

lemma face_of_halfspace_le:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<le> b} \<longleftrightarrow>
         F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<le> b}"
     (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True then show ?thesis
    using face_of_affine_eq affine_UNIV by auto
next
  case False
  then have ine: "interior {x. a \<bullet> x \<le> b} \<noteq> {}"
    using halfspace_eq_empty_lt interior_halfspace_le by blast
  show ?thesis
  proof
    assume L: ?lhs
    have "F face_of {x. a \<bullet> x = b}" if "F \<noteq> {x. a \<bullet> x \<le> b}"
    proof -
      have "F face_of rel_frontier {x. a \<bullet> x \<le> b}"
      proof (rule face_of_subset [OF L])
        show "F \<subseteq> rel_frontier {x. a \<bullet> x \<le> b}"
          by (simp add: L face_of_subset_rel_frontier that)
      qed (force simp: rel_frontier_def closed_halfspace_le)
      then show ?thesis
        using False 
        by (simp add: frontier_halfspace_le rel_frontier_nonempty_interior [OF ine])
    qed
    with L show ?rhs
      using affine_hyperplane face_of_affine_eq by blast
  next
    assume ?rhs
    then show ?lhs
      by (metis convex_halfspace_le empty_face_of face_of_refl hyperplane_face_of_halfspace_le)
  qed
qed

lemma face_of_halfspace_ge:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow>
         F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<ge> b}"
using face_of_halfspace_le [of F "-a" "-b"] by simp

subsection\<open>Exposed faces\<close>

text\<open>That is, faces that are intersection with supporting hyperplane\<close>

definition\<^marker>\<open>tag important\<close> exposed_face_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                               (infixr "(exposed'_face'_of)" 50)
  where "T exposed_face_of S \<longleftrightarrow>
         T face_of S \<and> (\<exists>a b. S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b})"

lemma empty_exposed_face_of [iff]: "{} exposed_face_of S"
  apply (simp add: exposed_face_of_def)
  apply (rule_tac x=0 in exI)
  apply (rule_tac x=1 in exI, force)
  done

lemma exposed_face_of_refl_eq [simp]: "S exposed_face_of S \<longleftrightarrow> convex S"
proof
  assume S: "convex S"
  have "S \<subseteq> {x. 0 \<bullet> x \<le> 0} \<and> S = S \<inter> {x. 0 \<bullet> x = 0}"
    by auto
  with S show "S exposed_face_of S"
    using exposed_face_of_def face_of_refl_eq by blast
qed (simp add: exposed_face_of_def face_of_refl_eq)

lemma exposed_face_of_refl: "convex S \<Longrightarrow> S exposed_face_of S"
  by simp

lemma exposed_face_of:
    "T exposed_face_of S \<longleftrightarrow>
     T face_of S \<and>
     (T = {} \<or> T = S \<or>
      (\<exists>a b. a \<noteq> 0 \<and> S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b}))"
proof (cases "T = {}")
  case True then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof (cases "T = S")
    case True then show ?thesis
      by (simp add: face_of_refl_eq)
  next
    case False
    with \<open>T \<noteq> {}\<close> show ?thesis
      apply (auto simp: exposed_face_of_def)
      apply (metis inner_zero_left)
      done
  qed
qed

lemma exposed_face_of_Int_supporting_hyperplane_le:
   "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
by (force simp: exposed_face_of_def face_of_Int_supporting_hyperplane_le)

lemma exposed_face_of_Int_supporting_hyperplane_ge:
   "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
using exposed_face_of_Int_supporting_hyperplane_le [of S "-a" "-b"] by simp

proposition exposed_face_of_Int:
  assumes "T exposed_face_of S"
      and "u exposed_face_of S"
    shows "(T \<inter> u) exposed_face_of S"
proof -
  obtain a b where T: "S \<inter> {x. a \<bullet> x = b} face_of S"
               and S: "S \<subseteq> {x. a \<bullet> x \<le> b}"
               and teq: "T = S \<inter> {x. a \<bullet> x = b}"
    using assms by (auto simp: exposed_face_of_def)
  obtain a' b' where u: "S \<inter> {x. a' \<bullet> x = b'} face_of S"
                 and s': "S \<subseteq> {x. a' \<bullet> x \<le> b'}"
                 and ueq: "u = S \<inter> {x. a' \<bullet> x = b'}"
    using assms by (auto simp: exposed_face_of_def)
  have tu: "T \<inter> u face_of S"
    using T teq u ueq by (simp add: face_of_Int)
  have ss: "S \<subseteq> {x. (a + a') \<bullet> x \<le> b + b'}"
    using S s' by (force simp: inner_left_distrib)
  show ?thesis
    apply (simp add: exposed_face_of_def tu)
    apply (rule_tac x="a+a'" in exI)
    apply (rule_tac x="b+b'" in exI)
    using S s'
    apply (fastforce simp: ss inner_left_distrib teq ueq)
    done
qed

proposition exposed_face_of_Inter:
    fixes P :: "'a::euclidean_space set set"
  assumes "P \<noteq> {}"
      and "\<And>T. T \<in> P \<Longrightarrow> T exposed_face_of S"
    shows "\<Inter>P exposed_face_of S"
proof -
  obtain Q where "finite Q" and QsubP: "Q \<subseteq> P" "card Q \<le> DIM('a) + 2" and IntQ: "\<Inter>Q = \<Inter>P"
    using Inter_faces_finite_altbound [of P S] assms [unfolded exposed_face_of]
    by force
  show ?thesis
  proof (cases "Q = {}")
    case True then show ?thesis
      by (metis IntQ Inter_UNIV_conv(2) assms(1) assms(2) ex_in_conv)
  next
    case False
    have "Q \<subseteq> {T. T exposed_face_of S}"
      using QsubP assms by blast
    moreover have "Q \<subseteq> {T. T exposed_face_of S} \<Longrightarrow> \<Inter>Q exposed_face_of S"
      using \<open>finite Q\<close> False
      by (induction Q rule: finite_induct; use exposed_face_of_Int in fastforce)
    ultimately show ?thesis
      by (simp add: IntQ)
  qed
qed

proposition exposed_face_of_sums:
  assumes "convex S" and "convex T"
      and "F exposed_face_of {x + y | x y. x \<in> S \<and> y \<in> T}"
          (is "F exposed_face_of ?ST")
  obtains k l
    where "k exposed_face_of S" "l exposed_face_of T"
          "F = {x + y | x y. x \<in> k \<and> y \<in> l}"
proof (cases "F = {}")
  case True then show ?thesis
    using that by blast
next
  case False
  show ?thesis
  proof (cases "F = ?ST")
    case True then show ?thesis
      using assms exposed_face_of_refl_eq that by blast
  next
    case False
    obtain p where "p \<in> F" using \<open>F \<noteq> {}\<close> by blast
    moreover
    obtain u z where T: "?ST \<inter> {x. u \<bullet> x = z} face_of ?ST"
                 and S: "?ST \<subseteq> {x. u \<bullet> x \<le> z}"
                 and feq: "F = ?ST \<inter> {x. u \<bullet> x = z}"
      using assms by (auto simp: exposed_face_of_def)
    ultimately obtain a0 b0
            where p: "p = a0 + b0" and "a0 \<in> S" "b0 \<in> T" and z: "u \<bullet> p = z"
      by auto
    have lez: "u \<bullet> (x + y) \<le> z" if "x \<in> S" "y \<in> T" for x y
      using S that by auto
    have sef: "S \<inter> {x. u \<bullet> x = u \<bullet> a0} exposed_face_of S"
    proof (rule exposed_face_of_Int_supporting_hyperplane_le [OF \<open>convex S\<close>])
      show "\<And>x. x \<in> S \<Longrightarrow> u \<bullet> x \<le> u \<bullet> a0"
        by (metis p z add_le_cancel_right inner_right_distrib lez [OF _ \<open>b0 \<in> T\<close>])
    qed
    have tef: "T \<inter> {x. u \<bullet> x = u \<bullet> b0} exposed_face_of T"
    proof (rule exposed_face_of_Int_supporting_hyperplane_le [OF \<open>convex T\<close>])
      show "\<And>x. x \<in> T \<Longrightarrow> u \<bullet> x \<le> u \<bullet> b0"
        by (metis p z add.commute add_le_cancel_right inner_right_distrib lez [OF \<open>a0 \<in> S\<close>])
    qed
    have "{x + y |x y. x \<in> S \<and> u \<bullet> x = u \<bullet> a0 \<and> y \<in> T \<and> u \<bullet> y = u \<bullet> b0} \<subseteq> F"
      by (auto simp: feq) (metis inner_right_distrib p z)
    moreover have "F \<subseteq> {x + y |x y. x \<in> S \<and> u \<bullet> x = u \<bullet> a0 \<and> y \<in> T \<and> u \<bullet> y = u \<bullet> b0}"
    proof -
      have "\<And>x y. \<lbrakk>z = u \<bullet> (x + y); x \<in> S; y \<in> T\<rbrakk>
           \<Longrightarrow> u \<bullet> x = u \<bullet> a0 \<and> u \<bullet> y = u \<bullet> b0"
        using z p \<open>a0 \<in> S\<close> \<open>b0 \<in> T\<close>
        apply (simp add: inner_right_distrib)
        apply (metis add_le_cancel_right antisym lez [unfolded inner_right_distrib] add.commute)
        done
      then show ?thesis
        using feq by blast
    qed
    ultimately have "F = {x + y |x y. x \<in> S \<inter> {x. u \<bullet> x = u \<bullet> a0} \<and> y \<in> T \<inter> {x. u \<bullet> x = u \<bullet> b0}}"
      by blast
    then show ?thesis
      by (rule that [OF sef tef])
  qed
qed

proposition exposed_face_of_parallel:
   "T exposed_face_of S \<longleftrightarrow>
         T face_of S \<and>
         (\<exists>a b. S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b} \<and>
                (T \<noteq> {} \<longrightarrow> T \<noteq> S \<longrightarrow> a \<noteq> 0) \<and>
                (T \<noteq> S \<longrightarrow> (\<forall>w \<in> affine hull S. (w + a) \<in> affine hull S)))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
  proof (clarsimp simp: exposed_face_of_def)
    fix a b
    assume faceS: "S \<inter> {x. a \<bullet> x = b} face_of S" and Ssub: "S \<subseteq> {x. a \<bullet> x \<le> b}" 
    show "\<exists>c d. S \<subseteq> {x. c \<bullet> x \<le> d} \<and>
                S \<inter> {x. a \<bullet> x = b} = S \<inter> {x. c \<bullet> x = d} \<and>
                (S \<inter> {x. a \<bullet> x = b} \<noteq> {} \<longrightarrow> S \<inter> {x. a \<bullet> x = b} \<noteq> S \<longrightarrow> c \<noteq> 0) \<and>
                (S \<inter> {x. a \<bullet> x = b} \<noteq> S \<longrightarrow> (\<forall>w \<in> affine hull S. w + c \<in> affine hull S))"
    proof (cases "affine hull S \<inter> {x. -a \<bullet> x \<le> -b} = {} \<or> affine hull S \<subseteq> {x. - a \<bullet> x \<le> - b}")
      case True
      then show ?thesis
      proof
        assume "affine hull S \<inter> {x. - a \<bullet> x \<le> - b} = {}"
       then show ?thesis
         apply (rule_tac x="0" in exI)
         apply (rule_tac x="1" in exI)
         using hull_subset by fastforce
    next
      assume "affine hull S \<subseteq> {x. - a \<bullet> x \<le> - b}"
      then show ?thesis
         apply (rule_tac x="0" in exI)
         apply (rule_tac x="0" in exI)
        using Ssub hull_subset by fastforce
    qed
  next
    case False
    then obtain a' b' where "a' \<noteq> 0" 
      and le: "affine hull S \<inter> {x. a' \<bullet> x \<le> b'} = affine hull S \<inter> {x. - a \<bullet> x \<le> - b}" 
      and eq: "affine hull S \<inter> {x. a' \<bullet> x = b'} = affine hull S \<inter> {x. - a \<bullet> x = - b}" 
      and mem: "\<And>w. w \<in> affine hull S \<Longrightarrow> w + a' \<in> affine hull S"
      using affine_parallel_slice affine_affine_hull by metis 
    show ?thesis
    proof (intro conjI impI allI ballI exI)
      have *: "S \<subseteq> - (affine hull S \<inter> {x. P x}) \<union> affine hull S \<inter> {x. Q x} \<Longrightarrow> S \<subseteq> {x. \<not> P x \<or> Q x}" 
        for P Q 
        using hull_subset by fastforce  
      have "S \<subseteq> {x. \<not> (a' \<bullet> x \<le> b') \<or> a' \<bullet> x = b'}"
        by (rule *) (use le eq Ssub in auto)
      then show "S \<subseteq> {x. - a' \<bullet> x \<le> - b'}"
        by auto 
      show "S \<inter> {x. a \<bullet> x = b} = S \<inter> {x. - a' \<bullet> x = - b'}"
        using eq hull_subset [of S affine] by force
      show "\<lbrakk>S \<inter> {x. a \<bullet> x = b} \<noteq> {}; S \<inter> {x. a \<bullet> x = b} \<noteq> S\<rbrakk> \<Longrightarrow> - a' \<noteq> 0"
        using \<open>a' \<noteq> 0\<close> by auto
      show "w + - a' \<in> affine hull S"
        if "S \<inter> {x. a \<bullet> x = b} \<noteq> S" "w \<in> affine hull S" for w
      proof -
        have "w + 1 *\<^sub>R (w - (w + a')) \<in> affine hull S"
          using affine_affine_hull mem mem_affine_3_minus that(2) by blast
        then show ?thesis  by simp
      qed
    qed
  qed
qed
next
  assume ?rhs then show ?lhs
    unfolding exposed_face_of_def by blast
qed

subsection\<open>Extreme points of a set: its singleton faces\<close>

definition\<^marker>\<open>tag important\<close> extreme_point_of :: "['a::real_vector, 'a set] \<Rightarrow> bool"
                               (infixr "(extreme'_point'_of)" 50)
  where "x extreme_point_of S \<longleftrightarrow>
         x \<in> S \<and> (\<forall>a \<in> S. \<forall>b \<in> S. x \<notin> open_segment a b)"

lemma extreme_point_of_stillconvex:
   "convex S \<Longrightarrow> (x extreme_point_of S \<longleftrightarrow> x \<in> S \<and> convex(S - {x}))"
  by (fastforce simp add: convex_contains_segment extreme_point_of_def open_segment_def)

lemma face_of_singleton:
   "{x} face_of S \<longleftrightarrow> x extreme_point_of S"
by (fastforce simp add: extreme_point_of_def face_of_def)

lemma extreme_point_not_in_REL_INTERIOR:
    fixes S :: "'a::real_normed_vector set"
    shows "\<lbrakk>x extreme_point_of S; S \<noteq> {x}\<rbrakk> \<Longrightarrow> x \<notin> rel_interior S"
  by (metis disjoint_iff face_of_disjoint_rel_interior face_of_singleton insertI1)

lemma extreme_point_not_in_interior:
  fixes S :: "'a::{real_normed_vector, perfect_space} set"
  assumes "x extreme_point_of S" shows "x \<notin> interior S"
proof (cases "S = {x}")
  case False
  then show ?thesis
    by (meson assms subsetD extreme_point_not_in_REL_INTERIOR interior_subset_rel_interior)
qed (simp add: empty_interior_finite)

lemma extreme_point_of_face:
     "F face_of S \<Longrightarrow> v extreme_point_of F \<longleftrightarrow> v extreme_point_of S \<and> v \<in> F"
  by (meson empty_subsetI face_of_face face_of_singleton insert_subset)

lemma extreme_point_of_convex_hull:
  "x extreme_point_of (convex hull S) \<Longrightarrow> x \<in> S"
  using hull_minimal [of S "(convex hull S) - {x}" convex]
  using hull_subset [of S convex]
  by (force simp add: extreme_point_of_stillconvex)

proposition extreme_points_of_convex_hull:
   "{x. x extreme_point_of (convex hull S)} \<subseteq> S"
  using extreme_point_of_convex_hull by auto

lemma extreme_point_of_empty [simp]: "\<not> (x extreme_point_of {})"
  by (simp add: extreme_point_of_def)

lemma extreme_point_of_singleton [iff]: "x extreme_point_of {a} \<longleftrightarrow> x = a"
  using extreme_point_of_stillconvex by auto

lemma extreme_point_of_translation_eq:
   "(a + x) extreme_point_of (image (\<lambda>x. a + x) S) \<longleftrightarrow> x extreme_point_of S"
by (auto simp: extreme_point_of_def)

lemma extreme_points_of_translation:
   "{x. x extreme_point_of (image (\<lambda>x. a + x) S)} =
    (\<lambda>x. a + x) ` {x. x extreme_point_of S}"
  using extreme_point_of_translation_eq
  by auto (metis (no_types, lifting) image_iff mem_Collect_eq minus_add_cancel)

lemma extreme_points_of_translation_subtract:
   "{x. x extreme_point_of (image (\<lambda>x. x - a) S)} =
    (\<lambda>x. x - a) ` {x. x extreme_point_of S}"
  using extreme_points_of_translation [of "- a" S]
  by simp

lemma extreme_point_of_Int:
   "\<lbrakk>x extreme_point_of S; x extreme_point_of T\<rbrakk> \<Longrightarrow> x extreme_point_of (S \<inter> T)"
by (simp add: extreme_point_of_def)

lemma extreme_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
  by (metis convex_singleton face_of_Int_supporting_hyperplane_le_strong face_of_singleton)

lemma extreme_point_of_Int_supporting_hyperplane_ge:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
  using extreme_point_of_Int_supporting_hyperplane_le [of S "-a" "-b" c]
  by simp

lemma exposed_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
  unfolding exposed_face_of_def
  by (force simp: face_of_singleton extreme_point_of_Int_supporting_hyperplane_le)

lemma exposed_point_of_Int_supporting_hyperplane_ge:
  "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
  using exposed_point_of_Int_supporting_hyperplane_le [of S "-a" "-b" c]
  by simp

lemma extreme_point_of_convex_hull_insert:
  assumes "finite S" "a \<notin> convex hull S"
  shows "a extreme_point_of (convex hull (insert a S))"
proof (cases "a \<in> S")
  case False
  then show ?thesis
   using face_of_convex_hulls [of "insert a S" "{a}"] assms
   by (auto simp: face_of_singleton hull_same)
qed (use assms  in \<open>simp add: hull_inc\<close>)

subsection\<open>Facets\<close>

definition\<^marker>\<open>tag important\<close> facet_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                    (infixr "(facet'_of)" 50)
  where "F facet_of S \<longleftrightarrow> F face_of S \<and> F \<noteq> {} \<and> aff_dim F = aff_dim S - 1"

lemma facet_of_empty [simp]: "\<not> S facet_of {}"
  by (simp add: facet_of_def)

lemma facet_of_irrefl [simp]: "\<not> S facet_of S "
  by (simp add: facet_of_def)

lemma facet_of_imp_face_of: "F facet_of S \<Longrightarrow> F face_of S"
  by (simp add: facet_of_def)

lemma facet_of_imp_subset: "F facet_of S \<Longrightarrow> F \<subseteq> S"
  by (simp add: face_of_imp_subset facet_of_def)

lemma hyperplane_facet_of_halfspace_le:
   "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<le> b}"
unfolding facet_of_def hyperplane_eq_empty
by (auto simp: hyperplane_face_of_halfspace_ge hyperplane_face_of_halfspace_le
           Suc_leI of_nat_diff aff_dim_halfspace_le)

lemma hyperplane_facet_of_halfspace_ge:
    "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<ge> b}"
unfolding facet_of_def hyperplane_eq_empty
by (auto simp: hyperplane_face_of_halfspace_le hyperplane_face_of_halfspace_ge
           Suc_leI of_nat_diff aff_dim_halfspace_ge)

lemma facet_of_halfspace_le:
    "F facet_of {x. a \<bullet> x \<le> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
    (is "?lhs = ?rhs")
proof
  assume c: ?lhs
  with c facet_of_irrefl show ?rhs
    by (force simp: aff_dim_halfspace_le facet_of_def face_of_halfspace_le cong: conj_cong split: if_split_asm)
next
  assume ?rhs then show ?lhs
    by (simp add: hyperplane_facet_of_halfspace_le)
qed

lemma facet_of_halfspace_ge:
    "F facet_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
using facet_of_halfspace_le [of F "-a" "-b"] by simp

subsection \<open>Edges: faces of affine dimension 1\<close> (*FIXME too small subsection, rearrange? *)

definition\<^marker>\<open>tag important\<close> edge_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"  (infixr "(edge'_of)" 50)
  where "e edge_of S \<longleftrightarrow> e face_of S \<and> aff_dim e = 1"

lemma edge_of_imp_subset:
   "S edge_of T \<Longrightarrow> S \<subseteq> T"
by (simp add: edge_of_def face_of_imp_subset)

subsection\<open>Existence of extreme points\<close>

proposition different_norm_3_collinear_points:
  fixes a :: "'a::euclidean_space"
  assumes "x \<in> open_segment a b" "norm(a) = norm(b)" "norm(x) = norm(b)"
  shows False
proof -
  obtain u where "norm ((1 - u) *\<^sub>R a + u *\<^sub>R b) = norm b"
             and "a \<noteq> b"
             and u01: "0 < u" "u < 1"
    using assms by (auto simp: open_segment_image_interval if_splits)
  then have "(1 - u) *\<^sub>R a \<bullet> (1 - u) *\<^sub>R a + ((1 - u) * 2) *\<^sub>R a \<bullet> u *\<^sub>R b =
             (1 - u * u) *\<^sub>R (a \<bullet> a)"
    using assms by (simp add: norm_eq algebra_simps inner_commute)
  then have "(1 - u) *\<^sub>R ((1 - u) *\<^sub>R a \<bullet> a + (2 * u) *\<^sub>R  a \<bullet> b) =
             (1 - u) *\<^sub>R ((1 + u) *\<^sub>R (a \<bullet> a))"
    by (simp add: algebra_simps)
  then have "(1 - u) *\<^sub>R (a \<bullet> a) + (2 * u) *\<^sub>R (a \<bullet> b) = (1 + u) *\<^sub>R (a \<bullet> a)"
    using u01 by auto
  then have "a \<bullet> b = a \<bullet> a"
    using u01 by (simp add: algebra_simps)
  then have "a = b"
    using \<open>norm(a) = norm(b)\<close> norm_eq vector_eq by fastforce
  then show ?thesis
    using \<open>a \<noteq> b\<close> by force
qed

proposition extreme_point_exists_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S" "S \<noteq> {}"
  obtains x where "x extreme_point_of S"
proof -
  obtain x where "x \<in> S" and xsup: "\<And>y. y \<in> S \<Longrightarrow> norm y \<le> norm x"
    using distance_attains_sup [of S 0] assms by auto
  have False if "a \<in> S" "b \<in> S" and x: "x \<in> open_segment a b" for a b
  proof -
    have noax: "norm a \<le> norm x" and nobx: "norm b \<le> norm x" using xsup that by auto
    have "a \<noteq> b"
      using empty_iff open_segment_idem x by auto
    show False
      by (metis dist_0_norm dist_decreases_open_segment noax nobx not_le x)
  qed
  then show ?thesis
    by (meson \<open>x \<in> S\<close> extreme_point_of_def that)
qed

subsection\<open>Krein-Milman, the weaker form\<close>

proposition Krein_Milman:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = closure(convex hull {x. x extreme_point_of S})"
proof (cases "S = {}")
  case True then show ?thesis   by simp
next
  case False
  have "closed S"
    by (simp add: \<open>compact S\<close> compact_imp_closed)
  have "closure (convex hull {x. x extreme_point_of S}) \<subseteq> S"
    by (simp add: \<open>closed S\<close> assms closure_minimal extreme_point_of_def hull_minimal)
  moreover have "u \<in> closure (convex hull {x. x extreme_point_of S})"
                if "u \<in> S" for u
  proof (rule ccontr)
    assume unot: "u \<notin> closure(convex hull {x. x extreme_point_of S})"
    then obtain a b where "a \<bullet> u < b"
          and ab: "\<And>x. x \<in> closure(convex hull {x. x extreme_point_of S}) \<Longrightarrow> b < a \<bullet> x"
      using separating_hyperplane_closed_point [of "closure(convex hull {x. x extreme_point_of S})"]
      by blast
    have "continuous_on S ((\<bullet>) a)"
      by (rule continuous_intros)+
    then obtain m where "m \<in> S" and m: "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> m \<le> a \<bullet> y"
      using continuous_attains_inf [of S "\<lambda>x. a \<bullet> x"] \<open>compact S\<close> \<open>u \<in> S\<close>
      by auto
    define T where "T = S \<inter> {x. a \<bullet> x = a \<bullet> m}"
    have "m \<in> T"
      by (simp add: T_def \<open>m \<in> S\<close>)
    moreover have "compact T"
      by (simp add: T_def compact_Int_closed [OF \<open>compact S\<close> closed_hyperplane])
    moreover have "convex T"
      by (simp add: T_def convex_Int [OF \<open>convex S\<close> convex_hyperplane])
    ultimately obtain v where v: "v extreme_point_of T"
      using extreme_point_exists_convex [of T] by auto
    then have "{v} face_of T"
      by (simp add: face_of_singleton)
    also have "T face_of S"
      by (simp add: T_def m face_of_Int_supporting_hyperplane_ge [OF \<open>convex S\<close>])
    finally have "v extreme_point_of S"
      by (simp add: face_of_singleton)
    then have "b < a \<bullet> v"
      using closure_subset by (simp add: closure_hull hull_inc ab)
    then show False
      using \<open>a \<bullet> u < b\<close> \<open>{v} face_of T\<close> face_of_imp_subset m T_def that by fastforce
  qed
  ultimately show ?thesis
    by blast
qed

text\<open>Now the sharper form.\<close>

lemma Krein_Milman_Minkowski_aux:
  fixes S :: "'a::euclidean_space set"
  assumes n: "dim S = n" and S: "compact S" "convex S" "0 \<in> S"
    shows "0 \<in> convex hull {x. x extreme_point_of S}"
using n S
proof (induction n arbitrary: S rule: less_induct)
  case (less n S) show ?case
  proof (cases "0 \<in> rel_interior S")
    case True with Krein_Milman less.prems 
    show ?thesis
      by (metis subsetD convex_convex_hull convex_rel_interior_closure rel_interior_subset)
  next
    case False
    have "rel_interior S \<noteq> {}"
      by (simp add: rel_interior_convex_nonempty_aux less)
    then obtain c where c: "c \<in> rel_interior S" by blast
    obtain a where "a \<noteq> 0"
              and le_ay: "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> 0 \<le> a \<bullet> y"
              and less_ay: "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> 0 < a \<bullet> y"
      by (blast intro: supporting_hyperplane_rel_boundary intro!: less False)
    have face: "S \<inter> {x. a \<bullet> x = 0} face_of S"
      using face_of_Int_supporting_hyperplane_ge le_ay \<open>convex S\<close> by auto
    then have co: "compact (S \<inter> {x. a \<bullet> x = 0})" "convex (S \<inter> {x. a \<bullet> x = 0})"
      using less.prems by (blast intro: face_of_imp_compact face_of_imp_convex)+
    have "a \<bullet> y = 0" if "y \<in> span (S \<inter> {x. a \<bullet> x = 0})" for y
    proof -
      have "y \<in> span {x. a \<bullet> x = 0}"
        by (metis inf.cobounded2 span_mono subsetCE that)
      then show ?thesis
        by (blast intro: span_induct [OF _ subspace_hyperplane])
    qed
    then have "dim (S \<inter> {x. a \<bullet> x = 0}) < n"
      by (metis (no_types) less_ay c subsetD dim_eq_span inf.strict_order_iff
           inf_le1 \<open>dim S = n\<close> not_le rel_interior_subset span_0 span_base)
    then have "0 \<in> convex hull {x. x extreme_point_of (S \<inter> {x. a \<bullet> x = 0})}"
      by (rule less.IH) (auto simp: co less.prems)
    then show ?thesis
      by (metis (mono_tags, lifting) Collect_mono_iff face extreme_point_of_face hull_mono subset_iff)
  qed
qed


theorem Krein_Milman_Minkowski:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = convex hull {x. x extreme_point_of S}"
proof
  show "S \<subseteq> convex hull {x. x extreme_point_of S}"
  proof
    fix a assume [simp]: "a \<in> S"
    have 1: "compact ((+) (- a) ` S)"
      by (simp add: \<open>compact S\<close> compact_translation_subtract cong: image_cong_simp)
    have 2: "convex ((+) (- a) ` S)"
      by (simp add: \<open>convex S\<close> compact_translation_subtract)
    show a_invex: "a \<in> convex hull {x. x extreme_point_of S}"
      using Krein_Milman_Minkowski_aux [OF refl 1 2]
            convex_hull_translation [of "-a"]
      by (auto simp: extreme_points_of_translation_subtract translation_assoc cong: image_cong_simp)
    qed
next
  show "convex hull {x. x extreme_point_of S} \<subseteq> S"
  proof -
    have "{a. a extreme_point_of S} \<subseteq> S"
      using extreme_point_of_def by blast
    then show ?thesis
      by (simp add: \<open>convex S\<close> hull_minimal)
  qed
qed


subsection\<open>Applying it to convex hulls of explicitly indicated finite sets\<close>

corollary Krein_Milman_polytope:
  fixes S :: "'a::euclidean_space set"
  shows
   "finite S
       \<Longrightarrow> convex hull S =
           convex hull {x. x extreme_point_of (convex hull S)}"
  by (simp add: Krein_Milman_Minkowski finite_imp_compact_convex_hull)

lemma extreme_points_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
        \<Longrightarrow> {x. x extreme_point_of (convex hull S)} = S"
by (metis (full_types) Krein_Milman_Minkowski compact_convex_hull convex_convex_hull extreme_points_of_convex_hull psubsetI)


lemma extreme_point_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
    \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
using extreme_points_of_convex_hull_eq by auto

lemma extreme_point_of_convex_hull_convex_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and S: "\<And>a. a \<in> S \<Longrightarrow> a \<notin> convex hull (S - {a})"
  shows "(x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
proof -
  have "convex hull T \<noteq> convex hull S" if "T \<subset> S" for T
  proof -
    obtain a where  "T \<subseteq> S" "a \<in> S" "a \<notin> T" using \<open>T \<subset> S\<close> by blast
    then show ?thesis
      by (metis (full_types) Diff_eq_empty_iff Diff_insert0 S hull_mono hull_subset insert_Diff_single subsetCE)
  qed
  then show ?thesis
    by (rule extreme_point_of_convex_hull_eq [OF \<open>compact S\<close>])
qed

lemma extreme_point_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<not> affine_dependent S
         \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
by (metis aff_independent_finite affine_dependent_def affine_hull_convex_hull extreme_point_of_convex_hull_convex_independent finite_imp_compact hull_inc)

text\<open>Elementary proofs exist, not requiring Euclidean spaces and all this development\<close>
lemma extreme_point_of_convex_hull_2:
  fixes x :: "'a::euclidean_space"
  shows "x extreme_point_of (convex hull {a,b}) \<longleftrightarrow> x = a \<or> x = b"
proof -
  have "x extreme_point_of (convex hull {a,b}) \<longleftrightarrow> x \<in> {a,b}"
    by (intro extreme_point_of_convex_hull_affine_independent affine_independent_2)
  then show ?thesis
    by simp
qed

lemma extreme_point_of_segment:
  fixes x :: "'a::euclidean_space"
  shows
   "x extreme_point_of closed_segment a b \<longleftrightarrow> x = a \<or> x = b"
by (simp add: extreme_point_of_convex_hull_2 segment_convex_hull)

lemma face_of_convex_hull_subset:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and T: "T face_of (convex hull S)"
  obtains s' where "s' \<subseteq> S" "T = convex hull s'"
proof
  show "{x. x extreme_point_of T} \<subseteq> S"
    using T extreme_point_of_convex_hull extreme_point_of_face by blast
  show "T = convex hull {x. x extreme_point_of T}"
  proof (rule Krein_Milman_Minkowski)
    show "compact T"
      using T assms compact_convex_hull face_of_imp_compact by auto
    show "convex T"
      using T face_of_imp_convex by blast
  qed
qed


lemma face_of_convex_hull_aux:
  assumes eq: "x *\<^sub>R p = u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c"
    and x: "u + v + w = x" "x \<noteq> 0" and S: "affine S" "a \<in> S" "b \<in> S" "c \<in> S"
  shows "p \<in> S"
proof -
  have "p = (u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c) /\<^sub>R x"
    by (metis \<open>x \<noteq> 0\<close> eq mult.commute right_inverse scaleR_one scaleR_scaleR)
  moreover have "affine hull {a,b,c} \<subseteq> S"
    by (simp add: S hull_minimal)
  moreover have "(u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c) /\<^sub>R x \<in> affine hull {a,b,c}"
    apply (simp add: affine_hull_3)
    apply (rule_tac x="u/x" in exI)
    apply (rule_tac x="v/x" in exI)
    apply (rule_tac x="w/x" in exI)
    using x apply (auto simp: field_split_simps)
    done
  ultimately show ?thesis by force
qed

proposition face_of_convex_hull_insert_eq:
  fixes a :: "'a :: euclidean_space"
  assumes "finite S" and a: "a \<notin> affine hull S"
  shows "(F face_of (convex hull (insert a S)) \<longleftrightarrow>
          F face_of (convex hull S) \<or>
          (\<exists>F'. F' face_of (convex hull S) \<and> F = convex hull (insert a F')))"
         (is "F face_of ?CAS \<longleftrightarrow> _")
proof safe
  assume F: "F face_of ?CAS"
    and *: "\<nexists>F'. F' face_of convex hull S \<and> F = convex hull insert a F'"
  obtain T where T: "T \<subseteq> insert a S" and FeqT: "F = convex hull T"
    by (metis F \<open>finite S\<close> compact_insert finite_imp_compact face_of_convex_hull_subset)
  show "F face_of convex hull S"
  proof (cases "a \<in> T")
    case True
    have "F = convex hull insert a (convex hull T \<inter> convex hull S)"
    proof
      have "T \<subseteq> insert a (convex hull T \<inter> convex hull S)"
        using T hull_subset by fastforce
      then show "F \<subseteq> convex hull insert a (convex hull T \<inter> convex hull S)"
        by (simp add: FeqT hull_mono)
      show "convex hull insert a (convex hull T \<inter> convex hull S) \<subseteq> F"
        by (simp add: FeqT True hull_inc hull_minimal)
    qed
    moreover have "convex hull T \<inter> convex hull S face_of convex hull S"
      by (metis F FeqT convex_convex_hull face_of_slice hull_mono inf.absorb_iff2 subset_insertI)
    ultimately show ?thesis
      using * by force
  next
    case False
    then show ?thesis
      by (metis FeqT F T face_of_subset hull_mono subset_insert subset_insertI)
  qed
next
  assume "F face_of convex hull S"
  show "F face_of ?CAS"
    by (simp add: \<open>F face_of convex hull S\<close> a face_of_convex_hull_insert \<open>finite S\<close>)
next
  fix F
  assume F: "F face_of convex hull S"
  show "convex hull insert a F face_of ?CAS"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using F face_of_affine_eq by auto
  next
    case False
    have anotc: "a \<notin> convex hull S"
      by (metis (no_types) a affine_hull_convex_hull hull_inc)
    show ?thesis
    proof (cases "F = {}")
      case True show ?thesis
        using anotc by (simp add: \<open>F = {}\<close> \<open>finite S\<close> extreme_point_of_convex_hull_insert face_of_singleton)
    next
      case False
      have "convex hull insert a F \<subseteq> ?CAS"
        by (simp add: F a \<open>finite S\<close> convex_hull_subset face_of_convex_hull_insert face_of_imp_subset hull_inc)
      moreover
      have "(\<exists>y v. (1 - ub) *\<^sub>R a + ub *\<^sub>R b = (1 - v) *\<^sub>R a + v *\<^sub>R y \<and>
                   0 \<le> v \<and> v \<le> 1 \<and> y \<in> F) \<and>
            (\<exists>x u. (1 - uc) *\<^sub>R a + uc *\<^sub>R c = (1 - u) *\<^sub>R a + u *\<^sub>R x \<and>
                   0 \<le> u \<and> u \<le> 1 \<and> x \<in> F)"
        if *: "(1 - ux) *\<^sub>R a + ux *\<^sub>R x
               \<in> open_segment ((1 - ub) *\<^sub>R a + ub *\<^sub>R b) ((1 - uc) *\<^sub>R a + uc *\<^sub>R c)"
          and "0 \<le> ub" "ub \<le> 1" "0 \<le> uc" "uc \<le> 1" "0 \<le> ux" "ux \<le> 1"
          and b: "b \<in> convex hull S" and c: "c \<in> convex hull S" and "x \<in> F"
        for b c ub uc ux x
      proof -
        have xah: "x \<in> affine hull S"
          using F convex_hull_subset_affine_hull face_of_imp_subset \<open>x \<in> F\<close> by blast
        have ah: "b \<in> affine hull S" "c \<in> affine hull S" 
          using b c convex_hull_subset_affine_hull by blast+
        obtain v where ne: "(1 - ub) *\<^sub>R a + ub *\<^sub>R b \<noteq> (1 - uc) *\<^sub>R a + uc *\<^sub>R c"
          and eq: "(1 - ux) *\<^sub>R a + ux *\<^sub>R x =
                    (1 - v) *\<^sub>R ((1 - ub) *\<^sub>R a + ub *\<^sub>R b) + v *\<^sub>R ((1 - uc) *\<^sub>R a + uc *\<^sub>R c)"
          and "0 < v" "v < 1"
          using * by (auto simp: in_segment)
        then have 0: "((1 - ux) - ((1 - v) * (1 - ub) + v * (1 - uc))) *\<^sub>R a +
                      (ux *\<^sub>R x - (((1 - v) * ub) *\<^sub>R b + (v * uc) *\<^sub>R c)) = 0"
          by (auto simp: algebra_simps)
        then have "((1 - ux) - ((1 - v) * (1 - ub) + v * (1 - uc))) *\<^sub>R a =
                   ((1 - v) * ub) *\<^sub>R b + (v * uc) *\<^sub>R c + (-ux) *\<^sub>R x"
          by (auto simp: algebra_simps)
        then have "a \<in> affine hull S" if "1 - ux - ((1 - v) * (1 - ub) + v * (1 - uc)) \<noteq> 0"
          by (rule face_of_convex_hull_aux) (use b c xah ah that in \<open>auto simp: algebra_simps\<close>)
        then have "1 - ux - ((1 - v) * (1 - ub) + v * (1 - uc)) = 0"
          using a by blast
        with 0 have equx: "(1 - v) * ub + v * uc = ux"
          and uxx: "ux *\<^sub>R x = (((1 - v) * ub) *\<^sub>R b + (v * uc) *\<^sub>R c)"
          by auto (auto simp: algebra_simps)
        show ?thesis
        proof (cases "uc = 0")
          case True
          then show ?thesis
            using equx \<open>0 \<le> ub\<close> \<open>ub \<le> 1\<close> \<open>v < 1\<close> uxx \<open>x \<in> F\<close> by force
        next
          case False
          show ?thesis
          proof (cases "ub = 0")
            case True
            then show ?thesis
              using equx \<open>0 \<le> uc\<close> \<open>uc \<le> 1\<close> \<open>0 < v\<close> uxx \<open>x \<in> F\<close> by force
          next
            case False
            then have "0 < ub" "0 < uc"
              using \<open>uc \<noteq> 0\<close> \<open>0 \<le> ub\<close> \<open>0 \<le> uc\<close> by auto
            then have "(1 - v) * ub > 0" "v * uc > 0"
              by (simp_all add: \<open>0 < uc\<close> \<open>0 < v\<close> \<open>v < 1\<close>)
            then have "ux \<noteq> 0"
              using equx \<open>0 < v\<close> by auto
            have "b \<in> F \<and> c \<in> F"
            proof (cases "b = c")
              case True
              then show ?thesis
                by (metis \<open>ux \<noteq> 0\<close> equx real_vector.scale_cancel_left scaleR_add_left uxx \<open>x \<in> F\<close>)
            next
              case False
              have "x = (((1 - v) * ub) *\<^sub>R b + (v * uc) *\<^sub>R c) /\<^sub>R ux"
                by (metis \<open>ux \<noteq> 0\<close> uxx mult.commute right_inverse scaleR_one scaleR_scaleR)
              also have "... = (1 - v * uc / ux) *\<^sub>R b + (v * uc / ux) *\<^sub>R c"
                using \<open>ux \<noteq> 0\<close> equx apply (auto simp: field_split_simps)
                by (metis add.commute add_diff_eq add_divide_distrib diff_add_cancel scaleR_add_left)
              finally have "x = (1 - v * uc / ux) *\<^sub>R b + (v * uc / ux) *\<^sub>R c" .
              then have "x \<in> open_segment b c"
                apply (simp add: in_segment \<open>b \<noteq> c\<close>)
                apply (rule_tac x="(v * uc) / ux" in exI)
                using \<open>0 \<le> ux\<close> \<open>ux \<noteq> 0\<close> \<open>0 < uc\<close> \<open>0 < v\<close> \<open>0 < ub\<close> \<open>v < 1\<close> equx
                apply (force simp: field_split_simps)
                done
              then show ?thesis
                by (rule face_ofD [OF F _ b c \<open>x \<in> F\<close>])
            qed
            with \<open>0 \<le> ub\<close> \<open>ub \<le> 1\<close> \<open>0 \<le> uc\<close> \<open>uc \<le> 1\<close> show ?thesis by blast
          qed
        qed
      qed
      moreover have "convex hull F = F"
        by (meson F convex_hull_eq face_of_imp_convex)
      ultimately show ?thesis
        unfolding face_of_def by (fastforce simp: convex_hull_insert_alt \<open>S \<noteq> {}\<close> \<open>F \<noteq> {}\<close>)
    qed
  qed
qed

lemma face_of_convex_hull_insert2:
  fixes a :: "'a :: euclidean_space"
  assumes S: "finite S" and a: "a \<notin> affine hull S" and F: "F face_of convex hull S"
  shows "convex hull (insert a F) face_of convex hull (insert a S)"
  by (metis F face_of_convex_hull_insert_eq [OF S a])

proposition face_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
    shows "(T face_of (convex hull S) \<longleftrightarrow> (\<exists>c. c \<subseteq> S \<and> T = convex hull c))"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson \<open>T face_of convex hull S\<close> aff_independent_finite assms face_of_convex_hull_subset finite_imp_compact)
next
  assume ?rhs
  then obtain c where "c \<subseteq> S" and T: "T = convex hull c"
    by blast
  have "affine hull c \<inter> affine hull (S - c) = {}"
    by (intro disjoint_affine_hull [OF assms \<open>c \<subseteq> S\<close>], auto)
  then have "affine hull c \<inter> convex hull (S - c) = {}"
    using convex_hull_subset_affine_hull by fastforce
  then show ?lhs
    by (metis face_of_convex_hulls \<open>c \<subseteq> S\<close> aff_independent_finite assms T)
qed

lemma facet_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
    shows "T facet_of (convex hull S) \<longleftrightarrow>
           T \<noteq> {} \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u}))"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "T face_of (convex hull S)" "T \<noteq> {}"
        and afft: "aff_dim T = aff_dim (convex hull S) - 1"
    by (auto simp: facet_of_def)
  then obtain c where "c \<subseteq> S" and c: "T = convex hull c"
    by (auto simp: face_of_convex_hull_affine_independent [OF assms])
  then have affs: "aff_dim S = aff_dim c + 1"
    by (metis aff_dim_convex_hull afft eq_diff_eq)
  have "\<not> affine_dependent c"
    using \<open>c \<subseteq> S\<close> affine_dependent_subset assms by blast
  with affs have "card (S - c) = 1"
    apply (simp add: aff_dim_affine_independent [symmetric] aff_dim_convex_hull)
    by (metis aff_dim_affine_independent aff_independent_finite One_nat_def \<open>c \<subseteq> S\<close> add.commute
                add_diff_cancel_right' assms card_Diff_subset card_mono of_nat_1 of_nat_diff of_nat_eq_iff)
  then obtain u where u: "u \<in> S - c"
    by (metis DiffI \<open>c \<subseteq> S\<close> aff_independent_finite assms cancel_comm_monoid_add_class.diff_cancel
                card_Diff_subset subsetI subset_antisym zero_neq_one)
  then have u: "S = insert u c"
    by (metis Diff_subset \<open>c \<subseteq> S\<close> \<open>card (S - c) = 1\<close> card_1_singletonE double_diff insert_Diff insert_subset singletonD)
  have "T = convex hull (c - {u})"
    by (metis Diff_empty Diff_insert0 \<open>T facet_of convex hull S\<close> c facet_of_irrefl insert_absorb u)
  with \<open>T \<noteq> {}\<close> show ?rhs
    using c u by auto
next
  assume ?rhs
  then obtain u where "T \<noteq> {}" "u \<in> S" and u: "T = convex hull (S - {u})"
    by (force simp: facet_of_def)
  then have "\<not> S \<subseteq> {u}"
    using \<open>T \<noteq> {}\<close> u by auto
  have "aff_dim (S - {u}) = aff_dim S - 1"
    using assms \<open>u \<in> S\<close>
    unfolding affine_dependent_def
    by (metis add_diff_cancel_right' aff_dim_insert insert_Diff [of u S])
  then have "aff_dim (convex hull (S - {u})) = aff_dim (convex hull S) - 1"
    by (simp add: aff_dim_convex_hull)
  then show ?lhs
    by (metis Diff_subset \<open>T \<noteq> {}\<close> assms face_of_convex_hull_affine_independent facet_of_def u)
qed

lemma facet_of_convex_hull_affine_independent_alt:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "(T facet_of (convex hull S) \<longleftrightarrow> 2 \<le> card S \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u})))"
        (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  then obtain x where
    "x \<in> S" and x: "T = convex hull (S - {x})" and "finite S"
    using assms facet_of_convex_hull_affine_independent aff_independent_finite by blast
  moreover have "Suc (Suc 0) \<le> card S"
    using L  x \<open>x \<in> S\<close> \<open>finite S\<close>
    by (metis Suc_leI assms card.remove convex_hull_eq_empty card_gt_0_iff facet_of_convex_hull_affine_independent finite_Diff not_less_eq_eq)
  ultimately show ?rhs
    by auto
next
  assume ?rhs then show ?lhs
    using assms
    by (auto simp: facet_of_convex_hull_affine_independent Set.subset_singleton_iff)
qed

lemma segment_face_of:
  assumes "(closed_segment a b) face_of S"
  shows "a extreme_point_of S" "b extreme_point_of S"
proof -
  have as: "{a} face_of S"
    by (metis (no_types) assms convex_hull_singleton empty_iff extreme_point_of_convex_hull_insert face_of_face face_of_singleton finite.emptyI finite.insertI insert_absorb insert_iff segment_convex_hull)
  moreover have "{b} face_of S"
  proof -
    have "b \<in> convex hull {a} \<or> b extreme_point_of convex hull {b, a}"
      by (meson extreme_point_of_convex_hull_insert finite.emptyI finite.insertI)
    moreover have "closed_segment a b = convex hull {b, a}"
      using closed_segment_commute segment_convex_hull by blast
    ultimately show ?thesis
      by (metis as assms face_of_face convex_hull_singleton empty_iff face_of_singleton insertE)
    qed
  ultimately show "a extreme_point_of S" "b extreme_point_of S"
    using face_of_singleton by blast+
qed


proposition Krein_Milman_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "compact S"
    shows "S = convex hull (frontier S)"
          (is "?lhs = ?rhs")
proof
  have "?lhs \<subseteq> convex hull {x. x extreme_point_of S}"
    using Krein_Milman_Minkowski assms by blast
  also have "... \<subseteq> ?rhs"
  proof (rule hull_mono)
    show "{x. x extreme_point_of S} \<subseteq> frontier S"
      using closure_subset
      by (auto simp: frontier_def extreme_point_not_in_interior extreme_point_of_def)
  qed
  finally show "?lhs \<subseteq> ?rhs" .
next
  have "?rhs \<subseteq> convex hull S"
    by (metis Diff_subset \<open>compact S\<close> closure_closed compact_eq_bounded_closed frontier_def hull_mono)
  also have "... \<subseteq> ?lhs"
    by (simp add: \<open>convex S\<close> hull_same)
  finally show "?rhs \<subseteq> ?lhs" .
qed

subsection\<open>Polytopes\<close>

definition\<^marker>\<open>tag important\<close> polytope where
 "polytope S \<equiv> \<exists>v. finite v \<and> S = convex hull v"

lemma polytope_translation_eq: "polytope (image (\<lambda>x. a + x) S) \<longleftrightarrow> polytope S"
proof -
  have "\<And>a A. polytope A \<Longrightarrow> polytope ((+) a ` A)"
    by (metis (no_types) convex_hull_translation finite_imageI polytope_def)
  then show ?thesis
    by (metis (no_types) add.left_inverse image_add_0 translation_assoc)
qed

lemma polytope_linear_image: "\<lbrakk>linear f; polytope p\<rbrakk> \<Longrightarrow> polytope(image f p)"
  unfolding polytope_def using convex_hull_linear_image by blast

lemma polytope_empty: "polytope {}"
  using convex_hull_empty polytope_def by blast

lemma polytope_convex_hull: "finite S \<Longrightarrow> polytope(convex hull S)"
  using polytope_def by auto

lemma polytope_Times: "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<times> T)"
  unfolding polytope_def
  by (metis finite_cartesian_product convex_hull_Times)

lemma face_of_polytope_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>polytope S; F face_of S\<rbrakk> \<Longrightarrow> polytope F"
unfolding polytope_def
by (meson face_of_convex_hull_subset finite_imp_compact finite_subset)

lemma finite_polytope_faces:
  fixes S :: "'a::euclidean_space set"
  assumes "polytope S"
  shows "finite {F. F face_of S}"
proof -
  obtain v where "finite v" "S = convex hull v"
    using assms polytope_def by auto
  have "finite ((hull) convex ` {T. T \<subseteq> v})"
    by (simp add: \<open>finite v\<close>)
  moreover have "{F. F face_of S} \<subseteq> ((hull) convex ` {T. T \<subseteq> v})"
    by (metis (no_types, lifting) \<open>finite v\<close> \<open>S = convex hull v\<close> face_of_convex_hull_subset finite_imp_compact image_eqI mem_Collect_eq subsetI)
  ultimately show ?thesis
    by (blast intro: finite_subset)
qed

lemma finite_polytope_facets:
  assumes "polytope S"
  shows "finite {T. T facet_of S}"
by (simp add: assms facet_of_def finite_polytope_faces)

lemma polytope_scaling:
  assumes "polytope S"  shows "polytope (image (\<lambda>x. c *\<^sub>R x) S)"
by (simp add: assms polytope_linear_image)

lemma polytope_imp_compact:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> compact S"
by (metis finite_imp_compact_convex_hull polytope_def)

lemma polytope_imp_convex: "polytope S \<Longrightarrow> convex S"
  by (metis convex_convex_hull polytope_def)

lemma polytope_imp_closed:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> closed S"
by (simp add: compact_imp_closed polytope_imp_compact)

lemma polytope_imp_bounded:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> bounded S"
by (simp add: compact_imp_bounded polytope_imp_compact)

lemma polytope_interval: "polytope(cbox a b)"
  unfolding polytope_def by (meson closed_interval_as_convex_hull)

lemma polytope_sing: "polytope {a}"
  using polytope_def by force

lemma face_of_polytope_insert:
     "\<lbrakk>polytope S; a \<notin> affine hull S; F face_of S\<rbrakk> \<Longrightarrow> F face_of convex hull (insert a S)"
  by (metis (no_types, lifting) affine_hull_convex_hull face_of_convex_hull_insert hull_insert polytope_def)

proposition face_of_polytope_insert2:
  fixes a :: "'a :: euclidean_space"
  assumes "polytope S" "a \<notin> affine hull S" "F face_of S"
  shows "convex hull (insert a F) face_of convex hull (insert a S)"
proof -
  obtain V where "finite V" "S = convex hull V"
    using assms by (auto simp: polytope_def)
  then have "convex hull (insert a F) face_of convex hull (insert a V)"
    using affine_hull_convex_hull assms face_of_convex_hull_insert2 by blast
  then show ?thesis
    by (metis \<open>S = convex hull V\<close> hull_insert)
qed


subsection\<open>Polyhedra\<close>

definition\<^marker>\<open>tag important\<close> polyhedron where
 "polyhedron S \<equiv>
        \<exists>F. finite F \<and>
            S = \<Inter> F \<and>
            (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b})"

lemma polyhedron_Int [intro,simp]:
   "\<lbrakk>polyhedron S; polyhedron T\<rbrakk> \<Longrightarrow> polyhedron (S \<inter> T)"
  apply (clarsimp simp add: polyhedron_def)
  subgoal for F G
    by (rule_tac x="F \<union> G" in exI, auto)
  done

lemma polyhedron_UNIV [iff]: "polyhedron UNIV"
  unfolding polyhedron_def
  by (rule_tac x="{}" in exI) auto

lemma polyhedron_Inter [intro,simp]:
   "\<lbrakk>finite F; \<And>S. S \<in> F \<Longrightarrow> polyhedron S\<rbrakk> \<Longrightarrow> polyhedron(\<Inter>F)"
by (induction F rule: finite_induct) auto


lemma polyhedron_empty [iff]: "polyhedron ({} :: 'a :: euclidean_space set)"
proof -
  define i::'a where "(i \<equiv> SOME i. i \<in> Basis)"
  have "\<exists>a. a \<noteq> 0 \<and> (\<exists>b. {x. i \<bullet> x \<le> -1} = {x. a \<bullet> x \<le> b})"
    by (rule_tac x="i" in exI) (force simp: i_def SOME_Basis nonzero_Basis)
  moreover have "\<exists>a b. a \<noteq> 0 \<and> {x. -i \<bullet> x \<le> - 1} = {x. a \<bullet> x \<le> b}"
      apply (rule_tac x="-i" in exI)
      apply (rule_tac x="-1" in exI)
      apply (simp add: i_def SOME_Basis nonzero_Basis)
      done
  ultimately show ?thesis
    unfolding polyhedron_def
    by (rule_tac x="{{x. i \<bullet> x \<le> -1}, {x. -i \<bullet> x \<le> -1}}" in exI) force
qed

lemma polyhedron_halfspace_le:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<le> b}"
proof (cases "a = 0")
  case True then show ?thesis by auto
next
  case False
  then show ?thesis
    unfolding polyhedron_def
    by (rule_tac x="{{x. a \<bullet> x \<le> b}}" in exI) auto
qed

lemma polyhedron_halfspace_ge:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<ge> b}"
using polyhedron_halfspace_le [of "-a" "-b"] by simp

lemma polyhedron_hyperplane:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x = b}"
proof -
  have "{x. a \<bullet> x = b} = {x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x \<ge> b}"
    by force
  then show ?thesis
    by (simp add: polyhedron_halfspace_ge polyhedron_halfspace_le)
qed

lemma affine_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "affine S \<Longrightarrow> polyhedron S"
by (metis affine_hull_eq polyhedron_Inter polyhedron_hyperplane affine_hull_finite_intersection_hyperplanes [of S])

lemma polyhedron_imp_closed:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> closed S"
  by (metis closed_Inter closed_halfspace_le polyhedron_def)

lemma polyhedron_imp_convex:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> convex S"
  by (metis convex_Inter convex_halfspace_le polyhedron_def)

lemma polyhedron_affine_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron(affine hull S)"
by (simp add: affine_imp_polyhedron)


subsection\<open>Canonical polyhedron representation making facial structure explicit\<close>

proposition polyhedron_Int_affine:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
           (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
                (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using hull_subset polyhedron_def by fastforce
next
  assume ?rhs then show ?lhs
    by (metis polyhedron_Int polyhedron_Inter polyhedron_affine_hull polyhedron_halfspace_le)
qed

proposition rel_interior_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "rel_interior S = {x \<in> S. \<forall>h \<in> F. a h \<bullet> x < b h}"
proof -
  have rels: "\<And>x. x \<in> rel_interior S \<Longrightarrow> x \<in> S"
    by (meson IntE mem_rel_interior)
  moreover have "a i \<bullet> x < b i" if x: "x \<in> rel_interior S" and "i \<in> F" for x i
  proof -
    have fif: "F - {i} \<subset> F"
      using \<open>i \<in> F\<close> Diff_insert_absorb Diff_subset set_insert psubsetI by blast
    then have "S \<subset> affine hull S \<inter> \<Inter>(F - {i})"
      by (rule psub)
    then obtain z where ssub: "S \<subseteq> \<Inter>(F - {i})" and zint: "z \<in> \<Inter>(F - {i})"
                    and "z \<notin> S" and zaff: "z \<in> affine hull S"
      by auto
    have "z \<noteq> x"
      using \<open>z \<notin> S\<close> rels x by blast
    have "z \<notin> affine hull S \<inter> \<Inter>F"
      using \<open>z \<notin> S\<close> seq by auto
    then have aiz: "a i \<bullet> z > b i"
      using faceq zint zaff by fastforce
    obtain e where "e > 0" "x \<in> S" and e: "ball x e \<inter> affine hull S \<subseteq> S"
      using x by (auto simp: mem_rel_interior_ball)
    then have ins: "\<And>y. \<lbrakk>norm (x - y) < e; y \<in> affine hull S\<rbrakk> \<Longrightarrow> y \<in> S"
      by (metis IntI subsetD dist_norm mem_ball)
    define \<xi> where "\<xi> = min (1/2) (e / 2 / norm(z - x))"
    have "norm (\<xi> *\<^sub>R x - \<xi> *\<^sub>R z) = norm (\<xi> *\<^sub>R (x - z))"
      by (simp add: \<xi>_def algebra_simps norm_mult)
    also have "... = \<xi> * norm (x - z)"
      using \<open>e > 0\<close> by (simp add: \<xi>_def)
    also have "... < e"
      using \<open>z \<noteq> x\<close> \<open>e > 0\<close> by (simp add: \<xi>_def min_def field_split_simps norm_minus_commute)
    finally have lte: "norm (\<xi> *\<^sub>R x - \<xi> *\<^sub>R z) < e" .
    have \<xi>_aff: "\<xi> *\<^sub>R z + (1 - \<xi>) *\<^sub>R x \<in> affine hull S"
      by (metis \<open>x \<in> S\<close> add.commute affine_affine_hull diff_add_cancel hull_inc mem_affine zaff)
    have "\<xi> *\<^sub>R z + (1 - \<xi>) *\<^sub>R x \<in> S"
      using ins [OF _ \<xi>_aff] by (simp add: algebra_simps lte)
    then obtain l where l: "0 < l" "l < 1" and ls: "(l *\<^sub>R z + (1 - l) *\<^sub>R x) \<in> S"
      using \<open>e > 0\<close> \<open>z \<noteq> x\<close>  
      by (rule_tac l = \<xi> in that) (auto simp: \<xi>_def)
    then have i: "l *\<^sub>R z + (1 - l) *\<^sub>R x \<in> i"
      using seq \<open>i \<in> F\<close> by auto
    have "b i * l + (a i \<bullet> x) * (1 - l) < a i \<bullet> (l *\<^sub>R z + (1 - l) *\<^sub>R x)"
      using l by (simp add: algebra_simps aiz)
    also have "\<dots> \<le> b i" using i l
      using faceq mem_Collect_eq \<open>i \<in> F\<close> by blast
    finally have "(a i \<bullet> x) * (1 - l) < b i * (1 - l)"
      by (simp add: algebra_simps)
    with l show ?thesis
      by simp
  qed
  moreover have "x \<in> rel_interior S"
           if "x \<in> S" and less: "\<And>h. h \<in> F \<Longrightarrow> a h \<bullet> x < b h" for x
  proof -
    have 1: "\<And>h. h \<in> F \<Longrightarrow> x \<in> interior h"
      by (metis interior_halfspace_le mem_Collect_eq less faceq)
    have 2: "\<And>y. \<lbrakk>\<forall>h\<in>F. y \<in> interior h; y \<in> affine hull S\<rbrakk> \<Longrightarrow> y \<in> S"
      by (metis IntI Inter_iff subsetD interior_subset seq)
    show ?thesis
      apply (simp add: rel_interior \<open>x \<in> S\<close>)
      apply (rule_tac x="\<Inter>h\<in>F. interior h" in exI)
      apply (auto simp: \<open>finite F\<close> open_INT 1 2)
      done
  qed
  ultimately show ?thesis by blast
qed


lemma polyhedron_Int_affine_parallel:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain F where "finite F" and seq: "S = (affine hull S) \<inter> \<Inter>F"
                  and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
    by (fastforce simp add: polyhedron_Int_affine)
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  show ?rhs
  proof -
    have "\<exists>a' b'. a' \<noteq> 0 \<and>
                  affine hull S \<inter> {x. a' \<bullet> x \<le> b'} = affine hull S \<inter> h \<and>
                  (\<forall>w \<in> affine hull S. (w + a') \<in> affine hull S)"
        if "h \<in> F" "\<not>(affine hull S \<subseteq> h)" for h
    proof -
      have "a h \<noteq> 0" and "h = {x. a h \<bullet> x \<le> b h}" "h \<inter> \<Inter>F = \<Inter>F"
        using \<open>h \<in> F\<close> ab by auto
      then have "(affine hull S) \<inter> {x. a h \<bullet> x \<le> b h} \<noteq> {}"
        by (metis (no_types) affine_hull_eq_empty inf.absorb_iff2 inf_assoc inf_bot_right inf_commute seq that(2))
      moreover have "\<not> (affine hull S \<subseteq> {x. a h \<bullet> x \<le> b h})"
        using \<open>h = {x. a h \<bullet> x \<le> b h}\<close> that(2) by blast
      ultimately show ?thesis
        using affine_parallel_slice [of "affine hull S"]
        by (metis \<open>h = {x. a h \<bullet> x \<le> b h}\<close> affine_affine_hull)
    qed
    then obtain a b
         where ab: "\<And>h. \<lbrakk>h \<in> F; \<not> (affine hull S \<subseteq> h)\<rbrakk>
             \<Longrightarrow> a h \<noteq> 0 \<and>
                  affine hull S \<inter> {x. a h \<bullet> x \<le> b h} = affine hull S \<inter> h \<and>
                  (\<forall>w \<in> affine hull S. (w + a h) \<in> affine hull S)"
      by metis
    have seq2: "S = affine hull S \<inter> (\<Inter>h\<in>{h \<in> F. \<not> affine hull S \<subseteq> h}. {x. a h \<bullet> x \<le> b h})"
      by (subst seq) (auto simp: ab INT_extend_simps)
    show ?thesis
      apply (rule_tac x="(\<lambda>h. {x. a h \<bullet> x \<le> b h}) ` {h. h \<in> F \<and> \<not>(affine hull S \<subseteq> h)}" in exI)
      apply (intro conjI seq2)
        using \<open>finite F\<close> apply force
       using ab apply blast
       done
  qed
next
  assume ?rhs then show ?lhs
    by (metis polyhedron_Int_affine)
qed


proposition polyhedron_Int_affine_parallel_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> (\<Inter>F')))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain f0
           where f0: "finite f0"
                 "S = (affine hull S) \<inter> (\<Inter>f0)"
                   (is "?P f0")
                 "\<forall>h \<in> f0. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)"
                   (is "?Q f0")
    by (force simp: polyhedron_Int_affine_parallel)
  define n where "n = (LEAST n. \<exists>F. card F = n \<and> finite F \<and> ?P F \<and> ?Q F)"
  have nf: "\<exists>F. card F = n \<and> finite F \<and> ?P F \<and> ?Q F"
    apply (simp add: n_def)
    apply (rule LeastI [where k = "card f0"])
    using f0 apply auto
    done
  then obtain F where F: "card F = n" "finite F" and seq: "?P F" and aff: "?Q F"
    by blast
  then have "\<not> (finite g \<and> ?P g \<and> ?Q g)" if "card g < n" for g
    using that by (auto simp: n_def dest!: not_less_Least)
  then have *: "\<not> (?P g \<and> ?Q g)" if "g \<subset> F" for g
    using that \<open>finite F\<close> psubset_card_mono \<open>card F = n\<close>
    by (metis finite_Int inf.strict_order_iff)
  have 1: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subseteq> affine hull S \<inter> \<Inter>F'"
    by (subst seq) blast
  have 2: "S \<noteq> affine hull S \<inter> \<Inter>F'" if "F' \<subset> F" for F'
    using * [OF that] by (metis IntE aff inf.strict_order_iff that)
  show ?rhs
    by (metis \<open>finite F\<close> seq aff psubsetI 1 2)
next
  assume ?rhs then show ?lhs
    by (auto simp: polyhedron_Int_affine_parallel)
qed


lemma polyhedron_Int_affine_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (force simp: polyhedron_Int_affine_parallel_minimal elim!: ex_forward)
qed (auto simp: polyhedron_Int_affine elim!: ex_forward)

proposition facet_of_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "C facet_of S \<longleftrightarrow> (\<exists>h. h \<in> F \<and> C = S \<inter> {x. a h \<bullet> x = b h})"
proof (cases "S = {}")
  case True with psub show ?thesis by force
next
  case False
  have "polyhedron S"
    unfolding polyhedron_Int_affine by (metis \<open>finite F\<close> faceq seq)
  then have "convex S"
    by (rule polyhedron_imp_convex)
  with False rel_interior_eq_empty have "rel_interior S \<noteq> {}" by blast
  then obtain x where "x \<in> rel_interior S" by auto
  then obtain T where "open T" "x \<in> T" "x \<in> S" "T \<inter> affine hull S \<subseteq> S"
    by (force simp: mem_rel_interior)
  then have xaff: "x \<in> affine hull S" and xint: "x \<in> \<Inter>F"
    using seq hull_inc by auto
  have "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  with \<open>x \<in> rel_interior S\<close>
  have [simp]: "\<And>h. h\<in>F \<Longrightarrow> a h \<bullet> x < b h" by blast
  have *: "(S \<inter> {x. a h \<bullet> x = b h}) facet_of S" if "h \<in> F" for h
  proof -
    have "S \<subset> affine hull S \<inter> \<Inter>(F - {h})"
      using psub that by (metis Diff_disjoint Diff_subset insert_disjoint(2) psubsetI)
    then obtain z where zaff: "z \<in> affine hull S" and zint: "z \<in> \<Inter>(F - {h})" and "z \<notin> S"
      by force
    then have "z \<noteq> x" "z \<notin> h" using seq \<open>x \<in> S\<close> by auto
    have "x \<in> h" using that xint by auto
    then have able: "a h \<bullet> x \<le> b h"
      using faceq that by blast
    also have "... < a h \<bullet> z" using \<open>z \<notin> h\<close> faceq [OF that] xint by auto
    finally have xltz: "a h \<bullet> x < a h \<bullet> z" .
    define l where "l = (b h - a h \<bullet> x) / (a h \<bullet> z - a h \<bullet> x)"
    define w where "w = (1 - l) *\<^sub>R x + l *\<^sub>R z"
    have "0 < l" "l < 1"
      using able xltz \<open>b h < a h \<bullet> z\<close> \<open>h \<in> F\<close>
      by (auto simp: l_def field_split_simps)
    have awlt: "a i \<bullet> w < b i" if "i \<in> F" "i \<noteq> h" for i
    proof -
      have "(1 - l) * (a i \<bullet> x) < (1 - l) * b i"
        by (simp add: \<open>l < 1\<close> \<open>i \<in> F\<close>)
      moreover have "l * (a i \<bullet> z) \<le> l * b i"
      proof (rule mult_left_mono)
        show "a i \<bullet> z \<le> b i"
          by (metis Diff_insert_absorb Inter_iff Set.set_insert \<open>h \<in> F\<close> faceq insertE mem_Collect_eq that zint)
      qed (use \<open>0 < l\<close> in auto)
      ultimately show ?thesis by (simp add: w_def algebra_simps)
    qed
    have weq: "a h \<bullet> w = b h"
      using xltz unfolding w_def l_def
      by (simp add: algebra_simps) (simp add: field_simps)
    have faceS: "S \<inter> {x. a h \<bullet> x = b h} face_of S"
    proof (rule face_of_Int_supporting_hyperplane_le)
      show "\<And>x. x \<in> S \<Longrightarrow> a h \<bullet> x \<le> b h"
        using faceq seq that by fastforce
    qed fact
    have "w \<in> affine hull S"
      by (simp add: w_def mem_affine xaff zaff)
    moreover have "w \<in> \<Inter>F"
      using \<open>a h \<bullet> w = b h\<close> awlt faceq less_eq_real_def by blast
    ultimately have "w \<in> S"
      using seq by blast
    with weq have ne: "S \<inter> {x. a h \<bullet> x = b h} \<noteq> {}" by blast
    moreover have "affine hull (S \<inter> {x. a h \<bullet> x = b h}) = (affine hull S) \<inter> {x. a h \<bullet> x = b h}"
    proof
      show "affine hull (S \<inter> {x. a h \<bullet> x = b h}) \<subseteq> affine hull S \<inter> {x. a h \<bullet> x = b h}"
        apply (intro Int_greatest hull_mono Int_lower1)
        apply (metis affine_hull_eq affine_hyperplane hull_mono inf_le2)
        done
    next
      show "affine hull S \<inter> {x. a h \<bullet> x = b h} \<subseteq> affine hull (S \<inter> {x. a h \<bullet> x = b h})"
      proof
        fix y
        assume yaff: "y \<in> affine hull S \<inter> {y. a h \<bullet> y = b h}"
        obtain T where "0 < T"
                 and T: "\<And>j. \<lbrakk>j \<in> F; j \<noteq> h\<rbrakk> \<Longrightarrow> T * (a j \<bullet> y - a j \<bullet> w) \<le> b j - a j \<bullet> w"
        proof (cases "F - {h} = {}")
          case True then show ?thesis
            by (rule_tac T=1 in that) auto
        next
          case False
          then obtain h' where h': "h' \<in> F - {h}" by auto
          let ?body = "(\<lambda>j. if 0 < a j \<bullet> y - a j \<bullet> w
              then (b j - a j \<bullet> w) / (a j \<bullet> y - a j \<bullet> w) else 1) ` (F - {h})"
          define inff where "inff = Inf ?body"
          from \<open>finite F\<close> have "finite ?body"
            by blast
          moreover from h' have "?body \<noteq> {}"
            by blast
          moreover have "j > 0" if "j \<in> ?body" for j
          proof -
            from that obtain x where "x \<in> F" and "x \<noteq> h" and *: "j =
              (if 0 < a x \<bullet> y - a x \<bullet> w
                then (b x - a x \<bullet> w) / (a x \<bullet> y - a x \<bullet> w) else 1)"
              by blast
            with awlt [of x] have "a x \<bullet> w < b x"
              by simp
            with * show ?thesis
              by simp
          qed
          ultimately have "0 < inff"
            by (simp_all add: finite_less_Inf_iff inff_def)
          moreover have "inff * (a j \<bullet> y - a j \<bullet> w) \<le> b j - a j \<bullet> w"
                        if "j \<in> F" "j \<noteq> h" for j
          proof (cases "a j \<bullet> w < a j \<bullet> y")
            case True
            then have "inff \<le> (b j - a j \<bullet> w) / (a j \<bullet> y - a j \<bullet> w)"
              unfolding inff_def
              using \<open>finite F\<close> by (auto intro: cInf_le_finite simp add: that split: if_split_asm)
            then show ?thesis
              using \<open>0 < inff\<close> awlt [OF that] mult_strict_left_mono
              by (fastforce simp add: field_split_simps split: if_split_asm)
          next
            case False
            with \<open>0 < inff\<close> have "inff * (a j \<bullet> y - a j \<bullet> w) \<le> 0"
              by (simp add: mult_le_0_iff)
            also have "... < b j - a j \<bullet> w"
              by (simp add: awlt that)
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            by (blast intro: that)
        qed
        define C where "C = (1 - T) *\<^sub>R w + T *\<^sub>R y"
        have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> j" if "j \<in> F" for j
        proof (cases "j = h")
          case True
          have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> {x. a h \<bullet> x \<le> b h}"
            using weq yaff by (auto simp: algebra_simps)
          with True faceq [OF that] show ?thesis by metis
        next
          case False
          with T that have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> {x. a j \<bullet> x \<le> b j}"
            by (simp add: algebra_simps)
          with faceq [OF that] show ?thesis by simp
        qed
        moreover have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> affine hull S"
          using yaff \<open>w \<in> affine hull S\<close> affine_affine_hull affine_alt by blast
        ultimately have "C \<in> S"
          using seq by (force simp: C_def)
        moreover have "a h \<bullet> C = b h"
          using yaff by (force simp: C_def algebra_simps weq)
        ultimately have caff: "C \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          by (simp add: hull_inc)
        have waff: "w \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          using \<open>w \<in> S\<close> weq by (blast intro: hull_inc)
        have yeq: "y = (1 - inverse T) *\<^sub>R w + C /\<^sub>R T"
          using \<open>0 < T\<close> by (simp add: C_def algebra_simps)
        show "y \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          by (metis yeq affine_affine_hull [simplified affine_alt, rule_format, OF waff caff])
      qed
    qed
    ultimately have "aff_dim (affine hull (S \<inter> {x. a h \<bullet> x = b h})) = aff_dim S - 1"
      using \<open>b h < a h \<bullet> z\<close> zaff by (force simp: aff_dim_affine_Int_hyperplane)
    then show ?thesis
      by (simp add: ne faceS facet_of_def)
  qed
  show ?thesis
  proof
    show "\<exists>h. h \<in> F \<and> C = S \<inter> {x. a h \<bullet> x = b h} \<Longrightarrow> C facet_of S"
      using * by blast
  next
    assume "C facet_of S"
    then have "C face_of S" "convex C" "C \<noteq> {}" and affc: "aff_dim C = aff_dim S - 1"
      by (auto simp: facet_of_def face_of_imp_convex)
    then obtain x where x: "x \<in> rel_interior C"
      by (force simp: rel_interior_eq_empty)
    then have "x \<in> C"
      by (meson subsetD rel_interior_subset)
    then have "x \<in> S"
      using \<open>C facet_of S\<close> facet_of_imp_subset by blast
    have rels: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
      by (rule rel_interior_polyhedron_explicit [OF assms])
    have "C \<noteq> S"
      using \<open>C facet_of S\<close> facet_of_irrefl by blast
    then have "x \<notin> rel_interior S"
      by (metis IntI empty_iff \<open>x \<in> C\<close> \<open>C \<noteq> S\<close> \<open>C face_of S\<close> face_of_disjoint_rel_interior)
    with rels \<open>x \<in> S\<close> obtain i where "i \<in> F" and i: "a i \<bullet> x \<ge> b i"
      by force
    have "x \<in> {u. a i \<bullet> u \<le> b i}"
      by (metis IntD2 InterE \<open>i \<in> F\<close> \<open>x \<in> S\<close> faceq seq)
    then have "a i \<bullet> x \<le> b i" by simp
    then have "a i \<bullet> x = b i" using i by auto
    have "C \<subseteq> S \<inter> {x. a i \<bullet> x = b i}"
    proof (rule subset_of_face_of [of _ S])
      show "S \<inter> {x. a i \<bullet> x = b i} face_of S"
        by (simp add: "*" \<open>i \<in> F\<close> facet_of_imp_face_of)
      show "C \<subseteq> S"
        by (simp add: \<open>C face_of S\<close> face_of_imp_subset)
      show "S \<inter> {x. a i \<bullet> x = b i} \<inter> rel_interior C \<noteq> {}"
        using \<open>a i \<bullet> x = b i\<close> \<open>x \<in> S\<close> x by blast
    qed
    then have cface: "C face_of (S \<inter> {x. a i \<bullet> x = b i})"
      by (meson \<open>C face_of S\<close> face_of_subset inf_le1)
    have con: "convex (S \<inter> {x. a i \<bullet> x = b i})"
      by (simp add: \<open>convex S\<close> convex_Int convex_hyperplane)
    show "\<exists>h. h \<in> F \<and> C = S \<inter> {x. a h \<bullet> x = b h}"
      apply (rule_tac x=i in exI)
      by (metis (no_types) * \<open>i \<in> F\<close> affc facet_of_def less_irrefl face_of_aff_dim_lt [OF con cface])
  qed
qed


lemma face_of_polyhedron_subset_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and C: "C face_of S" and "C \<noteq> {}" "C \<noteq> S"
   obtains h where "h \<in> F" "C \<subseteq> S \<inter> {x. a h \<bullet> x = b h}"
proof -
  have "C \<subseteq> S" using \<open>C face_of S\<close>
    by (simp add: face_of_imp_subset)
  have "polyhedron S"
    by (metis \<open>finite F\<close> faceq polyhedron_Int polyhedron_Inter polyhedron_affine_hull polyhedron_halfspace_le seq)
  then have "convex S"
    by (simp add: polyhedron_imp_convex)
  then have *: "(S \<inter> {x. a h \<bullet> x = b h}) face_of S" if "h \<in> F" for h
    using faceq seq face_of_Int_supporting_hyperplane_le that by fastforce
  have "rel_interior C \<noteq> {}"
    using C \<open>C \<noteq> {}\<close> face_of_imp_convex rel_interior_eq_empty by blast
  then obtain x where "x \<in> rel_interior C" by auto
  have rels: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  then have xnot: "x \<notin> rel_interior S"
    by (metis IntI \<open>x \<in> rel_interior C\<close> C \<open>C \<noteq> S\<close> contra_subsetD empty_iff face_of_disjoint_rel_interior rel_interior_subset)
  then have "x \<in> S"
    using \<open>C \<subseteq> S\<close> \<open>x \<in> rel_interior C\<close> rel_interior_subset by auto
  then have xint: "x \<in> \<Inter>F"
    using seq by blast
  have "F \<noteq> {}" using assms
    by (metis affine_Int affine_Inter affine_affine_hull ex_in_conv face_of_affine_trivial)
  then obtain i where "i \<in> F" "\<not> (a i \<bullet> x < b i)"
    using \<open>x \<in> S\<close> rels xnot by auto
  with xint have "a i \<bullet> x = b i"
    by (metis eq_iff mem_Collect_eq not_le Inter_iff faceq)
  have face: "S \<inter> {x. a i \<bullet> x = b i} face_of S"
    by (simp add: "*" \<open>i \<in> F\<close>)
  show ?thesis
  proof
    show "C \<subseteq> S \<inter> {x. a i \<bullet> x = b i}"
      using subset_of_face_of [OF face \<open>C \<subseteq> S\<close>] \<open>a i \<bullet> x = b i\<close> \<open>x \<in> rel_interior C\<close> \<open>x \<in> S\<close> by blast
  qed fact
qed

text\<open>Initial part of proof duplicates that above\<close>
proposition face_of_polyhedron_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and C: "C face_of S" and "C \<noteq> {}" "C \<noteq> S"
    shows "C = \<Inter>{S \<inter> {x. a h \<bullet> x = b h} | h. h \<in> F \<and> C \<subseteq> S \<inter> {x. a h \<bullet> x = b h}}"
proof -
  let ?ab = "\<lambda>h. {x. a h \<bullet> x = b h}"
  have "C \<subseteq> S" using \<open>C face_of S\<close>
    by (simp add: face_of_imp_subset)
  have "polyhedron S"
    by (metis \<open>finite F\<close> faceq polyhedron_Int polyhedron_Inter polyhedron_affine_hull polyhedron_halfspace_le seq)
  then have "convex S"
    by (simp add: polyhedron_imp_convex)
  then have *: "(S \<inter> ?ab h) face_of S" if "h \<in> F" for h
    using faceq seq face_of_Int_supporting_hyperplane_le that by fastforce
  have "rel_interior C \<noteq> {}"
    using C \<open>C \<noteq> {}\<close> face_of_imp_convex rel_interior_eq_empty by blast
  then obtain z where z: "z \<in> rel_interior C" by auto
  have rels: "rel_interior S = {z \<in> S. \<forall>h\<in>F. a h \<bullet> z < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  then have xnot: "z \<notin> rel_interior S"
    by (metis IntI \<open>z \<in> rel_interior C\<close> C \<open>C \<noteq> S\<close> contra_subsetD empty_iff face_of_disjoint_rel_interior rel_interior_subset)
  then have "z \<in> S"
    using \<open>C \<subseteq> S\<close> \<open>z \<in> rel_interior C\<close> rel_interior_subset by auto
  with seq have xint: "z \<in> \<Inter>F" by blast
  have "open (\<Inter>h\<in>{h \<in> F. a h \<bullet> z < b h}. {w. a h \<bullet> w < b h})"
    by (auto simp: \<open>finite F\<close> open_halfspace_lt open_INT)
  then obtain e where "0 < e"
                 "ball z e \<subseteq> (\<Inter>h\<in>{h \<in> F. a h \<bullet> z < b h}. {w. a h \<bullet> w < b h})"
    by (auto intro: openE [of _ z])
  then have e: "\<And>h. \<lbrakk>h \<in> F; a h \<bullet> z < b h\<rbrakk> \<Longrightarrow> ball z e \<subseteq> {w. a h \<bullet> w < b h}"
    by blast
  have "C \<subseteq> (S \<inter> ?ab h) \<longleftrightarrow> z \<in> S \<inter> ?ab h" if "h \<in> F" for h
  proof
    show "z \<in> S \<inter> ?ab h \<Longrightarrow> C \<subseteq> S \<inter> ?ab h"
      by (metis "*" Collect_cong IntI \<open>C \<subseteq> S\<close> empty_iff subset_of_face_of that z)
  next
    show "C \<subseteq> S \<inter> ?ab h \<Longrightarrow> z \<in> S \<inter> ?ab h"
      using \<open>z \<in> rel_interior C\<close> rel_interior_subset by force
  qed
  then have **: "{S \<inter> ?ab h | h. h \<in> F \<and> C \<subseteq> S \<and> C \<subseteq> ?ab h} =
                 {S \<inter> ?ab h |h. h \<in> F \<and> z \<in> S \<inter> ?ab h}"
    by blast
  have bsub: "ball z e \<inter> affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
             \<subseteq> affine hull S \<inter> \<Inter>F \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
            if "i \<in> F" and i: "a i \<bullet> z = b i" for i
  proof -
    have sub: "ball z e \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> j"
             if "j \<in> F" for j
    proof -
      have "a j \<bullet> z \<le> b j" using faceq that xint by auto
      then consider "a j \<bullet> z < b j" | "a j \<bullet> z = b j" by linarith
      then have "\<exists>G. G \<in> {?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<and> ball z e \<inter> G \<subseteq> j"
      proof cases
        assume "a j \<bullet> z < b j"
        then have "ball z e \<inter> {x. a i \<bullet> x = b i} \<subseteq> j"
          using e [OF \<open>j \<in> F\<close>] faceq that
          by (fastforce simp: ball_def)
        then show ?thesis
          by (rule_tac x="{x. a i \<bullet> x = b i}" in exI) (force simp: \<open>i \<in> F\<close> i)
      next
        assume eq: "a j \<bullet> z = b j"
        with faceq that show ?thesis
          by (rule_tac x="{x. a j \<bullet> x = b j}" in exI) (fastforce simp add: \<open>j \<in> F\<close>)
      qed
      then show ?thesis  by blast
    qed
    have 1: "affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> affine hull S"
      using that \<open>z \<in> S\<close> by (intro hull_mono) auto
    have 2: "affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
          \<subseteq> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
      by (rule hull_minimal) (auto intro: affine_hyperplane)
    have 3: "ball z e \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> \<Inter>F"
      by (iprover intro: sub Inter_greatest)
    have *: "\<lbrakk>A \<subseteq> (B :: 'a set); A \<subseteq> C; E \<inter> C \<subseteq> D\<rbrakk> \<Longrightarrow> E \<inter> A \<subseteq> (B \<inter> D) \<inter> C"
             for A B C D E  by blast
    show ?thesis by (intro * 1 2 3)
  qed
  have "\<exists>h. h \<in> F \<and> C \<subseteq> ?ab h"
    using assms
    by (metis face_of_polyhedron_subset_explicit [OF \<open>finite F\<close> seq faceq psub] le_inf_iff)
  then have fac: "\<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> C \<subseteq> S \<inter> ?ab h} face_of S"
    using * by (force simp: \<open>C \<subseteq> S\<close> intro: face_of_Inter)
  have red: "(\<And>a. P a \<Longrightarrow> T \<subseteq> S \<inter> \<Inter>{F X |X. P X}) \<Longrightarrow> T \<subseteq> \<Inter>{S \<inter> F X |X::'a set. P X}" for P T F   
    by blast
  have "ball z e \<inter> affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
        \<subseteq> \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
    by (rule red) (metis seq bsub)
  with \<open>0 < e\<close> have zinrel: "z \<in> rel_interior
                    (\<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> z \<in> S \<and> a h \<bullet> z = b h})"
    by (auto simp: mem_rel_interior_ball \<open>z \<in> S\<close>)
  show ?thesis
    using z zinrel
    by (intro face_of_eq [OF C fac]) (force simp: **)
qed


subsection\<open>More general corollaries from the explicit representation\<close>

corollary facet_of_polyhedron:
  assumes "polyhedron S" and "C facet_of S"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x \<le> b}" "C = S \<inter> {x. a \<bullet> x = b}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  obtain i where "i \<in> F" and C: "C = S \<inter> {x. a i \<bullet> x = b i}"
    using facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min] assms
    by force
  moreover have ssub: "S \<subseteq> {x. a i \<bullet> x \<le> b i}"
     using \<open>i \<in> F\<close> ab by (subst seq) auto
  ultimately show ?thesis
    by (rule_tac a = "a i" and b = "b i" in that) (simp_all add: ab)
qed

corollary face_of_polyhedron:
  assumes "polyhedron S" and "C face_of S" and "C \<noteq> {}" and "C \<noteq> S"
    shows "C = \<Inter>{F. F facet_of S \<and> C \<subseteq> F}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  show ?thesis
    apply (subst face_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
    apply (auto simp: assms facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min] cong: Collect_cong)
    done
qed

lemma face_of_polyhedron_subset_facet:
  assumes "polyhedron S" and "C face_of S" and "C \<noteq> {}" and "C \<noteq> S"
  obtains F where "F facet_of S" "C \<subseteq> F"
  using face_of_polyhedron assms
  by (metis (no_types, lifting) Inf_greatest antisym_conv face_of_imp_subset mem_Collect_eq)


lemma exposed_face_of_polyhedron:
  assumes "polyhedron S"
    shows "F exposed_face_of S \<longleftrightarrow> F face_of S"
proof
  show "F exposed_face_of S \<Longrightarrow> F face_of S"
    by (simp add: exposed_face_of_def)
next
  assume "F face_of S"
  show "F exposed_face_of S"
  proof (cases "F = {} \<or> F = S")
    case True then show ?thesis
      using \<open>F face_of S\<close> exposed_face_of by blast
  next
    case False
    then have "{g. g facet_of S \<and> F \<subseteq> g} \<noteq> {}"
      by (metis Collect_empty_eq_bot \<open>F face_of S\<close> assms empty_def face_of_polyhedron_subset_facet)
    moreover have "\<And>T. \<lbrakk>T facet_of S; F \<subseteq> T\<rbrakk> \<Longrightarrow> T exposed_face_of S"
      by (metis assms exposed_face_of facet_of_imp_face_of facet_of_polyhedron)
    ultimately have "\<Inter>{G. G facet_of S \<and> F \<subseteq> G} exposed_face_of S"
      by (metis (no_types, lifting) mem_Collect_eq exposed_face_of_Inter)
    then show ?thesis
      using False \<open>F face_of S\<close> assms face_of_polyhedron by fastforce
  qed
qed

lemma face_of_polyhedron_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S" "c face_of S" shows "polyhedron c"
by (metis assms face_of_imp_eq_affine_Int polyhedron_Int polyhedron_affine_hull polyhedron_imp_convex)

lemma finite_polyhedron_faces:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "finite {F. F face_of S}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min:   "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  have "finite {\<Inter>{S \<inter> {x. a h \<bullet> x = b h} |h. h \<in> F'}| F'. F' \<in> Pow F}"
    by (simp add: \<open>finite F\<close>)
  moreover have "{F. F face_of S} - {{}, S} \<subseteq> {\<Inter>{S \<inter> {x. a h \<bullet> x = b h} |h. h \<in> F'}| F'. F' \<in> Pow F}"
    apply clarify
    apply (rename_tac c)
    apply (drule face_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min, simplified], simp_all)
    apply (rule_tac x="{h \<in> F. c \<subseteq> S \<inter> {x. a h \<bullet> x = b h}}" in exI, auto)
    done
  ultimately show ?thesis
    by (meson finite.emptyI finite.insertI finite_Diff2 finite_subset)
qed

lemma finite_polyhedron_exposed_faces:
   "polyhedron S \<Longrightarrow> finite {F. F exposed_face_of S}"
using exposed_face_of_polyhedron finite_polyhedron_faces by fastforce

lemma finite_polyhedron_extreme_points:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S" shows "finite {v. v extreme_point_of S}"
proof -
  have "finite {v. {v} face_of S}"
    using assms by (intro finite_subset [OF _ finite_vimageI [OF finite_polyhedron_faces]], auto)
  then show ?thesis
    by (simp add: face_of_singleton)
qed

lemma finite_polyhedron_facets:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> finite {F. F facet_of S}"
  unfolding facet_of_def
  by (blast intro: finite_subset [OF _ finite_polyhedron_faces])


proposition rel_interior_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_interior S = S - \<Union>{F. F facet_of S}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  have facet: "(c facet_of S) \<longleftrightarrow> (\<exists>h. h \<in> F \<and> c = S \<inter> {x. a h \<bullet> x = b h})" for c
    by (rule facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
  have rel: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
  have "a h \<bullet> x < b h" if "x \<in> S" "h \<in> F" and xnot: "x \<notin> \<Union>{F. F facet_of S}" for x h
  proof -
    have "x \<in> \<Inter>F" using seq that by force
    with \<open>h \<in> F\<close> ab have "a h \<bullet> x \<le> b h" by auto
    then consider "a h \<bullet> x < b h" | "a h \<bullet> x = b h" by linarith
    then show ?thesis
    proof cases
      case 1 then show ?thesis .
    next
      case 2
      have "Collect ((\<in>) x) \<notin> Collect ((\<in>) (\<Union>{A. A facet_of S}))"
        using xnot by fastforce
      then have "F \<notin> Collect ((\<in>) h)"
        using 2 \<open>x \<in> S\<close> facet by blast
      with 2 that \<open>x \<in> \<Inter>F\<close> show ?thesis
        by blast
      qed
  qed
  moreover have "\<exists>h\<in>F. a h \<bullet> x \<ge> b h" if "x \<in> \<Union>{F. F facet_of S}" for x
    using that by (force simp: facet)
  ultimately show ?thesis
    by (force simp: rel)
qed

lemma rel_boundary_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "S - rel_interior S = \<Union> {F. F facet_of S}"
using facet_of_imp_subset by (fastforce simp add: rel_interior_of_polyhedron assms)

lemma rel_frontier_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_frontier S = \<Union> {F. F facet_of S}"
by (simp add: assms rel_frontier_def polyhedron_imp_closed rel_boundary_of_polyhedron)

lemma rel_frontier_of_polyhedron_alt:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
  shows "rel_frontier S = \<Union> {F. F face_of S \<and> F \<noteq> S}"
proof
  show "rel_frontier S \<subseteq> \<Union> {F. F face_of S \<and> F \<noteq> S}"
    by (force simp: rel_frontier_of_polyhedron facet_of_def assms)
qed (use face_of_subset_rel_frontier in fastforce)


text\<open>A characterization of polyhedra as having finitely many faces\<close>

proposition polyhedron_eq_finite_exposed_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F exposed_face_of S}"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: polyhedron_imp_closed polyhedron_imp_convex finite_polyhedron_exposed_faces)
next
  assume ?rhs
  then have "closed S" "convex S" and fin: "finite {F. F exposed_face_of S}" by auto
  show ?lhs
  proof (cases "S = {}")
    case True then show ?thesis by auto
  next
    case False
    define F where "F = {h. h exposed_face_of S \<and> h \<noteq> {} \<and> h \<noteq> S}"
    have "finite F" by (simp add: fin F_def)
    have hface: "h face_of S"
      and "\<exists>a b. a \<noteq> 0 \<and> S \<subseteq> {x. a \<bullet> x \<le> b} \<and> h = S \<inter> {x. a \<bullet> x = b}"
      if "h \<in> F" for h
      using exposed_face_of F_def that by blast+
    then obtain a b where ab:
      "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> S \<subseteq> {x. a h \<bullet> x \<le> b h} \<and> h = S \<inter> {x. a h \<bullet> x = b h}"
      by metis
    have *: "False"
      if paff: "p \<in> affine hull S" and "p \<notin> S"
      and pint: "p \<in> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F}" for p
    proof -
      have "rel_interior S \<noteq> {}"
        by (simp add: \<open>S \<noteq> {}\<close> \<open>convex S\<close> rel_interior_eq_empty)
      then obtain c where c: "c \<in> rel_interior S" by auto
      with rel_interior_subset have "c \<in> S"  by blast
      have ccp: "closed_segment c p \<subseteq> affine hull S"
        by (meson affine_affine_hull affine_imp_convex c closed_segment_subset hull_subset paff rel_interior_subset subsetCE)
      have oS: "openin (top_of_set (closed_segment c p)) (closed_segment c p \<inter> rel_interior S)"
        by (force simp: openin_rel_interior openin_Int intro: openin_subtopology_Int_subset [OF _ ccp])
      obtain x where xcl: "x \<in> closed_segment c p" and "x \<in> S" and xnot: "x \<notin> rel_interior S"
        using connected_openin [of "closed_segment c p"]
        apply simp
        apply (drule_tac x="closed_segment c p \<inter> rel_interior S" in spec)
        apply (drule mp [OF _ oS])
        apply (drule_tac x="closed_segment c p \<inter> (- S)" in spec)
        using rel_interior_subset \<open>closed S\<close> c \<open>p \<notin> S\<close> apply blast
        done
      then obtain \<mu> where "0 \<le> \<mu>" "\<mu> \<le> 1" and xeq: "x = (1 - \<mu>) *\<^sub>R c + \<mu> *\<^sub>R p"
        by (auto simp: in_segment)
      show False
      proof (cases "\<mu>=0 \<or> \<mu>=1")
        case True with xeq c xnot \<open>x \<in> S\<close> \<open>p \<notin> S\<close>
        show False by auto
      next
        case False
        then have xos: "x \<in> open_segment c p"
          using \<open>x \<in> S\<close> c open_segment_def that(2) xcl xnot by auto
        have xclo: "x \<in> closure S"
          using \<open>x \<in> S\<close> closure_subset by blast
        obtain d where "d \<noteq> 0"
              and dle: "\<And>y. y \<in> closure S \<Longrightarrow> d \<bullet> x \<le> d \<bullet> y"
              and dless: "\<And>y. y \<in> rel_interior S \<Longrightarrow> d \<bullet> x < d \<bullet> y"
          by (metis supporting_hyperplane_relative_frontier [OF \<open>convex S\<close> xclo xnot])
        have sex: "S \<inter> {y. d \<bullet> y = d \<bullet> x} exposed_face_of S"
          by (simp add: \<open>closed S\<close> dle exposed_face_of_Int_supporting_hyperplane_ge [OF \<open>convex S\<close>])
        have sne: "S \<inter> {y. d \<bullet> y = d \<bullet> x} \<noteq> {}"
          using \<open>x \<in> S\<close> by blast
        have sns: "S \<inter> {y. d \<bullet> y = d \<bullet> x} \<noteq> S"
          by (metis (mono_tags) Int_Collect c subsetD dless not_le order_refl rel_interior_subset)
        obtain h where "h \<in> F" "x \<in> h"
          using F_def \<open>x \<in> S\<close> sex sns by blast
        have abface: "{y. a h \<bullet> y = b h} face_of {y. a h \<bullet> y \<le> b h}"
          using hyperplane_face_of_halfspace_le by blast
        then have "c \<in> h"
          using face_ofD [OF abface xos] \<open>c \<in> S\<close> \<open>h \<in> F\<close> ab pint \<open>x \<in> h\<close> by blast
        with c have "h \<inter> rel_interior S \<noteq> {}" by blast
        then show False
          using \<open>h \<in> F\<close> F_def face_of_disjoint_rel_interior hface by auto
      qed
    qed
    have "S \<subseteq> affine hull S \<inter> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F}"
      using ab by (auto simp: hull_subset)
    moreover have "affine hull S \<inter> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F} \<subseteq> S"
      using * by blast
    ultimately have "S = affine hull S \<inter> \<Inter> {{x. a h \<bullet> x \<le> b h} |h. h \<in> F}" ..
    then show ?thesis
      apply (rule ssubst)
      apply (force intro: polyhedron_affine_hull polyhedron_halfspace_le simp: \<open>finite F\<close>)
      done
  qed
qed

corollary polyhedron_eq_finite_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F face_of S}"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: finite_polyhedron_faces polyhedron_imp_closed polyhedron_imp_convex)
next
  assume ?rhs
  then show ?lhs
    by (force simp: polyhedron_eq_finite_exposed_faces exposed_face_of intro: finite_subset)
qed

lemma polyhedron_linear_image_eq:
  fixes h :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "linear h" "bij h"
    shows "polyhedron (h ` S) \<longleftrightarrow> polyhedron S"
proof -
  have *: "{f. P f} = (image h) ` {f. P (h ` f)}" for P
    apply safe
    apply (rule_tac x="inv h ` x" in image_eqI)
    apply (auto simp: \<open>bij h\<close> bij_is_surj image_f_inv_f)
    done
  have "inj h" using bij_is_inj assms by blast
  then have injim: "inj_on ((`) h) A" for A
    by (simp add: inj_on_def inj_image_eq_iff)
  show ?thesis
    using \<open>linear h\<close> \<open>inj h\<close>
    apply (simp add: polyhedron_eq_finite_faces closed_injective_linear_image_eq)
    apply (simp add: * face_of_linear_image [of h _ S, symmetric] finite_image_iff injim)
    done
qed

lemma polyhedron_negations:
  fixes S :: "'a :: euclidean_space set"
  shows   "polyhedron S \<Longrightarrow> polyhedron(image uminus S)"
  by (subst polyhedron_linear_image_eq) (auto simp: bij_uminus intro!: linear_uminus)

subsection\<open>Relation between polytopes and polyhedra\<close>

proposition polytope_eq_bounded_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<longleftrightarrow> polyhedron S \<and> bounded S"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: finite_polytope_faces polyhedron_eq_finite_faces
                  polytope_imp_closed polytope_imp_convex polytope_imp_bounded)
next
  assume R: ?rhs 
  then have "finite {v. v extreme_point_of S}"
    by (simp add: finite_polyhedron_extreme_points)
  moreover have "S = convex hull {v. v extreme_point_of S}"
    using R by (simp add: Krein_Milman_Minkowski compact_eq_bounded_closed polyhedron_imp_closed polyhedron_imp_convex)
  ultimately show ?lhs
    unfolding polytope_def by blast
qed

lemma polytope_Int:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
by (simp add: polytope_eq_bounded_polyhedron bounded_Int)


lemma polytope_Int_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polyhedron T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
  by (simp add: bounded_Int polytope_eq_bounded_polyhedron)

lemma polyhedron_Int_polytope:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polyhedron S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
  by (simp add: bounded_Int polytope_eq_bounded_polyhedron)

lemma polytope_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron S"
  by (simp add: polytope_eq_bounded_polyhedron)

lemma polytope_facet_exists:
  fixes p :: "'a :: euclidean_space set"
  assumes "polytope p" "0 < aff_dim p"
  obtains F where "F facet_of p"
proof (cases "p = {}")
  case True with assms show ?thesis by auto
next
  case False
  then obtain v where "v extreme_point_of p"
    using extreme_point_exists_convex
    by (blast intro: \<open>polytope p\<close> polytope_imp_compact polytope_imp_convex)
  then
  show ?thesis
    by (metis face_of_polyhedron_subset_facet polytope_imp_polyhedron aff_dim_sing
       all_not_in_conv assms face_of_singleton less_irrefl singletonI that)
qed

lemma polyhedron_interval [iff]: "polyhedron(cbox a b)"
by (metis polytope_imp_polyhedron polytope_interval)

lemma polyhedron_convex_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "finite S \<Longrightarrow> polyhedron(convex hull S)"
by (simp add: polytope_convex_hull polytope_imp_polyhedron)


subsection\<open>Relative and absolute frontier of a polytope\<close>

lemma rel_boundary_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "\<not> affine_dependent S"
      shows "(convex hull S) - rel_interior(convex hull S) = (\<Union>a\<in>S. convex hull (S - {a}))"
proof -
  have "finite S" by (metis assms aff_independent_finite)
  then consider "card S = 0" | "card S = 1" | "2 \<le> card S" by arith
  then show ?thesis
  proof cases
    case 1 then have "S = {}" by (simp add: \<open>finite S\<close>)
    then show ?thesis by simp
  next
    case 2 show ?thesis
      by (auto intro: card_1_singletonE [OF \<open>card S = 1\<close>])
  next
    case 3
    with assms show ?thesis
      by (auto simp: polyhedron_convex_hull rel_boundary_of_polyhedron facet_of_convex_hull_affine_independent_alt \<open>finite S\<close>)
  qed
qed

proposition frontier_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "card S = Suc (DIM('a))"
      shows "frontier(convex hull S) = \<Union> {convex hull (S - {a}) | a. a \<in> S}"
proof (cases "affine_dependent S")
  case True
    have [iff]: "finite S"
      using assms using card.infinite by force
    then have ccs: "closed (convex hull S)"
      by (simp add: compact_imp_closed finite_imp_compact_convex_hull)
    { fix x T
      assume "int (card T) \<le> aff_dim S + 1"  "finite T" "T \<subseteq> S""x \<in> convex hull T"
      then have "S \<noteq> T"
        using True \<open>finite S\<close> aff_dim_le_card affine_independent_iff_card by fastforce
      then obtain a where "a \<in> S" "a \<notin> T"
        using \<open>T \<subseteq> S\<close> by blast
      then have "\<exists>y\<in>S. x \<in> convex hull (S - {y})"
        using True affine_independent_iff_card [of S]
        by (metis (no_types, hide_lams) Diff_eq_empty_iff Diff_insert0 \<open>a \<notin> T\<close> \<open>T \<subseteq> S\<close> \<open>x \<in> convex hull T\<close> hull_mono insert_Diff_single subsetCE)
    } note * = this
    have 1: "convex hull S \<subseteq> (\<Union> a\<in>S. convex hull (S - {a}))"
      by (subst caratheodory_aff_dim) (blast dest: *)
    have 2: "\<Union>((\<lambda>a. convex hull (S - {a})) ` S) \<subseteq> convex hull S"
      by (rule Union_least) (metis (no_types, lifting)  Diff_subset hull_mono imageE)
    show ?thesis using True
      apply (simp add: segment_convex_hull frontier_def)
      using interior_convex_hull_eq_empty [OF assms]
      apply (simp add: closure_closed [OF ccs])
      using "1" "2" by auto
next
  case False
  then have "frontier (convex hull S) = closure (convex hull S) - interior (convex hull S)"
    by (simp add: rel_boundary_of_convex_hull frontier_def)
  also have "\<dots> = (convex hull S) - rel_interior(convex hull S)"
    by (metis False aff_independent_finite assms closure_convex_hull finite_imp_compact_convex_hull hull_hull interior_convex_hull_eq_empty rel_interior_nonempty_interior)
  also have "\<dots> = \<Union>{convex hull (S - {a}) |a. a \<in> S}"
  proof -
    have "convex hull S - rel_interior (convex hull S) = rel_frontier (convex hull S)"
      by (simp add: False aff_independent_finite polyhedron_convex_hull rel_boundary_of_polyhedron rel_frontier_of_polyhedron)
    then show ?thesis
      by (simp add: False rel_frontier_convex_hull_cases)
  qed
  finally show ?thesis .
qed

subsection\<open>Special case of a triangle\<close>

proposition frontier_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "frontier(convex hull {a,b,c}) = closed_segment a b \<union> closed_segment b c \<union> closed_segment c a"
          (is "?lhs = ?rhs")
proof (cases "b = a \<or> c = a \<or> c = b")
  case True then show ?thesis
    by (auto simp: assms segment_convex_hull frontier_def empty_interior_convex_hull insert_commute card_insert_le_m1 hull_inc insert_absorb)
next
  case False then have [simp]: "card {a, b, c} = Suc (DIM('a))"
    by (simp add: card.insert_remove Set.insert_Diff_if assms)
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      using False
      by (force simp: segment_convex_hull frontier_of_convex_hull insert_Diff_if insert_commute split: if_split_asm)
    show "?rhs \<subseteq> ?lhs"
      using False
      apply (simp add: frontier_of_convex_hull segment_convex_hull)
      apply (intro conjI subsetI)
        apply (rule_tac X="convex hull {a,b}" in UnionI; force simp: Set.insert_Diff_if)
       apply (rule_tac X="convex hull {b,c}" in UnionI; force)
      apply (rule_tac X="convex hull {a,c}" in UnionI; force simp: insert_commute Set.insert_Diff_if)
      done
  qed
qed

corollary inside_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "inside (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a) = interior(convex hull {a,b,c})"
by (metis assms frontier_of_triangle bounded_empty bounded_insert convex_convex_hull inside_frontier_eq_interior bounded_convex_hull)

corollary interior_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "interior(convex hull {a,b,c}) =
           convex hull {a,b,c} - (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a)"
  using interior_subset
  by (force simp: frontier_of_triangle [OF assms, symmetric] frontier_def Diff_Diff_Int)

subsection\<open>Subdividing a cell complex\<close>

lemma subdivide_interval:
  fixes x::real
  assumes "a < \<bar>x - y\<bar>" "0 < a"
  obtains n where "n \<in> \<int>" "x < n * a \<and> n * a < y \<or> y <  n * a \<and> n * a < x"
proof -
  consider "a + x < y" | "a + y < x"
    using assms by linarith
  then show ?thesis
  proof cases
    case 1
    let ?n = "of_int (floor (x/a)) + 1"
    have x: "x < ?n * a"
      by (meson \<open>0 < a\<close> divide_less_eq floor_eq_iff)
    have "?n * a \<le> a + x"
      apply (simp add: algebra_simps)
      by (metis assms(2) floor_divide_lower mult.commute)
    also have "... < y"
      by (rule 1)
    finally have "?n * a < y" .
    with x show ?thesis
      using Ints_1 Ints_add Ints_of_int that by blast
  next
    case 2
    let ?n = "of_int (floor (y/a)) + 1"
    have y: "y < ?n * a"
      by (meson \<open>0 < a\<close> divide_less_eq floor_eq_iff)
    have "?n * a \<le> a + y"
      apply (simp add: algebra_simps)
      by (metis assms(2) floor_divide_lower mult.commute)
    also have "... < x"
      by (rule 2)
    finally have "?n * a < x" .
    then show ?thesis
      using Ints_1 Ints_add Ints_of_int that y by blast
  qed
qed

lemma cell_subdivision_lemma:
  assumes "finite \<F>"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and "finite I"
    shows "\<exists>\<G>. \<Union>\<G> = \<Union>\<F> \<and>
                 finite \<G> \<and>
                 (\<forall>C \<in> \<G>. \<exists>D. D \<in> \<F> \<and> C \<subseteq> D) \<and>
                 (\<forall>C \<in> \<F>. \<forall>x \<in> C. \<exists>D. D \<in> \<G> \<and> x \<in> D \<and> D \<subseteq> C) \<and>
                 (\<forall>X \<in> \<G>. polytope X) \<and>
                 (\<forall>X \<in> \<G>. aff_dim X \<le> d) \<and>
                 (\<forall>X \<in> \<G>. \<forall>Y \<in> \<G>. X \<inter> Y face_of X) \<and>
                 (\<forall>X \<in> \<G>. \<forall>x \<in> X. \<forall>y \<in> X. \<forall>a b.
                          (a,b) \<in> I \<longrightarrow> a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or>
                                        a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b)"
  using \<open>finite I\<close>
proof induction
  case empty
  then show ?case
    by (rule_tac x="\<F>" in exI) (auto simp: assms)
next
  case (insert ab I)
  then obtain \<G> where eq: "\<Union>\<G> = \<Union>\<F>" and "finite \<G>"
                   and sub1: "\<And>C. C \<in> \<G> \<Longrightarrow> \<exists>D. D \<in> \<F> \<and> C \<subseteq> D"
                   and sub2: "\<And>C x. C \<in> \<F> \<and> x \<in> C \<Longrightarrow> \<exists>D. D \<in> \<G> \<and> x \<in> D \<and> D \<subseteq> C"
                   and poly: "\<And>X. X \<in> \<G> \<Longrightarrow> polytope X"
                   and aff: "\<And>X. X \<in> \<G> \<Longrightarrow> aff_dim X \<le> d"
                   and face: "\<And>X Y. \<lbrakk>X \<in> \<G>; Y \<in> \<G>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
                   and I: "\<And>X x y a b.  \<lbrakk>X \<in> \<G>; x \<in> X; y \<in> X; (a,b) \<in> I\<rbrakk> \<Longrightarrow>
                                    a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or> a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
    by (auto simp: that)
  obtain a b where "ab = (a,b)"
    by fastforce
  let ?\<G> = "(\<lambda>X. X \<inter> {x. a \<bullet> x \<le> b}) ` \<G> \<union> (\<lambda>X. X \<inter> {x. a \<bullet> x \<ge> b}) ` \<G>"
  have eqInt: "(S \<inter> Collect P) \<inter> (T \<inter> Collect Q) = (S \<inter> T) \<inter> (Collect P \<inter> Collect Q)" for S T::"'a set" and P Q
    by blast
  show ?case
  proof (intro conjI exI)
    show "\<Union>?\<G> = \<Union>\<F>"
      by (force simp: eq [symmetric])
    show "finite ?\<G>"
      using \<open>finite \<G>\<close> by force
    show "\<forall>X \<in> ?\<G>. polytope X"
      by (force simp: poly polytope_Int_polyhedron polyhedron_halfspace_le polyhedron_halfspace_ge)
    show "\<forall>X \<in> ?\<G>. aff_dim X \<le> d"
      by (auto; metis order_trans aff aff_dim_subset inf_le1)
    show "\<forall>X \<in> ?\<G>. \<forall>x \<in> X. \<forall>y \<in> X. \<forall>a b.
                          (a,b) \<in> insert ab I \<longrightarrow> a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or>
                                                  a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
      using \<open>ab = (a, b)\<close> I by fastforce
    show "\<forall>X \<in> ?\<G>. \<forall>Y \<in> ?\<G>. X \<inter> Y face_of X"
      by (auto simp: eqInt halfspace_Int_eq face_of_Int_Int face face_of_halfspace_le face_of_halfspace_ge)
    show "\<forall>C \<in> ?\<G>. \<exists>D. D \<in> \<F> \<and> C \<subseteq> D"
      using sub1 by force
    show "\<forall>C\<in>\<F>. \<forall>x\<in>C. \<exists>D. D \<in> ?\<G> \<and> x \<in> D \<and> D \<subseteq> C"
    proof (intro ballI)
      fix C z
      assume "C \<in> \<F>" "z \<in> C"
      with sub2 obtain D where D: "D \<in> \<G>" "z \<in> D" "D \<subseteq> C" by blast
      have "D \<in> \<G> \<and> z \<in> D \<inter> {x. a \<bullet> x \<le> b} \<and> D \<inter> {x. a \<bullet> x \<le> b} \<subseteq> C \<or>
            D \<in> \<G> \<and> z \<in> D \<inter> {x. a \<bullet> x \<ge> b} \<and> D \<inter> {x. a \<bullet> x \<ge> b} \<subseteq> C"
        using linorder_class.linear [of "a \<bullet> z" b] D by blast
      then show "\<exists>D. D \<in> ?\<G> \<and> z \<in> D \<and> D \<subseteq> C"
        by blast
    qed
  qed
qed


proposition cell_complex_subdivision_exists:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "0 < e" "finite \<F>"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
  obtains "\<F>'" where "finite \<F>'" "\<Union>\<F>' = \<Union>\<F>" "\<And>X. X \<in> \<F>' \<Longrightarrow> diameter X < e"
                "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X" "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
                "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
                "\<And>C. C \<in> \<F>' \<Longrightarrow> \<exists>D. D \<in> \<F> \<and> C \<subseteq> D"
                "\<And>C x. C \<in> \<F> \<and> x \<in> C \<Longrightarrow> \<exists>D. D \<in> \<F>' \<and> x \<in> D \<and> D \<subseteq> C"
proof -
  have "bounded(\<Union>\<F>)"
    by (simp add: \<open>finite \<F>\<close> poly bounded_Union polytope_imp_bounded)
  then obtain B where "B > 0" and B: "\<And>x. x \<in> \<Union>\<F> \<Longrightarrow> norm x < B"
    by (meson bounded_pos_less)
  define C where "C \<equiv> {z \<in> \<int>. \<bar>z * e / 2 / real DIM('a)\<bar> \<le> B}"
  define I where "I \<equiv> \<Union>i \<in> Basis. \<Union>j \<in> C. { (i::'a, j * e / 2 / DIM('a)) }"
  have "C \<subseteq> {x \<in> \<int>. - B / (e / 2 / real DIM('a)) \<le> x \<and> x \<le> B / (e / 2 / real DIM('a))}"
    using \<open>0 < e\<close> by (auto simp: field_split_simps C_def)
  then have "finite C"
    using finite_int_segment finite_subset by blast
  then have "finite I"
    by (simp add: I_def)
  obtain \<F>' where eq: "\<Union>\<F>' = \<Union>\<F>" and "finite \<F>'"
              and poly: "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X"
              and aff: "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
              and face: "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
              and I: "\<And>X x y a b.  \<lbrakk>X \<in> \<F>'; x \<in> X; y \<in> X; (a,b) \<in> I\<rbrakk> \<Longrightarrow>
                                     a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or> a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
              and sub1: "\<And>C. C \<in> \<F>' \<Longrightarrow> \<exists>D. D \<in> \<F> \<and> C \<subseteq> D"
              and sub2: "\<And>C x. C \<in> \<F> \<and> x \<in> C \<Longrightarrow> \<exists>D. D \<in> \<F>' \<and> x \<in> D \<and> D \<subseteq> C"
    apply (rule exE [OF cell_subdivision_lemma])
    using assms \<open>finite I\<close> by auto
  show ?thesis
  proof (rule_tac \<F>'="\<F>'" in that)
    show "diameter X < e" if "X \<in> \<F>'" for X
    proof -
      have "diameter X \<le> e/2"
      proof (rule diameter_le)
        show "norm (x - y) \<le> e / 2" if "x \<in> X" "y \<in> X" for x y
        proof -
          have "norm x < B" "norm y < B"
            using B \<open>X \<in> \<F>'\<close> eq that by blast+
          have "norm (x - y) \<le> (\<Sum>b\<in>Basis. \<bar>(x-y) \<bullet> b\<bar>)"
            by (rule norm_le_l1)
          also have "... \<le> of_nat (DIM('a)) * (e / 2 / DIM('a))"
          proof (rule sum_bounded_above)
            fix i::'a
            assume "i \<in> Basis"
            then have I': "\<And>z b. \<lbrakk>z \<in> C; b = z * e / (2 * real DIM('a))\<rbrakk> \<Longrightarrow> i \<bullet> x \<le> b \<and> i \<bullet> y \<le> b \<or> i \<bullet> x \<ge> b \<and> i \<bullet> y \<ge> b"
              using I[of X x y] \<open>X \<in> \<F>'\<close> that unfolding I_def by auto
            show "\<bar>(x - y) \<bullet> i\<bar> \<le> e / 2 / real DIM('a)"
            proof (rule ccontr)
              assume "\<not> \<bar>(x - y) \<bullet> i\<bar> \<le> e / 2 / real DIM('a)"
              then have xyi: "\<bar>i \<bullet> x - i \<bullet> y\<bar> > e / 2 / real DIM('a)"
                by (simp add: inner_commute inner_diff_right)
              obtain n where "n \<in> \<int>" and n: "i \<bullet> x < n * (e / 2 / real DIM('a)) \<and> n * (e / 2 / real DIM('a)) < i \<bullet> y \<or> i \<bullet> y < n * (e / 2 / real DIM('a)) \<and> n * (e / 2 / real DIM('a)) < i \<bullet> x"
                using subdivide_interval [OF xyi] DIM_positive \<open>0 < e\<close>
                by (auto simp: zero_less_divide_iff)
              have "\<bar>i \<bullet> x\<bar> < B"
                by (metis \<open>i \<in> Basis\<close> \<open>norm x < B\<close> inner_commute norm_bound_Basis_lt)
              have "\<bar>i \<bullet> y\<bar> < B"
                by (metis \<open>i \<in> Basis\<close> \<open>norm y < B\<close> inner_commute norm_bound_Basis_lt)
              have *: "\<bar>n * e\<bar> \<le> B * (2 * real DIM('a))"
                      if "\<bar>ix\<bar> < B" "\<bar>iy\<bar> < B"
                         and ix: "ix * (2 * real DIM('a)) < n * e"
                         and iy: "n * e < iy * (2 * real DIM('a))" for ix iy
              proof (rule abs_leI)
                have "iy * (2 * real DIM('a)) \<le> B * (2 * real DIM('a))"
                  by (rule mult_right_mono) (use \<open>\<bar>iy\<bar> < B\<close> in linarith)+
                then show "n * e \<le> B * (2 * real DIM('a))"
                  using iy by linarith
              next
                have "- ix * (2 * real DIM('a)) \<le> B * (2 * real DIM('a))"
                  by (rule mult_right_mono) (use \<open>\<bar>ix\<bar> < B\<close> in linarith)+
                then show "- (n * e) \<le> B * (2 * real DIM('a))"
                  using ix by linarith
              qed
              have "n \<in> C"
                using \<open>n \<in> \<int>\<close> n  by (auto simp: C_def divide_simps intro: * \<open>\<bar>i \<bullet> x\<bar> < B\<close> \<open>\<bar>i \<bullet> y\<bar> < B\<close>)
              show False
                using  I' [OF \<open>n \<in> C\<close> refl] n  by auto
            qed
          qed
          also have "... = e / 2"
            by simp
          finally show ?thesis .
        qed
      qed (use \<open>0 < e\<close> in force)
      also have "... < e"
        by (simp add: \<open>0 < e\<close>)
      finally show ?thesis .
    qed
  qed (auto simp: eq poly aff face sub1 sub2 \<open>finite \<F>'\<close>)
qed


subsection\<open>Simplexes\<close>

text\<open>The notion of n-simplex for integer \<^term>\<open>n \<ge> -1\<close>\<close>

definition\<^marker>\<open>tag important\<close> simplex :: "int \<Rightarrow> 'a::euclidean_space set \<Rightarrow> bool" (infix "simplex" 50)
  where "n simplex S \<equiv> \<exists>C. \<not> affine_dependent C \<and> int(card C) = n + 1 \<and> S = convex hull C"

lemma simplex:
    "n simplex S \<longleftrightarrow> (\<exists>C. finite C \<and>
                       \<not> affine_dependent C \<and>
                       int(card C) = n + 1 \<and>
                       S = convex hull C)"
  by (auto simp add: simplex_def intro: aff_independent_finite)

lemma simplex_convex_hull:
   "\<not> affine_dependent C \<and> int(card C) = n + 1 \<Longrightarrow> n simplex (convex hull C)"
  by (auto simp add: simplex_def)

lemma convex_simplex: "n simplex S \<Longrightarrow> convex S"
  by (metis convex_convex_hull simplex_def)

lemma compact_simplex: "n simplex S \<Longrightarrow> compact S"
  unfolding simplex
  using finite_imp_compact_convex_hull by blast

lemma closed_simplex: "n simplex S \<Longrightarrow> closed S"
  by (simp add: compact_imp_closed compact_simplex)

lemma simplex_imp_polytope:
   "n simplex S \<Longrightarrow> polytope S"
  unfolding simplex_def polytope_def
  using aff_independent_finite by blast

lemma simplex_imp_polyhedron:
   "n simplex S \<Longrightarrow> polyhedron S"
  by (simp add: polytope_imp_polyhedron simplex_imp_polytope)

lemma simplex_dim_ge: "n simplex S \<Longrightarrow> -1 \<le> n"
  by (metis (no_types, hide_lams) aff_dim_geq affine_independent_iff_card diff_add_cancel diff_diff_eq2 simplex_def)

lemma simplex_empty [simp]: "n simplex {} \<longleftrightarrow> n = -1"
proof
  assume "n simplex {}"
  then show "n = -1"
    unfolding simplex by (metis card.empty convex_hull_eq_empty diff_0 diff_eq_eq of_nat_0)
next
  assume "n = -1" then show "n simplex {}"
    by (fastforce simp: simplex)
qed

lemma simplex_minus_1 [simp]: "-1 simplex S \<longleftrightarrow> S = {}"
  by (metis simplex cancel_comm_monoid_add_class.diff_cancel card_0_eq diff_minus_eq_add of_nat_eq_0_iff simplex_empty)


lemma aff_dim_simplex:
   "n simplex S \<Longrightarrow> aff_dim S = n"
  by (metis simplex add.commute add_diff_cancel_left' aff_dim_convex_hull affine_independent_iff_card)

lemma zero_simplex_sing: "0 simplex {a}"
  apply (simp add: simplex_def)
  using affine_independent_1 card_1_singleton_iff convex_hull_singleton by blast

lemma simplex_sing [simp]: "n simplex {a} \<longleftrightarrow> n = 0"
  using aff_dim_simplex aff_dim_sing zero_simplex_sing by blast

lemma simplex_zero: "0 simplex S \<longleftrightarrow> (\<exists>a. S = {a})"
  by (metis aff_dim_eq_0 aff_dim_simplex simplex_sing)

lemma one_simplex_segment: "a \<noteq> b \<Longrightarrow> 1 simplex closed_segment a b"
  unfolding simplex_def
  by (rule_tac x="{a,b}" in exI) (auto simp: segment_convex_hull)

lemma simplex_segment_cases:
   "(if a = b then 0 else 1) simplex closed_segment a b"
  by (auto simp: one_simplex_segment)

lemma simplex_segment:
   "\<exists>n. n simplex closed_segment a b"
  using simplex_segment_cases by metis

lemma polytope_lowdim_imp_simplex:
  assumes "polytope P" "aff_dim P \<le> 1"
  obtains n where "n simplex P"
proof (cases "P = {}")
  case True
  then show ?thesis
    by (simp add: that)
next
  case False
  then show ?thesis
    by (metis assms compact_convex_collinear_segment collinear_aff_dim polytope_imp_compact polytope_imp_convex simplex_segment_cases that)
qed

lemma simplex_insert_dimplus1:
  fixes n::int
  assumes "n simplex S" and a: "a \<notin> affine hull S"
  shows "(n+1) simplex (convex hull (insert a S))"
proof -
  obtain C where C: "finite C" "\<not> affine_dependent C" "int(card C) = n+1" and S: "S = convex hull C"
    using assms unfolding simplex by force
  show ?thesis
    unfolding simplex
  proof (intro exI conjI)
      have "aff_dim S = n"
        using aff_dim_simplex assms(1) by blast
      moreover have "a \<notin> affine hull C"
        using S a affine_hull_convex_hull by blast
      moreover have "a \<notin> C"
          using S a hull_inc by fastforce
      ultimately show "\<not> affine_dependent (insert a C)"
        by (simp add: C S aff_dim_convex_hull aff_dim_insert affine_independent_iff_card)
  next
    have "a \<notin> C"
      using S a hull_inc by fastforce
    then show "int (card (insert a C)) = n + 1 + 1"
      by (simp add: C)
  next
    show "convex hull insert a S = convex hull (insert a C)"
      by (simp add: S convex_hull_insert_segments)
  qed (use C in auto)
qed

subsection \<open>Simplicial complexes and triangulations\<close>

definition\<^marker>\<open>tag important\<close> simplicial_complex where
 "simplicial_complex \<C> \<equiv>
        finite \<C> \<and>
        (\<forall>S \<in> \<C>. \<exists>n. n simplex S) \<and>
        (\<forall>F S. S \<in> \<C> \<and> F face_of S \<longrightarrow> F \<in> \<C>) \<and>
        (\<forall>S S'. S \<in> \<C> \<and> S' \<in> \<C> \<longrightarrow> (S \<inter> S') face_of S)"

definition\<^marker>\<open>tag important\<close> triangulation where
 "triangulation \<T> \<equiv>
        finite \<T> \<and>
        (\<forall>T \<in> \<T>. \<exists>n. n simplex T) \<and>
        (\<forall>T T'. T \<in> \<T> \<and> T' \<in> \<T> \<longrightarrow> (T \<inter> T') face_of T)"


subsection\<open>Refining a cell complex to a simplicial complex\<close>

proposition convex_hull_insert_Int_eq:
  fixes z :: "'a :: euclidean_space"
  assumes z: "z \<in> rel_interior S"
      and T: "T \<subseteq> rel_frontier S"
      and U: "U \<subseteq> rel_frontier S"
      and "convex S" "convex T" "convex U"
  shows "convex hull (insert z T) \<inter> convex hull (insert z U) = convex hull (insert z (T \<inter> U))"
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof (cases "T={} \<or> U={}")
    case True then show ?thesis by auto
  next
    case False
    then have "T \<noteq> {}" "U \<noteq> {}" by auto
    have TU: "convex (T \<inter> U)"
      by (simp add: \<open>convex T\<close> \<open>convex U\<close> convex_Int)
    have "(\<Union>x\<in>T. closed_segment z x) \<inter> (\<Union>x\<in>U. closed_segment z x)
          \<subseteq> (if T \<inter> U = {} then {z} else \<Union>((closed_segment z) ` (T \<inter> U)))" (is "_ \<subseteq> ?IF")
    proof clarify
      fix x t u
      assume xt: "x \<in> closed_segment z t"
        and xu: "x \<in> closed_segment z u"
        and "t \<in> T" "u \<in> U"
      then have ne: "t \<noteq> z" "u \<noteq> z"
        using T U z unfolding rel_frontier_def by blast+
      show "x \<in> ?IF"
      proof (cases "x = z")
        case True then show ?thesis by auto
      next
        case False
        have t: "t \<in> closure S"
          using T \<open>t \<in> T\<close> rel_frontier_def by auto
        have u: "u \<in> closure S"
          using U \<open>u \<in> U\<close> rel_frontier_def by auto
        show ?thesis
        proof (cases "t = u")
          case True
          then show ?thesis
            using \<open>t \<in> T\<close> \<open>u \<in> U\<close> xt by auto
        next
          case False
          have tnot: "t \<notin> closed_segment u z"
          proof -
            have "t \<in> closure S - rel_interior S"
              using T \<open>t \<in> T\<close> rel_frontier_def by blast
            then have "t \<notin> open_segment z u"
              by (meson DiffD2 rel_interior_closure_convex_segment [OF \<open>convex S\<close> z u] subsetD)
            then show ?thesis
              by (simp add: \<open>t \<noteq> u\<close> \<open>t \<noteq> z\<close> open_segment_commute open_segment_def)
          qed
          moreover have "u \<notin> closed_segment z t"
            using rel_interior_closure_convex_segment [OF \<open>convex S\<close> z t] \<open>u \<in> U\<close> \<open>u \<noteq> z\<close>
              U [unfolded rel_frontier_def] tnot
            by (auto simp: closed_segment_eq_open)
          ultimately
          have "\<not>(between (t,u) z | between (u,z) t | between (z,t) u)" if "x \<noteq> z"
            using that xt xu
            by (meson between_antisym between_mem_segment between_trans_2 ends_in_segment(2))
          then have "\<not> collinear {t, z, u}" if "x \<noteq> z"
            by (auto simp: that collinear_between_cases between_commute)
          moreover have "collinear {t, z, x}"
            by (metis closed_segment_commute collinear_2 collinear_closed_segment collinear_triples ends_in_segment(1) insert_absorb insert_absorb2 xt)
          moreover have "collinear {z, x, u}"
            by (metis closed_segment_commute collinear_2 collinear_closed_segment collinear_triples ends_in_segment(1) insert_absorb insert_absorb2 xu)
          ultimately have False
            using collinear_3_trans [of t z x u] \<open>x \<noteq> z\<close> by blast
          then show ?thesis by metis
        qed
      qed
    qed
    then show ?thesis
      using False \<open>convex T\<close> \<open>convex U\<close> TU
      by (simp add: convex_hull_insert_segments hull_same split: if_split_asm)
  qed
  show "?rhs \<subseteq> ?lhs"
    by (metis inf_greatest hull_mono inf.cobounded1 inf.cobounded2 insert_mono)
qed

lemma simplicial_subdivision_aux:
  assumes "finite \<M>"
      and "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C \<le> of_nat n"
      and "\<And>C F. \<lbrakk>C \<in> \<M>; F face_of C\<rbrakk> \<Longrightarrow> F \<in> \<M>"
      and "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
    shows "\<exists>\<T>. simplicial_complex \<T> \<and>
                (\<forall>K \<in> \<T>. aff_dim K \<le> of_nat n) \<and>
                \<Union>\<T> = \<Union>\<M> \<and>
                (\<forall>C \<in> \<M>. \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F) \<and>
                (\<forall>K \<in> \<T>. \<exists>C. C \<in> \<M> \<and> K \<subseteq> C)"
  using assms
proof (induction n arbitrary: \<M> rule: less_induct)
  case (less n)
  then have poly\<M>: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
    and aff\<M>:    "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C \<le> of_nat n"
    and face\<M>:   "\<And>C F. \<lbrakk>C \<in> \<M>; F face_of C\<rbrakk> \<Longrightarrow> F \<in> \<M>"
    and intface\<M>: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
    by metis+
  show ?case
  proof (cases "n \<le> 1")
    case True
    have "\<And>s. \<lbrakk>n \<le> 1; s \<in> \<M>\<rbrakk> \<Longrightarrow> \<exists>m. m simplex s"
      using poly\<M> aff\<M> by (force intro: polytope_lowdim_imp_simplex)
    then show ?thesis
      unfolding simplicial_complex_def using True
      by (rule_tac x="\<M>" in exI) (auto simp: less.prems)
  next
    case False
    define \<S> where "\<S> \<equiv> {C \<in> \<M>. aff_dim C < n}"
    have "finite \<S>" "\<And>C. C \<in> \<S> \<Longrightarrow> polytope C" "\<And>C. C \<in> \<S> \<Longrightarrow> aff_dim C \<le> int (n - 1)"
      "\<And>C1 C2. \<lbrakk>C1 \<in> \<S>; C2 \<in> \<S>\<rbrakk>  \<Longrightarrow> C1 \<inter> C2 face_of C1"
      using less.prems by (auto simp: \<S>_def)
    moreover have \<section>: "\<And>C F. \<lbrakk>C \<in> \<S>; F face_of C\<rbrakk> \<Longrightarrow> F \<in> \<S>"
      using less.prems unfolding \<S>_def 
      by (metis (no_types, lifting) mem_Collect_eq aff_dim_subset face_of_imp_subset less_le not_le)
    ultimately obtain \<U> where "simplicial_complex \<U>"
      and aff_dim\<U>: "\<And>K. K \<in> \<U> \<Longrightarrow> aff_dim K \<le> int (n - 1)"
      and        "\<Union>\<U> = \<Union>\<S>"
      and fin\<U>:  "\<And>C. C \<in> \<S> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<U> \<and> C = \<Union>F"
      and C\<U>:    "\<And>K. K \<in> \<U> \<Longrightarrow> \<exists>C. C \<in> \<S> \<and> K \<subseteq> C"
      using less.IH [of "n-1" \<S>] False by auto
    then have "finite \<U>"
      and simpl\<U>: "\<And>S. S \<in> \<U> \<Longrightarrow> \<exists>n. n simplex S"
      and face\<U>:  "\<And>F S. \<lbrakk>S \<in> \<U>; F face_of S\<rbrakk> \<Longrightarrow> F \<in> \<U>"
      and faceI\<U>: "\<And>S S'. \<lbrakk>S \<in> \<U>; S' \<in> \<U>\<rbrakk> \<Longrightarrow> (S \<inter> S') face_of S"
      by (auto simp: simplicial_complex_def)
    define \<N> where "\<N> \<equiv> {C \<in> \<M>. aff_dim C = n}"
    have "finite \<N>"
      by (simp add: \<N>_def less.prems(1))
    have poly\<N>: "\<And>C. C \<in> \<N> \<Longrightarrow> polytope C"
      and convex\<N>: "\<And>C. C \<in> \<N> \<Longrightarrow> convex C"
      and closed\<N>: "\<And>C. C \<in> \<N> \<Longrightarrow> closed C"
      by (auto simp: \<N>_def poly\<M> polytope_imp_convex polytope_imp_closed)
    have in_rel_interior: "(SOME z. z \<in> rel_interior C) \<in> rel_interior C" if "C \<in> \<N>" for C
      using that poly\<M> polytope_imp_convex rel_interior_aff_dim some_in_eq by (fastforce simp: \<N>_def)
    have *: "\<exists>T. \<not> affine_dependent T \<and> card T \<le> n \<and> aff_dim K < n \<and> K = convex hull T"
      if "K \<in> \<U>" for K
    proof -
      obtain r where r: "r simplex K"
        using \<open>K \<in> \<U>\<close> simpl\<U> by blast
      have "r = aff_dim K"
        using \<open>r simplex K\<close> aff_dim_simplex by blast
      with r
      show ?thesis
        unfolding simplex_def
        using False \<open>\<And>K. K \<in> \<U> \<Longrightarrow> aff_dim K \<le> int (n - 1)\<close> that by fastforce
    qed
    have ahK_C_disjoint: "affine hull K \<inter> rel_interior C = {}"
      if "C \<in> \<N>" "K \<in> \<U>" "K \<subseteq> rel_frontier C" for C K
    proof -
      have "convex C" "closed C"
        by (auto simp: convex\<N> closed\<N> \<open>C \<in> \<N>\<close>)
      obtain F where F: "F face_of C" and "F \<noteq> C" "K \<subseteq> F"
      proof -
        obtain L where "L \<in> \<S>" "K \<subseteq> L"
          using \<open>K \<in> \<U>\<close> C\<U> by blast
        have "K \<le> rel_frontier C"
          by (simp add: \<open>K \<subseteq> rel_frontier C\<close>)
        also have "... \<le> C"
          by (simp add: \<open>closed C\<close> rel_frontier_def subset_iff)
        finally have "K \<subseteq> C" .
        have "L \<inter> C face_of C"
          using \<N>_def \<S>_def \<open>C \<in> \<N>\<close> \<open>L \<in> \<S>\<close> intface\<M> by (simp add: inf_commute)
        moreover have "L \<inter> C \<noteq> C"
          using \<open>C \<in> \<N>\<close> \<open>L \<in> \<S>\<close>
          by (metis (mono_tags, lifting) \<N>_def \<S>_def intface\<M> mem_Collect_eq not_le order_refl \<section>)
        moreover have "K \<subseteq> L \<inter> C"
          using \<open>C \<in> \<N>\<close> \<open>L \<in> \<S>\<close> \<open>K \<subseteq> C\<close> \<open>K \<subseteq> L\<close> by (auto simp: \<N>_def \<S>_def)
        ultimately show ?thesis using that by metis
      qed
      have "affine hull F \<inter> rel_interior C = {}"
        by (rule affine_hull_face_of_disjoint_rel_interior [OF \<open>convex C\<close> F \<open>F \<noteq> C\<close>])
      with hull_mono [OF \<open>K \<subseteq> F\<close>]
      show "affine hull K \<inter> rel_interior C = {}"
        by fastforce
    qed
    let ?\<T> = "(\<Union>C \<in> \<N>. \<Union>K \<in> \<U> \<inter> Pow (rel_frontier C).
                     {convex hull (insert (SOME z. z \<in> rel_interior C) K)})"
    have "\<exists>\<T>. simplicial_complex \<T> \<and>
              (\<forall>K \<in> \<T>. aff_dim K \<le> of_nat n) \<and>
              (\<forall>C \<in> \<M>. \<exists>F. F \<subseteq> \<T> \<and> C = \<Union>F) \<and>
              (\<forall>K \<in> \<T>. \<exists>C. C \<in> \<M> \<and> K \<subseteq> C)"
    proof (rule exI, intro conjI ballI)
      show "simplicial_complex (\<U> \<union> ?\<T>)"
        unfolding simplicial_complex_def
      proof (intro conjI impI ballI allI)
        show "finite (\<U> \<union> ?\<T>)"
          using \<open>finite \<U>\<close> \<open>finite \<N>\<close> by simp
        show "\<exists>n. n simplex S" if "S \<in> \<U> \<union> ?\<T>" for S
          using that ahK_C_disjoint in_rel_interior simpl\<U> simplex_insert_dimplus1 by fastforce
        show "F \<in> \<U> \<union> ?\<T>" if S: "S \<in> \<U> \<union> ?\<T> \<and> F face_of S" for F S
        proof -
          have "F \<in> \<U>" if "S \<in> \<U>"
            using S face\<U> that by blast
          moreover have "F \<in> \<U> \<union> ?\<T>"
            if "F face_of S" "C \<in> \<N>" "K \<in> \<U>" and "K \<subseteq> rel_frontier C"
              and S: "S = convex hull insert (SOME z. z \<in> rel_interior C) K" for C K
          proof -
            let ?z = "SOME z. z \<in> rel_interior C"
            have "?z \<in> rel_interior C"
              by (simp add: in_rel_interior \<open>C \<in> \<N>\<close>)
            moreover
            obtain I where "\<not> affine_dependent I" "card I \<le> n" "aff_dim K < int n" "K = convex hull I"
              using * [OF \<open>K \<in> \<U>\<close>] by auto
            ultimately have "?z \<notin> affine hull I"
              using ahK_C_disjoint affine_hull_convex_hull that by blast
            have "compact I" "finite I"
              by (auto simp: \<open>\<not> affine_dependent I\<close> aff_independent_finite finite_imp_compact)
            moreover have "F face_of convex hull insert ?z I"
              by (metis S \<open>F face_of S\<close> \<open>K = convex hull I\<close> convex_hull_eq_empty convex_hull_insert_segments hull_hull)
            ultimately obtain J where "J \<subseteq> insert ?z I" "F = convex hull J"
              using face_of_convex_hull_subset [of "insert ?z I" F] by auto
            show ?thesis
            proof (cases "?z \<in> J")
              case True
              have "F \<in> (\<Union>K\<in>\<U> \<inter> Pow (rel_frontier C). {convex hull insert ?z K})"
              proof
                have "convex hull (J - {?z}) face_of K"
                  by (metis True \<open>J \<subseteq> insert ?z I\<close> \<open>K = convex hull I\<close> \<open>\<not> affine_dependent I\<close> face_of_convex_hull_affine_independent subset_insert_iff)
                then have "convex hull (J - {?z}) \<in> \<U>"
                  by (rule face\<U> [OF \<open>K \<in> \<U>\<close>])
                moreover
                have "\<And>x. x \<in> convex hull (J - {?z}) \<Longrightarrow> x \<in> rel_frontier C"
                  by (metis True \<open>J \<subseteq> insert ?z I\<close> \<open>K = convex hull I\<close> subsetD hull_mono subset_insert_iff that(4))
                ultimately show "convex hull (J - {?z}) \<in> \<U> \<inter> Pow (rel_frontier C)" by auto
                let ?F = "convex hull insert ?z (convex hull (J - {?z}))"
                have "F \<subseteq> ?F"
                  apply (clarsimp simp: \<open>F = convex hull J\<close>)
                  by (metis True subsetD hull_mono hull_subset subset_insert_iff)
                moreover have "?F \<subseteq> F"
                  apply (clarsimp simp: \<open>F = convex hull J\<close>)
                  by (metis (no_types, lifting) True convex_hull_eq_empty convex_hull_insert_segments hull_hull insert_Diff)
                ultimately
                show "F \<in> {?F}" by auto
              qed
              with \<open>C\<in>\<N>\<close> show ?thesis by auto
            next
              case False
              then have "F \<in> \<U>"
                using face_of_convex_hull_affine_independent [OF \<open>\<not> affine_dependent I\<close>]
                by (metis Int_absorb2 Int_insert_right_if0 \<open>F = convex hull J\<close> \<open>J \<subseteq> insert ?z I\<close> \<open>K = convex hull I\<close> face\<U> inf_le2 \<open>K \<in> \<U>\<close>)
              then show "F \<in> \<U> \<union> ?\<T>"
                by blast
            qed
          qed
          ultimately show ?thesis
            using that by auto
        qed
        have \<section>: "X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
          if XY: "X \<in> \<U>" "Y \<in> ?\<T>" for X Y
        proof -
          obtain C K
            where "C \<in> \<N>" "K \<in> \<U>" "K \<subseteq> rel_frontier C"
              and Y: "Y = convex hull insert (SOME z. z \<in> rel_interior C) K"
            using XY by blast
          have "convex C"
            by (simp add: \<open>C \<in> \<N>\<close> convex\<N>)
          have "K \<subseteq> C"
            by (metis DiffE \<open>C \<in> \<N>\<close> \<open>K \<subseteq> rel_frontier C\<close> closed\<N> closure_closed rel_frontier_def subset_iff)
          let ?z = "(SOME z. z \<in> rel_interior C)"
          have z: "?z \<in> rel_interior C"
            using \<open>C \<in> \<N>\<close> in_rel_interior by blast
          obtain D where "D \<in> \<S>" "X \<subseteq> D"
            using C\<U> \<open>X \<in> \<U>\<close> by blast
          have "D \<inter> rel_interior C = (C \<inter> D) \<inter> rel_interior C"
            using rel_interior_subset by blast
          also have "(C \<inter> D) \<inter> rel_interior C = {}"
          proof (rule face_of_disjoint_rel_interior)
            show "C \<inter> D face_of C"
              using \<N>_def \<S>_def \<open>C \<in> \<N>\<close> \<open>D \<in> \<S>\<close> intface\<M> by blast
            show "C \<inter> D \<noteq> C"
              by (metis (mono_tags, lifting) Int_lower2 \<N>_def \<S>_def \<open>C \<in> \<N>\<close> \<open>D \<in> \<S>\<close> aff_dim_subset mem_Collect_eq not_le)
          qed
          finally have DC: "D \<inter> rel_interior C = {}" .
          have eq: "X \<inter> convex hull (insert ?z K) = X \<inter> convex hull K"
          proof (rule Int_convex_hull_insert_rel_exterior [OF \<open>convex C\<close> \<open>K \<subseteq> C\<close> z])
            show "disjnt X (rel_interior C)"
              using DC by (meson \<open>X \<subseteq> D\<close> disjnt_def disjnt_subset1)
          qed
          obtain I where I: "\<not> affine_dependent I"
            and Keq: "K = convex hull I" and [simp]: "convex hull K = K"
            using "*" \<open>K \<in> \<U>\<close> by force
          then have "?z \<notin> affine hull I"
            using ahK_C_disjoint \<open>C \<in> \<N>\<close> \<open>K \<in> \<U>\<close> \<open>K \<subseteq> rel_frontier C\<close> affine_hull_convex_hull z by blast
          have "X \<inter> K face_of K"
            by (simp add: XY(1) \<open>K \<in> \<U>\<close> faceI\<U> inf_commute)
          also have "... face_of convex hull insert ?z K"
            by (metis I Keq \<open>?z \<notin> affine hull I\<close> aff_independent_finite convex_convex_hull face_of_convex_hull_insert face_of_refl hull_insert)
          finally have "X \<inter> K face_of convex hull insert ?z K" .
          then show ?thesis
            by (simp add: XY(1) Y \<open>K \<in> \<U>\<close> eq faceI\<U>)
        qed

        show "S \<inter> S' face_of S"
          if "S \<in> \<U> \<union> ?\<T> \<and> S' \<in> \<U> \<union> ?\<T>" for S S'
          using that
        proof (elim conjE UnE)
          fix X Y
          assume "X \<in> \<U>" and "Y \<in> \<U>"
          then show "X \<inter> Y face_of X"
            by (simp add: faceI\<U>)
        next
          fix X Y
          assume XY: "X \<in> \<U>" "Y \<in> ?\<T>"
          then show "X \<inter> Y face_of X" "Y \<inter> X face_of Y"
            using \<section> [OF XY] by (auto simp: Int_commute)
        next
          fix X Y
          assume XY: "X \<in> ?\<T>" "Y \<in> ?\<T>"
          show "X \<inter> Y face_of X"
          proof -
            obtain C K D L
              where "C \<in> \<N>" "K \<in> \<U>" "K \<subseteq> rel_frontier C"
                and X: "X = convex hull insert (SOME z. z \<in> rel_interior C) K"
                and "D \<in> \<N>" "L \<in> \<U>" "L \<subseteq> rel_frontier D"
                and Y: "Y = convex hull insert (SOME z. z \<in> rel_interior D) L"
              using XY by blast
            let ?z = "(SOME z. z \<in> rel_interior C)"
            have z: "?z \<in> rel_interior C"
              using \<open>C \<in> \<N>\<close> in_rel_interior by blast
            have "convex C"
              by (simp add: \<open>C \<in> \<N>\<close> convex\<N>)
            have "convex K"
              using "*" \<open>K \<in> \<U>\<close> by blast
            have "convex L"
              by (meson \<open>L \<in> \<U>\<close> convex_simplex simpl\<U>)
            show ?thesis
            proof (cases "D=C")
              case True
              then have "L \<subseteq> rel_frontier C"
                using \<open>L \<subseteq> rel_frontier D\<close> by auto
              have "convex hull insert (SOME z. z \<in> rel_interior C) (K \<inter> L) face_of
                    convex hull insert (SOME z. z \<in> rel_interior C) K"
                by (metis face_of_polytope_insert2 "*" IntI \<open>C \<in> \<N>\<close> aff_independent_finite ahK_C_disjoint empty_iff faceI\<U> polytope_def z \<open>K \<in> \<U>\<close> \<open>L \<in> \<U>\<close>\<open>K \<subseteq> rel_frontier C\<close>)
              then show ?thesis
                using True X Y \<open>K \<subseteq> rel_frontier C\<close> \<open>L \<subseteq> rel_frontier C\<close> \<open>convex C\<close> \<open>convex K\<close> \<open>convex L\<close> convex_hull_insert_Int_eq z by force
            next
              case False
              have "convex D"
                by (simp add: \<open>D \<in> \<N>\<close> convex\<N>)
              have "K \<subseteq> C"
                by (metis DiffE \<open>C \<in> \<N>\<close> \<open>K \<subseteq> rel_frontier C\<close> closed\<N> closure_closed rel_frontier_def subset_eq)
              have "L \<subseteq> D"
                by (metis DiffE \<open>D \<in> \<N>\<close> \<open>L \<subseteq> rel_frontier D\<close> closed\<N> closure_closed rel_frontier_def subset_eq)
              let ?w = "(SOME w. w \<in> rel_interior D)"
              have w: "?w \<in> rel_interior D"
                using \<open>D \<in> \<N>\<close> in_rel_interior by blast
              have "C \<inter> rel_interior D = (D \<inter> C) \<inter> rel_interior D"
                using rel_interior_subset by blast
              also have "(D \<inter> C) \<inter> rel_interior D = {}"
              proof (rule face_of_disjoint_rel_interior)
                show "D \<inter> C face_of D"
                  using \<N>_def \<open>C \<in> \<N>\<close> \<open>D \<in> \<N>\<close> intface\<M> by blast
                have "D \<in> \<M> \<and> aff_dim D = int n"
                  using \<N>_def \<open>D \<in> \<N>\<close> by blast
                moreover have "C \<in> \<M> \<and> aff_dim C = int n"
                  using \<N>_def \<open>C \<in> \<N>\<close> by blast
                ultimately show "D \<inter> C \<noteq> D"
                  by (metis Int_commute False face_of_aff_dim_lt inf.idem inf_le1 intface\<M> not_le poly\<M> polytope_imp_convex)
              qed
              finally have CD: "C \<inter> (rel_interior D) = {}" .
              have zKC: "(convex hull insert ?z K) \<subseteq> C"
                by (metis DiffE \<open>C \<in> \<N>\<close> \<open>K \<subseteq> rel_frontier C\<close> closed\<N> closure_closed convex\<N> hull_minimal insert_subset rel_frontier_def rel_interior_subset subset_iff z)
              have "disjnt (convex hull insert (SOME z. z \<in> rel_interior C) K) (rel_interior D)"
                using zKC CD by (force simp: disjnt_def)
              then have eq: "convex hull (insert ?z K) \<inter> convex hull (insert ?w L) =
                             convex hull (insert ?z K) \<inter> convex hull L"
                by (rule Int_convex_hull_insert_rel_exterior [OF \<open>convex D\<close> \<open>L \<subseteq> D\<close> w])
              have ch_id: "convex hull K = K" "convex hull L = L"
                using "*" \<open>K \<in> \<U>\<close> \<open>L \<in> \<U>\<close> hull_same by auto
              have "convex C"
                by (simp add: \<open>C \<in> \<N>\<close> convex\<N>)
              have "convex hull (insert ?z K) \<inter> L = L \<inter> convex hull (insert ?z K)"
                by blast
              also have "... = convex hull K \<inter> L"
              proof (subst Int_convex_hull_insert_rel_exterior [OF \<open>convex C\<close> \<open>K \<subseteq> C\<close> z])
                have "(C \<inter> D) \<inter> rel_interior C = {}"
                proof (rule face_of_disjoint_rel_interior)
                  show "C \<inter> D face_of C"
                    using \<N>_def \<open>C \<in> \<N>\<close> \<open>D \<in> \<N>\<close> intface\<M> by blast
                  have "D \<in> \<M>" "aff_dim D = int n"
                    using \<N>_def \<open>D \<in> \<N>\<close> by fastforce+
                  moreover have "C \<in> \<M>" "aff_dim C = int n"
                    using \<N>_def \<open>C \<in> \<N>\<close> by fastforce+
                  ultimately have "aff_dim D + - 1 * aff_dim C \<le> 0"
                    by fastforce
                  then have "\<not> C face_of D"
                    using False \<open>convex D\<close> face_of_aff_dim_lt by fastforce
                  show "C \<inter> D \<noteq> C"
                    by (metis inf_commute \<open>C \<in> \<M>\<close> \<open>D \<in> \<M>\<close> \<open>\<not> C face_of D\<close> intface\<M>)
                qed
                then have "D \<inter> rel_interior C = {}"
                  by (metis inf.absorb_iff2 inf_assoc inf_sup_aci(1) rel_interior_subset)
                then show "disjnt L (rel_interior C)"
                  by (meson \<open>L \<subseteq> D\<close> disjnt_def disjnt_subset1)
              next
                show "L \<inter> convex hull K = convex hull K \<inter> L"
                  by force
              qed
              finally have chKL: "convex hull (insert ?z K) \<inter> L = convex hull K \<inter> L" .
              have "convex hull insert ?z K \<inter> convex hull L face_of K"
                by (simp add: \<open>K \<in> \<U>\<close> \<open>L \<in> \<U>\<close> ch_id chKL faceI\<U>)
              also have "... face_of convex hull insert ?z K"
              proof -
                obtain I where I: "\<not> affine_dependent I" "K = convex hull I"
                  using * [OF \<open>K \<in> \<U>\<close>] by auto
                then have "\<And>a. a \<notin> rel_interior C \<or> a \<notin> affine hull I"
                  using ahK_C_disjoint \<open>C \<in> \<N>\<close> \<open>K \<in> \<U>\<close> \<open>K \<subseteq> rel_frontier C\<close> affine_hull_convex_hull by blast
                then show ?thesis
                  by (metis I affine_independent_insert face_of_convex_hull_affine_independent hull_insert subset_insertI z)
              qed
              finally have 1: "convex hull insert ?z K \<inter> convex hull L face_of convex hull insert ?z K" .
              have "convex hull insert ?z K \<inter> convex hull L face_of L"
                by (metis \<open>K \<in> \<U>\<close> \<open>L \<in> \<U>\<close> chKL ch_id faceI\<U> inf_commute)
              also have "... face_of convex hull insert ?w L"
              proof -
                obtain I where I: "\<not> affine_dependent I" "L = convex hull I"
                  using * [OF \<open>L \<in> \<U>\<close>] by auto
                then have "\<And>a. a \<notin> rel_interior D \<or> a \<notin> affine hull I"
                  using \<open>D \<in> \<N>\<close> \<open>L \<in> \<U>\<close> \<open>L \<subseteq> rel_frontier D\<close> affine_hull_convex_hull ahK_C_disjoint by blast
                then show ?thesis
                  by (metis I aff_independent_finite convex_convex_hull face_of_convex_hull_insert face_of_refl hull_insert w)
              qed
              finally have 2: "convex hull insert ?z K \<inter> convex hull L face_of convex hull insert ?w L" .
              show ?thesis
                by (simp add: X Y eq 1 2)
            qed
          qed
        qed 
      qed
      show "\<exists>F \<subseteq> \<U> \<union> ?\<T>. C = \<Union>F" if "C \<in> \<M>" for C
      proof (cases "C \<in> \<S>")
        case True
        then show ?thesis
          by (meson UnCI fin\<U> subsetD subsetI)
      next
        case False
        then have "C \<in> \<N>"
          by (simp add: \<N>_def \<S>_def aff\<M> less_le that)
        let ?z = "SOME z. z \<in> rel_interior C"
        have z: "?z \<in> rel_interior C"
          using \<open>C \<in> \<N>\<close> in_rel_interior by blast
        let ?F = "\<Union>K \<in> \<U> \<inter> Pow (rel_frontier C). {convex hull (insert ?z K)}"
        have "?F \<subseteq> ?\<T>"
          using \<open>C \<in> \<N>\<close> by blast
        moreover have "C \<subseteq> \<Union>?F"
        proof
          fix x
          assume "x \<in> C"
          have "convex C"
            using \<open>C \<in> \<N>\<close> convex\<N> by blast
          have "bounded C"
            using \<open>C \<in> \<N>\<close> by (simp add: poly\<M> polytope_imp_bounded that)
          have "polytope C"
            using \<open>C \<in> \<N>\<close> poly\<N> by auto
          have "\<not> (?z = x \<and> C = {?z})"
            using \<open>C \<in> \<N>\<close> aff_dim_sing [of ?z] \<open>\<not> n \<le> 1\<close> by (force simp: \<N>_def)
          then obtain y where y: "y \<in> rel_frontier C" and xzy: "x \<in> closed_segment ?z y"
            and sub: "open_segment ?z y \<subseteq> rel_interior C"
            by (blast intro: segment_to_rel_frontier [OF \<open>convex C\<close> \<open>bounded C\<close> z \<open>x \<in> C\<close>])
          then obtain F where "y \<in> F" "F face_of C" "F \<noteq> C"
            by (auto simp: rel_frontier_of_polyhedron_alt [OF polytope_imp_polyhedron [OF \<open>polytope C\<close>]])
          then obtain \<G> where "finite \<G>" "\<G> \<subseteq> \<U>" "F = \<Union>\<G>"
            by (metis (mono_tags, lifting) \<S>_def \<open>C \<in> \<M>\<close> \<open>convex C\<close> aff\<M> face\<M> face_of_aff_dim_lt fin\<U> le_less_trans mem_Collect_eq not_less)
          then obtain K where "y \<in> K" "K \<in> \<G>"
            using \<open>y \<in> F\<close> by blast
          moreover have x: "x \<in> convex hull {?z,y}"
            using segment_convex_hull xzy by auto
          moreover have "convex hull {?z,y} \<subseteq> convex hull insert ?z K"
            by (metis (full_types) \<open>y \<in> K\<close> hull_mono empty_subsetI insertCI insert_subset)
          moreover have "K \<in> \<U>"
            using \<open>K \<in> \<G>\<close> \<open>\<G> \<subseteq> \<U>\<close> by blast
          moreover have "K \<subseteq> rel_frontier C"
            using \<open>F = \<Union>\<G>\<close> \<open>F \<noteq> C\<close> \<open>F face_of C\<close> \<open>K \<in> \<G>\<close> face_of_subset_rel_frontier by fastforce
          ultimately show "x \<in> \<Union>?F"
            by force
        qed
        moreover
        have "convex hull insert (SOME z. z \<in> rel_interior C) K \<subseteq> C"
          if "K \<in> \<U>" "K \<subseteq> rel_frontier C" for K
        proof (rule hull_minimal)
          show "insert (SOME z. z \<in> rel_interior C) K \<subseteq> C"
            using that \<open>C \<in> \<N>\<close> in_rel_interior rel_interior_subset
            by (force simp: closure_eq rel_frontier_def closed\<N>)
          show "convex C"
            by (simp add: \<open>C \<in> \<N>\<close> convex\<N>)
        qed
        then have "\<Union>?F \<subseteq> C"
          by auto
        ultimately show ?thesis
          by blast
      qed
      have "(\<exists>C. C \<in> \<M> \<and> L \<subseteq> C) \<and> aff_dim L \<le> int n"  if "L \<in> \<U> \<union> ?\<T>" for L
        using that
      proof
        assume "L \<in> \<U>"
        then show ?thesis
          using C\<U> \<S>_def "*" by fastforce
      next
        assume "L \<in> ?\<T>"
        then obtain C K where "C \<in> \<N>"
          and L: "L = convex hull insert (SOME z. z \<in> rel_interior C) K"
          and K: "K \<in> \<U>" "K \<subseteq> rel_frontier C"
          by auto
        then have "convex hull C = C"
          by (meson convex\<N> convex_hull_eq)
        then have "convex C"
          by (metis (no_types) convex_convex_hull)
        have "rel_frontier C \<subseteq> C"
          by (metis DiffE closed\<N> \<open>C \<in> \<N>\<close> closure_closed rel_frontier_def subsetI)
        have "K \<subseteq> C"
          using K \<open>rel_frontier C \<subseteq> C\<close> by blast
        have "C \<in> \<M>"
          using \<N>_def \<open>C \<in> \<N>\<close> by auto
        moreover have "L \<subseteq> C"
          using K L \<open>C \<in> \<N>\<close>
          by (metis \<open>K \<subseteq> C\<close> \<open>convex hull C = C\<close> contra_subsetD hull_mono in_rel_interior insert_subset rel_interior_subset)
        ultimately show ?thesis
          using \<open>rel_frontier C \<subseteq> C\<close> \<open>L \<subseteq> C\<close> aff\<M> aff_dim_subset \<open>C \<in> \<M>\<close> dual_order.trans by blast
      qed
      then show "\<exists>C. C \<in> \<M> \<and> L \<subseteq> C" "aff_dim L \<le> int n" if "L \<in> \<U> \<union> ?\<T>" for L
        using that by auto
    qed
    then show ?thesis
      apply (rule ex_forward, safe)
        apply (meson Union_iff subsetCE, fastforce)
      by (meson infinite_super simplicial_complex_def)
  qed
qed


lemma simplicial_subdivision_of_cell_complex_lowdim:
  assumes "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
      and aff: "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C \<le> d"
  obtains \<T> where "simplicial_complex \<T>" "\<And>K. K \<in> \<T> \<Longrightarrow> aff_dim K \<le> d"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
proof (cases "d \<ge> 0")
  case True
  then obtain n where n: "d = of_nat n"
    using zero_le_imp_eq_int by blast
  have "\<exists>\<T>. simplicial_complex \<T> \<and>
            (\<forall>K\<in>\<T>. aff_dim K \<le> int n) \<and>
            \<Union>\<T> = \<Union>(\<Union>C\<in>\<M>. {F. F face_of C}) \<and>
            (\<forall>C\<in>\<Union>C\<in>\<M>. {F. F face_of C}.
                \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F) \<and>
            (\<forall>K\<in>\<T>. \<exists>C. C \<in> (\<Union>C\<in>\<M>. {F. F face_of C}) \<and> K \<subseteq> C)"
  proof (rule simplicial_subdivision_aux)
    show "finite (\<Union>C\<in>\<M>. {F. F face_of C})"
      using \<open>finite \<M>\<close> poly polyhedron_eq_finite_faces polytope_imp_polyhedron by fastforce
    show "polytope F" if "F \<in> (\<Union>C\<in>\<M>. {F. F face_of C})" for F
      using poly that face_of_polytope_polytope by blast
    show "aff_dim F \<le> int n" if "F \<in> (\<Union>C\<in>\<M>. {F. F face_of C})" for F
      using that
      by clarify (metis n aff_dim_subset aff face_of_imp_subset order_trans)
    show "F \<in> (\<Union>C\<in>\<M>. {F. F face_of C})"
      if "G \<in> (\<Union>C\<in>\<M>. {F. F face_of C})" and "F face_of G" for F G
      using that face_of_trans by blast
  next
    fix F1 F2
    assume "F1 \<in> (\<Union>C\<in>\<M>. {F. F face_of C})" and "F2 \<in> (\<Union>C\<in>\<M>. {F. F face_of C})"
    then obtain C1 C2 where "C1 \<in> \<M>" "C2 \<in> \<M>" and F: "F1 face_of C1" "F2 face_of C2"
      by auto
    show "F1 \<inter> F2 face_of F1"
      using face_of_Int_subface [OF _ _ F]
      by (metis \<open>C1 \<in> \<M>\<close> \<open>C2 \<in> \<M>\<close> face inf_commute)
  qed
  moreover
  have "\<Union>(\<Union>C\<in>\<M>. {F. F face_of C}) = \<Union>\<M>"
    using face_of_imp_subset face by blast
  ultimately show ?thesis
    using face_of_imp_subset n
    by (fastforce intro!: that simp add: poly face_of_refl polytope_imp_convex)
next
  case False
  then have m1: "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C = -1"
    by (metis aff aff_dim_empty_eq aff_dim_negative_iff dual_order.trans not_less)
  then have face\<M>: "\<And>F S. \<lbrakk>S \<in> \<M>; F face_of S\<rbrakk> \<Longrightarrow> F \<in> \<M>"
    by (metis aff_dim_empty face_of_empty)
  show ?thesis
  proof
    have "\<And>S. S \<in> \<M> \<Longrightarrow> \<exists>n. n simplex S"
      by (metis (no_types) m1 aff_dim_empty simplex_minus_1)
    then show "simplicial_complex \<M>"
      by (auto simp: simplicial_complex_def \<open>finite \<M>\<close> face intro: face\<M>)
    show "aff_dim K \<le> d" if "K \<in> \<M>" for K
      by (simp add: that aff)
    show "\<exists>F. finite F \<and> F \<subseteq> \<M> \<and> C = \<Union>F" if "C \<in> \<M>" for C
      using \<open>C \<in> \<M>\<close> equals0I by auto
    show "\<exists>C. C \<in> \<M> \<and> K \<subseteq> C" if "K \<in> \<M>" for K
      using \<open>K \<in> \<M>\<close> by blast
  qed auto
qed

proposition simplicial_subdivision_of_cell_complex:
  assumes "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "simplicial_complex \<T>"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
  by (blast intro: simplicial_subdivision_of_cell_complex_lowdim [OF assms aff_dim_le_DIM])

corollary fine_simplicial_subdivision_of_cell_complex:
  assumes "0 < e" "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "simplicial_complex \<T>"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> diameter K < e"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
proof -
  obtain \<N> where \<N>: "finite \<N>" "\<Union>\<N> = \<Union>\<M>" 
              and diapoly: "\<And>X. X \<in> \<N> \<Longrightarrow> diameter X < e" "\<And>X. X \<in> \<N> \<Longrightarrow> polytope X"
               and      "\<And>X Y. \<lbrakk>X \<in> \<N>; Y \<in> \<N>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
               and \<N>covers: "\<And>C x. C \<in> \<M> \<and> x \<in> C \<Longrightarrow> \<exists>D. D \<in> \<N> \<and> x \<in> D \<and> D \<subseteq> C"
               and \<N>covered: "\<And>C. C \<in> \<N> \<Longrightarrow> \<exists>D. D \<in> \<M> \<and> C \<subseteq> D"
    by (blast intro: cell_complex_subdivision_exists [OF \<open>0 < e\<close> \<open>finite \<M>\<close> poly aff_dim_le_DIM face])
  then obtain \<T> where \<T>: "simplicial_complex \<T>" "\<Union>\<T> = \<Union>\<N>"
                   and \<T>covers: "\<And>C. C \<in> \<N> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                   and \<T>covered: "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<N> \<and> K \<subseteq> C"
    using simplicial_subdivision_of_cell_complex [OF \<open>finite \<N>\<close>] by metis
  show ?thesis
  proof
    show "simplicial_complex \<T>"
      by (rule \<T>)
    show "diameter K < e" if "K \<in> \<T>" for K
      by (metis le_less_trans diapoly \<T>covered diameter_subset polytope_imp_bounded that)
    show "\<Union>\<T> = \<Union>\<M>"
      by (simp add: \<N>(2) \<open>\<Union>\<T> = \<Union>\<N>\<close>)
    show "\<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F" if "C \<in> \<M>" for C
    proof -
      { fix x
        assume "x \<in> C"
        then obtain D where "D \<in> \<T>" "x \<in> D" "D \<subseteq> C"
          using \<N>covers \<open>C \<in> \<M>\<close> \<T>covers by force
        then have "\<exists>X\<in>\<T> \<inter> Pow C. x \<in> X"
          using \<open>D \<in> \<T>\<close> \<open>D \<subseteq> C\<close> \<open>x \<in> D\<close> by blast
      }
      moreover
      have "finite (\<T> \<inter> Pow C)"
        using \<open>simplicial_complex \<T>\<close> simplicial_complex_def by auto
      ultimately show ?thesis
        by (rule_tac x="(\<T> \<inter> Pow C)" in exI) auto
    qed
    show "\<exists>C. C \<in> \<M> \<and> K \<subseteq> C" if "K \<in> \<T>" for K
      by (meson \<N>covered \<T>covered order_trans that)
  qed
qed

subsection\<open>Some results on cell division with full-dimensional cells only\<close>

lemma convex_Union_fulldim_cells:
  assumes "finite \<S>" and clo: "\<And>C. C \<in> \<S> \<Longrightarrow> closed C" and con: "\<And>C. C \<in> \<S> \<Longrightarrow> convex C"
      and eq: "\<Union>\<S> = U"and  "convex U"
 shows "\<Union>{C \<in> \<S>. aff_dim C = aff_dim U} = U"  (is "?lhs = U")
proof -
  have "closed U"
    using \<open>finite \<S>\<close> clo eq by blast
  have "?lhs \<subseteq> U"
    using eq by blast
  moreover have "U \<subseteq> ?lhs"
  proof (cases "\<forall>C \<in> \<S>. aff_dim C = aff_dim U")
    case True
    then show ?thesis
      using eq by blast
  next
    case False
    have "closed ?lhs"
      by (simp add: \<open>finite \<S>\<close> clo closed_Union)
    moreover have "U \<subseteq> closure ?lhs"
    proof -
      have "U \<subseteq> closure(\<Inter>{U - C |C. C \<in> \<S> \<and> aff_dim C < aff_dim U})"
      proof (rule Baire [OF \<open>closed U\<close>])
        show "countable {U - C |C. C \<in> \<S> \<and> aff_dim C < aff_dim U}"
          using \<open>finite \<S>\<close> uncountable_infinite by fastforce
        have "\<And>C. C \<in> \<S> \<Longrightarrow> openin (top_of_set U) (U-C)"
          by (metis Sup_upper clo closed_limpt closedin_limpt eq openin_diff openin_subtopology_self)
        then show "openin (top_of_set U) T \<and> U \<subseteq> closure T"
          if "T \<in> {U - C |C. C \<in> \<S> \<and> aff_dim C < aff_dim U}" for T
          using that dense_complement_convex_closed \<open>closed U\<close> \<open>convex U\<close> by auto
      qed
      also have "... \<subseteq> closure ?lhs"
      proof -
        obtain C where "C \<in> \<S>" "aff_dim C < aff_dim U"
          by (metis False Sup_upper aff_dim_subset eq eq_iff not_le)
        have "\<exists>X. X \<in> \<S> \<and> aff_dim X = aff_dim U \<and> x \<in> X"
          if "\<And>V. (\<exists>C. V = U - C \<and> C \<in> \<S> \<and> aff_dim C < aff_dim U) \<Longrightarrow> x \<in> V" for x
        proof -
          have "x \<in> U \<and> x \<in> \<Union>\<S>"
            using \<open>C \<in> \<S>\<close> \<open>aff_dim C < aff_dim U\<close> eq that by blast
          then show ?thesis
            by (metis Diff_iff Sup_upper Union_iff aff_dim_subset dual_order.order_iff_strict eq that)
        qed
        then show ?thesis
          by (auto intro!: closure_mono)
      qed
      finally show ?thesis .
    qed
    ultimately show ?thesis
      using closure_subset_eq by blast
  qed
  ultimately show ?thesis by blast
qed

proposition fine_triangular_subdivision_of_cell_complex:
  assumes "0 < e" "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and aff: "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C = d"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "triangulation \<T>" "\<And>k. k \<in> \<T> \<Longrightarrow> diameter k < e"
                 "\<And>k. k \<in> \<T> \<Longrightarrow> aff_dim k = d" "\<Union>\<T> = \<Union>\<M>"
                 "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>f. finite f \<and> f \<subseteq> \<T> \<and> C = \<Union>f"
                 "\<And>k. k \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> k \<subseteq> C"
proof -
  obtain \<T> where "simplicial_complex \<T>"
             and dia\<T>: "\<And>K. K \<in> \<T> \<Longrightarrow> diameter K < e"
             and "\<Union>\<T> = \<Union>\<M>"
             and in\<M>: "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
             and in\<T>: "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
    by (blast intro: fine_simplicial_subdivision_of_cell_complex [OF \<open>e > 0\<close> \<open>finite \<M>\<close> poly face])
  let ?\<T> = "{K \<in> \<T>. aff_dim K = d}"
  show thesis
  proof
    show "triangulation ?\<T>"
      using \<open>simplicial_complex \<T>\<close> by (auto simp: triangulation_def simplicial_complex_def)
    show "diameter L < e" if "L \<in> {K \<in> \<T>. aff_dim K = d}" for L
      using that by (auto simp: dia\<T>)
    show "aff_dim L = d" if "L \<in> {K \<in> \<T>. aff_dim K = d}" for L
      using that by auto
    show "\<exists>F. finite F \<and> F \<subseteq> {K \<in> \<T>. aff_dim K = d} \<and> C = \<Union>F" if "C \<in> \<M>" for C
    proof -
      obtain F where "finite F" "F \<subseteq> \<T>" "C = \<Union>F"
        using in\<M> [OF \<open>C \<in> \<M>\<close>] by auto
      show ?thesis
      proof (intro exI conjI)
        show "finite {K \<in> F. aff_dim K = d}"
          by (simp add: \<open>finite F\<close>)
        show "{K \<in> F. aff_dim K = d} \<subseteq> {K \<in> \<T>. aff_dim K = d}"
          using \<open>F \<subseteq> \<T>\<close> by blast
        have "d = aff_dim C"
          by (simp add: aff that)
        moreover have "\<And>K. K \<in> F \<Longrightarrow> closed K \<and> convex K"
          using \<open>simplicial_complex \<T>\<close> \<open>F \<subseteq> \<T>\<close>
          unfolding simplicial_complex_def by (metis subsetCE \<open>F \<subseteq> \<T>\<close> closed_simplex convex_simplex)
        moreover have "convex (\<Union>F)"
          using \<open>C = \<Union>F\<close> poly polytope_imp_convex that by blast
        ultimately show "C = \<Union>{K \<in> F. aff_dim K = d}"
          by (simp add: convex_Union_fulldim_cells \<open>C = \<Union>F\<close> \<open>finite F\<close>)
      qed
    qed
    then show "\<Union>{K \<in> \<T>. aff_dim K = d} = \<Union>\<M>"
      by auto (meson in\<T> subsetCE)
    show "\<exists>C. C \<in> \<M> \<and> L \<subseteq> C"
      if "L \<in> {K \<in> \<T>. aff_dim K = d}" for L
      using that by (auto simp: in\<T>)
  qed
qed

end
