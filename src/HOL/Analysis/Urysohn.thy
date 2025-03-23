(*  Title:      HOL/Analysis/Urysohn.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>The Urysohn lemma, its consequences and other advanced material about metric spaces\<close>

theory Urysohn
imports Abstract_Topological_Spaces Abstract_Metric_Spaces Infinite_Sum Arcwise_Connected
begin

subsection \<open>Urysohn lemma and Tietze's theorem\<close>

proposition Urysohn_lemma:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T" "a \<le> b" 
  obtains f where "continuous_map X (top_of_set {a..b}) f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
proof -
  obtain U where "openin X U" "S \<subseteq> U" "X closure_of U \<subseteq> topspace X - T"
    using assms unfolding normal_space_alt disjnt_def
    by (metis Diff_mono Un_Diff_Int closedin_def subset_eq sup_bot_right)
  have "\<exists>G :: real \<Rightarrow> 'a set. G 0 = U \<and> G 1 = topspace X - T \<and>
               (\<forall>x \<in> dyadics \<inter> {0..1}. \<forall>y \<in> dyadics \<inter> {0..1}. x < y \<longrightarrow> openin X (G x) \<and> openin X (G y) \<and> X closure_of (G x) \<subseteq> G y)"
  proof (rule recursion_on_dyadic_fractions)
    show "openin X U \<and> openin X (topspace X - T) \<and> X closure_of U \<subseteq> topspace X - T"
      using \<open>X closure_of U \<subseteq> topspace X - T\<close> \<open>openin X U\<close> \<open>closedin X T\<close> by blast
    show "\<exists>z. (openin X x \<and> openin X z \<and> X closure_of x \<subseteq> z) \<and> openin X z \<and> openin X y \<and> X closure_of z \<subseteq> y"
      if "openin X x \<and> openin X y \<and> X closure_of x \<subseteq> y" for x y
      by (meson that closedin_closure_of normal_space_alt \<open>normal_space X\<close>)
    show "openin X x \<and> openin X z \<and> X closure_of x \<subseteq> z"
      if "openin X x \<and> openin X y \<and> X closure_of x \<subseteq> y" and "openin X y \<and> openin X z \<and> X closure_of y \<subseteq> z" for x y z
      by (meson that closure_of_subset openin_subset subset_trans)
  qed
  then obtain G :: "real \<Rightarrow> 'a set"
      where G0: "G 0 = U" and G1: "G 1 = topspace X - T"
        and G: "\<And>x y. \<lbrakk>x \<in> dyadics; y \<in> dyadics; 0 \<le> x; x < y; y \<le> 1\<rbrakk>
                      \<Longrightarrow> openin X (G x) \<and> openin X (G y) \<and> X closure_of (G x) \<subseteq> G y"
    by (smt (verit, del_insts) Int_iff atLeastAtMost_iff)
  define f where "f \<equiv> \<lambda>x. Inf(insert 1 {r. r \<in> dyadics \<inter> {0..1} \<and> x \<in> G r})"
  have f_ge: "f x \<ge> 0" if "x \<in> topspace X" for x
    unfolding f_def by (force intro: cInf_greatest)
  moreover have f_le1: "f x \<le> 1" if "x \<in> topspace X" for x
  proof -
    have "bdd_below {r \<in> dyadics \<inter> {0..1}. x \<in> G r}"
      by (auto simp: bdd_below_def)
    then show ?thesis
       by (auto simp: f_def cInf_lower)
  qed
  ultimately have fim: "f \<in> topspace X \<rightarrow> {0..1}"
    by (auto simp: f_def)
  have 0: "0 \<in> dyadics \<inter> {0..1::real}" and 1: "1 \<in> dyadics \<inter> {0..1::real}"
    by (force simp: dyadics_def)+
  then have opeG: "openin X (G r)" if "r \<in> dyadics \<inter> {0..1}" for r
    using G G0 \<open>openin X U\<close> less_eq_real_def that by auto
  have "x \<in> G 0" if "x \<in> S" for x
    using G0 \<open>S \<subseteq> U\<close> that by blast
  with 0 have fimS: "f ` S \<subseteq> {0}"
    unfolding f_def by (force intro!: cInf_eq_minimum)
  have False if "r \<in> dyadics" "0 \<le> r" "r < 1" "x \<in> G r" "x \<in> T" for r x
    using G [of r 1] 1
    by (smt (verit, best) DiffD2 G1 Int_iff closure_of_subset inf.orderE openin_subset that)
  then have "r\<ge>1" if "r \<in> dyadics" "0 \<le> r" "r \<le> 1" "x \<in> G r" "x \<in> T" for r x
    using linorder_not_le that by blast
  then have fimT: "f ` T \<subseteq> {1}"
    unfolding f_def by (force intro!: cInf_eq_minimum)
  have fle1: "f z \<le> 1" for z
    by (force simp: f_def intro: cInf_lower)
  have fle: "f z \<le> x" if "x \<in> dyadics \<inter> {0..1}" "z \<in> G x" for z x
    using that by (force simp: f_def intro: cInf_lower)
  have *: "b \<le> f z" if "b \<le> 1" "\<And>x. \<lbrakk>x \<in> dyadics \<inter> {0..1}; z \<in> G x\<rbrakk> \<Longrightarrow> b \<le> x" for z b
    using that by (force simp: f_def intro: cInf_greatest)
  have **: "r \<le> f x" if r: "r \<in> dyadics \<inter> {0..1}" "x \<notin> G r" for r x
  proof (rule *)
    show "r \<le> s" if "s \<in> dyadics \<inter> {0..1}" and "x \<in> G s" for s :: real
      using that r G [of s r] by (force simp: dest: closure_of_subset openin_subset)
  qed (use that in force)

  have "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y \<in> U. \<bar>f y - f x\<bar> < \<epsilon>)"
    if "x \<in> topspace X" and "0 < \<epsilon>" for x \<epsilon>
  proof -
    have A: "\<exists>r. r \<in> dyadics \<inter> {0..1} \<and> r < y \<and> \<bar>r - y\<bar> < d" if "0 < y" "y \<le> 1" "0 < d" for y d::real
    proof -
      obtain n q r 
        where "of_nat q / 2^n < y" "y < of_nat r / 2^n" "\<bar>q / 2^n - r / 2^n \<bar> < d"
        by (smt (verit, del_insts) padic_rational_approximation_straddle_pos  \<open>0 < d\<close> \<open>0 < y\<close>) 
      then show ?thesis
        unfolding dyadics_def
        using divide_eq_0_iff that(2) by fastforce
    qed
    have B: "\<exists>r. r \<in> dyadics \<inter> {0..1} \<and> y < r \<and> \<bar>r - y\<bar> < d" if "0 \<le> y" "y < 1" "0 < d" for y d::real
    proof -
      obtain n q r 
        where "of_nat q / 2^n \<le> y" "y < of_nat r / 2^n" "\<bar>q / 2^n - r / 2^n \<bar> < d"
        using padic_rational_approximation_straddle_pos_le
        by (smt (verit, del_insts) \<open>0 < d\<close> \<open>0 \<le> y\<close>) 
      then show ?thesis
        apply (clarsimp simp: dyadics_def)
        using divide_eq_0_iff \<open>y < 1\<close>
        by (smt (verit) divide_nonneg_nonneg divide_self of_nat_0_le_iff of_nat_1 power_0 zero_le_power) 
    qed
    show ?thesis
    proof (cases "f x = 0")
      case True
      with B[of 0] obtain r where r: "r \<in> dyadics \<inter> {0..1}" "0 < r" "\<bar>r\<bar> < \<epsilon>/2"
        by (smt (verit) \<open>0 < \<epsilon>\<close> half_gt_zero)
      show ?thesis
      proof (intro exI conjI)
        show "openin X (G r)"
          using opeG r(1) by blast
        show "x \<in> G r"
          using True ** r by force
        show "\<forall>y \<in> G r. \<bar>f y - f x\<bar> < \<epsilon>"
          using f_ge \<open>openin X (G r)\<close> fle openin_subset r by (fastforce simp: True)
      qed
    next
      case False
      show ?thesis 
      proof (cases "f x = 1")
        case True
        with A[of 1] obtain r where r: "r \<in> dyadics \<inter> {0..1}" "r < 1" "\<bar>r-1\<bar> < \<epsilon>/2"
          by (smt (verit) \<open>0 < \<epsilon>\<close> half_gt_zero)
        define G' where "G' \<equiv> topspace X - X closure_of G r"
        show ?thesis
        proof (intro exI conjI)
          show "openin X G'"
            unfolding G'_def by fastforce
          obtain r' where "r' \<in> dyadics \<and> 0 \<le> r' \<and> r' \<le> 1 \<and> r < r' \<and> \<bar>r' - r\<bar> < 1 - r"
            using B r by force 
          moreover
          have "1 - r \<in> dyadics" "0 \<le> r"
            using 1 r dyadics_diff by force+
          ultimately have "x \<notin> X closure_of G r"
            using G True r fle by force
          then show "x \<in> G'"
            by (simp add: G'_def that)
          show "\<forall>y \<in> G'. \<bar>f y - f x\<bar> < \<epsilon>"
            using ** f_le1 in_closure_of r by (fastforce simp: True G'_def)
        qed
      next
        case False
        have "0 < f x" "f x < 1"
          using fle1 f_ge that(1) \<open>f x \<noteq> 0\<close> \<open>f x \<noteq> 1\<close> by (metis order_le_less) +
        obtain r where r: "r \<in> dyadics \<inter> {0..1}" "r < f x" "\<bar>r - f x\<bar> < \<epsilon> / 2"
          using A \<open>0 < \<epsilon>\<close> \<open>0 < f x\<close> \<open>f x < 1\<close> by (smt (verit, best) half_gt_zero)
        obtain r' where r': "r' \<in> dyadics \<inter> {0..1}" "f x < r'" "\<bar>r' - f x\<bar> < \<epsilon> / 2"
          using B \<open>0 < \<epsilon>\<close> \<open>0 < f x\<close> \<open>f x < 1\<close> by (smt (verit, best) half_gt_zero)
        have "r < 1"
          using \<open>f x < 1\<close> r(2) by force
        show ?thesis
        proof (intro conjI exI)
          show "openin X (G r' - X closure_of G r)"
            using closedin_closure_of opeG r' by blast
          have "x \<in> X closure_of G r \<Longrightarrow> False"
            using B [of r "f x - r"] r \<open>r < 1\<close> G [of r] fle by force
          then show "x \<in> G r' - X closure_of G r"
            using ** r' by fastforce
          show "\<forall>y\<in>G r' - X closure_of G r. \<bar>f y - f x\<bar> < \<epsilon>"
            using r r' ** G closure_of_subset field_sum_of_halves fle openin_subset subset_eq
            by (smt (verit) DiffE opeG)
        qed
      qed
    qed
  qed
  then have contf: "continuous_map X (top_of_set {0..1}) f"
    by (auto simp: Met_TC.continuous_map_to_metric dist_real_def continuous_map_in_subtopology fim abs_minus_commute simp flip: mtopology_is_euclidean)
  define g where "g \<equiv> \<lambda>x. a + (b - a) * f x"
  show thesis
  proof
    have "continuous_map X euclideanreal g"
      using contf \<open>a \<le> b\<close> unfolding g_def by (auto simp: continuous_intros continuous_map_in_subtopology)
    moreover have "g \<in> (topspace X) \<rightarrow> {a..b}"
      using mult_left_le [of "f _" "b-a"] contf \<open>a \<le> b\<close> 
      by (simp add: g_def Pi_iff add.commute continuous_map_in_subtopology image_subset_iff le_diff_eq)
    ultimately show "continuous_map X (top_of_set {a..b}) g"
      using continuous_map_in_subtopology by blast
    show "g ` S \<subseteq> {a}" "g ` T \<subseteq> {b}"
      using fimS fimT by (auto simp: g_def)
  qed
qed

lemma Urysohn_lemma_alt:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X euclideanreal f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
  by (metis Urysohn_lemma assms continuous_map_in_subtopology disjnt_sym linear)

lemma normal_space_iff_Urysohn_gen_alt:
  assumes "a \<noteq> b"
  shows "normal_space X \<longleftrightarrow>
         (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
                \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
 (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" 
    by (metis Urysohn_lemma_alt)
next
  assume R: ?rhs 
  show ?lhs
    unfolding normal_space_def
  proof clarify
    fix S T
    assume "closedin X S" and "closedin X T" and "disjnt S T"
    with R obtain f where contf: "continuous_map X euclideanreal f" and "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
      by meson
    show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
    proof (intro conjI exI)
      show "openin X {x \<in> topspace X. f x \<in> ball a (\<bar>a - b\<bar> / 2)}"
        by (force intro!: openin_continuous_map_preimage [OF contf])
      show "openin X {x \<in> topspace X. f x \<in> ball b (\<bar>a - b\<bar> / 2)}"
        by (force intro!: openin_continuous_map_preimage [OF contf])
      show "S \<subseteq> {x \<in> topspace X. f x \<in> ball a (\<bar>a - b\<bar> / 2)}"
        using \<open>closedin X S\<close> closedin_subset \<open>f ` S \<subseteq> {a}\<close> assms by force
      show "T \<subseteq> {x \<in> topspace X. f x \<in> ball b (\<bar>a - b\<bar> / 2)}"
        using \<open>closedin X T\<close> closedin_subset \<open>f ` T \<subseteq> {b}\<close> assms by force
      have "\<And>x. \<lbrakk>x \<in> topspace X; dist a (f x) < \<bar>a-b\<bar>/2; dist b (f x) < \<bar>a-b\<bar>/2\<rbrakk> \<Longrightarrow> False"
        by (smt (verit, best) dist_real_def dist_triangle_half_l)
      then show "disjnt {x \<in> topspace X. f x \<in> ball a (\<bar>a-b\<bar> / 2)} {x \<in> topspace X. f x \<in> ball b (\<bar>a-b\<bar> / 2)}"
        using disjnt_iff by fastforce
    qed
  qed
qed 

lemma normal_space_iff_Urysohn_gen:
  fixes a b::real
  shows
   "a < b \<Longrightarrow> 
      normal_space X \<longleftrightarrow>
        (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and>
                        f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
  by (metis linear not_le Urysohn_lemma normal_space_iff_Urysohn_gen_alt continuous_map_in_subtopology)

lemma normal_space_iff_Urysohn_alt:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and>
                   f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
  by (rule normal_space_iff_Urysohn_gen_alt) auto

lemma normal_space_iff_Urysohn:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
            \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and> 
                               f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
  by (rule normal_space_iff_Urysohn_gen) auto

lemma normal_space_perfect_map_image:
   "\<lbrakk>normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> normal_space Y"
  unfolding perfect_map_def proper_map_def
  using normal_space_continuous_closed_map_image by fastforce

lemma Hausdorff_normal_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; closed_map X Y f; continuous_map X Y f;
     f ` topspace X = topspace Y; t1_space Y\<rbrakk>
    \<Longrightarrow> Hausdorff_space Y"
  by (metis normal_space_continuous_closed_map_image normal_t1_imp_Hausdorff_space)

lemma normal_Hausdorff_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; Hausdorff_space X; closed_map X Y f;
     continuous_map X Y f; f ` topspace X = topspace Y\<rbrakk>
    \<Longrightarrow> normal_space Y \<and> Hausdorff_space Y"
  by (meson normal_space_continuous_closed_map_image normal_t1_eq_Hausdorff_space t1_space_closed_map_image)

lemma Lindelof_cover:
  assumes "regular_space X" and "Lindelof_space X" and "S \<noteq> {}" 
    and clo: "closedin X S" "closedin X T" "disjnt S T"
  obtains h :: "nat \<Rightarrow> 'a set" where 
    "\<And>n. openin X (h n)" "\<And>n. disjnt T (X closure_of (h n))" and  "S \<subseteq> \<Union>(range h)"
proof -
  have "\<exists>U. openin X U \<and> x \<in> U \<and> disjnt T (X closure_of U)"
    if "x \<in> S" for x
    using \<open>regular_space X\<close> unfolding regular_space 
    by (metis (full_types) Diff_iff \<open>disjnt S T\<close> clo closure_of_eq disjnt_iff in_closure_of that)
  then obtain h where oh: "\<And>x. x \<in> S \<Longrightarrow> openin X (h x)"
    and xh: "\<And>x. x \<in> S \<Longrightarrow> x \<in> h x"
    and dh: "\<And>x. x \<in> S \<Longrightarrow> disjnt T (X closure_of h x)"
    by metis
  have "Lindelof_space(subtopology X S)"
    by (simp add: Lindelof_space_closedin_subtopology \<open>Lindelof_space X\<close> \<open>closedin X S\<close>)
  then obtain \<U> where \<U>: "countable \<U> \<and> \<U> \<subseteq> h ` S \<and> S \<subseteq> \<Union>\<U>"
    unfolding Lindelof_space_subtopology_subset [OF closedin_subset [OF \<open>closedin X S\<close>]]
    by (smt (verit, del_insts) oh xh UN_I image_iff subsetI)
  with \<open>S \<noteq> {}\<close> have "\<U> \<noteq> {}"
    by blast
  show ?thesis
  proof
    show "openin X (from_nat_into \<U> n)" for n
      by (metis \<U> from_nat_into image_iff \<open>\<U> \<noteq> {}\<close> oh subsetD)
    show "disjnt T (X closure_of (from_nat_into \<U>) n)" for n
      using dh from_nat_into [OF \<open>\<U> \<noteq> {}\<close>]
      by (metis \<U> f_inv_into_f inv_into_into subset_eq)
    show "S \<subseteq> \<Union>(range (from_nat_into \<U>))"
      by (simp add: \<U> \<open>\<U> \<noteq> {}\<close>)
  qed
qed

lemma regular_Lindelof_imp_normal_space:
  assumes "regular_space X" and "Lindelof_space X"
  shows "normal_space X"
  unfolding normal_space_def
proof clarify
  fix S T
  assume clo: "closedin X S" "closedin X T" and "disjnt S T"
  show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof (cases "S={} \<or> T={}")
    case True
    with clo show ?thesis
      by (meson closedin_def disjnt_empty1 disjnt_empty2 openin_empty openin_topspace subset_empty)
  next
    case False
    obtain h :: "nat \<Rightarrow> 'a set" where 
      opeh: "\<And>n. openin X (h n)" and dish: "\<And>n. disjnt T (X closure_of (h n))"
      and Sh: "S \<subseteq> \<Union>(range h)"
      by (metis Lindelof_cover False \<open>disjnt S T\<close> assms clo)
    obtain k :: "nat \<Rightarrow> 'a set" where 
      opek: "\<And>n. openin X (k n)" and disk: "\<And>n. disjnt S (X closure_of (k n))"
      and Tk: "T \<subseteq> \<Union>(range k)"
      by (metis Lindelof_cover False \<open>disjnt S T\<close> assms clo disjnt_sym)
    define U where "U \<equiv> \<Union>i. h i - (\<Union>j<i. X closure_of k j)"
    define V where "V \<equiv> \<Union>i. k i - (\<Union>j\<le>i. X closure_of h j)"
    show ?thesis
    proof (intro exI conjI)
      show "openin X U" "openin X V"
        unfolding U_def V_def
        by (force intro!: opek opeh closedin_Union closedin_closure_of)+
      show "S \<subseteq> U" "T \<subseteq> V"
        using Sh Tk dish disk by (fastforce simp: U_def V_def disjnt_iff)+
      have "\<And>x i j. \<lbrakk>x \<in> k i; x \<in> h j; \<forall>j\<le>i. x \<notin> X closure_of h j\<rbrakk>
                 \<Longrightarrow> \<exists>i<j. x \<in> X closure_of k i"
        by (metis in_closure_of linorder_not_less opek openin_subset subsetD)
      then show "disjnt U V"
        by (force simp: U_def V_def disjnt_iff)
    qed
  qed
qed

theorem Tietze_extension_closed_real_interval:
  assumes "normal_space X" and "closedin X S"
    and contf: "continuous_map (subtopology X S) euclideanreal f"
    and fim: "f ` S \<subseteq> {a..b}" and "a \<le> b"
  obtains g 
  where "continuous_map X euclideanreal g" 
        "\<And>x. x \<in> S \<Longrightarrow> g x = f x" "g ` topspace X \<subseteq> {a..b}"
proof -
  define c where "c \<equiv> max \<bar>a\<bar> \<bar>b\<bar> + 1"
  have "0 < c" and c: "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<le> c"
    using fim by (auto simp: c_def image_subset_iff)
  define good where 
    "good \<equiv> \<lambda>g n. continuous_map X euclideanreal g \<and> (\<forall>x \<in> S. \<bar>f x - g x\<bar> \<le> c * (2/3)^n)"
  have step: "\<exists>g. good g (Suc n) \<and>
              (\<forall>x \<in> topspace X. \<bar>g x - h x\<bar> \<le> c * (2/3)^n / 3)"
    if h: "good h n" for n h
  proof -
    have pos: "0 < c * (2/3) ^ n"
      by (simp add: \<open>0 < c\<close>)
    have S_eq: "S = topspace(subtopology X S)" and "S \<subseteq> topspace X"
      using \<open>closedin X S\<close> closedin_subset by auto
    define d where "d \<equiv> c/3 * (2/3) ^ n"
    define SA where "SA \<equiv> {x \<in> S. f x - h x \<in> {..-d}}"
    define SB where "SB \<equiv> {x \<in> S. f x - h x \<in> {d..}}"
    have contfh: "continuous_map (subtopology X S) euclideanreal (\<lambda>x. f x - h x)"
      using that
      by (simp add: contf good_def continuous_map_diff continuous_map_from_subtopology)
    then have "closedin (subtopology X S) SA"
      unfolding SA_def
      by (smt (verit, del_insts) closed_closedin continuous_map_closedin Collect_cong S_eq closed_real_atMost)
    then have "closedin X SA"
      using \<open>closedin X S\<close> closedin_trans_full by blast
    moreover have  "closedin (subtopology X S) SB"      
      unfolding SB_def
      using closedin_continuous_map_preimage_gen [OF contfh]
      by (metis (full_types) S_eq closed_atLeast closed_closedin closedin_topspace)
    then have "closedin X SB"
      using \<open>closedin X S\<close> closedin_trans_full by blast
    moreover have "disjnt SA SB"
      using pos by (auto simp: d_def disjnt_def SA_def SB_def)
    moreover have "-d \<le> d"
      using pos by (auto simp: d_def)
    ultimately
    obtain g where contg: "continuous_map X (top_of_set {- d..d}) g"
      and ga: "g ` SA \<subseteq> {- d}" and gb: "g ` SB \<subseteq> {d}"
      using Urysohn_lemma \<open>normal_space X\<close> by metis
    then have g_le_d: "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>g x\<bar> \<le> d"
      by (fastforce simp: abs_le_iff continuous_map_def minus_le_iff)
    have g_eq_d: "\<And>x. \<lbrakk>x \<in> S; f x - h x \<le> -d\<rbrakk> \<Longrightarrow> g x = -d"
      using ga by (auto simp: SA_def)
    have g_eq_negd: "\<And>x. \<lbrakk>x \<in> S; f x - h x \<ge> d\<rbrakk> \<Longrightarrow> g x = d"
      using gb by (auto simp: SB_def)
    show ?thesis
      unfolding good_def
    proof (intro conjI strip exI)
      show "continuous_map X euclideanreal (\<lambda>x. h x + g x)"
        using contg continuous_map_add continuous_map_in_subtopology that
        unfolding good_def by blast
      show "\<bar>f x - (h x + g x)\<bar> \<le> c * (2 / 3) ^ Suc n" if "x \<in> S" for x
      proof -
        have x: "x \<in> topspace X"
          using \<open>S \<subseteq> topspace X\<close> that by auto
        have "\<bar>f x - h x\<bar> \<le> c * (2/3) ^ n"
          using good_def h that by blast
        with g_eq_d [OF that] g_eq_negd [OF that] g_le_d [OF x] 
        have "\<bar>f x - (h x + g x)\<bar> \<le> d + d"
          unfolding d_def by linarith
        then show ?thesis 
          by (simp add: d_def)
      qed
      show "\<bar>h x + g x - h x\<bar> \<le> c * (2 / 3) ^ n / 3" if "x \<in> topspace X" for x
        using that d_def g_le_d by auto
    qed
  qed
  then obtain nxtg where nxtg: "\<And>h n. good h n \<Longrightarrow> 
          good (nxtg h n) (Suc n) \<and> (\<forall>x \<in> topspace X. \<bar>nxtg h n x - h x\<bar> \<le> c * (2/3)^n / 3)"
    by metis
  define g where "g \<equiv> rec_nat (\<lambda>x. 0) (\<lambda>n r. nxtg r n)"
  have [simp]: "g 0 x = 0" for x
    by (auto simp: g_def)
  have g_Suc: "g(Suc n) = nxtg (g n) n" for n
    by (auto simp: g_def)
  have good: "good (g n) n" for n
  proof (induction n)
    case 0
    with c show ?case
      by (auto simp: good_def)
  qed (simp add: g_Suc nxtg)
  have *: "\<And>n x. x \<in> topspace X \<Longrightarrow> \<bar>g(Suc n) x - g n x\<bar> \<le> c * (2/3) ^ n / 3"
    using nxtg g_Suc good by force
  obtain h where conth:  "continuous_map X euclideanreal h"
    and h: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. dist (g n x) (h x) < \<epsilon>"
  proof (rule Met_TC.continuous_map_uniformly_Cauchy_limit)
    show "\<forall>\<^sub>F n in sequentially. continuous_map X (Met_TC.mtopology) (g n)"
      using good good_def by fastforce
    show "\<exists>N. \<forall>m n x. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> x \<in> topspace X \<longrightarrow> dist (g m x) (g n x) < \<epsilon>"
      if "\<epsilon> > 0" for \<epsilon> 
    proof -
      have "\<forall>\<^sub>F n in sequentially. \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
      proof (rule Archimedean_eventually_pow_inverse)
        show "0 < \<epsilon> / c"
          by (simp add: \<open>0 < c\<close> that)
      qed auto
      then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
        by (meson eventually_sequentially order_le_less_trans)
      have "\<bar>g m x - g n x\<bar> < \<epsilon>"
        if "N \<le> m" "N \<le> n" and x: "x \<in> topspace X" "m \<le> n" for m n x
      proof (cases "m < n")
        case True
        have 23: "(\<Sum>k = m..<n. (2/3)^k) = 3 * ((2/3) ^ m - (2/3::real) ^ n)"
          using \<open>m \<le> n\<close>
          by (induction n) (auto simp: le_Suc_eq)
        have "\<bar>g m x - g n x\<bar> \<le> \<bar>\<Sum>k = m..<n. g (Suc k) x - g k x\<bar>"
          by (subst sum_Suc_diff' [OF \<open>m \<le> n\<close>]) linarith
        also have "\<dots> \<le> (\<Sum>k = m..<n. \<bar>g (Suc k) x - g k x\<bar>)"
          by (rule sum_abs)
        also have "\<dots> \<le> (\<Sum>k = m..<n. c * (2/3)^k / 3)"
          by (meson "*" sum_mono x(1))
        also have "\<dots> = (c/3) * (\<Sum>k = m..<n. (2/3)^k)"
          by (simp add: sum_distrib_left)
        also have "\<dots> = (c/3) * 3 * ((2/3) ^ m - (2/3) ^ n)"
          by (simp add: sum_distrib_left 23)
        also have "... < (c/3) * 3 * ((2/3) ^ m)"
          using \<open>0 < c\<close> by auto
        also have "\<dots> < \<epsilon>"
          using N [OF \<open>N \<le> m\<close>] \<open>0 < c\<close> by (simp add: field_simps)
        finally show ?thesis .
      qed (use \<open>0 < \<epsilon>\<close> \<open>m \<le> n\<close> in auto)
      then show ?thesis
        by (metis dist_commute_lessI dist_real_def nle_le)
    qed
  qed auto
  define \<phi> where "\<phi> \<equiv> \<lambda>x. max a (min (h x) b)"
  show thesis
  proof
    show "continuous_map X euclidean \<phi>"
      unfolding \<phi>_def using conth by (intro continuous_intros) auto
    show "\<phi> x = f x" if "x \<in> S" for x 
    proof -
      have x: "x \<in> topspace X"
        using \<open>closedin X S\<close> closedin_subset that by blast
      have "h x = f x"
      proof (rule Met_TC.limitin_metric_unique)
        show "limitin Met_TC.mtopology (\<lambda>n. g n x) (h x) sequentially"
          using h x by (force simp: tendsto_iff eventually_sequentially)
        show "limitin Met_TC.mtopology (\<lambda>n. g n x) (f x) sequentially"
        proof (clarsimp simp: tendsto_iff)
          fix \<epsilon>::real
          assume "\<epsilon> > 0"
          then have "\<forall>\<^sub>F n in sequentially. \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
            by (intro Archimedean_eventually_pow_inverse) (auto simp: \<open>c > 0\<close>)
          then show "\<forall>\<^sub>F n in sequentially. dist (g n x) (f x) < \<epsilon>"
            apply eventually_elim
            by (smt (verit) good x good_def \<open>c > 0\<close> dist_real_def mult.commute pos_less_divide_eq that)
        qed
      qed auto
      then show ?thesis
        using that fim by (auto simp: \<phi>_def)
    qed
    then show "\<phi> ` topspace X \<subseteq> {a..b}"
      using fim \<open>a \<le> b\<close> by (auto simp: \<phi>_def)
  qed
qed


theorem Tietze_extension_realinterval:
  assumes XS: "normal_space X" "closedin X S" and T: "is_interval T" "T \<noteq> {}" 
    and contf: "continuous_map (subtopology X S) euclideanreal f" 
    and "f ` S \<subseteq> T"
  obtains g where "continuous_map X euclideanreal g"  "g ` topspace X \<subseteq> T"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  define \<Phi> where 
        "\<Phi> \<equiv> \<lambda>T::real set. \<forall>f. continuous_map (subtopology X S) euclidean f \<longrightarrow> f`S \<subseteq> T
               \<longrightarrow> (\<exists>g. continuous_map X euclidean g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x \<in> S. g x = f x))"
  have "\<Phi> T"
    if *: "\<And>T. \<lbrakk>bounded T; is_interval T; T \<noteq> {}\<rbrakk> \<Longrightarrow> \<Phi> T"
      and "is_interval T" "T \<noteq> {}" for T
    unfolding \<Phi>_def
  proof (intro strip)
    fix f
    assume contf: "continuous_map (subtopology X S) euclideanreal f"
      and "f ` S \<subseteq> T"
    have \<Phi>T: "\<Phi> ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
    proof (rule *)
      show "bounded ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
        using shrink_range [of T] by (force intro: boundedI [where B=1])
      show "is_interval ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
        using connected_shrink that(2) is_interval_connected_1 by blast
      show "(\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T \<noteq> {}"
        using \<open>T \<noteq> {}\<close> by auto
    qed
    moreover have "continuous_map (subtopology X S) euclidean ((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f)"
      by (metis contf continuous_map_compose continuous_map_into_fulltopology continuous_map_real_shrink)
    moreover have "((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f) ` S \<subseteq> (\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T"
      using \<open>f ` S \<subseteq> T\<close> by auto
    ultimately obtain g 
       where contg: "continuous_map X euclidean g" 
         and gim: "g ` topspace X \<subseteq> (\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T"
         and geq: "\<And>x. x \<in> S \<Longrightarrow> g x = ((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f) x"
      using \<Phi>T unfolding \<Phi>_def by force
    show "\<exists>g. continuous_map X euclideanreal g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x\<in>S. g x = f x)"
    proof (intro conjI exI)
      have "continuous_map X (top_of_set {-1<..<1}) g"
        using contg continuous_map_in_subtopology gim shrink_range by blast
      then show "continuous_map X euclideanreal ((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g)"
        by (rule continuous_map_compose) (auto simp: continuous_on_real_grow)
      show "((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g) ` topspace X \<subseteq> T"
        using gim real_grow_shrink by fastforce
      show "\<forall>x\<in>S. ((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g) x = f x"
        using geq real_grow_shrink by force
    qed
  qed
  moreover have "\<Phi> T"
    if "bounded T" "is_interval T" "T \<noteq> {}" for T
    unfolding \<Phi>_def
  proof (intro strip)
    fix f
    assume contf: "continuous_map (subtopology X S) euclideanreal f"
      and "f ` S \<subseteq> T"
    obtain a b where ab: "closure T = {a..b}"
      by (meson \<open>bounded T\<close> \<open>is_interval T\<close> compact_closure connected_compact_interval_1 
            connected_imp_connected_closure is_interval_connected)
    with \<open>T \<noteq> {}\<close> have "a \<le> b" by auto
    have "f ` S \<subseteq> {a..b}"
      using \<open>f ` S \<subseteq> T\<close> ab closure_subset by auto
    then obtain g where contg: "continuous_map X euclideanreal g"
      and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x" and gim: "g ` topspace X \<subseteq> {a..b}"
      using Tietze_extension_closed_real_interval [OF XS contf _ \<open>a \<le> b\<close>] by metis
    define W where "W \<equiv> {x \<in> topspace X. g x \<in> closure T - T}"
    have "{a..b} - {a, b} \<subseteq> T"
      using that
      by (metis ab atLeastAtMost_diff_ends convex_interior_closure interior_atLeastAtMost_real 
          interior_subset is_interval_convex)
    with finite_imp_compact have "compact (closure T - T)"
      by (metis Diff_eq_empty_iff Diff_insert2 ab finite.emptyI finite_Diff_insert)
    then have "closedin X W"
      unfolding W_def using closedin_continuous_map_preimage [OF contg] compact_imp_closed by force
    moreover have "disjnt W S"
      unfolding W_def disjnt_iff using \<open>f ` S \<subseteq> T\<close> gf by blast
    ultimately obtain h :: "'a \<Rightarrow> real" 
      where conth: "continuous_map X (top_of_set {0..1}) h" 
            and him: "h ` W \<subseteq> {0}" "h ` S \<subseteq> {1}"
      by (metis XS normal_space_iff_Urysohn) 
    then have him01: "h \<in> topspace X \<rightarrow> {0..1}"
      by (metis continuous_map_in_subtopology)
    obtain z where "z \<in> T"
      using \<open>T \<noteq> {}\<close> by blast
    define g' where "g' \<equiv> \<lambda>x. z + h x * (g x - z)"
    show "\<exists>g. continuous_map X euclidean g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x\<in>S. g x = f x)"
    proof (intro exI conjI)
      show "continuous_map X euclideanreal g'"
        unfolding g'_def using contg conth continuous_map_in_subtopology
        by (intro continuous_intros) auto
      show "g' ` topspace X \<subseteq> T"
        unfolding g'_def 
      proof clarify
        fix x
        assume "x \<in> topspace X"
        show "z + h x * (g x - z) \<in> T"
        proof (cases "g x \<in> T")
          case True
          define w where "w \<equiv> z + h x * (g x - z)"
          have "\<bar>h x\<bar> * \<bar>g x - z\<bar> \<le> \<bar>g x - z\<bar>" "\<bar>1 - h x\<bar> * \<bar>g x - z\<bar> \<le> \<bar>g x - z\<bar>"
            using him01 \<open>x \<in> topspace X\<close> by (force simp: intro: mult_left_le_one_le)+
          then consider "z \<le> w \<and> w \<le> g x" | "g x \<le> w \<and> w \<le> z"
            unfolding w_def by (smt (verit) left_diff_distrib mult_cancel_right2 mult_minus_right zero_less_mult_iff)
          then show ?thesis
            using \<open>is_interval T\<close> unfolding w_def is_interval_1 by (metis True \<open>z \<in> T\<close>)
        next
          case False
          then have "g x \<in> closure T"
            using \<open>x \<in> topspace X\<close> ab gim by blast
          then have "h x = 0"
            using him False \<open>x \<in> topspace X\<close> by (auto simp: W_def image_subset_iff)
          then show ?thesis
            by (simp add: \<open>z \<in> T\<close>)
        qed
      qed
      show "\<forall>x\<in>S. g' x = f x"
        using gf him by (auto simp: W_def g'_def)
    qed 
  qed
  ultimately show thesis
    using assms that unfolding \<Phi>_def by best
qed

lemma normal_space_iff_Tietze:
   "normal_space X \<longleftrightarrow>
    (\<forall>f S. closedin X S \<and>
           continuous_map (subtopology X S) euclidean f
           \<longrightarrow> (\<exists>g:: 'a \<Rightarrow> real. continuous_map X euclidean g \<and> (\<forall>x \<in> S. g x = f x)))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs 
  then show ?rhs
    by (metis Tietze_extension_realinterval empty_not_UNIV is_interval_univ subset_UNIV)
next
  assume R: ?rhs 
  show ?lhs
    unfolding normal_space_iff_Urysohn_alt
  proof clarify
    fix S T
    assume "closedin X S"
      and "closedin X T"
      and "disjnt S T"
    then have cloST: "closedin X (S \<union> T)"
      by (simp add: closedin_Un)
    moreover 
    have "continuous_map (subtopology X (S \<union> T)) euclideanreal (\<lambda>x. if x \<in> S then 0 else 1)"
      unfolding continuous_map_closedin
    proof (intro conjI strip)
      fix C :: "real set"
      define D where "D \<equiv> {x \<in> topspace X. if x \<in> S then 0 \<in> C else x \<in> T \<and> 1 \<in> C}"
      have "D \<in> {{}, S, T, S \<union> T}"
        unfolding D_def
        using closedin_subset [OF \<open>closedin X S\<close>] closedin_subset [OF \<open>closedin X T\<close>] \<open>disjnt S T\<close>
        by (auto simp: disjnt_iff)
      then have "closedin X D"
        using \<open>closedin X S\<close> \<open>closedin X T\<close> closedin_empty by blast
      with closedin_subset_topspace
      show "closedin (subtopology X (S \<union> T)) {x \<in> topspace (subtopology X (S \<union> T)). (if x \<in> S then 0::real else 1) \<in> C}"
        apply (simp add: D_def)
        by (smt (verit, best) Collect_cong Collect_mono_iff Un_def closedin_subset_topspace)
    qed auto
    ultimately obtain g :: "'a \<Rightarrow> real"  where 
      contg: "continuous_map X euclidean g" and gf: "\<forall>x \<in> S \<union> T. g x = (if x \<in> S then 0 else 1)"
      using R by blast
    then show "\<exists>f. continuous_map X euclideanreal f \<and> f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}"
      by (smt (verit) Un_iff \<open>disjnt S T\<close> disjnt_iff image_subset_iff insert_iff)
  qed
qed

subsection \<open>Random metric space stuff\<close>

lemma metrizable_imp_k_space:
  assumes "metrizable_space X"
  shows "k_space X"
proof -
  obtain M d where "Metric_space M d" and Xeq: "X = Metric_space.mtopology M d"
    using assms unfolding metrizable_space_def by metis
  then interpret Metric_space M d 
    by blast
  show ?thesis
    unfolding k_space Xeq
  proof clarsimp
    fix S
    assume "S \<subseteq> M" and S: "\<forall>K. compactin mtopology K \<longrightarrow> closedin (subtopology mtopology K) (K \<inter> S)"
    have "l \<in> S"
      if \<sigma>: "range \<sigma> \<subseteq> S" and l: "limitin mtopology \<sigma> l sequentially" for \<sigma> l
    proof -
      define K where "K \<equiv> insert l (range \<sigma>)"
      interpret Submetric M d K
      proof
        show "K \<subseteq> M"
          unfolding K_def using l limitin_mspace \<open>S \<subseteq> M\<close> \<sigma> by blast
      qed
      have "compactin mtopology K"
        unfolding K_def using \<open>S \<subseteq> M\<close> \<sigma>
        by (force intro: compactin_sequence_with_limit [OF l])
      then have *: "closedin sub.mtopology (K \<inter> S)"
        by (simp add: S mtopology_submetric)
      have "\<sigma> n \<in> K \<inter> S" for n
        by (simp add: K_def range_subsetD \<sigma>)
      moreover have "limitin sub.mtopology \<sigma> l sequentially"
        using l 
        unfolding sub.limit_metric_sequentially limit_metric_sequentially
        by (force simp: K_def)
      ultimately have "l \<in> K \<inter> S"
        by (meson * \<sigma> image_subsetI sub.metric_closedin_iff_sequentially_closed) 
      then show ?thesis
        by simp
    qed
    then show "closedin mtopology S"
      unfolding metric_closedin_iff_sequentially_closed
      using \<open>S \<subseteq> M\<close> by blast
  qed
qed

lemma (in Metric_space) k_space_mtopology: "k_space mtopology"
  by (simp add: metrizable_imp_k_space metrizable_space_mtopology)

lemma k_space_euclideanreal: "k_space (euclidean :: 'a::metric_space topology)"
  using metrizable_imp_k_space metrizable_space_euclidean by auto


subsection\<open>Hereditarily normal spaces\<close>

lemma hereditarily_B:
  assumes "\<And>S T. separatedin X S T
      \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  shows "hereditarily normal_space X"
  unfolding hereditarily_def
proof (intro strip)
  fix W
  assume "W \<subseteq> topspace X"
  show "normal_space (subtopology X W)"
    unfolding normal_space_def
  proof clarify
    fix S T
    assume clo: "closedin (subtopology X W) S" "closedin (subtopology X W) T"
      and "disjnt S T"
    then have "separatedin (subtopology X W) S T"
      by (simp add: separatedin_closed_sets)
    then obtain U V where "openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
      using assms [of S T] by (meson separatedin_subtopology)
    then show "\<exists>U V. openin (subtopology X W) U \<and> openin (subtopology X W) V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
      apply (simp add: openin_subtopology_alt)
      by (meson clo closedin_imp_subset disjnt_subset1 disjnt_subset2 inf_le2)
  qed
qed

lemma hereditarily_C: 
  assumes "separatedin X S T" and norm: "\<And>U. openin X U \<Longrightarrow> normal_space (subtopology X U)"
  shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
proof -
  define ST where "ST \<equiv> X closure_of S \<inter> X closure_of T"
  have subX: "S \<subseteq> topspace X" "T \<subseteq> topspace X"
    by (meson \<open>separatedin X S T\<close> separation_closedin_Un_gen)+
  have sub: "S \<subseteq> topspace X - ST" "T \<subseteq> topspace X - ST"
    unfolding ST_def
    by (metis Diff_mono Diff_triv \<open>separatedin X S T\<close> Int_lower1 Int_lower2 separatedin_def)+
  have "normal_space (subtopology X (topspace X - ST))"
    by (simp add: ST_def norm closedin_Int openin_diff)
  moreover have " disjnt (subtopology X (topspace X - ST) closure_of S)
                         (subtopology X (topspace X - ST) closure_of T)"
    using Int_absorb1 ST_def sub by (fastforce simp: disjnt_iff closure_of_subtopology)
  ultimately show ?thesis
    using sub subX
    apply (simp add: normal_space_closures)
    by (metis ST_def closedin_Int closedin_closure_of closedin_def openin_trans_full)
qed

lemma hereditarily_normal_space: 
  "hereditarily normal_space X \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> normal_space(subtopology X U))"
  by (metis hereditarily_B hereditarily_C hereditarily)

lemma hereditarily_normal_separation:
  "hereditarily normal_space X \<longleftrightarrow>
        (\<forall>S T. separatedin X S T
             \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))"
  by (metis hereditarily_B hereditarily_C hereditarily)


lemma metrizable_imp_hereditarily_normal_space:
   "metrizable_space X \<Longrightarrow> hereditarily normal_space X"
  by (simp add: hereditarily metrizable_imp_normal_space metrizable_space_subtopology)

lemma metrizable_space_separation:
   "\<lbrakk>metrizable_space X; separatedin X S T\<rbrakk>
    \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  by (metis hereditarily hereditarily_C metrizable_imp_hereditarily_normal_space)

lemma hereditarily_normal_separation_pairwise:
   "hereditarily normal_space X \<longleftrightarrow>
    (\<forall>\<U>. finite \<U> \<and> (\<forall>S \<in> \<U>. S \<subseteq> topspace X) \<and> pairwise (separatedin X) \<U>
        \<longrightarrow> (\<exists>\<F>. (\<forall>S \<in> \<U>. openin X (\<F> S) \<and> S \<subseteq> \<F> S) \<and>
                pairwise (\<lambda>S T. disjnt (\<F> S) (\<F> T)) \<U>))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix \<U>
    assume "finite \<U>" and \<U>: "\<forall>S\<in>\<U>. S \<subseteq> topspace X" 
      and pw\<U>: "pairwise (separatedin X) \<U>"
    have "\<exists>V W. openin X V \<and> openin X W \<and> S \<subseteq> V \<and>
                    (\<forall>T. T \<in> \<U> \<and> T \<noteq> S \<longrightarrow> T \<subseteq> W) \<and> disjnt V W" 
      if "S \<in> \<U>" for S
    proof -
      have "separatedin X S (\<Union>(\<U> - {S}))"
        by (metis \<U> \<open>finite \<U>\<close> pw\<U> finite_Diff pairwise_alt separatedin_Union(1) that)
      with L show ?thesis
        unfolding hereditarily_normal_separation
        by (smt (verit) Diff_iff UnionI empty_iff insert_iff subset_iff)
    qed
    then obtain \<F> \<G> 
        where *: "\<And>S. S \<in> \<U> \<Longrightarrow> S \<subseteq> \<F> S \<and> (\<forall>T. T \<in> \<U> \<and> T \<noteq> S \<longrightarrow> T \<subseteq> \<G> S)" 
        and ope: "\<And>S. S \<in> \<U> \<Longrightarrow> openin X (\<F> S) \<and> openin X (\<G> S)" 
        and dis: "\<And>S. S \<in> \<U> \<Longrightarrow> disjnt (\<F> S) (\<G> S)" 
      by metis
    define \<H> where "\<H> \<equiv> \<lambda>S. \<F> S \<inter> (\<Inter>T \<in> \<U> - {S}. \<G> T)"
    show "\<exists>\<F>. (\<forall>S\<in>\<U>. openin X (\<F> S) \<and> S \<subseteq> \<F> S) \<and> pairwise (\<lambda>S T. disjnt (\<F> S) (\<F> T)) \<U>"
    proof (intro exI conjI strip)
      show "openin X (\<H> S)" if "S \<in> \<U>" for S
        unfolding \<H>_def 
        by (smt (verit) ope that DiffD1 \<open>finite \<U>\<close> finite_Diff finite_imageI imageE openin_Int_Inter)
      show "S \<subseteq> \<H> S" if "S \<in> \<U>" for S
        unfolding \<H>_def using "*" that by auto 
    show "pairwise (\<lambda>S T. disjnt (\<H> S) (\<H> T)) \<U>"
      using dis by (fastforce simp: disjnt_iff pairwise_alt \<H>_def)
    qed
  qed
next
  assume R: ?rhs 
  show ?lhs
    unfolding hereditarily_normal_separation
  proof (intro strip)
    fix S T
    assume "separatedin X S T"
    show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
    proof (cases "T=S")
      case True
      then show ?thesis
        using \<open>separatedin X S T\<close> by force
    next
      case False
      have "pairwise (separatedin X) {S, T}"
        by (simp add: \<open>separatedin X S T\<close> pairwise_insert separatedin_sym)
      moreover have "\<forall>S\<in>{S, T}. S \<subseteq> topspace X"
        by (metis \<open>separatedin X S T\<close> insertE separatedin_def singletonD)
        ultimately show ?thesis
        using R by (smt (verit) False finite.emptyI finite.insertI insertCI pairwiseD)
    qed
  qed
qed

lemma hereditarily_normal_space_perfect_map_image:
   "\<lbrakk>hereditarily normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> hereditarily normal_space Y"
  unfolding perfect_map_def proper_map_def
  by (meson hereditarily_normal_space_continuous_closed_map_image)

lemma regular_second_countable_imp_hereditarily_normal_space:
  assumes "regular_space X \<and> second_countable X"
  shows  "hereditarily normal_space X"
  unfolding hereditarily
  proof (intro regular_Lindelof_imp_normal_space strip)
  show "regular_space (subtopology X S)" for S
    by (simp add: assms regular_space_subtopology)
  show "Lindelof_space (subtopology X S)" for S
    using assms by (simp add: second_countable_imp_Lindelof_space second_countable_subtopology)
qed


subsection\<open>Completely regular spaces\<close>

definition completely_regular_space where
 "completely_regular_space X \<equiv>
    \<forall>S x. closedin X S \<and> x \<in> topspace X - S
          \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and>
                  f x = 0 \<and> (f ` S \<subseteq> {1}))"

lemma homeomorphic_completely_regular_space_aux:
  assumes X: "completely_regular_space X" and hom: "X homeomorphic_space Y"
  shows "completely_regular_space Y"
proof -
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  show ?thesis
    unfolding completely_regular_space_def
  proof clarify
    fix S x
    assume A: "closedin Y S" and x: "x \<in> topspace Y" and "x \<notin> S"
    then have "closedin X (g`S)"
      using hmg homeomorphic_map_closedness_eq by blast
    moreover have "g x \<notin> g`S"
      by (meson A x \<open>x \<notin> S\<close> closedin_subset hmg homeomorphic_imp_injective_map inj_on_image_mem_iff)
    ultimately obtain \<phi> where \<phi>: "continuous_map X (top_of_set {0..1::real}) \<phi> \<and> \<phi> (g x) = 0 \<and> \<phi> ` g`S \<subseteq> {1}"
      by (metis DiffI X completely_regular_space_def hmg homeomorphic_imp_surjective_map image_eqI x)
    then have "continuous_map Y (top_of_set {0..1::real}) (\<phi> \<circ> g)"
      by (meson continuous_map_compose hmg homeomorphic_imp_continuous_map)
    then show "\<exists>\<psi>. continuous_map Y (top_of_set {0..1::real}) \<psi> \<and> \<psi> x = 0 \<and> \<psi> ` S \<subseteq> {1}"
      by (metis \<phi> comp_apply image_comp)
  qed
qed

lemma homeomorphic_completely_regular_space:
  assumes "X homeomorphic_space Y"
  shows "completely_regular_space X \<longleftrightarrow> completely_regular_space Y"
  by (meson assms homeomorphic_completely_regular_space_aux homeomorphic_space_sym)

lemma completely_regular_space_alt:
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}))"
proof -
  have "\<exists>f. continuous_map X (top_of_set {0..1::real}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
    if "closedin X S" "x \<in> topspace X - S" and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {0..1}) (\<lambda>x. max 0 (min (f x) 1))"
      using that
      by (auto simp: continuous_map_in_subtopology intro!: continuous_map_real_max continuous_map_real_min)
  qed (use that in auto)
  with continuous_map_in_subtopology show ?thesis
    unfolding completely_regular_space_def by metis 
qed

text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_alt':
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. openin X S \<longrightarrow> x \<in> S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` (topspace X - S) \<subseteq> {1}))"
  apply (simp add: completely_regular_space_alt all_closedin)
  by (meson openin_subset subsetD)

lemma completely_regular_space_gen_alt:
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` S \<subseteq> {b})))"
proof -
  have "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. inverse(b - a) * (x - a)) \<circ> f)"
      using that by (intro continuous_intros) auto
  qed (use that assms in auto)
  moreover
  have "\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. a + (b - a) * x) \<circ> f)"
      using that by (intro continuous_intros) auto
  qed (use that in auto)
  ultimately show ?thesis
    unfolding completely_regular_space_alt by meson
qed

text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_gen_alt':
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. openin X S \<longrightarrow> x \<in> S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` (topspace X - S) \<subseteq> {b})))"
  apply (simp add: completely_regular_space_gen_alt[OF assms] all_closedin)
  by (meson openin_subset subsetD)

lemma completely_regular_space_gen:
  fixes a b::real
  assumes "a < b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<and> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and> f x = a \<and> f ` S \<subseteq> {b}))"
proof -
  have "\<exists>f. continuous_map X (top_of_set {a..b}) f \<and> f x = a \<and> f ` S \<subseteq> {b}" 
    if "closedin X S" "x \<in> topspace X - S" 
      and f: "continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {a..b}) (\<lambda>x. max a (min (f x) b))"
      using that assms
      by (auto simp: continuous_map_in_subtopology intro!: continuous_map_real_max continuous_map_real_min)
  qed (use that assms in auto)
  with continuous_map_in_subtopology assms show ?thesis
    using completely_regular_space_gen_alt [of a b]
    by (smt (verit) atLeastAtMost_singleton atLeastatMost_empty singletonI)
qed

lemma normal_imp_completely_regular_space_A:
  assumes "normal_space X" "t1_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_alt
proof clarify
  fix x S
  assume A: "closedin X S" "x \<notin> S"
  assume "x \<in> topspace X" 
  then have "closedin X {x}"
    by (simp add: \<open>t1_space X\<close> closedin_t1_singleton)
  with A \<open>normal_space X\<close> have "\<exists>f. continuous_map X euclideanreal f \<and> f ` {x} \<subseteq> {0} \<and> f ` S \<subseteq> {1}"
    using assms unfolding normal_space_iff_Urysohn_alt disjnt_iff by blast
  then show "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    by auto
qed

lemma normal_imp_completely_regular_space_B:
  assumes "normal_space X" "regular_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_alt
proof clarify
  fix x S
  assume "closedin X S" "x \<notin> S" "x \<in> topspace X" 
  then obtain U C where "openin X U" "closedin X C" "x \<in> U" "U \<subseteq> C" "C \<subseteq> topspace X - S"
    using assms
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of closedin_def by (metis Diff_iff)
  then obtain f where "continuous_map X euclideanreal f \<and> f ` C \<subseteq> {0} \<and> f ` S \<subseteq> {1}"
    using assms unfolding normal_space_iff_Urysohn_alt
    by (metis Diff_iff \<open>closedin X S\<close> disjnt_iff subsetD)
  then show "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    by (meson \<open>U \<subseteq> C\<close> \<open>x \<in> U\<close> image_subset_iff singletonD subsetD)
qed

lemma normal_imp_completely_regular_space_gen:
   "\<lbrakk>normal_space X; t1_space X \<or> Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
  using normal_imp_completely_regular_space_A normal_imp_completely_regular_space_B t1_or_Hausdorff_space by blast

lemma normal_imp_completely_regular_space:
   "\<lbrakk>normal_space X; Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
  by (simp add: normal_imp_completely_regular_space_gen)

lemma (in Metric_space) completely_regular_space_mtopology:
   "completely_regular_space mtopology"
  by (simp add: normal_imp_completely_regular_space normal_space_mtopology regular_space_mtopology)

lemma metrizable_imp_completely_regular_space:
   "metrizable_space X \<Longrightarrow> completely_regular_space X"
  by (simp add: metrizable_imp_normal_space metrizable_imp_regular_space normal_imp_completely_regular_space)

lemma completely_regular_space_discrete_topology:
   "completely_regular_space(discrete_topology U)"
  by (simp add: normal_imp_completely_regular_space normal_space_discrete_topology)

lemma completely_regular_space_subtopology:
  assumes "completely_regular_space X"
  shows "completely_regular_space (subtopology X S)"
  unfolding completely_regular_space_def
proof clarify
  fix A x
  assume "closedin (subtopology X S) A" and x: "x \<in> topspace (subtopology X S)" and "x \<notin> A"
  then obtain T where "closedin X T" "A = S \<inter> T" "x \<in> topspace X" "x \<in> S"
    by (force simp: closedin_subtopology_alt image_iff)
  then show "\<exists>f. continuous_map (subtopology X S) (top_of_set {0::real..1}) f \<and> f x = 0 \<and> f ` A \<subseteq> {1}"
    using assms \<open>x \<notin> A\<close>  
    apply (simp add: completely_regular_space_def continuous_map_from_subtopology)
    using continuous_map_from_subtopology by fastforce
qed

lemma completely_regular_space_retraction_map_image:
   " \<lbrakk>retraction_map X Y r; completely_regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space Y"
  using completely_regular_space_subtopology hereditary_imp_retractive_property homeomorphic_completely_regular_space by blast

lemma completely_regular_imp_regular_space:
  assumes "completely_regular_space X" 
  shows "regular_space X"
proof -
  have *: "\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
    if contf: "continuous_map X euclideanreal f" and a: "a \<in> topspace X - C" and "closedin X C"
      and fim: "f \<in> topspace X \<rightarrow> {0..1}" and f0: "f a = 0" and f1: "f ` C \<subseteq> {1}"
    for C a f
  proof (intro exI conjI)
    show "openin X {x \<in> topspace X. f x \<in> {..<1 / 2}}" "openin X {x \<in> topspace X. f x \<in> {1 / 2<..}}"
      using openin_continuous_map_preimage [OF contf]
      by (meson open_lessThan open_greaterThan open_openin)+
    show "a \<in> {x \<in> topspace X. f x \<in> {..<1 / 2}}"
      using a f0 by auto
    show "C \<subseteq> {x \<in> topspace X. f x \<in> {1 / 2<..}}"
      using \<open>closedin X C\<close> f1 closedin_subset by auto
  qed (auto simp: disjnt_iff)
  show ?thesis
    using assms *
    unfolding completely_regular_space_def regular_space_def continuous_map_in_subtopology
    by metis
qed


proposition locally_compact_regular_imp_completely_regular_space:
  assumes "locally_compact_space X" "Hausdorff_space X \<or> regular_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_def
proof clarify
  fix S x
  assume "closedin X S" and "x \<in> topspace X" and "x \<notin> S"
  have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  then have nbase: "neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
    using assms(1) locally_compact_regular_space_neighbourhood_base by blast
  then obtain U M where "openin X U" "compactin X M" "closedin X M" "x \<in> U" "U \<subseteq> M" "M \<subseteq> topspace X - S"
    unfolding neighbourhood_base_of by (metis (no_types, lifting) Diff_iff \<open>closedin X S\<close> \<open>x \<in> topspace X\<close> \<open>x \<notin> S\<close> closedin_def)
  then have "M \<subseteq> topspace X"
    by blast
  obtain V K where "openin X V" "closedin X K" "x \<in> V" "V \<subseteq> K" "K \<subseteq> U"
    by (metis (no_types, lifting) \<open>openin X U\<close> \<open>x \<in> U\<close> neighbourhood_base_of nbase)
  have "compact_space (subtopology X M)"
    by (simp add: \<open>compactin X M\<close> compact_space_subtopology)
  then have "normal_space (subtopology X M)"
    by (simp add: \<open>regular_space X\<close> compact_Hausdorff_or_regular_imp_normal_space regular_space_subtopology)
  moreover have "closedin (subtopology X M) K"
    using \<open>K \<subseteq> U\<close> \<open>U \<subseteq> M\<close> \<open>closedin X K\<close> closedin_subset_topspace by fastforce
  moreover have "closedin (subtopology X M) (M - U)"
    by (simp add: \<open>closedin X M\<close> \<open>openin X U\<close> closedin_diff closedin_subset_topspace)
  moreover have "disjnt K (M - U)"
    by (meson DiffD2 \<open>K \<subseteq> U\<close> disjnt_iff subsetD)
  ultimately obtain f::"'a\<Rightarrow>real" where contf: "continuous_map (subtopology X M) (top_of_set {0..1}) f" 
    and f0: "f ` K \<subseteq> {0}" and f1: "f ` (M - U) \<subseteq> {1}"
    using Urysohn_lemma [of "subtopology X M" K "M-U" 0 1] by auto
  then obtain g::"'a\<Rightarrow>real" where contg: "continuous_map (subtopology X M) euclidean g" and gim: "g ` M \<subseteq> {0..1}"
    and g0: "\<And>x. x \<in> K \<Longrightarrow> g x = 0" and g1: "\<And>x. \<lbrakk>x \<in> M; x \<notin> U\<rbrakk> \<Longrightarrow> g x = 1"
    using \<open>M \<subseteq> topspace X\<close> by (force simp: continuous_map_in_subtopology image_subset_iff)
  show "\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {0..1}) (\<lambda>x. if x \<in> M then g x else 1)"
      unfolding continuous_map_closedin
    proof (intro strip conjI)
      fix C
      assume C: "closedin (top_of_set {0::real..1}) C"
      have eq: "{x \<in> topspace X. (if x \<in> M then g x else 1) \<in> C} = {x \<in> M. g x \<in> C} \<union> (if 1 \<in> C then topspace X - U else {})"
        using \<open>U \<subseteq> M\<close> \<open>M \<subseteq> topspace X\<close> g1 by auto
      show "closedin X {x \<in> topspace X. (if x \<in> M then g x else 1) \<in> C}"
        unfolding eq
      proof (intro closedin_Un)
        have "closedin euclidean C"
          using C closed_closedin closedin_closed_trans by blast
        then have "closedin (subtopology X M) {x \<in> M. g x \<in> C}"
          using closedin_continuous_map_preimage_gen [OF contg] \<open>M \<subseteq> topspace X\<close> by auto
        then show "closedin X {x \<in> M. g x \<in> C}"
          using \<open>closedin X M\<close> closedin_trans_full by blast
      qed (use \<open>openin X U\<close> in force)
    qed (use gim in force)
    show "(if x \<in> M then g x else 1) = 0"
      using \<open>U \<subseteq> M\<close> \<open>V \<subseteq> K\<close> g0 \<open>x \<in> U\<close> \<open>x \<in> V\<close> by auto
    show "(\<lambda>x. if x \<in> M then g x else 1) ` S \<subseteq> {1}"
      using \<open>M \<subseteq> topspace X - S\<close> by auto
  qed
qed

lemma completely_regular_eq_regular_space:
   "locally_compact_space X
        \<Longrightarrow> (completely_regular_space X \<longleftrightarrow> regular_space X)"
  using completely_regular_imp_regular_space locally_compact_regular_imp_completely_regular_space 
  by blast

lemma completely_regular_space_prod_topology:
   "completely_regular_space (prod_topology X Y) \<longleftrightarrow>
      (prod_topology X Y) = trivial_topology \<or>
      completely_regular_space X \<and> completely_regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_prod_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "(prod_topology X Y) = trivial_topology")
    case False
    then have X: "completely_regular_space X" and Y: "completely_regular_space Y"
      using R by blast+
    show ?thesis
      unfolding completely_regular_space_alt'
    proof clarify
      fix W x y
      assume "openin (prod_topology X Y) W" and "(x, y) \<in> W"
      then obtain U V where "openin X U" "openin Y V" "x \<in> U" "y \<in> V" "U\<times>V \<subseteq> W"
        by (force simp: openin_prod_topology_alt)
      then have "x \<in> topspace X" "y \<in> topspace Y"
        using openin_subset by fastforce+
      obtain f where contf: "continuous_map X euclideanreal f" and "f x = 0" 
        and f1: "\<And>x. x \<in> topspace X \<Longrightarrow> x \<notin> U \<Longrightarrow> f x = 1"
        using X \<open>openin X U\<close> \<open>x \<in> U\<close> unfolding completely_regular_space_alt'
        by (smt (verit, best) Diff_iff image_subset_iff singletonD)
      obtain g where contg: "continuous_map Y euclideanreal g" and "g y = 0" 
        and g1: "\<And>y. y \<in> topspace Y \<Longrightarrow> y \<notin> V \<Longrightarrow> g y = 1"
        using Y \<open>openin Y V\<close> \<open>y \<in> V\<close> unfolding completely_regular_space_alt'
        by (smt (verit, best) Diff_iff image_subset_iff singletonD)
      define h where "h \<equiv> \<lambda>(x,y). 1 - (1 - f x) * (1 - g y)"
      show "\<exists>h. continuous_map (prod_topology X Y) euclideanreal h \<and> h (x,y) = 0 \<and> h ` (topspace (prod_topology X Y) - W) \<subseteq> {1}"
      proof (intro exI conjI)
        have "continuous_map (prod_topology X Y) euclideanreal (f \<circ> fst)"
          using contf continuous_map_of_fst by blast
        moreover
        have "continuous_map (prod_topology X Y) euclideanreal (g \<circ> snd)"
          using contg continuous_map_of_snd by blast
        ultimately
        show "continuous_map (prod_topology X Y) euclideanreal h"
          unfolding o_def h_def case_prod_unfold
          by (intro continuous_intros) auto
        show "h (x, y) = 0"
          by (simp add: h_def \<open>f x = 0\<close> \<open>g y = 0\<close>)
        show "h ` (topspace (prod_topology X Y) - W) \<subseteq> {1}"
          using \<open>U \<times> V \<subseteq> W\<close> f1 g1 by (force simp: h_def)
      qed
    qed
  qed (force simp: completely_regular_space_def)
qed


proposition completely_regular_space_product_topology:
   "completely_regular_space (product_topology X I) \<longleftrightarrow>
    (\<exists>i\<in>I. X i = trivial_topology) \<or> (\<forall>i \<in> I. completely_regular_space (X i))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_product_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "\<exists>i\<in>I. X i = trivial_topology")
    case False
    show ?thesis
      unfolding completely_regular_space_alt'
    proof clarify
      fix W x
      assume W: "openin (product_topology X I) W" and "x \<in> W"
      then obtain U where finU: "finite {i \<in> I. U i \<noteq> topspace (X i)}" 
             and ope: "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (U i)" 
             and x: "x \<in> Pi\<^sub>E I U" and "Pi\<^sub>E I U \<subseteq> W"
        by (auto simp: openin_product_topology_alt)
      have "\<forall>i \<in> I. openin (X i) (U i) \<and> x i \<in> U i
              \<longrightarrow> (\<exists>f. continuous_map (X i) euclideanreal f \<and>
                       f (x i) = 0 \<and> (\<forall>x \<in> topspace(X i). x \<notin> U i \<longrightarrow> f x = 1))"
        using R unfolding completely_regular_space_alt'
        by (smt (verit) DiffI False image_subset_iff singletonD)
      with ope x have "\<And>i. \<exists>f. i \<in> I \<longrightarrow> continuous_map (X i) euclideanreal f \<and>
              f (x i) = 0 \<and> (\<forall>x \<in> topspace (X i). x \<notin> U i \<longrightarrow> f x = 1)"
        by auto
      then obtain f where f: "\<And>i. i \<in> I \<Longrightarrow> continuous_map (X i) euclideanreal (f i) \<and>
                                             f i (x i) = 0 \<and> (\<forall>x \<in> topspace (X i). x \<notin> U i \<longrightarrow> f i x = 1)"
        by metis
      define h where "h \<equiv> \<lambda>z. 1 - prod (\<lambda>i. 1 - f i (z i)) {i\<in>I. U i \<noteq> topspace(X i)}"
      show "\<exists>h. continuous_map (product_topology X I) euclideanreal h \<and> h x = 0 \<and>
                     h ` (topspace (product_topology X I) - W) \<subseteq> {1}"
      proof (intro conjI exI)
        have "continuous_map (product_topology X I) euclidean (f i \<circ> (\<lambda>x. x i))" if "i\<in>I" for i
          using f that
          by (blast intro: continuous_intros continuous_map_product_projection)
        then show "continuous_map (product_topology X I) euclideanreal h"
          unfolding h_def o_def by (intro continuous_intros) (auto simp: finU)
        show "h x = 0"
          by (simp add: h_def f)
        show "h ` (topspace (product_topology X I) - W) \<subseteq> {1}"
          proof -
          have "\<exists>i. i \<in> I \<and> U i \<noteq> topspace (X i) \<and> f i (x' i) = 1"
            if "x' \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))" "x' \<notin> W" for x'
            using that \<open>Pi\<^sub>E I U \<subseteq> W\<close> by (smt (verit, best) PiE_iff f in_mono)
          then show ?thesis
            by (auto simp: f h_def finU)
        qed
      qed
    qed      
  qed (force simp: completely_regular_space_def)
qed


lemma zero_dimensional_imp_completely_regular_space:
  assumes "X dim_le 0" 
  shows "completely_regular_space X"
proof (clarsimp simp: completely_regular_space_def)
  fix C a
  assume "closedin X C" and "a \<in> topspace X" and "a \<notin> C"
  then obtain U where "closedin X U" "openin X U" "a \<in> U" and U: "U \<subseteq> topspace X - C"
    using assms by (force simp add: closedin_def dimension_le_0_neighbourhood_base_of_clopen open_neighbourhood_base_of)
  show "\<exists>f. continuous_map X (top_of_set {0::real..1}) f \<and> f a = 0 \<and> f ` C \<subseteq> {1}"
  proof (intro exI conjI)
    have "continuous_map X euclideanreal (\<lambda>x. if x \<in> U then 0 else 1)"
      using \<open>closedin X U\<close> \<open>openin X U\<close> apply (clarsimp simp: continuous_map_def closedin_def)
      by (smt (verit) Diff_iff mem_Collect_eq openin_subopen subset_eq)
    then show "continuous_map X (top_of_set {0::real..1}) (\<lambda>x. if x \<in> U then 0 else 1)"
      by (auto simp: continuous_map_in_subtopology)
  qed (use U \<open>a \<in> U\<close> in auto)
qed

lemma zero_dimensional_imp_regular_space: "X dim_le 0 \<Longrightarrow> regular_space X"
  by (simp add: completely_regular_imp_regular_space zero_dimensional_imp_completely_regular_space)

lemma (in Metric_space) t1_space_mtopology:
   "t1_space mtopology"
  using Hausdorff_space_mtopology t1_or_Hausdorff_space by blast


subsection\<open>More generally, the k-ification functor\<close>

definition kification_open 
  where "kification_open \<equiv> 
          \<lambda>X S. S \<subseteq> topspace X \<and> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S))"

definition kification 
  where "kification X \<equiv> topology (kification_open X)"

lemma istopology_kification_open: "istopology (kification_open X)"
  unfolding istopology_def
proof (intro conjI strip)
  show "kification_open X (S \<inter> T)"
    if "kification_open X S" and "kification_open X T" for S T
    using that unfolding kification_open_def
    by (smt (verit, best) inf.idem inf_commute inf_left_commute le_infI2 openin_Int)
  show "kification_open X (\<Union> \<K>)" if "\<forall>K\<in>\<K>. kification_open X K" for \<K>
    using that unfolding kification_open_def Int_Union by blast
qed

lemma openin_kification:
   "openin (kification X) U \<longleftrightarrow>
        U \<subseteq> topspace X \<and>
        (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> U))"
  by (metis topology_inverse' kification_def istopology_kification_open kification_open_def)

lemma openin_kification_finer:
   "openin X S \<Longrightarrow> openin (kification X) S"
  by (simp add: openin_kification openin_subset openin_subtopology_Int2)

lemma topspace_kification [simp]:
   "topspace(kification X) = topspace X"
  by (meson openin_kification openin_kification_finer openin_topspace subset_antisym)

lemma closedin_kification:
   "closedin (kification X) U \<longleftrightarrow>
      U \<subseteq> topspace X \<and>
      (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> U))"
proof (cases "U \<subseteq> topspace X")
  case True
  then show ?thesis
    by (simp add: closedin_def Diff_Int_distrib inf_commute le_infI2 openin_kification)
qed (simp add: closedin_def)

lemma closedin_kification_finer: "closedin X S \<Longrightarrow> closedin (kification X) S"
  by (simp add: closedin_def openin_kification_finer)

lemma kification_eq_self: "kification X = X \<longleftrightarrow> k_space X"
  unfolding fun_eq_iff openin_kification k_space_alt openin_inject [symmetric]
  by (metis openin_closedin_eq)

lemma compactin_kification [simp]:
   "compactin (kification X) K \<longleftrightarrow> compactin X K" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: compactin_contractive openin_kification_finer)
next
  assume R: ?rhs
  show ?lhs
    unfolding compactin_def
  proof (intro conjI strip)
    show "K \<subseteq> topspace (kification X)"
      by (simp add: R compactin_subset_topspace)
    fix \<U>
    assume \<U>: "Ball \<U> (openin (kification X)) \<and> K \<subseteq> \<Union> \<U>"
    then have *: "\<And>U. U \<in> \<U> \<Longrightarrow> U \<subseteq> topspace X \<and> openin (subtopology X K) (K \<inter> U)"
      by (simp add: R openin_kification)
    have "K \<subseteq> topspace X" "compact_space (subtopology X K)"
      using R compactin_subspace by force+
    then have "\<exists>V. finite V \<and> V \<subseteq> (\<lambda>U. K \<inter> U) ` \<U> \<and> \<Union> V = topspace (subtopology X K)"
      unfolding compact_space
      by (smt (verit, del_insts) Int_Union \<U> * image_iff inf.order_iff inf_commute topspace_subtopology)
    then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union> \<F>"
      by (metis Int_Union \<open>K \<subseteq> topspace X\<close> finite_subset_image inf.orderI topspace_subtopology_subset)
  qed
qed

lemma compact_space_kification [simp]:
   "compact_space(kification X) \<longleftrightarrow> compact_space X"
  by (simp add: compact_space_def)

lemma kification_kification [simp]:
   "kification(kification X) = kification X"
  unfolding openin_inject [symmetric]
proof
  fix U
  show "openin (kification (kification X)) U = openin (kification X) U"
  proof
    show "openin (kification (kification X)) U \<Longrightarrow> openin (kification X) U"
      by (metis compactin_kification inf_commute openin_kification openin_subtopology topspace_kification)
  qed (simp add: openin_kification_finer)
qed

lemma k_space_kification [iff]: "k_space(kification X)"
  using kification_eq_self by fastforce

lemma continuous_map_into_kification:
  assumes "k_space X"
  shows "continuous_map X (kification Y) f \<longleftrightarrow> continuous_map X Y f" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: continuous_map_def openin_kification_finer)
next
  assume R: ?rhs
  have "openin X {x \<in> topspace X. f x \<in> V}" if V: "openin (kification Y) V" for V
  proof -
    have "openin (subtopology X K) (K \<inter> {x \<in> topspace X. f x \<in> V})"
      if "compactin X K" for K
    proof -
      have "compactin Y (f ` K)"
        using R image_compactin that by blast
      then have "openin (subtopology Y (f ` K)) (f ` K \<inter> V)"
        by (meson V openin_kification)
      then obtain U where U: "openin Y U" "f`K \<inter> V = U \<inter> f`K"
        by (meson openin_subtopology)
      show ?thesis
        unfolding openin_subtopology
      proof (intro conjI exI)
        show "openin X {x \<in> topspace X. f x \<in> U}"
          using R U openin_continuous_map_preimage_gen by (simp add: continuous_map_def)
      qed (use U in auto)
    qed
    then show ?thesis
      by (metis (full_types) Collect_subset assms k_space_open)
  qed
  with R show ?lhs
    by (simp add: continuous_map_def)
qed

lemma continuous_map_from_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) Y f"
  by (simp add: continuous_map_openin_preimage_eq openin_kification_finer)

lemma continuous_map_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) (kification Y) f"
  by (simp add: continuous_map_from_kification continuous_map_into_kification)

lemma subtopology_kification_compact:
  assumes "compactin X K"
  shows "subtopology (kification X) K = subtopology X K"
  unfolding openin_inject [symmetric]
proof
  fix U
  show "openin (subtopology (kification X) K) U = openin (subtopology X K) U"
    by (metis assms inf_commute openin_kification openin_subset openin_subtopology)
qed


lemma subtopology_kification_finer:
  assumes "openin (subtopology (kification X) S) U"
  shows "openin (kification (subtopology X S)) U"
  using assms 
  by (fastforce simp: openin_subtopology_alt image_iff openin_kification subtopology_subtopology compactin_subtopology)

lemma proper_map_from_kification:
  assumes "k_space Y"
  shows "proper_map (kification X) Y f \<longleftrightarrow> proper_map X Y f"   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: closed_map_def closedin_kification_finer proper_map_alt)
next
  assume R: ?rhs
  have "compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}" for K
    using R proper_map_alt by auto
  with R show ?lhs
    by (simp add: assms proper_map_into_k_space_eq subtopology_kification_compact)
qed

lemma perfect_map_from_kification:
   "\<lbrakk>k_space Y; perfect_map X Y f\<rbrakk> \<Longrightarrow> perfect_map(kification X) Y f"
  by (simp add: continuous_map_from_kification perfect_map_def proper_map_from_kification)

lemma k_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" "perfect_map X Y f"
  shows "k_space X \<longleftrightarrow> k_space Y"
proof
  show "k_space X \<Longrightarrow> k_space Y"
    using k_space_perfect_map_image assms by blast
  assume "k_space Y"
  have "homeomorphic_map (kification X) X id"
    unfolding homeomorphic_eq_injective_perfect_map
    proof (intro conjI perfect_map_from_composition_right [where f = id])
  show "perfect_map (kification X) Y (f \<circ> id)"
    by (simp add: \<open>k_space Y\<close> assms(2) perfect_map_from_kification)
  show "continuous_map (kification X) X id"
    by (simp add: continuous_map_from_kification)
qed (use assms perfect_map_def in auto)
  then show "k_space X"
    using homeomorphic_k_space homeomorphic_space by blast 
qed


subsection\<open>One-point compactifications and the Alexandroff extension construction\<close>

lemma one_point_compactification_dense:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X closure_of (topspace X - {a}) = topspace X"
  unfolding closure_of_complement
  by (metis Diff_empty closedin_compact_space interior_of_eq_empty openin_closedin_eq subset_singletonD)

lemma one_point_compactification_interior:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X interior_of {a} = {}"
  by (simp add: interior_of_eq_empty_complement one_point_compactification_dense)

proposition kc_space_one_point_compactification_gen:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         openin X (topspace X - {a}) \<and> (\<forall>K. compactin X K \<and> a\<notin>K \<longrightarrow> closedin X K) \<and>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
 (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs show ?rhs
  proof (intro conjI strip)
    show "openin X (topspace X - {a})"
      using L kc_imp_t1_space t1_space_openin_delete_alt by auto
    then show "k_space (subtopology X (topspace X - {a}))"
      by (simp add: L assms k_space_open_subtopology_aux)
    show "closedin X k" if "compactin X k \<and> a \<notin> k" for k :: "'a set"
      using L kc_space_def that by blast
    show "kc_space (subtopology X (topspace X - {a}))"
      by (simp add: L kc_space_subtopology)
  qed
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume "compactin X S"
    then have "S \<subseteq>topspace X"
      by (simp add: compactin_subset_topspace)
    show "closedin X S"
    proof (cases "a \<in> S")
      case True
      then have "topspace X - S = topspace X - {a} - (S - {a})"
        by auto
      moreover have "openin X (topspace X - {a} - (S - {a}))"
      proof (rule openin_trans_full)
        show "openin (subtopology X (topspace X - {a})) (topspace X - {a} - (S - {a}))"
        proof
          show "openin (subtopology X (topspace X - {a})) (topspace X - {a})"
            using R openin_open_subtopology by blast
          have "closedin (subtopology X ((topspace X - {a}) \<inter> K)) (K \<inter> (S - {a}))"
            if "compactin X K" "K \<subseteq> topspace X - {a}" for K
          proof (intro closedin_subset_topspace)
            show "closedin X (K \<inter> (S - {a}))"
              using that
              by (metis IntD1 Int_insert_right_if0 R True \<open>compactin X S\<close> closed_Int_compactin insert_Diff subset_Diff_insert)
          qed (use that in auto)
          moreover have "k_space (subtopology X (topspace X - {a}))"
            using R by blast
          moreover have "S-{a} \<subseteq> topspace X \<and> S-{a} \<subseteq> topspace X - {a}"
            using \<open>S \<subseteq> topspace X\<close> by auto
          ultimately show "closedin (subtopology X (topspace X - {a})) (S - {a})"
            using \<open>S \<subseteq> topspace X\<close> True
            by (simp add: k_space_def compactin_subtopology subtopology_subtopology)
        qed 
        show "openin X (topspace X - {a})"
          by (simp add: R)
      qed
      ultimately show ?thesis
        by (simp add: \<open>S \<subseteq> topspace X\<close> closedin_def)
    next
      case False
      then show ?thesis
        by (simp add: R \<open>compactin X S\<close>)
    qed
  qed
qed

  
inductive Alexandroff_open for X where
  base: "openin X U \<Longrightarrow> Alexandroff_open X (Some ` U)"
| ext: "\<lbrakk>compactin X C; closedin X C\<rbrakk> \<Longrightarrow> Alexandroff_open X (insert None (Some ` (topspace X - C)))"

hide_fact (open) base ext

lemma Alexandroff_open_iff: "Alexandroff_open X S \<longleftrightarrow>
   (\<exists>U. (S = Some ` U \<and> openin X U) \<or> (S = insert None (Some ` (topspace X - U)) \<and> compactin X U \<and> closedin X U))"
  by (meson Alexandroff_open.cases Alexandroff_open.ext Alexandroff_open.base)

lemma Alexandroff_open_Un_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<union> T)"
  using \<open>Alexandroff_open X T\<close>
proof (induction rule: Alexandroff_open.induct)
  case (base V)
  then show ?case
    by (metis Alexandroff_open.base U image_Un openin_Un)
next
  case (ext C)
  have "U \<subseteq> topspace X"
    by (simp add: U openin_subset)
  then have eq: "Some ` U \<union> insert None (Some ` (topspace X - C)) = insert None (Some ` (topspace X - (C \<inter> (topspace X - U))))"
    by force
  have "closedin X (C \<inter> (topspace X - U))"
    using U ext.hyps(2) by blast
  moreover
  have "compactin X (C \<inter> (topspace X - U))"
    using U compact_Int_closedin ext.hyps(1) by blast
  ultimately show ?case
    unfolding eq using Alexandroff_open.ext by blast
qed

lemma Alexandroff_open_Un:
  assumes "Alexandroff_open X S" and "Alexandroff_open X T"
  shows "Alexandroff_open X (S \<union> T)"
  using assms
proof (induction rule: Alexandroff_open.induct)
  case (base U)
  then show ?case
    by (simp add: Alexandroff_open_Un_aux)
next
  case (ext C)
  then show ?case
    by (smt (verit, best) Alexandroff_open_Un_aux Alexandroff_open_iff Un_commute Un_insert_left closedin_def insert_absorb2)
qed

lemma Alexandroff_open_Int_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<inter> T)"
  using \<open>Alexandroff_open X T\<close>
proof (induction rule: Alexandroff_open.induct)
  case (base V)
  then show ?case
    by (metis Alexandroff_open.base U image_Int inj_Some openin_Int)
next
  case (ext C)
  have eq: "Some ` U \<inter> insert None (Some ` (topspace X - C)) = Some ` (topspace X - (C \<union> (topspace X - U)))"
    by force
  have "openin X (topspace X - (C \<union> (topspace X - U)))"
    using U ext.hyps(2) by blast
  then show ?case
    unfolding eq using Alexandroff_open.base by blast
qed

proposition istopology_Alexandroff_open: "istopology (Alexandroff_open X)"
  unfolding istopology_def
proof (intro conjI strip)
  fix S T
  assume "Alexandroff_open X S" and "Alexandroff_open X T"
  then show "Alexandroff_open X (S \<inter> T)"
  proof (induction rule: Alexandroff_open.induct)
    case (base U)
    then show ?case
      using Alexandroff_open_Int_aux by blast
  next
    case EC: (ext C)
    show ?case
      using \<open>Alexandroff_open X T\<close>
    proof (induction rule: Alexandroff_open.induct)
      case (base V)
      then show ?case
        by (metis Alexandroff_open.ext Alexandroff_open_Int_aux EC.hyps inf_commute)
    next
      case (ext D)
      have eq: "insert None (Some ` (topspace X - C)) \<inter> insert None (Some ` (topspace X - D))
              = insert None (Some ` (topspace X - (C \<union> D)))"
        by auto
      show ?case
        unfolding eq
        by (simp add: Alexandroff_open.ext EC.hyps closedin_Un compactin_Un ext.hyps)
    qed
  qed
next
  fix \<K>
  assume \<section>: "\<forall>K\<in>\<K>. Alexandroff_open X K"
  show "Alexandroff_open X (\<Union>\<K>)"
  proof (cases "None \<in> \<Union>\<K>")
    case True
    have "\<forall>K\<in>\<K>. \<exists>U. (openin X U \<and> K = Some ` U) \<or> (K = insert None (Some ` (topspace X - U)) \<and> compactin X U \<and> closedin X U)"
      by (metis \<section> Alexandroff_open_iff)
    then obtain U where U: 
      "\<And>K. K \<in> \<K> \<Longrightarrow> openin X (U K) \<and> K = Some ` (U K) 
                    \<or> (K = insert None (Some ` (topspace X - U K)) \<and> compactin X (U K) \<and> closedin X (U K))"
      by metis
    define \<K>N where "\<K>N \<equiv> {K \<in> \<K>. None \<in> K}"
    define A where "A \<equiv> \<Union>K\<in>\<K>-\<K>N. U K"
    define B where "B \<equiv> \<Inter>K\<in>\<K>N. U K"
    have U1: "\<And>K. K \<in> \<K>-\<K>N \<Longrightarrow> openin X (U K) \<and> K = Some ` (U K)"
      using U \<K>N_def by auto
    have U2: "\<And>K. K \<in> \<K>N \<Longrightarrow> K = insert None (Some ` (topspace X - U K)) \<and> compactin X (U K) \<and> closedin X (U K)"
      using U \<K>N_def by auto
    have eqA: "\<Union>(\<K>-\<K>N) = Some ` A"
    proof
      show "\<Union> (\<K> - \<K>N) \<subseteq> Some ` A"
        by (metis A_def Sup_le_iff U1 UN_upper subset_image_iff)
      show "Some ` A \<subseteq> \<Union> (\<K> - \<K>N)"
        using A_def U1 by blast
    qed
    have eqB: "\<Union>\<K>N = insert None (Some ` (topspace X - B))"
      using U2 True
      by (auto simp: B_def image_iff \<K>N_def)
    have "\<Union>\<K> = \<Union>\<K>N \<union> \<Union>(\<K>-\<K>N)"
      by (auto simp: \<K>N_def)
    then have eq: "\<Union>\<K> = (Some ` A) \<union> (insert None (Some ` (topspace X - B)))"
      by (simp add: eqA eqB Un_commute)
    show ?thesis
      unfolding eq
    proof (intro Alexandroff_open_Un Alexandroff_open.intros)
      show "openin X A"
        using A_def U1 by blast
      show "closedin X B"
        unfolding B_def using U2 True \<K>N_def by auto
      show "compactin X B"
        by (metis B_def U2 eqB Inf_lower Union_iff \<open>closedin X B\<close> closed_compactin imageI insertI1)
    qed
  next
    case False
    then have "\<forall>K\<in>\<K>. \<exists>U. openin X U \<and> K = Some ` U"
      by (metis Alexandroff_open.simps UnionI \<section> insertCI)
    then obtain U where U: "\<forall>K\<in>\<K>. openin X (U K) \<and> K = Some ` (U K)"
      by metis
    then have eq: "\<Union>\<K> = Some ` (\<Union> K\<in>\<K>. U K)"
      using image_iff by fastforce
    show ?thesis
      unfolding eq by (simp add: U Alexandroff_open.base openin_clauses(3))
  qed
qed


definition Alexandroff_compactification where
  "Alexandroff_compactification X \<equiv> topology (Alexandroff_open X)"

lemma openin_Alexandroff_compactification:
   "openin(Alexandroff_compactification X) V \<longleftrightarrow>
        (\<exists>U. openin X U \<and> V = Some ` U) \<or>
        (\<exists>C. compactin X C \<and> closedin X C \<and> V = insert None (Some ` (topspace X - C)))"
  by (auto simp: Alexandroff_compactification_def istopology_Alexandroff_open Alexandroff_open.simps)


lemma topspace_Alexandroff_compactification [simp]:
   "topspace(Alexandroff_compactification X) = insert None (Some ` topspace X)"
   (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (force simp: topspace_def openin_Alexandroff_compactification)
  have "None \<in> topspace (Alexandroff_compactification X)"
    by (meson closedin_empty compactin_empty insert_subset openin_Alexandroff_compactification openin_subset)
  moreover have "Some x \<in> topspace (Alexandroff_compactification X)"
    if "x \<in> topspace X" for x 
    by (meson that imageI openin_Alexandroff_compactification openin_subset openin_topspace subsetD)
  ultimately show "?rhs \<subseteq> ?lhs"
    by (auto simp: image_subset_iff)
qed

lemma closedin_Alexandroff_compactification:
   "closedin (Alexandroff_compactification X) C \<longleftrightarrow>
      (\<exists>K. compactin X K \<and> closedin X K \<and> C = Some ` K) \<or>
      (\<exists>U. openin X U \<and> C = topspace(Alexandroff_compactification X) - Some ` U)"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    apply (clarsimp simp: closedin_def openin_Alexandroff_compactification)
    by (smt (verit) Diff_Diff_Int None_notin_image_Some image_set_diff inf.absorb_iff2 inj_Some insert_Diff_if subset_insert)
  show "?rhs \<Longrightarrow> ?lhs"
    using openin_subset 
    by (fastforce simp: closedin_def openin_Alexandroff_compactification)
qed

lemma openin_Alexandroff_compactification_image_Some [simp]:
   "openin(Alexandroff_compactification X) (Some ` U) \<longleftrightarrow> openin X U"
  by (auto simp: openin_Alexandroff_compactification inj_image_eq_iff)

lemma closedin_Alexandroff_compactification_image_Some [simp]:
   "closedin (Alexandroff_compactification X) (Some ` K) \<longleftrightarrow> compactin X K \<and> closedin X K"
  by (auto simp: closedin_Alexandroff_compactification inj_image_eq_iff)

lemma open_map_Some: "open_map X (Alexandroff_compactification X) Some"
  using open_map_def openin_Alexandroff_compactification by blast

lemma continuous_map_Some: "continuous_map X (Alexandroff_compactification X) Some"
  unfolding continuous_map_def 
proof (intro conjI strip)
  fix U
  assume "openin (Alexandroff_compactification X) U"
  then consider V where "openin X V" "U = Some ` V" 
    | C where "compactin X C" "closedin X C" "U = insert None (Some ` (topspace X - C))" 
    by (auto simp: openin_Alexandroff_compactification)
  then show "openin X {x \<in> topspace X. Some x \<in> U}"
  proof cases
    case 1
    then show ?thesis
      using openin_subopen openin_subset by fastforce
  next
    case 2
    then show ?thesis
      by (simp add: closedin_def image_iff set_diff_eq)
  qed
qed auto


lemma embedding_map_Some: "embedding_map X (Alexandroff_compactification X) Some"
  by (simp add: continuous_map_Some injective_open_imp_embedding_map open_map_Some)

lemma compact_space_Alexandroff_compactification [simp]:
   "compact_space(Alexandroff_compactification X)"
proof (clarsimp simp: compact_space_alt image_subset_iff)
  fix \<U> U
  assume ope [rule_format]: "\<forall>U\<in>\<U>. openin (Alexandroff_compactification X) U"
      and cover: "\<forall>x\<in>topspace X. \<exists>X\<in>\<U>. Some x \<in> X"
      and "U \<in> \<U>" "None \<in> U"
  then have Usub: "U \<subseteq> insert None (Some ` topspace X)"
    by (metis openin_subset topspace_Alexandroff_compactification)
  with ope [OF \<open>U \<in> \<U>\<close>] \<open>None \<in> U\<close>
  obtain C where C: "compactin X C \<and> closedin X C \<and>
          insert None (Some ` topspace X) - U = Some ` C"
    by (auto simp: openin_closedin closedin_Alexandroff_compactification)
  then have D: "compactin (Alexandroff_compactification X) (insert None (Some ` topspace X) - U)"
    by (metis continuous_map_Some image_compactin)
  consider V where "openin X V" "U = Some ` V" 
    | C where "compactin X C" "closedin X C" "U = insert None (Some ` (topspace X - C))" 
    using ope [OF \<open>U \<in> \<U>\<close>] by (auto simp: openin_Alexandroff_compactification)
  then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> (\<exists>X\<in>\<F>. None \<in> X) \<and> (\<forall>x\<in>topspace X. \<exists>X\<in>\<F>. Some x \<in> X)"
  proof cases
    case 1
    then show ?thesis
      using \<open>None \<in> U\<close> by blast      
  next
    case 2
    obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<U>" "insert None (Some ` topspace X) - U \<subseteq> \<Union>\<F>"
      by (smt (verit, del_insts) C D Union_iff compactinD compactin_subset_topspace cover image_subset_iff ope subsetD)
    with \<open>U \<in> \<U>\<close> show ?thesis
      by (rule_tac x="insert U \<F>" in exI) auto
  qed
qed

lemma topspace_Alexandroff_compactification_delete:
   "topspace(Alexandroff_compactification X) - {None} = Some ` topspace X"
  by simp

lemma Alexandroff_compactification_dense:
  assumes "\<not> compact_space X"
  shows "(Alexandroff_compactification X) closure_of (Some ` topspace X) =
         topspace(Alexandroff_compactification X)"
  unfolding topspace_Alexandroff_compactification_delete [symmetric]
proof (intro one_point_compactification_dense)
  show "\<not> compactin (Alexandroff_compactification X) (topspace (Alexandroff_compactification X) - {None})"
    using assms compact_space_proper_map_preimage compact_space_subtopology embedding_map_Some embedding_map_def homeomorphic_imp_proper_map by fastforce
qed auto


lemma t0_space_one_point_compactification:
  assumes "compact_space X \<and> openin X (topspace X - {a})"
  shows "t0_space X \<longleftrightarrow> t0_space (subtopology X (topspace X - {a}))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using t0_space_subtopology by blast
  show "?rhs \<Longrightarrow> ?lhs"
    using assms
    unfolding t0_space_def by (bestsimp simp flip: Int_Diff dest: openin_trans_full)
qed

lemma t0_space_Alexandroff_compactification [simp]:
   "t0_space (Alexandroff_compactification X) \<longleftrightarrow> t0_space X"
  using t0_space_one_point_compactification [of "Alexandroff_compactification X" None]
  using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_t0_space by fastforce

lemma t1_space_one_point_compactification:
  assumes Xa: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "t1_space X \<longleftrightarrow> t1_space (subtopology X (topspace X - {a}))"  (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using t1_space_subtopology by blast
  assume R: ?rhs
  show ?lhs
    unfolding t1_space_closedin_singleton
  proof (intro strip)
    fix x
    assume "x \<in> topspace X"
    show "closedin X {x}"
    proof (cases "x=a")
      case True
      then show ?thesis
        using \<open>x \<in> topspace X\<close> Xa closedin_def by blast
    next
      case False
      show ?thesis
        by (simp add: "\<section>" False R \<open>x \<in> topspace X\<close> closedin_t1_singleton)
    qed
  qed
qed

lemma closedin_Alexandroff_I: 
  assumes "compactin (Alexandroff_compactification X) K" "K \<subseteq> Some ` topspace X"
          "closedin (Alexandroff_compactification X) T" "K = T \<inter> Some ` topspace X"
  shows "closedin (Alexandroff_compactification X) K"
proof -
  obtain S where S: "S \<subseteq> topspace X" "K = Some ` S"
    by (meson \<open>K \<subseteq> Some ` topspace X\<close> subset_imageE)
  with assms have "compactin X S"
    by (metis compactin_subtopology embedding_map_Some embedding_map_def homeomorphic_map_compactness)
  moreover have "closedin X S"
    using assms S
    by (metis closedin_subtopology embedding_map_Some embedding_map_def homeomorphic_map_closedness)
  ultimately show ?thesis
    by (simp add: S)
qed


lemma t1_space_Alexandroff_compactification [simp]:
  "t1_space(Alexandroff_compactification X) \<longleftrightarrow> t1_space X"
proof -
  have "openin (Alexandroff_compactification X) (topspace (Alexandroff_compactification X) - {None})"
    by auto
  then show ?thesis
    using t1_space_one_point_compactification [of "Alexandroff_compactification X" None]
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_t1_space 
    by (fastforce simp: compactin_subtopology closedin_Alexandroff_I closedin_subtopology)
qed


lemma kc_space_one_point_compactification:
  assumes "compact_space X"
    and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk>
                \<Longrightarrow> closedin X K"
  shows "kc_space X \<longleftrightarrow>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
proof -
  have "closedin X K"
    if "kc_space (subtopology X (topspace X - {a}))" and "compactin X K" "a \<notin> K" for K
    using that unfolding kc_space_def 
    by (metis "\<section>" Diff_empty compactin_subspace compactin_subtopology subset_Diff_insert)
  then show ?thesis
    by (metis \<open>compact_space X\<close> kc_space_one_point_compactification_gen ope)
qed

lemma kc_space_Alexandroff_compactification:
  "kc_space(Alexandroff_compactification X) \<longleftrightarrow> (k_space X \<and> kc_space X)" (is "kc_space ?Y = _")
proof -
  have "kc_space (Alexandroff_compactification X) \<longleftrightarrow>
      (k_space (subtopology ?Y (topspace ?Y - {None})) \<and> kc_space (subtopology ?Y (topspace ?Y - {None})))"
    by (rule kc_space_one_point_compactification) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> k_space X \<and> kc_space X"
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_k_space homeomorphic_kc_space by simp blast
  finally show ?thesis .
qed


proposition regular_space_one_point_compactification:
  assumes "compact_space X" and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "regular_space X \<longleftrightarrow>
           regular_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using assms(1) compact_imp_locally_compact_space locally_compact_space_open_subset ope regular_space_subtopology by blast
  assume R: ?rhs
  let ?Xa = "subtopology X (topspace X - {a})"
  show ?lhs
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of imp_conjL
  proof (intro strip)
    fix W x
    assume "openin X W" and "x \<in> W"
    show "\<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
    proof (cases "x=a")
      case True
      have "compactin ?Xa (topspace X - W)"
        using \<open>openin X W\<close> assms(1) closedin_compact_space
        by (metis Diff_mono True \<open>x \<in> W\<close> compactin_subtopology empty_subsetI insert_subset openin_closedin_eq order_refl)
      then obtain V K where V: "openin ?Xa V" and K: "compactin ?Xa K" "closedin ?Xa K" and "topspace X - W \<subseteq> V" "V \<subseteq> K"
        by (metis locally_compact_space_compact_closed_compact R)
      show ?thesis
      proof (intro exI conjI)
        show "openin X (topspace X - K)"
          using "\<section>" K by blast
        show "closedin X (topspace X - V)"
          using V ope openin_trans_full by blast
        show "x \<in> topspace X - K"
        proof (rule)
          show "x \<in> topspace X"
            using \<open>openin X W\<close> \<open>x \<in> W\<close> openin_subset by blast
          show "x \<notin> K"
            using K True closedin_imp_subset by blast
        qed
        show "topspace X - K \<subseteq> topspace X - V"
          by (simp add: Diff_mono \<open>V \<subseteq> K\<close>)
        show "topspace X - V \<subseteq> W"
          using \<open>topspace X - W \<subseteq> V\<close> by auto
      qed
    next
      case False
      have "openin ?Xa ((topspace X - {a}) \<inter> W)"
        using \<open>openin X W\<close> openin_subtopology_Int2 by blast
      moreover have "x \<in> (topspace X - {a}) \<inter> W"
        using \<open>openin X W\<close> \<open>x \<in> W\<close> openin_subset False by blast
      ultimately obtain U V where "openin ?Xa U" "compactin ?Xa V" "closedin ?Xa V"
               "x \<in> U" "U \<subseteq> V" "V \<subseteq> (topspace X - {a}) \<inter> W"
        using R locally_compact_regular_space_neighbourhood_base neighbourhood_base_of
        by (metis (no_types, lifting))
      then show ?thesis
        by (meson "\<section>" le_infE ope openin_trans_full)
    qed
  qed
qed


lemma regular_space_Alexandroff_compactification:
  "regular_space(Alexandroff_compactification X) \<longleftrightarrow> regular_space X \<and> locally_compact_space X" 
  (is "regular_space ?Y = ?rhs")
proof -
  have "regular_space ?Y \<longleftrightarrow>
        regular_space (subtopology ?Y (topspace ?Y - {None})) \<and> locally_compact_space (subtopology ?Y (topspace ?Y - {None}))"
    by (rule regular_space_one_point_compactification) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> regular_space X \<and> locally_compact_space X"
    by (metis embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_locally_compact_space 
        homeomorphic_regular_space topspace_Alexandroff_compactification_delete)
  finally show ?thesis .
qed


lemma Hausdorff_space_one_point_compactification:
  assumes "compact_space X" and  "openin X (topspace X - {a})"
    and "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "Hausdorff_space X \<longleftrightarrow>
           Hausdorff_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show ?rhs if ?lhs
  proof -
    have "locally_compact_space (subtopology X (topspace X - {a}))"
      using assms that compact_imp_locally_compact_space locally_compact_space_open_subset 
      by blast
    with that show ?rhs
      by (simp add: Hausdorff_space_subtopology)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (metis assms locally_compact_Hausdorff_or_regular regular_space_one_point_compactification
        regular_t1_eq_Hausdorff_space t1_space_one_point_compactification)
qed

lemma Hausdorff_space_Alexandroff_compactification:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow> Hausdorff_space X \<and> locally_compact_space X"
  by (meson compact_Hausdorff_imp_regular_space compact_space_Alexandroff_compactification 
      locally_compact_Hausdorff_or_regular regular_space_Alexandroff_compactification 
      regular_t1_eq_Hausdorff_space t1_space_Alexandroff_compactification)

lemma completely_regular_space_Alexandroff_compactification:
   "completely_regular_space(Alexandroff_compactification X) \<longleftrightarrow>
        completely_regular_space X \<and> locally_compact_space X"
  by (metis regular_space_Alexandroff_compactification completely_regular_eq_regular_space
      compact_imp_locally_compact_space compact_space_Alexandroff_compactification)

proposition Hausdorff_space_one_point_compactification_asymmetric_prod:
  assumes "compact_space X"
  shows "Hausdorff_space X \<longleftrightarrow>
         kc_space (prod_topology X (subtopology X (topspace X - {a}))) \<and>
         k_space (prod_topology X (subtopology X (topspace X - {a})))"  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "a \<in> topspace X")
  case True
  show ?thesis
  proof 
    show ?rhs if ?lhs
    proof
      show "kc_space (prod_topology X (subtopology X (topspace X - {a})))"
        using Hausdorff_imp_kc_space kc_space_prod_topology_right kc_space_subtopology that by blast
      show "k_space (prod_topology X (subtopology X (topspace X - {a})))"
        by (meson Hausdorff_imp_kc_space assms compact_imp_locally_compact_space k_space_prod_topology_left 
            kc_space_one_point_compactification_gen that)
    qed
  next
    assume R: ?rhs
    define D where "D \<equiv> (\<lambda>x. (x,x)) ` (topspace X - {a})"
    show ?lhs
    proof (cases "topspace X = {a}")
      case True
      then show ?thesis
        by (simp add: Hausdorff_space_def)
    next
      case False
      with R True have "kc_space X"
        using kc_space_retraction_map_image [of "prod_topology X (subtopology X (topspace X - {a}))" X fst]
        by (metis Diff_subset insert_Diff retraction_map_fst topspace_discrete_topology topspace_subtopology_subset)
      have "closedin (subtopology (prod_topology X (subtopology X (topspace X - {a}))) K) (K \<inter> D)" 
        if "compactin (prod_topology X (subtopology X (topspace X - {a}))) K" for K
      proof (intro closedin_subtopology_Int_subset[where V=K] closedin_subset_topspace)
        show "fst ` K \<times> snd ` K \<inter> D \<subseteq> fst ` K \<times> snd ` K" "K \<subseteq> fst ` K \<times> snd ` K"
          by force+
        have eq: "(fst ` K \<times> snd ` K \<inter> D) = ((\<lambda>x. (x,x)) ` (fst ` K \<inter> snd ` K))"
          using compactin_subset_topspace that by (force simp: D_def image_iff)
        have "compactin (prod_topology X (subtopology X (topspace X - {a}))) (fst ` K \<times> snd ` K \<inter> D)"
          unfolding eq
        proof (rule image_compactin [of "subtopology X (topspace X - {a})"])
          have "compactin X (fst ` K)" "compactin X (snd ` K)"
            by (meson compactin_subtopology continuous_map_fst continuous_map_snd image_compactin that)+
          moreover have "fst ` K \<inter> snd ` K \<subseteq> topspace X - {a}"
            using compactin_subset_topspace that by force
          ultimately
          show "compactin (subtopology X (topspace X - {a})) (fst ` K \<inter> snd ` K)"
            unfolding compactin_subtopology
            by (meson \<open>kc_space X\<close> closed_Int_compactin kc_space_def)
          show "continuous_map (subtopology X (topspace X - {a})) (prod_topology X (subtopology X (topspace X - {a}))) (\<lambda>x. (x,x))"
            by (simp add: continuous_map_paired)
        qed
        then show "closedin (prod_topology X (subtopology X (topspace X - {a}))) (fst ` K \<times> snd ` K \<inter> D)"
          using R compactin_imp_closedin_gen by blast
      qed
      moreover have "D \<subseteq> topspace X \<times> (topspace X \<inter> (topspace X - {a}))"
        by (auto simp: D_def)
      ultimately have *: "closedin (prod_topology X (subtopology X (topspace X - {a}))) D"
        using R by (auto simp: k_space)
      have "x=y"
        if "x \<in> topspace X" "y \<in> topspace X" 
          and \<section>: "\<And>T. \<lbrakk>(x,y) \<in> T; openin (prod_topology X X) T\<rbrakk> \<Longrightarrow> \<exists>z \<in> topspace X. (z,z) \<in> T" for x y
      proof (cases "x=a \<and> y=a")
        case False
        then consider "x\<noteq>a" | "y\<noteq>a"
          by blast
        then show ?thesis
        proof cases
          case 1
          have "\<exists>z \<in> topspace X - {a}. (z,z) \<in> T"
            if "(y,x) \<in> T" "openin (prod_topology X (subtopology X (topspace X - {a}))) T" for T
          proof -
            have "(x,y) \<in> {z \<in> topspace (prod_topology X X). (snd z,fst z) \<in> T \<inter> topspace X \<times> (topspace X - {a})}"
              by (simp add: "1" \<open>x \<in> topspace X\<close> \<open>y \<in> topspace X\<close> that)
            moreover have "openin (prod_topology X X) {z \<in> topspace (prod_topology X X). (snd z,fst z) \<in> T \<inter> topspace X \<times> (topspace X - {a})}"
            proof (rule openin_continuous_map_preimage)
              show "continuous_map (prod_topology X X) (prod_topology X X) (\<lambda>x. (snd x, fst x))"
                by (simp add: continuous_map_fst continuous_map_pairedI continuous_map_snd)
              have "openin (prod_topology X X) (topspace X \<times> (topspace X - {a}))"
                using \<open>kc_space X\<close> assms kc_space_one_point_compactification_gen openin_prod_Times_iff by fastforce
              moreover have "openin (prod_topology X X) T"
                using kc_space_one_point_compactification_gen [OF \<open>compact_space X\<close>] \<open>kc_space X\<close> that
                by (metis openin_prod_Times_iff openin_topspace openin_trans_full prod_topology_subtopology(2))
              ultimately show "openin (prod_topology X X) (T \<inter> topspace X \<times> (topspace X - {a}))"
                by blast
            qed
            ultimately show ?thesis
              by (smt (verit) \<section> Int_iff fst_conv mem_Collect_eq mem_Sigma_iff snd_conv)
          qed
          then have "(y,x) \<in> prod_topology X (subtopology X (topspace X - {a})) closure_of D"
            by (simp add: "1" D_def in_closure_of that)
          then show ?thesis
            using that "*" D_def closure_of_closedin by fastforce
        next
          case 2
          have "\<exists>z \<in> topspace X - {a}. (z,z) \<in> T"
            if "(x,y) \<in> T" "openin (prod_topology X (subtopology X (topspace X - {a}))) T" for T
          proof -
            have "openin (prod_topology X X) (topspace X \<times> (topspace X - {a}))"
              using \<open>kc_space X\<close> assms kc_space_one_point_compactification_gen openin_prod_Times_iff by fastforce
            moreover have XXT: "openin (prod_topology X X) T"
              using kc_space_one_point_compactification_gen [OF \<open>compact_space X\<close>] \<open>kc_space X\<close> that
              by (metis openin_prod_Times_iff openin_topspace openin_trans_full prod_topology_subtopology(2))
            ultimately have "openin (prod_topology X X) (T \<inter> topspace X \<times> (topspace X - {a}))"
              by blast
            then show ?thesis
              by (smt (verit) "\<section>" Diff_subset XXT mem_Sigma_iff openin_subset subsetD that topspace_prod_topology topspace_subtopology_subset)
          qed
          then have "(x,y) \<in> prod_topology X (subtopology X (topspace X - {a})) closure_of D"
            by (simp add: "2" D_def in_closure_of that)
          then show ?thesis
            using that "*" D_def closure_of_closedin by fastforce
        qed
      qed auto
      then show ?thesis
        unfolding Hausdorff_space_closedin_diagonal closure_of_subset_eq [symmetric] 
          by (force simp: closure_of_def)
    qed
  qed
next
  case False
  then show ?thesis
    by (simp add: assms compact_imp_k_space compact_space_prod_topology kc_space_compact_prod_topology)
qed


lemma Hausdorff_space_Alexandroff_compactification_asymmetric_prod:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow>
        kc_space(prod_topology (Alexandroff_compactification X) X) \<and>
        k_space(prod_topology (Alexandroff_compactification X) X)"
    (is "Hausdorff_space ?Y = ?rhs")
proof -
  have *: "subtopology (Alexandroff_compactification X)
     (topspace (Alexandroff_compactification X) -
      {None}) homeomorphic_space X"
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_space_sym by fastforce
  have "Hausdorff_space (Alexandroff_compactification X) \<longleftrightarrow>
      (kc_space (prod_topology ?Y (subtopology ?Y (topspace ?Y - {None}))) \<and>
       k_space (prod_topology ?Y (subtopology ?Y (topspace ?Y - {None}))))"
    by (rule Hausdorff_space_one_point_compactification_asymmetric_prod) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> ?rhs"
    using homeomorphic_k_space homeomorphic_kc_space homeomorphic_space_prod_topology 
          homeomorphic_space_refl * by blast
  finally show ?thesis .
qed

lemma kc_space_as_compactification_unique:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and> compactin X (topspace X - U)
                   else openin (subtopology X (topspace X - {a})) U)"
proof (cases "a \<in> U")
  case True
  then show ?thesis
    by (meson assms closedin_compact_space compactin_imp_closedin_gen openin_closedin_eq)
next
  case False
  then show ?thesis
  by (metis Diff_empty kc_space_one_point_compactification_gen openin_open_subtopology openin_subset subset_Diff_insert assms)
qed

lemma kc_space_as_compactification_unique_explicit:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and>
                     compactin (subtopology X (topspace X - {a})) (topspace X - U) \<and>
                     closedin (subtopology X (topspace X - {a})) (topspace X - U)
                else openin (subtopology X (topspace X - {a})) U)"
  apply (simp add: kc_space_subtopology compactin_imp_closedin_gen assms compactin_subtopology cong: conj_cong)
  by (metis Diff_mono assms bot.extremum insert_subset kc_space_as_compactification_unique subset_refl)

lemma Alexandroff_compactification_unique:
  assumes "kc_space X" "compact_space X" and a: "a \<in> topspace X"
  shows "Alexandroff_compactification (subtopology X (topspace X - {a})) homeomorphic_space X"
        (is "?Y homeomorphic_space X")
proof -
  have [simp]: "topspace X \<inter> (topspace X - {a}) = topspace X - {a}"  
    by auto
  have [simp]: "insert None (Some ` A) = insert None (Some ` B) \<longleftrightarrow> A = B" 
               "insert None (Some ` A) \<noteq> Some ` B" for A B
    by auto
  have "quotient_map X ?Y (\<lambda>x. if x = a then None else Some x)"
    unfolding quotient_map_def
  proof (intro conjI strip)
    show "(\<lambda>x. if x = a then None else Some x) ` topspace X = topspace ?Y"
      using \<open>a \<in> topspace X\<close>  by force
    show "openin X {x \<in> topspace X. (if x = a then None else Some x) \<in> U} = openin ?Y U" (is "?L = ?R")
      if "U \<subseteq> topspace ?Y" for U
    proof (cases "None \<in> U")
      case True
      then obtain T where T[simp]: "U = insert None (Some ` T)"
        by (metis Int_insert_right UNIV_I UNIV_option_conv inf.orderE inf_le2 subsetI subset_imageE)
      have Tsub: "T \<subseteq> topspace X - {a}"
        using in_these_eq that by auto
      then have "{x \<in> topspace X. (if x = a then None else Some x) \<in> U} = insert a T"
        by (auto simp: a image_iff cong: conj_cong)
      then have "?L \<longleftrightarrow> openin X (insert a T)"
        by metis
      also have "\<dots> \<longleftrightarrow> ?R"
        using Tsub assms
        apply (simp add: openin_Alexandroff_compactification kc_space_as_compactification_unique_explicit [where a=a])
        by (smt (verit, best) Diff_insert2 Diff_subset closedin_imp_subset double_diff)
      finally show ?thesis .
    next
      case False
      then obtain T where [simp]: "U = Some ` T"
        by (metis Int_insert_right UNIV_I UNIV_option_conv inf.orderE inf_le2 subsetI subset_imageE)
      have **: "\<And>V. openin X V \<Longrightarrow> openin X (V - {a})"
        by (simp add: assms compactin_imp_closedin_gen openin_diff)
      have Tsub: "T \<subseteq> topspace X - {a}"
        using in_these_eq that by auto
      then have "{x \<in> topspace X. (if x = a then None else Some x) \<in> U} = T"
        by (auto simp: image_iff cong: conj_cong)
      then show ?thesis
        by (simp add: "**" Tsub openin_open_subtopology)
    qed
  qed
  moreover have "inj_on (\<lambda>x. if x = a then None else Some x) (topspace X)"
    by (auto simp: inj_on_def)
  ultimately show ?thesis
    using homeomorphic_space_sym homeomorphic_space homeomorphic_map_def by blast
qed

subsection\<open>Extending continuous maps "pointwise" in a regular space\<close>

lemma continuous_map_on_intermediate_closure_of:
  assumes Y: "regular_space Y" 
    and T: "T \<subseteq> X closure_of S" 
    and f: "\<And>t. t \<in> T \<Longrightarrow> limitin Y f (f t) (atin_within X t S)"
  shows "continuous_map (subtopology X T) Y f"
proof (clarsimp simp add: continuous_map_atin)
  fix a
  assume "a \<in> topspace X" and "a \<in> T"
  have "f ` T \<subseteq> topspace Y"
    by (metis f image_subsetI limitin_topspace)
  have "\<forall>\<^sub>F x in atin_within X a T. f x \<in> W"
    if W: "openin Y W" "f a \<in> W" for W
  proof -
    obtain V C where "openin Y V" "closedin Y C" "f a \<in> V" "V \<subseteq> C" "C \<subseteq> W"
      by (metis Y W neighbourhood_base_of neighbourhood_base_of_closedin)
    have "\<forall>\<^sub>F x in atin_within X a S. f x \<in> V"
      by (metis \<open>a \<in> T\<close> \<open>f a \<in> V\<close> \<open>openin Y V\<close> f limitin_def)
    then obtain U where "openin X U" "a \<in> U" and U: "\<forall>x \<in> U - {a}. x \<in> S \<longrightarrow> f x \<in> V"
      by (smt (verit) Diff_iff \<open>a \<in> topspace X\<close> eventually_atin_within insert_iff)
    moreover have "f z \<in> W" if "z \<in> U" "z \<noteq> a" "z \<in> T" for z
    proof -
      have "z \<in> topspace X"
        using \<open>openin X U\<close> openin_subset \<open>z \<in> U\<close> by blast
      then have "f z \<in> topspace Y"
        using \<open>f ` T \<subseteq> topspace Y\<close> \<open>z \<in> T\<close> by blast
      { assume "f z \<in> topspace Y" "f z \<notin> C"
        then have "\<forall>\<^sub>F x in atin_within X z S. f x \<in> topspace Y - C"
          by (metis Diff_iff \<open>closedin Y C\<close> closedin_def f limitinD \<open>z \<in> T\<close>)
        then obtain U' where U': "openin X U'" "z \<in> U'" 
                 "\<And>x. x \<in> U' - {z} \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<notin> C"
          by (smt (verit) Diff_iff \<open>z \<in> topspace X\<close> eventually_atin_within insertCI)
        then have *: "\<And>D. z \<in> D \<and> openin X D \<Longrightarrow> \<exists>y. y \<in> S \<and> y \<in> D"
          by (meson T in_closure_of subsetD \<open>z \<in> T\<close>)
        have False
          using * [of "U \<inter> U'"] U' U \<open>V \<subseteq> C\<close> \<open>f a \<in> V\<close> \<open>f z \<notin> C\<close> \<open>openin X U\<close> that
          by blast
      }
      then show ?thesis
        using \<open>C \<subseteq> W\<close> \<open>f z \<in> topspace Y\<close> by auto
    qed
    ultimately have "\<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x \<in> U - {a}. x \<in> T \<longrightarrow> f x \<in> W)"
      by blast
    then show ?thesis
      using eventually_atin_within by fastforce
  qed
  then show "limitin Y f (f a) (atin (subtopology X T) a)"
    by (metis \<open>a \<in> T\<close> atin_subtopology_within f limitin_def)
qed


lemma continuous_map_on_intermediate_closure_of_eq:
  assumes "regular_space Y" "S \<subseteq> T" and Tsub: "T \<subseteq> X closure_of S"
  shows "continuous_map (subtopology X T) Y f \<longleftrightarrow> (\<forall>t \<in> T. limitin Y f (f t) (atin_within X t S))"
        (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (clarsimp simp add: continuous_map_atin)
    fix x
    assume "x \<in> T"
    with L Tsub closure_of_subset_topspace 
    have "limitin Y f (f x) (atin (subtopology X T) x)"
      by (fastforce simp: continuous_map_atin)
    then show "limitin Y f (f x) (atin_within X x S)"
      using \<open>x \<in> T\<close> \<open>S \<subseteq> T\<close>
      by (force simp: limitin_def atin_subtopology_within eventually_atin_within)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs" 
    using assms continuous_map_on_intermediate_closure_of by blast
qed

lemma continuous_map_extension_pointwise_alt:
  assumes \<section>: "regular_space Y" "S \<subseteq> T" "T \<subseteq> X closure_of S"
    and f: "continuous_map (subtopology X S) Y f"
    and lim: "\<And>t. t \<in> T-S \<Longrightarrow> \<exists>l. limitin Y f l (atin_within X t S)"
  obtains g where "continuous_map (subtopology X T) Y g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain g where g: "\<And>t. t \<in> T \<and> t \<notin> S \<Longrightarrow> limitin Y f (g t) (atin_within X t S)"
    by (metis Diff_iff lim)
  let ?h = "\<lambda>x. if x \<in> S then f x else g x"
  show thesis
  proof
    have T: "T \<subseteq> topspace X"
      using \<section> closure_of_subset_topspace by fastforce
    have "limitin Y ?h (f t) (atin_within X t S)" if "t \<in> T" "t \<in> S" for t
    proof -
      have "limitin Y f (f t) (atin_within X t S)"
        by (meson T f limit_continuous_map_within subset_eq that)
      then show ?thesis
        by (simp add: eventually_atin_within limitin_def)
    qed
    moreover have "limitin Y ?h (g t) (atin_within X t S)" if "t \<in> T" "t \<notin> S" for t
      by (smt (verit, del_insts) eventually_atin_within g limitin_def that)
    ultimately show "continuous_map (subtopology X T) Y ?h"
      unfolding continuous_map_on_intermediate_closure_of_eq [OF \<section>] 
      by (auto simp: \<section> atin_subtopology_within)
  qed auto
qed


lemma continuous_map_extension_pointwise:
  assumes "regular_space Y" "S \<subseteq> T" and Tsub: "T \<subseteq> X closure_of S"
    and ex: " \<And>x. x \<in> T \<Longrightarrow> \<exists>g. continuous_map (subtopology X (insert x S)) Y g \<and>
                     (\<forall>x \<in> S. g x = f x)"
  obtains g where "continuous_map (subtopology X T) Y g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (rule continuous_map_extension_pointwise_alt)
  show "continuous_map (subtopology X S) Y f"
  proof (clarsimp simp add: continuous_map_atin)
    fix t
    assume "t \<in> topspace X" and "t \<in> S"
    then obtain g where g: "limitin Y g (g t) (atin (subtopology X (insert t S)) t)" and gf: "\<forall>x \<in> S. g x = f x"
      by (metis Int_iff \<open>S \<subseteq> T\<close> continuous_map_atin ex inf.orderE insert_absorb topspace_subtopology)
    with \<open>t \<in> S\<close> show "limitin Y f (f t) (atin (subtopology X S) t)"
      by (simp add: limitin_def atin_subtopology_within_if eventually_atin_within gf insert_absorb)
  qed
  show "\<exists>l. limitin Y f l (atin_within X t S)" if "t \<in> T - S" for t
  proof -
    obtain g where g: "continuous_map (subtopology X (insert t S)) Y g" and gf: "\<forall>x \<in> S. g x = f x"
      using \<open>S \<subseteq> T\<close> ex \<open>t \<in> T - S\<close> by force
    then have "limitin Y g (g t) (atin_within X t (insert t S))"
      using Tsub in_closure_of limit_continuous_map_within that  by fastforce
    then show ?thesis
      unfolding limitin_def
      by (smt (verit) eventually_atin_within gf subsetD subset_insertI)
  qed
qed (use assms in auto)


subsection\<open>Extending Cauchy continuous functions to the closure\<close>

lemma Cauchy_continuous_map_extends_to_continuous_closure_of_aux:
  assumes m2: "mcomplete_of m2" and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> mspace m1"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) 
                        (mtopology_of m2) g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (rule continuous_map_extension_pointwise_alt)
  interpret L: Metric_space12 "mspace m1" "mdist m1" "mspace m2" "mdist m2"
    by (simp add: Metric_space12_mspace_mdist)
  interpret S: Metric_space "S \<inter> mspace m1" "mdist m1"
    by (simp add: L.M1.subspace)
  show "regular_space (mtopology_of m2)"
    by (simp add: Metric_space.regular_space_mtopology mtopology_of_def)
  show "S \<subseteq> mtopology_of m1 closure_of S"
    by (simp add: assms(3) closure_of_subset)    
  show "continuous_map (subtopology (mtopology_of m1) S) (mtopology_of m2) f"
    by (metis Cauchy_continuous_imp_continuous_map f mtopology_of_submetric)
  fix a
  assume a: "a \<in> mtopology_of m1 closure_of S - S"
  then obtain \<sigma> where ran\<sigma>: "range \<sigma> \<subseteq> S" "range \<sigma> \<subseteq> mspace m1" 
    and lim\<sigma>: "limitin L.M1.mtopology \<sigma> a sequentially"
    by (force simp: mtopology_of_def L.M1.closure_of_sequentially)
  then have "L.M1.MCauchy \<sigma>"
    by (simp add: L.M1.convergent_imp_MCauchy mtopology_of_def)
  then have "L.M2.MCauchy (f \<circ> \<sigma>)"
    using f ran\<sigma> by (simp add: Cauchy_continuous_map_def L.M1.subspace Metric_space.MCauchy_def)
  then obtain l where l: "limitin L.M2.mtopology (f \<circ> \<sigma>) l sequentially"
    by (meson L.M2.mcomplete_def m2 mcomplete_of_def)
  have "limitin L.M2.mtopology f l (atin_within L.M1.mtopology a S)"
    unfolding L.limit_atin_sequentially_within imp_conjL
  proof (intro conjI strip)
    show "l \<in> mspace m2"
      using L.M2.limitin_mspace l by blast
    fix \<rho>
    assume "range \<rho> \<subseteq> S \<inter> mspace m1 - {a}" and lim\<rho>: "limitin L.M1.mtopology \<rho> a sequentially"
    then have ran\<rho>: "range \<rho> \<subseteq> S" "range \<rho> \<subseteq> mspace m1" "\<And>n. \<rho> n \<noteq> a"
      by auto
    have "a \<in> mspace m1"
      using L.M1.limitin_mspace lim\<rho> by auto
    have "S.MCauchy \<sigma>" "S.MCauchy \<rho>"
      using L.M1.convergent_imp_MCauchy L.M1.MCauchy_def S.MCauchy_def lim\<sigma> ran\<sigma> lim\<rho> ran\<rho> by force+
    then have "L.M2.MCauchy (f \<circ> \<rho>)" "L.M2.MCauchy (f \<circ> \<sigma>)"
      using f by (auto simp: Cauchy_continuous_map_def)
    then have ran_f: "range (\<lambda>x. f (\<rho> x)) \<subseteq> mspace m2" "range (\<lambda>x. f (\<sigma> x)) \<subseteq> mspace m2"
      by (auto simp: L.M2.MCauchy_def)
    have "(\<lambda>n. mdist m2 (f (\<rho> n)) l) \<longlonglongrightarrow> 0"
    proof (rule Lim_null_comparison)
      have "mdist m2 (f (\<rho> n)) l \<le> mdist m2 (f (\<sigma> n)) l + mdist m2 (f (\<sigma> n)) (f (\<rho> n))" for n
        using \<open>l \<in> mspace m2\<close> ran_f L.M2.triangle'' by (smt (verit, best) range_subsetD)
      then show "\<forall>\<^sub>F n in sequentially. norm (mdist m2 (f (\<rho> n)) l) \<le> mdist m2 (f (\<sigma> n)) l + mdist m2 (f (\<sigma> n)) (f (\<rho> n))"
        by force
      define \<psi> where "\<psi> \<equiv> \<lambda>n. if even n then \<sigma> (n div 2) else \<rho> (n div 2)"
      have "(\<lambda>n. mdist m1 (\<sigma> n) (\<rho> n)) \<longlonglongrightarrow> 0"
      proof (rule Lim_null_comparison)
        show "\<forall>\<^sub>F n in sequentially. norm (mdist m1 (\<sigma> n) (\<rho> n)) \<le> mdist m1 (\<sigma> n) a + mdist m1 (\<rho> n) a"
          using L.M1.triangle' [of _ a] ran\<sigma> ran\<rho> \<open>a \<in> mspace m1\<close> by (simp add: range_subsetD)
        have "(\<lambda>n. mdist m1 (\<sigma> n) a) \<longlonglongrightarrow> 0"
          using L.M1.limitin_metric_dist_null lim\<sigma> by blast
        moreover have "(\<lambda>n. mdist m1 (\<rho> n) a) \<longlonglongrightarrow> 0"
          using L.M1.limitin_metric_dist_null lim\<rho> by blast
        ultimately show "(\<lambda>n. mdist m1 (\<sigma> n) a + mdist m1 (\<rho> n) a) \<longlonglongrightarrow> 0"
          by (simp add: tendsto_add_zero)
      qed
      with \<open>S.MCauchy \<sigma>\<close> \<open>S.MCauchy \<rho>\<close> have "S.MCauchy \<psi>"
        by (simp add: S.MCauchy_interleaving_gen \<psi>_def)
      then have "L.M2.MCauchy (f \<circ> \<psi>)"
        by (metis Cauchy_continuous_map_def f mdist_submetric mspace_submetric)
      then have "(\<lambda>n. mdist m2 (f (\<sigma> n)) (f (\<rho> n))) \<longlonglongrightarrow> 0"
        using L.M2.MCauchy_interleaving_gen [of "f \<circ> \<sigma>" "f \<circ> \<rho>"]  
        by (simp add: if_distrib \<psi>_def o_def cong: if_cong)
      moreover have "\<forall>\<^sub>F n in sequentially. f (\<sigma> n) \<in> mspace m2 \<and> (\<lambda>x. mdist m2 (f (\<sigma> x)) l) \<longlonglongrightarrow> 0"
        using l by (auto simp: L.M2.limitin_metric_dist_null \<open>l \<in> mspace m2\<close>)
      ultimately show "(\<lambda>n. mdist m2 (f (\<sigma> n)) l + mdist m2 (f (\<sigma> n)) (f (\<rho> n))) \<longlonglongrightarrow> 0"
        by (metis (mono_tags) tendsto_add_zero eventually_sequentially order_refl)
    qed
    with ran_f show "limitin L.M2.mtopology (f \<circ> \<rho>) l sequentially"
      by (auto simp: L.M2.limitin_metric_dist_null eventually_sequentially \<open>l \<in> mspace m2\<close>)
  qed
  then show "\<exists>l. limitin (mtopology_of m2) f l (atin_within (mtopology_of m1) a S)" 
    by (force simp: mtopology_of_def)
qed auto


lemma Cauchy_continuous_map_extends_to_continuous_closure_of:
  assumes "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                        (mtopology_of m2) g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain g where cmg: 
    "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of (mspace m1 \<inter> S))) 
                        (mtopology_of m2) g" 
    and gf: "(\<forall>x \<in> mspace m1 \<inter> S. g x = f x)"
    using Cauchy_continuous_map_extends_to_continuous_closure_of_aux assms
    by (metis inf_commute inf_le2 submetric_restrict)
  define h where "h \<equiv> \<lambda>x. if x \<in> topspace(mtopology_of m1) then g x else f x"
  show thesis
  proof
    show "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                         (mtopology_of m2) h"
      unfolding h_def
    proof (rule continuous_map_eq)
      show "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) (mtopology_of m2) g"
        by (metis closure_of_restrict cmg topspace_mtopology_of)
    qed auto
  qed (auto simp: gf h_def)
qed


lemma Cauchy_continuous_map_extends_to_continuous_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and T: "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) g" 
         "(\<forall>x \<in> S. g x = f x)"
  by (metis Cauchy_continuous_map_extends_to_continuous_closure_of T assms(1) continuous_map_from_subtopology_mono f)

text \<open>Technical lemma helpful for porting particularly ugly HOL Light proofs\<close>
lemma all_in_closure_of:
  assumes P: "\<forall>x \<in> S. P x" and clo: "closedin X {x \<in> topspace X. P x}"
  shows "\<forall>x \<in> X closure_of S. P x"
proof -
  have *: "topspace X \<inter> S \<subseteq> {x \<in> topspace X. P x}"
    using P by auto
    show ?thesis
  using closure_of_minimal [OF * clo]  closure_of_restrict by fastforce
qed

lemma Lipschitz_continuous_map_on_intermediate_closure_aux:
  assumes lcf: "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "Lipschitz_continuous_map (submetric m1 T) m2 f"
proof -
  interpret L: Metric_space12 "mspace m1" "mdist m1" "mspace m2" "mdist m2"
    by (simp add: Metric_space12_mspace_mdist)
  interpret S: Metric_space "S \<inter> mspace m1" "mdist m1"
    by (simp add: L.M1.subspace)
  have "T \<subseteq> mspace m1"
    using Tsub by (auto simp: mtopology_of_def closure_of_def)
  show ?thesis
    unfolding Lipschitz_continuous_map_pos
  proof
    show "f \<in> mspace (submetric m1 T) \<rightarrow> mspace m2"
      by (metis cmf Metric_space.metric_continuous_map Metric_space_mspace_mdist  mtopology_of_def 
          mtopology_of_submetric image_subset_iff_funcset)
    define X where "X \<equiv> prod_topology (subtopology L.M1.mtopology T) (subtopology L.M1.mtopology T)"
    obtain B::real where "B > 0" and B: "\<forall>(x,y) \<in> S\<times>S. mdist m2 (f x) (f y) \<le> B * mdist m1 x y"
      using lcf \<open>S \<subseteq> mspace m1\<close>  by (force simp: Lipschitz_continuous_map_pos)
    have eq: "{z \<in> A. case z of (x,y) \<Rightarrow> p x y \<le> B * q x y} = {z \<in> A. ((\<lambda>(x,y). B * q x y - p x y)z) \<in> {0..}}" 
        for p q and A::"('a*'a)set"
      by auto
    have clo: "closedin X {z \<in> topspace X. case z of (x, y) \<Rightarrow> mdist m2 (f x) (f y) \<le> B * mdist m1 x y}"
      unfolding eq
    proof (rule closedin_continuous_map_preimage)
      have *: "continuous_map X L.M2.mtopology (f \<circ> fst)" "continuous_map X L.M2.mtopology (f \<circ> snd)"
        using cmf by (auto simp: mtopology_of_def X_def intro: continuous_map_compose continuous_map_fst continuous_map_snd)
      then show "continuous_map X euclidean (\<lambda>x. case x of (x, y) \<Rightarrow> B * mdist m1 x y - mdist m2 (f x) (f y))"
        unfolding case_prod_unfold
      proof (intro continuous_intros; simp add: mtopology_of_def o_def)
        show "continuous_map X L.M1.mtopology fst" "continuous_map X L.M1.mtopology snd"
          by (simp_all add: X_def continuous_map_subtopology_fst continuous_map_subtopology_snd flip: subtopology_Times)
      qed
    qed auto
    have "mdist m2 (f x) (f y) \<le> B * mdist m1 x y" if "x \<in> T" "y \<in> T" for x y
      using all_in_closure_of [OF B clo] \<open>S \<subseteq> T\<close> Tsub
      by (fastforce simp: X_def subset_iff closure_of_Times closure_of_subtopology inf.absorb2  
          mtopology_of_def that)
    then show "\<exists>B>0. \<forall>x\<in>mspace (submetric m1 T).
             \<forall>y\<in>mspace (submetric m1 T).
                mdist m2 (f x) (f y) \<le> B * mdist (submetric m1 T) x y"
      using \<open>0 < B\<close> by auto
  qed
qed


lemma Lipschitz_continuous_map_on_intermediate_closure:
  assumes "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" "T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "Lipschitz_continuous_map (submetric m1 T) m2 f"
  by (metis Lipschitz_continuous_map_on_intermediate_closure_aux assms closure_of_subset_topspace subset_trans topspace_mtopology_of)


lemma Lipschitz_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "Lipschitz_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "Lipschitz_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain g 
    where g: "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                        (mtopology_of m2) g"  "(\<forall>x \<in> S. g x = f x)"
    by (metis Cauchy_continuous_map_extends_to_continuous_closure_of Lipschitz_imp_Cauchy_continuous_map f m2)
  have "Lipschitz_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g"
  proof (rule Lipschitz_continuous_map_on_intermediate_closure)
    show "Lipschitz_continuous_map (submetric m1 (mspace m1 \<inter> S)) m2 g"
      by (smt (verit, best) IntD2 Lipschitz_continuous_map_eq f g(2) inf_commute mspace_submetric submetric_restrict)
    show "mspace m1 \<inter> S \<subseteq> mtopology_of m1 closure_of S"
      using closure_of_subset_Int by force
    show "mtopology_of m1 closure_of S \<subseteq> mtopology_of m1 closure_of (mspace m1 \<inter> S)"
      by (metis closure_of_restrict subset_refl topspace_mtopology_of)
    show "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) (mtopology_of m2) g"
      by (simp add: g)
  qed
  with g that show thesis
    by metis
qed


lemma Lipschitz_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "Lipschitz_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  by (metis Lipschitz_continuous_map_extends_to_closure_of Lipschitz_continuous_map_from_submetric_mono assms)

text \<open>This proof uses the same trick to extend the function's domain to its closure\<close>
lemma uniformly_continuous_map_on_intermediate_closure_aux:
  assumes ucf: "uniformly_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "uniformly_continuous_map (submetric m1 T) m2 f"
proof -
  interpret L: Metric_space12 "mspace m1" "mdist m1" "mspace m2" "mdist m2"
    by (simp add: Metric_space12_mspace_mdist)
  interpret S: Metric_space "S \<inter> mspace m1" "mdist m1"
    by (simp add: L.M1.subspace)
  have "T \<subseteq> mspace m1"
    using Tsub by (auto simp: mtopology_of_def closure_of_def)
  show ?thesis
    unfolding uniformly_continuous_map_def
    proof (intro conjI strip)
    show "f \<in> mspace (submetric m1 T) \<rightarrow> mspace m2"
      by (metis cmf Metric_space.metric_continuous_map Metric_space_mspace_mdist  
          mtopology_of_def mtopology_of_submetric image_subset_iff_funcset)
    fix \<epsilon>::real
    assume "\<epsilon> > 0"
    then obtain \<delta> where "\<delta>>0" and \<delta>: "\<forall>(x,y) \<in> S\<times>S. mdist m1 x y < \<delta> \<longrightarrow> mdist m2 (f x) (f y) \<le> \<epsilon>/2"
      using ucf \<open>S \<subseteq> mspace m1\<close> unfolding uniformly_continuous_map_def mspace_submetric
      apply (simp add: Ball_def del: divide_const_simps)
      by (metis IntD2 half_gt_zero inf.orderE less_eq_real_def)
    define X where "X \<equiv> prod_topology (subtopology L.M1.mtopology T) (subtopology L.M1.mtopology T)"
    text \<open>A clever construction involving the union of two closed sets\<close>
    have eq: "{z \<in> A. case z of (x,y) \<Rightarrow> p x y < d \<longrightarrow> q x y \<le> e} 
            = {z \<in> A. ((\<lambda>(x,y). p x y - d)z) \<in> {0..}} \<union> {z \<in> A. ((\<lambda>(x,y). e - q x y)z) \<in> {0..}}" 
      for p q and d e::real and A::"('a*'a)set"
      by auto
    have clo: "closedin X {z \<in> topspace X. case z of (x, y) \<Rightarrow> mdist m1 x y < \<delta> \<longrightarrow> mdist m2 (f x) (f y) \<le> \<epsilon>/2}"
      unfolding eq
    proof (intro closedin_Un closedin_continuous_map_preimage)
      have *: "continuous_map X L.M1.mtopology fst" "continuous_map X L.M1.mtopology snd"
        by (metis X_def continuous_map_subtopology_fst subtopology_Times continuous_map_subtopology_snd)+
      show "continuous_map X euclidean (\<lambda>x. case x of (x, y) \<Rightarrow> mdist m1 x y - \<delta>)"
        unfolding case_prod_unfold
        by (intro continuous_intros; simp add: mtopology_of_def *)
      have *: "continuous_map X L.M2.mtopology (f \<circ> fst)" "continuous_map X L.M2.mtopology (f \<circ> snd)"
        using cmf by (auto simp: mtopology_of_def X_def intro: continuous_map_compose continuous_map_fst continuous_map_snd)
      then show "continuous_map X euclidean (\<lambda>x. case x of (x, y) \<Rightarrow> \<epsilon> / 2 - mdist m2 (f x) (f y))"
        unfolding case_prod_unfold
        by (intro continuous_intros; simp add: mtopology_of_def o_def)
    qed auto
    have "mdist m2 (f x) (f y) \<le> \<epsilon>/2" if "x \<in> T" "y \<in> T" "mdist m1 x y < \<delta>" for x y
      using all_in_closure_of [OF \<delta> clo] \<open>S \<subseteq> T\<close> Tsub
      by (fastforce simp: X_def subset_iff closure_of_Times closure_of_subtopology inf.absorb2  
          mtopology_of_def that)
    then show "\<exists>\<delta>>0. \<forall>x\<in>mspace (submetric m1 T). \<forall>y\<in>mspace (submetric m1 T). mdist (submetric m1 T) y x < \<delta> \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>"
      using \<open>0 < \<delta>\<close> \<open>0 < \<epsilon>\<close> by fastforce
  qed
qed

lemma uniformly_continuous_map_on_intermediate_closure:
  assumes "uniformly_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and"T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "uniformly_continuous_map (submetric m1 T) m2 f"
  by (metis assms closure_of_subset_topspace subset_trans topspace_mtopology_of 
      uniformly_continuous_map_on_intermediate_closure_aux)

lemma uniformly_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "uniformly_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "uniformly_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain g 
    where g: "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                        (mtopology_of m2) g"  "(\<forall>x \<in> S. g x = f x)"
    by (metis Cauchy_continuous_map_extends_to_continuous_closure_of uniformly_imp_Cauchy_continuous_map f m2)
  have "uniformly_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g"
  proof (rule uniformly_continuous_map_on_intermediate_closure)
    show "uniformly_continuous_map (submetric m1 (mspace m1 \<inter> S)) m2 g"
      by (smt (verit, best) IntD2 uniformly_continuous_map_eq f g(2) inf_commute mspace_submetric submetric_restrict)
    show "mspace m1 \<inter> S \<subseteq> mtopology_of m1 closure_of S"
      using closure_of_subset_Int by force
    show "mtopology_of m1 closure_of S \<subseteq> mtopology_of m1 closure_of (mspace m1 \<inter> S)"
      by (metis closure_of_restrict subset_refl topspace_mtopology_of)
    show "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) (mtopology_of m2) g"
      by (simp add: g)
  qed
  with g that show thesis
    by metis
qed


lemma uniformly_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "uniformly_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "uniformly_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  by (metis uniformly_continuous_map_extends_to_closure_of uniformly_continuous_map_from_submetric_mono assms)


lemma Cauchy_continuous_map_on_intermediate_closure_aux:
  assumes ucf: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "Cauchy_continuous_map (submetric m1 T) m2 f"
proof -
  interpret L: Metric_space12 "mspace m1" "mdist m1" "mspace m2" "mdist m2"
    by (simp add: Metric_space12_mspace_mdist)
  interpret S: Metric_space "S \<inter> mspace m1" "mdist m1"
    by (simp add: L.M1.subspace)
  interpret T: Metric_space T "mdist m1"
    by (metis L.M1.subspace Tsub closure_of_subset_topspace dual_order.trans topspace_mtopology_of)
  have "T \<subseteq> mspace m1"
    using Tsub by (auto simp: mtopology_of_def closure_of_def)
  then show ?thesis
  proof (clarsimp simp: Cauchy_continuous_map_def Int_absorb2)
    fix \<sigma>
    assume \<sigma>: "T.MCauchy \<sigma>"
    have "\<exists>y\<in>S. mdist m1 (\<sigma> n) y < inverse (Suc n) \<and> mdist m2 (f (\<sigma> n)) (f y) < inverse (Suc n)" for n
    proof -
      have "\<sigma> n \<in> T"
        using \<sigma> by (force simp: T.MCauchy_def)
      moreover have "continuous_map (mtopology_of (submetric m1 T)) L.M2.mtopology f"
        by (metis cmf mtopology_of_def mtopology_of_submetric)
      ultimately obtain \<delta> where "\<delta>>0" and \<delta>: "\<forall>x \<in> T. mdist m1 (\<sigma> n) x < \<delta> \<longrightarrow> mdist m2 (f(\<sigma> n)) (f x) < inverse (Suc n)"
        using \<open>T \<subseteq> mspace m1\<close>
        apply (simp add: mtopology_of_def Metric_space.metric_continuous_map L.M1.subspace Int_absorb2)
        by (metis inverse_Suc of_nat_Suc)
      have "\<exists>y \<in> S. mdist m1 (\<sigma> n) y < min \<delta> (inverse (Suc n))"
        using \<open>\<sigma> n \<in> T\<close> Tsub \<open>\<delta>>0\<close> 
        unfolding mtopology_of_def L.M1.metric_closure_of subset_iff mem_Collect_eq L.M1.in_mball
        by (smt (verit, del_insts) inverse_Suc )
      with \<delta> \<open>S \<subseteq> T\<close> show ?thesis
        by auto
    qed
    then obtain \<rho> where \<rho>S: "\<And>n. \<rho> n \<in> S" and \<rho>1: "\<And>n. mdist m1 (\<sigma> n) (\<rho> n) < inverse (Suc n)" 
                    and \<rho>2: "\<And>n. mdist m2 (f (\<sigma> n)) (f (\<rho> n)) < inverse (Suc n)" 
      by metis
    have "S.MCauchy \<rho>"
      unfolding S.MCauchy_def
    proof (intro conjI strip)
      show "range \<rho> \<subseteq> S \<inter> mspace m1"
        using \<open>S \<subseteq> mspace m1\<close> by (auto simp: \<rho>S)
      fix \<epsilon> :: real
      assume "\<epsilon>>0"
      then obtain M where M: "\<And>n n'. M \<le> n \<Longrightarrow> M \<le> n' \<Longrightarrow> mdist m1 (\<sigma> n) (\<sigma> n') < \<epsilon>/2"
        using \<sigma> unfolding T.MCauchy_def by (meson half_gt_zero)
      have "\<forall>\<^sub>F n in sequentially. inverse (Suc n) < \<epsilon>/4"
        using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> divide_pos_pos zero_less_numeral by blast
      then obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> inverse (Suc n) < \<epsilon>/4"
        by (meson eventually_sequentially)
      have "mdist m1 (\<rho> n) (\<rho> n') < \<epsilon>" if "n \<ge> max M N" "n' \<ge> max M N" for n n'
      proof -
        have "mdist m1 (\<rho> n) (\<rho> n') \<le> mdist m1 (\<rho> n) (\<sigma> n) + mdist m1 (\<sigma> n) (\<rho> n')"
          by (meson T.MCauchy_def T.triangle \<rho>S \<sigma> \<open>S \<subseteq> T\<close> rangeI subset_iff)
        also have "\<dots> \<le> mdist m1 (\<rho> n) (\<sigma> n) + mdist m1 (\<sigma> n) (\<sigma> n') + mdist m1 (\<sigma> n') (\<rho> n')"
          by (smt (verit, best) T.MCauchy_def T.triangle \<rho>S \<sigma> \<open>S \<subseteq> T\<close> in_mono rangeI)
        also have "\<dots> < \<epsilon>/4 + \<epsilon>/2 + \<epsilon>/4"
          using \<rho>1[of n] \<rho>1[of n'] N[of n] N[of n'] that M[of n n'] by (simp add: T.commute)
        also have "... \<le> \<epsilon>"
          by simp
        finally show ?thesis .
      qed
      then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> mdist m1 (\<rho> n) (\<rho> n') < \<epsilon>"
        by blast
    qed
    then have f\<rho>: "L.M2.MCauchy (f \<circ> \<rho>)"
      using ucf by (simp add: Cauchy_continuous_map_def)
    show "L.M2.MCauchy (f \<circ> \<sigma>)"
      unfolding L.M2.MCauchy_def
    proof (intro conjI strip)
      show "range (f \<circ> \<sigma>) \<subseteq> mspace m2"
        using \<open>T \<subseteq> mspace m1\<close> \<sigma> cmf
        apply (auto simp: )
        by (metis Metric_space.metric_continuous_map Metric_space_mspace_mdist T.MCauchy_def image_eqI inf.absorb1 mspace_submetric mtopology_of_def mtopology_of_submetric range_subsetD subset_iff)
      fix \<epsilon> :: real
      assume "\<epsilon>>0"
      then obtain M where M: "\<And>n n'. M \<le> n \<Longrightarrow> M \<le> n' \<Longrightarrow> mdist m2 ((f \<circ> \<rho>) n) ((f \<circ> \<rho>) n') < \<epsilon>/2"
        using f\<rho> unfolding L.M2.MCauchy_def by (meson half_gt_zero)
      have "\<forall>\<^sub>F n in sequentially. inverse (Suc n) < \<epsilon>/4"
        using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> divide_pos_pos zero_less_numeral by blast
      then obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> inverse (Suc n) < \<epsilon>/4"
        by (meson eventually_sequentially)
      have "mdist m2 ((f \<circ> \<sigma>) n) ((f \<circ> \<sigma>) n') < \<epsilon>" if "n \<ge> max M N" "n' \<ge> max M N" for n n'
      proof -
        have "mdist m2 ((f \<circ> \<sigma>) n) ((f \<circ> \<sigma>) n') \<le> mdist m2 ((f \<circ> \<sigma>) n) ((f \<circ> \<rho>) n) + mdist m2 ((f \<circ> \<rho>) n) ((f \<circ> \<sigma>) n')"
          by (meson L.M2.MCauchy_def \<open>range (f \<circ> \<sigma>) \<subseteq> mspace m2\<close> f\<rho> mdist_triangle rangeI subset_eq)
        also have "\<dots> \<le> mdist m2 ((f \<circ> \<sigma>) n) ((f \<circ> \<rho>) n) + mdist m2 ((f \<circ> \<rho>) n) ((f \<circ> \<rho>) n') + mdist m2 ((f \<circ> \<rho>) n') ((f \<circ> \<sigma>) n')"
          by (smt (verit) L.M2.MCauchy_def L.M2.triangle \<open>range (f \<circ> \<sigma>) \<subseteq> mspace m2\<close> f\<rho> range_subsetD)
        also have "\<dots> < \<epsilon>/4 + \<epsilon>/2 + \<epsilon>/4"
          using \<rho>2[of n] \<rho>2[of n'] N[of n] N[of n'] that M[of n n'] by (simp add: L.M2.commute)
        also have "... \<le> \<epsilon>"
          by simp
        finally show ?thesis .
      qed
      then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> mdist m2 ((f \<circ> \<sigma>) n) ((f \<circ> \<sigma>) n') < \<epsilon>"
        by blast
    qed
  qed
qed

lemma Cauchy_continuous_map_on_intermediate_closure:
  assumes "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and "T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "Cauchy_continuous_map (submetric m1 T) m2 f"
  by (metis Cauchy_continuous_map_on_intermediate_closure_aux assms closure_of_subset_topspace order.trans topspace_mtopology_of)


lemma Cauchy_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "Cauchy_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain g 
    where g: "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                        (mtopology_of m2) g"  "(\<forall>x \<in> S. g x = f x)"
    by (metis Cauchy_continuous_map_extends_to_continuous_closure_of f m2)
  have "Cauchy_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g"
  proof (rule Cauchy_continuous_map_on_intermediate_closure)
    show "Cauchy_continuous_map (submetric m1 (mspace m1 \<inter> S)) m2 g"
      by (smt (verit, best) IntD2 Cauchy_continuous_map_eq f g(2) inf_commute mspace_submetric submetric_restrict)
    show "mspace m1 \<inter> S \<subseteq> mtopology_of m1 closure_of S"
      using closure_of_subset_Int by force
    show "mtopology_of m1 closure_of S \<subseteq> mtopology_of m1 closure_of (mspace m1 \<inter> S)"
      by (metis closure_of_restrict subset_refl topspace_mtopology_of)
    show "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) (mtopology_of m2) g"
      by (simp add: g)
  qed
  with g that show thesis
    by metis
qed


lemma Cauchy_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "Cauchy_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  by (metis Cauchy_continuous_map_extends_to_closure_of Cauchy_continuous_map_from_submetric_mono assms)


subsection\<open>Metric space of bounded functions\<close>

context Metric_space
begin

definition fspace :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) set" where 
  "fspace \<equiv> \<lambda>S. {f. f`S \<subseteq> M \<and> f \<in> extensional S \<and> mbounded (f`S)}"

definition fdist :: "['b set, 'b \<Rightarrow> 'a, 'b \<Rightarrow> 'a] \<Rightarrow> real" where 
  "fdist \<equiv> \<lambda>S f g. if f \<in> fspace S \<and> g \<in> fspace S \<and> S \<noteq> {} 
                    then Sup ((\<lambda>x. d (f x) (g x)) ` S) else 0"

lemma fspace_empty [simp]: "fspace {} = {\<lambda>x. undefined}"
  by (auto simp: fspace_def)

lemma fdist_empty [simp]: "fdist {} = (\<lambda>x y. 0)"
  by (auto simp: fdist_def)

lemma fspace_in_M: "\<lbrakk>f \<in> fspace S; x \<in> S\<rbrakk> \<Longrightarrow> f x \<in> M"
  by (auto simp: fspace_def)

lemma bdd_above_dist:
  assumes f: "f \<in> fspace S" and g: "g \<in> fspace S" and "S \<noteq> {}"
  shows "bdd_above ((\<lambda>u. d (f u) (g u)) ` S)"
proof -
  obtain a where "a \<in> S"
    using \<open>S \<noteq> {}\<close> by blast
  obtain B x C y where "B>0"  and B: "f`S \<subseteq> mcball x B"
    and "C>0" and C: "g`S \<subseteq> mcball y C"
    using f g mbounded_pos by (auto simp: fspace_def)
  have "d (f u) (g u) \<le> B + d x y + C" if "u\<in>S" for u 
  proof -
    have "f u \<in> M"
      by (meson B image_eqI mbounded_mcball mbounded_subset_mspace subsetD that)
    have "g u \<in> M"
      by (meson C image_eqI mbounded_mcball mbounded_subset_mspace subsetD that)
    have "x \<in> M" "y \<in> M"
      using B C that by auto
    have "d (f u) (g u) \<le> d (f u) x + d x (g u)"
      by (simp add: \<open>f u \<in> M\<close> \<open>g u \<in> M\<close> \<open>x \<in> M\<close> triangle)
    also have "\<dots> \<le> d (f u) x + d x y + d y (g u)"
      by (simp add: \<open>f u \<in> M\<close> \<open>g u \<in> M\<close> \<open>x \<in> M\<close> \<open>y \<in> M\<close> triangle)
    also have "\<dots> \<le> B + d x y + C"
      using B C commute that by fastforce
    finally show ?thesis .
  qed
  then show ?thesis
    by (meson bdd_above.I2)
qed


lemma Metric_space_funspace: "Metric_space (fspace S) (fdist S)"
proof
  show *: "0 \<le> fdist S f g" for f g
    by (auto simp: fdist_def intro: cSUP_upper2 [OF bdd_above_dist])
  show "fdist S f g = fdist S g f" for f g
    by (auto simp: fdist_def commute)
  show "(fdist S f g = 0) = (f = g)"
    if fg: "f \<in> fspace S" "g \<in> fspace S" for f g
  proof
    assume 0: "fdist S f g = 0"
    show "f = g"
    proof (cases "S={}")
      case True
      with 0 that show ?thesis
        by (simp add: fdist_def fspace_def)
    next
      case False
      with 0 fg have Sup0: "(SUP x\<in>S. d (f x) (g x)) = 0"
        by (simp add: fdist_def)
      have "d (f x) (g x) = 0" if "x\<in>S" for x
          by (smt (verit) False Sup0 \<open>x\<in>S\<close> bdd_above_dist [OF fg] less_cSUP_iff nonneg)
      with fg show "f=g"
        by (simp add: fspace_def extensionalityI image_subset_iff)
    qed
  next
    show "f = g \<Longrightarrow> fdist S f g = 0"
      using fspace_in_M [OF \<open>g \<in> fspace S\<close>] by (auto simp: fdist_def)
  qed
  show "fdist S f h \<le> fdist S f g + fdist S g h"
    if fgh: "f \<in> fspace S" "g \<in> fspace S" "h \<in> fspace S" for f g h
  proof (clarsimp simp add: fdist_def that)
    assume "S \<noteq> {}"
    have dfh: "d (f x) (h x) \<le> d (f x) (g x) + d (g x) (h x)" if "x\<in>S" for x
      by (meson fgh fspace_in_M that triangle)
    have bdd_fgh: "bdd_above ((\<lambda>x. d (f x) (g x)) ` S)" "bdd_above ((\<lambda>x. d (g x) (h x)) ` S)"
      by (simp_all add: \<open>S \<noteq> {}\<close> bdd_above_dist that)
    then obtain B C where B: "\<And>x. x\<in>S \<Longrightarrow> d (f x) (g x) \<le> B" and C: "\<And>x. x\<in>S \<Longrightarrow> d (g x) (h x) \<le> C"
      by (auto simp: bdd_above_def)
    then have "\<And>x. x\<in>S \<Longrightarrow> d (f x) (g x) + d (g x) (h x) \<le> B+C"
      by force
    then have bdd: "bdd_above ((\<lambda>x. d (f x) (g x) + d (g x) (h x)) ` S)"
      by (auto simp: bdd_above_def)
    then have "(SUP x\<in>S. d (f x) (h x)) \<le> (SUP x\<in>S. d (f x) (g x) + d (g x) (h x))"
      by (metis (mono_tags, lifting) cSUP_mono \<open>S \<noteq> {}\<close> dfh)
    also have "\<dots> \<le> (SUP x\<in>S. d (f x) (g x)) + (SUP x\<in>S. d (g x) (h x))"
      by (simp add: \<open>S \<noteq> {}\<close> bdd cSUP_le_iff bdd_fgh add_mono cSup_upper)
    finally show "(SUP x\<in>S. d (f x) (h x)) \<le> (SUP x\<in>S. d (f x) (g x)) + (SUP x\<in>S. d (g x) (h x))" .
  qed
qed

end


definition funspace where
  "funspace S m \<equiv> metric (Metric_space.fspace (mspace m) (mdist m) S, 
                          Metric_space.fdist (mspace m) (mdist m) S)"

lemma mspace_funspace [simp]:
  "mspace (funspace S m) = Metric_space.fspace (mspace m) (mdist m) S"
  by (simp add: Metric_space.Metric_space_funspace Metric_space.mspace_metric funspace_def)

lemma mdist_funspace [simp]:
  "mdist (funspace S m) = Metric_space.fdist (mspace m) (mdist m) S"
  by (simp add: Metric_space.Metric_space_funspace Metric_space.mdist_metric funspace_def)

lemma funspace_imp_welldefined:
   "\<lbrakk>f \<in> mspace (funspace S m); x \<in> S\<rbrakk> \<Longrightarrow> f x \<in> mspace m"
  by (simp add: Metric_space.fspace_def subset_iff)

lemma funspace_imp_extensional:
   "f \<in> mspace (funspace S m) \<Longrightarrow> f \<in> extensional S"
  by (simp add: Metric_space.fspace_def)

lemma funspace_imp_bounded_image:
   "f \<in> mspace (funspace S m) \<Longrightarrow> Metric_space.mbounded (mspace m) (mdist m) (f ` S)"
  by (simp add: Metric_space.fspace_def)

lemma funspace_imp_bounded:
   "f \<in> mspace (funspace S m) \<Longrightarrow> S = {} \<or> (\<exists>c B. \<forall>x \<in> S. mdist m c (f x) \<le> B)"
  by (auto simp: Metric_space.fspace_def Metric_space.mbounded)


lemma (in Metric_space) funspace_imp_bounded2:
  assumes "f \<in> fspace S" "g \<in> fspace S"
  obtains B where "\<And>x. x \<in> S \<Longrightarrow> d (f x) (g x) \<le> B"
proof -
  have "mbounded (f ` S \<union> g ` S)"
    using mbounded_Un assms by (force simp: fspace_def)
  then show thesis
    by (metis UnCI imageI mbounded_alt that)
qed

lemma funspace_imp_bounded2:
  assumes "f \<in> mspace (funspace S m)" "g \<in> mspace (funspace S m)"
  obtains B where "\<And>x. x \<in> S \<Longrightarrow> mdist m (f x) (g x) \<le> B"
  by (metis Metric_space_mspace_mdist assms mspace_funspace Metric_space.funspace_imp_bounded2)

lemma (in Metric_space) funspace_mdist_le:
  assumes fg: "f \<in> fspace S" "g \<in> fspace S" and "S \<noteq> {}"
  shows "fdist S f g \<le> a \<longleftrightarrow> (\<forall>x \<in> S. d (f x) (g x) \<le> a)" 
    using assms bdd_above_dist [OF fg] by (simp add: fdist_def cSUP_le_iff)

lemma funspace_mdist_le:
  assumes "f \<in> mspace (funspace S m)" "g \<in> mspace (funspace S m)" and "S \<noteq> {}"
  shows "mdist (funspace S m) f g \<le> a \<longleftrightarrow> (\<forall>x \<in> S. mdist m (f x) (g x) \<le> a)" 
  using assms by (simp add: Metric_space.funspace_mdist_le)


lemma (in Metric_space) mcomplete_funspace:
  assumes "mcomplete"
  shows "mcomplete_of (funspace S Self)"
proof -
  interpret F: Metric_space "fspace S" "fdist S"
    by (simp add: Metric_space_funspace)
  show ?thesis
  proof (cases "S={}")
    case True
    then show ?thesis
      by (simp add: mcomplete_of_def mcomplete_trivial_singleton)
  next
    case False
    show ?thesis
    proof (clarsimp simp: mcomplete_of_def Metric_space.mcomplete_def)
      fix \<sigma>
      assume \<sigma>: "F.MCauchy \<sigma>"
      then have \<sigma>M: "\<And>n x. x \<in> S \<Longrightarrow> \<sigma> n x \<in> M"
        by (auto simp: F.MCauchy_def intro: fspace_in_M)
      have fdist_less: "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> fdist S (\<sigma> n) (\<sigma> n') < \<epsilon>" if "\<epsilon>>0" for \<epsilon>
        using \<sigma> that by (auto simp: F.MCauchy_def)
      have \<sigma>ext: "\<And>n. \<sigma> n \<in> extensional S"
        using \<sigma> unfolding F.MCauchy_def by (auto simp: fspace_def)
      have \<sigma>bd: "\<And>n. mbounded (\<sigma> n ` S)"
        using \<sigma> unfolding F.MCauchy_def by (simp add: fspace_def image_subset_iff)
      have \<sigma>in[simp]: "\<sigma> n \<in> fspace S" for n
        using F.MCauchy_def \<sigma> by blast
      have bd2: "\<And>n n'. \<exists>B. \<forall>x \<in> S. d (\<sigma> n x) (\<sigma> n' x) \<le> B"
        using \<sigma> unfolding F.MCauchy_def by (metis range_subsetD funspace_imp_bounded2)
      have sup: "\<And>n n' x0. x0 \<in> S \<Longrightarrow> d (\<sigma> n x0) (\<sigma> n' x0) \<le> Sup ((\<lambda>x. d (\<sigma> n x) (\<sigma> n' x)) ` S)"
      proof (rule cSup_upper)
        show "bdd_above ((\<lambda>x. d (\<sigma> n x) (\<sigma> n' x)) ` S)" if "x0 \<in> S" for n n' x0
          using that bd2 by (meson bdd_above.I2)
      qed auto
      have pcy: "MCauchy (\<lambda>n. \<sigma> n x)" if "x \<in> S" for x
        unfolding MCauchy_def
      proof (intro conjI strip)
        show "range (\<lambda>n. \<sigma> n x) \<subseteq> M"
          using \<sigma>M that by blast
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        then obtain N where N: "\<And>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> fdist S (\<sigma> n) (\<sigma> n') < \<epsilon>"
          using \<sigma> by (force simp: F.MCauchy_def)
        { fix n n'
          assume n: "N \<le> n" "N \<le> n'"
          have "d (\<sigma> n x) (\<sigma> n' x) \<le> (SUP x\<in>S. d (\<sigma> n x) (\<sigma> n' x))"
            using that sup by presburger
          then have "d (\<sigma> n x) (\<sigma> n' x) \<le> fdist S (\<sigma> n) (\<sigma> n')"
            by (simp add: fdist_def \<open>S \<noteq> {}\<close>)
          with N n have "d (\<sigma> n x) (\<sigma> n' x) < \<epsilon>"
            by fastforce
        } then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n x) (\<sigma> n' x) < \<epsilon>"
          by blast
      qed
      have "\<exists>l. limitin mtopology (\<lambda>n. \<sigma> n x) l sequentially" if "x \<in> S" for x
        using assms mcomplete_def pcy \<open>x \<in> S\<close> by presburger
      then obtain g0 where g0: "\<And>x. x \<in> S \<Longrightarrow> limitin mtopology (\<lambda>n. \<sigma> n x) (g0 x) sequentially"
        by metis
      define g where "g \<equiv> restrict g0 S"
      have gext: "g \<in> extensional S" 
       and glim: "\<And>x. x \<in> S \<Longrightarrow> limitin mtopology (\<lambda>n. \<sigma> n x) (g x) sequentially"
        by (auto simp: g_def g0)
      have gwd: "g x \<in> M" if "x \<in> S" for x
        using glim limitin_metric that by blast
      have unif: "\<exists>N. \<forall>x n. x \<in> S \<longrightarrow> N \<le> n \<longrightarrow> d (\<sigma> n x) (g x) < \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        obtain N where N: "\<And>n n'. N \<le> n \<and> N \<le> n' \<Longrightarrow> Sup ((\<lambda>x. d (\<sigma> n x) (\<sigma> n' x)) ` S) < \<epsilon>/2"
          using \<open>S\<noteq>{}\<close> \<open>\<epsilon>>0\<close> fdist_less [of "\<epsilon>/2"]
          by (metis (mono_tags) \<sigma>in fdist_def half_gt_zero) 
        show ?thesis
        proof (intro exI strip)
          fix x n
          assume "x \<in> S" and "N \<le> n"
          obtain N' where N': "\<And>n. N' \<le> n \<Longrightarrow> \<sigma> n x \<in> M \<and> d (\<sigma> n x) (g x) < \<epsilon>/2"
            by (metis \<open>0 < \<epsilon>\<close> \<open>x \<in> S\<close> glim half_gt_zero limit_metric_sequentially)
          have "d (\<sigma> n x) (g x) \<le> d (\<sigma> n x) (\<sigma> (max N N') x) + d (\<sigma> (max N N') x) (g x)"
            using \<open>x \<in> S\<close> \<sigma>M gwd triangle by presburger
          also have "\<dots> < \<epsilon>/2 + \<epsilon>/2"
            by (smt (verit) N N' \<open>N \<le> n\<close> \<open>x \<in> S\<close> max.cobounded1 max.cobounded2 sup)
          finally show "d (\<sigma> n x) (g x) < \<epsilon>" by simp
        qed
      qed
      have "limitin F.mtopology \<sigma> g sequentially"
        unfolding F.limit_metric_sequentially
      proof (intro conjI strip)
        obtain N where N: "\<And>n n'. N \<le> n \<and> N \<le> n' \<Longrightarrow> Sup ((\<lambda>x. d (\<sigma> n x) (\<sigma> n' x)) ` S) < 1"
          using fdist_less [of 1] \<open>S\<noteq>{}\<close> by (auto simp: fdist_def)
        have "\<And>x. x \<in> \<sigma> N ` S \<Longrightarrow> x \<in> M"
          using \<sigma>M by blast
        obtain a B where "a \<in> M" and B: "\<And>x. x \<in> (\<sigma> N) ` S \<Longrightarrow> d a x \<le> B"
          by (metis False \<sigma>M \<sigma>bd ex_in_conv imageI mbounded_alt_pos)
        have "d a (g x) \<le> B+1" if "x\<in>S" for x
        proof -
          have "d a (g x) \<le> d a (\<sigma> N x) + d (\<sigma> N x) (g x)"
            by (simp add: \<open>a \<in> M\<close> \<sigma>M gwd that triangle)
          also have "\<dots> \<le> B+1"
          proof -
            have "d a (\<sigma> N x) \<le> B"
              by (simp add: B that)
            moreover 
            have False if 1: "d (\<sigma> N x) (g x) > 1"
            proof -
              obtain r where "1 < r" and r: "r < d (\<sigma> N x) (g x)"
                using 1 dense by blast
              then obtain N' where N': "\<And>n. N' \<le> n \<Longrightarrow> \<sigma> n x \<in> M \<and> d (\<sigma> n x) (g x) < r-1"
                using glim [OF \<open>x\<in>S\<close>] by (fastforce simp: limit_metric_sequentially)
              have "d (\<sigma> N x) (g x) \<le> d (\<sigma> N x) (\<sigma> (max N N') x) + d (\<sigma> (max N N') x) (g x)"
                by (metis \<open>x \<in> S\<close> \<sigma>M commute gwd triangle')
              also have "\<dots> < 1 + (r-1)"
                by (smt (verit) N N' \<open>x \<in> S\<close> max.cobounded1 max.cobounded2 max.idem sup)
              finally have "d (\<sigma> N x) (g x) < r"
                by simp
              with r show False
                by linarith
            qed
            ultimately show ?thesis
              by force
          qed
          finally show ?thesis .
        qed
        with gwd \<open>a \<in> M\<close> have "mbounded (g ` S)"
          unfolding mbounded by blast
        with gwd gext show "g \<in> fspace S"
          by (auto simp: fspace_def)
        fix \<epsilon>::real
        assume "\<epsilon>>0"
        then obtain N where "\<And>x n. x \<in> S \<Longrightarrow> N \<le> n \<Longrightarrow> d (\<sigma> n x) (g x) < \<epsilon>/2"
          by (meson unif half_gt_zero)
        then have "fdist S (\<sigma> n) g \<le> \<epsilon>/2" if "N \<le> n" for n
          using \<open>g \<in> fspace S\<close> False that
          by (force simp: funspace_mdist_le simp del: divide_const_simps)
        then show "\<exists>N. \<forall>n\<ge>N. \<sigma> n \<in> fspace S \<and> fdist S (\<sigma> n) g < \<epsilon>"
          by (metis \<open>0 < \<epsilon>\<close> \<sigma>in add_strict_increasing field_sum_of_halves half_gt_zero)
      qed
      then show "\<exists>x. limitin F.mtopology \<sigma> x sequentially"
        by blast 
    qed
  qed
qed



subsection\<open>Metric space of continuous bounded functions\<close>

definition cfunspace where
  "cfunspace X m \<equiv> submetric (funspace (topspace X) m) {f. continuous_map X (mtopology_of m) f}"

lemma mspace_cfunspace [simp]:
  "mspace (cfunspace X m) = 
     {f. f \<in> topspace X \<rightarrow> mspace m \<and> f \<in> extensional (topspace X) \<and>
         Metric_space.mbounded (mspace m) (mdist m) (f ` (topspace X)) \<and>
         continuous_map X (mtopology_of m) f}"
  by (auto simp: cfunspace_def Metric_space.fspace_def)

lemma mdist_cfunspace_eq_mdist_funspace:
  "mdist (cfunspace X m) = mdist (funspace (topspace X) m)"
  by (auto simp: cfunspace_def)

lemma cfunspace_subset_funspace:
   "mspace (cfunspace X m) \<subseteq> mspace (funspace (topspace X) m)"
  by (simp add: cfunspace_def)

lemma cfunspace_mdist_le:
   "\<lbrakk>f \<in> mspace (cfunspace X m); g \<in> mspace (cfunspace X m); topspace X \<noteq> {}\<rbrakk>
     \<Longrightarrow> mdist (cfunspace X m) f g \<le> a \<longleftrightarrow> (\<forall>x \<in> topspace X. mdist m (f x) (g x) \<le> a)"
  by (simp add: cfunspace_def Metric_space.funspace_mdist_le)

lemma cfunspace_imp_bounded2:
  assumes "f \<in> mspace (cfunspace X m)" "g \<in> mspace (cfunspace X m)"
  obtains B where "\<And>x. x \<in> topspace X \<Longrightarrow> mdist m (f x) (g x) \<le> B"
  by (metis assms all_not_in_conv cfunspace_mdist_le nle_le)

lemma cfunspace_mdist_lt:
   "\<lbrakk>compactin X (topspace X); f \<in> mspace (cfunspace X m);
     g \<in> mspace (cfunspace X m); mdist (cfunspace X m) f g < a;
     x \<in> topspace X\<rbrakk>
     \<Longrightarrow> mdist m (f x) (g x) < a"
  by (metis (full_types) cfunspace_mdist_le empty_iff less_eq_real_def less_le_not_le)

lemma mdist_cfunspace_le:
  assumes "0 \<le> B" and B: "\<And>x. x \<in> topspace X \<Longrightarrow> mdist m (f x) (g x) \<le> B"
  shows "mdist (cfunspace X m) f g \<le> B"
proof (cases "X = trivial_topology")
  case True
  then show ?thesis
    by (simp add: Metric_space.fdist_empty \<open>B\<ge>0\<close> cfunspace_def)
next
  case False
  have bdd: "bdd_above ((\<lambda>u. mdist m (f u) (g u)) ` topspace X)"
    by (meson B bdd_above.I2)
  with assms bdd show ?thesis
    by (simp add: mdist_cfunspace_eq_mdist_funspace Metric_space.fdist_def cSUP_le_iff)
qed


lemma mdist_cfunspace_imp_mdist_le:
   "\<lbrakk>f \<in> mspace (cfunspace X m); g \<in> mspace (cfunspace X m);
     mdist (cfunspace X m) f g \<le> a; x \<in> topspace X\<rbrakk> \<Longrightarrow> mdist m (f x) (g x) \<le> a"
  using cfunspace_mdist_le by blast

lemma compactin_mspace_cfunspace:
   "compactin X (topspace X)
     \<Longrightarrow> mspace (cfunspace X m) =
          {f. (\<forall>x \<in> topspace X. f x \<in> mspace m) \<and>
               f \<in> extensional (topspace X) \<and>
               continuous_map X (mtopology_of m) f}"
  by (auto simp: Metric_space.compactin_imp_mbounded image_compactin mtopology_of_def) 

lemma (in Metric_space) mcomplete_cfunspace:
  assumes "mcomplete"
  shows "mcomplete_of (cfunspace X Self)"
proof -
  interpret F: Metric_space "fspace (topspace X)" "fdist (topspace X)"
    by (simp add: Metric_space_funspace)
  interpret S: Submetric "fspace (topspace X)" "fdist (topspace X)" "mspace (cfunspace X Self)"
  proof
    show "mspace (cfunspace X Self) \<subseteq> fspace (topspace X)"
      by (metis cfunspace_subset_funspace mdist_Self mspace_Self mspace_funspace)
  qed
  show ?thesis
  proof (cases "X = trivial_topology")
    case True
    then show ?thesis
      by (simp add: mcomplete_of_def mcomplete_trivial_singleton mdist_cfunspace_eq_mdist_funspace cong: conj_cong)
  next
    case False
    have *: "continuous_map X mtopology g"
      if "range \<sigma> \<subseteq> mspace (cfunspace X Self)"
        and g: "limitin F.mtopology \<sigma> g sequentially" for \<sigma> g
      unfolding continuous_map_to_metric
    proof (intro strip)
      have \<sigma>: "\<And>n. continuous_map X mtopology (\<sigma> n)"
        using that by (auto simp: mtopology_of_def)
      fix x and \<epsilon>::real
      assume "x \<in> topspace X" and "0 < \<epsilon>"
      then obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> \<sigma> n \<in> fspace (topspace X) \<and> fdist (topspace X) (\<sigma> n) g < \<epsilon>/3"
        unfolding mtopology_of_def F.limitin_metric
        by (metis F.limit_metric_sequentially divide_pos_pos g zero_less_numeral) 
      then obtain U where "openin X U" "x \<in> U" 
        and U: "\<And>y. y \<in> U \<Longrightarrow> \<sigma> N y \<in> mball (\<sigma> N x) (\<epsilon>/3)"
        by (metis Metric_space.continuous_map_to_metric Metric_space_axioms \<open>0 < \<epsilon>\<close> \<open>x \<in> topspace X\<close> \<sigma> divide_pos_pos zero_less_numeral)
      moreover
      have "g y \<in> mball (g x) \<epsilon>" if "y\<in>U" for y
      proof -
        have "U \<subseteq> topspace X"
          using \<open>openin X U\<close> by (simp add: openin_subset)
        have gx: "g x \<in> M"
          by (meson F.limitin_mspace \<open>x \<in> topspace X\<close> fspace_in_M g)
        have "y \<in> topspace X"
          using \<open>U \<subseteq> topspace X\<close> that by auto
        have gy: "g y \<in> M"
          by (meson F.limitin_mspace[OF g] \<open>U \<subseteq> topspace X\<close> fspace_in_M subsetD that)
        have "d (g x) (g y) < \<epsilon>"
        proof -
          have *: "d (\<sigma> N x0) (g x0) \<le> \<epsilon>/3" if "x0 \<in> topspace X" for x0
          proof -
            have "g \<in> fspace (topspace X)"
              using F.limit_metric_sequentially g by blast
            with N that have "bdd_above ((\<lambda>x. d (\<sigma> N x) (g x)) ` topspace X)"
              by (force intro: bdd_above_dist)
            then have "d (\<sigma> N x0) (g x0) \<le> Sup ((\<lambda>x. d (\<sigma> N x) (g x)) ` topspace X)"
              by (simp add: cSup_upper that)
            also have "\<dots> \<le> \<epsilon>/3"
              using g False N \<open>g \<in> fspace (topspace X)\<close> 
                by (fastforce simp: F.limit_metric_sequentially fdist_def)
            finally show ?thesis .
          qed
          have "d (g x) (g y) \<le> d (g x) (\<sigma> N x) + d (\<sigma> N x) (g y)"
            using U gx gy that triangle by force
          also have "\<dots> < \<epsilon>/3 + \<epsilon>/3 + \<epsilon>/3"
            by (smt (verit) "*" U gy \<open>x \<in> topspace X\<close> \<open>y \<in> topspace X\<close> commute in_mball that triangle)
          finally show ?thesis by simp
        qed
        with gx gy show ?thesis by simp
      qed
      ultimately show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. g y \<in> mball (g x) \<epsilon>)"
        by blast
    qed

    have "S.sub.mcomplete"
    proof (rule S.sequentially_closedin_mcomplete_imp_mcomplete)
      show "F.mcomplete"
        by (metis assms mcomplete_funspace mcomplete_of_def mdist_Self mdist_funspace mspace_Self mspace_funspace)
      fix \<sigma> g
      assume g: "range \<sigma> \<subseteq> mspace (cfunspace X Self) \<and> limitin F.mtopology \<sigma> g sequentially"
      show "g \<in> mspace (cfunspace X Self)"
      proof (simp add: mtopology_of_def, intro conjI)
        show "g \<in> topspace X \<rightarrow> M" "g \<in> extensional (topspace X)" "mbounded (g ` topspace X)"
          using g F.limitin_mspace by (force simp: fspace_def)+
        show "continuous_map X mtopology g"
          using * g by blast
      qed
    qed
    then show ?thesis
      by (simp add: mcomplete_of_def mdist_cfunspace_eq_mdist_funspace)
  qed
qed


subsection\<open>Existence of completion for any metric space M as a subspace of M=>R\<close>

lemma (in Metric_space) metric_completion_explicit:
  obtains f :: "['a,'a] \<Rightarrow> real" and S where
      "S \<subseteq> mspace(funspace M euclidean_metric)"
      "mcomplete_of (submetric (funspace M euclidean_metric) S)"
      "f \<in> M \<rightarrow> S"
      "mtopology_of(funspace M euclidean_metric) closure_of f ` M = S"
      "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk>
            \<Longrightarrow> mdist (funspace M euclidean_metric) (f x) (f y) = d x y"
proof -
  define m':: "('a\<Rightarrow>real) metric" where "m' \<equiv> funspace M euclidean_metric"
  show thesis
  proof (cases "M = {}")
    case True
    then show ?thesis
      using that by (simp add: mcomplete_of_def mcomplete_trivial)
  next
    case False
    then obtain a where "a \<in> M"
      by auto
    define f where "f \<equiv> \<lambda>x. (\<lambda>u \<in> M. d x u - d a u)"
    define S where "S \<equiv> mtopology_of(funspace M euclidean_metric) closure_of (f ` M)"
    interpret S: Submetric "Met_TC.fspace M" "Met_TC.fdist M" "S \<inter> Met_TC.fspace M"
      by (simp add: Met_TC.Metric_space_funspace Submetric.intro Submetric_axioms_def)

    have fim: "f ` M \<subseteq> mspace m'"
    proof (clarsimp simp: m'_def Met_TC.fspace_def)
      fix b
      assume "b \<in> M"
      then have "\<And>c. \<lbrakk>c \<in> M\<rbrakk> \<Longrightarrow> \<bar>d b c - d a c\<bar> \<le> d a b"
        by (smt (verit, best) \<open>a \<in> M\<close> commute triangle'')
      then have "(\<lambda>x. d b x - d a x) ` M \<subseteq> cball 0 (d a b)"
        by force
      then show "f b \<in> extensional M \<and> bounded (f b ` M)"
        by (metis bounded_cball bounded_subset f_def image_restrict_eq restrict_extensional_sub set_eq_subset)
    qed
    show thesis
    proof
      show "S \<subseteq> mspace (funspace M euclidean_metric)"
        by (simp add: S_def in_closure_of subset_iff)
      have "closedin S.mtopology (S \<inter> Met_TC.fspace M)"
        by (simp add: S_def closedin_Int funspace_def)
      moreover have "S.mcomplete"
        using Metric_space.mcomplete_funspace Met_TC.Metric_space_axioms by (fastforce simp: mcomplete_of_def)
      ultimately show "mcomplete_of (submetric (funspace M euclidean_metric) S)"
        by (simp add: S.closedin_eq_mcomplete mcomplete_of_def)
      show "f \<in> M \<rightarrow> S"
        using S_def fim in_closure_of m'_def by fastforce
      show "mtopology_of (funspace M euclidean_metric) closure_of f ` M = S"
        by (auto simp: f_def S_def mtopology_of_def)
      show "mdist (funspace M euclidean_metric) (f x) (f y) = d x y"
        if "x \<in> M" "y \<in> M" for x y
      proof -
        have "\<forall>c\<in>M. dist (f x c) (f y c) \<le> r \<Longrightarrow> d x y \<le> r" for r
          using that by (auto simp: f_def dist_real_def)
        moreover have "dist (f x z) (f y z) \<le> r" if "d x y \<le> r" and "z \<in> M" for r z
          using that \<open>x \<in> M\<close> \<open>y \<in> M\<close>  
          apply (simp add: f_def Met_TC.fdist_def dist_real_def)
          by (smt (verit, best) commute triangle')
        ultimately have "(SUP c \<in> M. dist (f x c) (f y c)) = d x y"
          by (intro cSup_unique) auto
        with that fim show ?thesis
          using that fim by (simp add: Met_TC.fdist_def False m'_def image_subset_iff)
      qed
    qed
  qed
qed


lemma (in Metric_space) metric_completion:
  obtains f :: "['a,'a] \<Rightarrow> real" and m' where
    "mcomplete_of m'"
    "f \<in> M \<rightarrow> mspace m' "
    "mtopology_of m' closure_of f ` M = mspace m'"
    "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
proof -
  obtain f :: "['a,'a] \<Rightarrow> real" and S where
    Ssub: "S \<subseteq> mspace(funspace M euclidean_metric)"
    and mcom: "mcomplete_of (submetric (funspace M euclidean_metric) S)"
    and fim: "f \<in> M \<rightarrow> S"
    and eqS: "mtopology_of(funspace M euclidean_metric) closure_of f ` M = S"
    and eqd: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist (funspace M euclidean_metric) (f x) (f y) = d x y"
    using metric_completion_explicit by metis
  define m' where "m' \<equiv> submetric (funspace M euclidean_metric) S"
  show thesis
  proof
    show "mcomplete_of m'"
      by (simp add: mcom m'_def)
    show "f \<in> M \<rightarrow> mspace m'"
      using Ssub fim m'_def by auto
    show "mtopology_of m' closure_of f ` M = mspace m'"
      using eqS fim Ssub
      by (force simp: m'_def mtopology_of_submetric closure_of_subtopology Int_absorb1 image_subset_iff_funcset)
    show "mdist m' (f x) (f y) = d x y" if "x \<in> M" and "y \<in> M" for x y
      using that eqd m'_def by force 
  qed 
qed

lemma metrizable_space_completion:
  assumes "metrizable_space X"
  obtains f :: "['a,'a] \<Rightarrow> real" and Y where
       "completely_metrizable_space Y" "embedding_map X Y f"
                "Y closure_of (f ` (topspace X)) = topspace Y"
proof -
  obtain M d where "Metric_space M d" and Xeq: "X = Metric_space.mtopology M d"
    using assms metrizable_space_def by blast
  then interpret Metric_space M d by simp
  obtain f :: "['a,'a] \<Rightarrow> real" and m' where
    "mcomplete_of m'"
    and fim: "f \<in> M \<rightarrow> mspace m' "
    and m': "mtopology_of m' closure_of f ` M = mspace m'"
    and eqd: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
    by (metis metric_completion)
  show thesis
  proof
    show "completely_metrizable_space (mtopology_of m')"
      using \<open>mcomplete_of m'\<close>
      unfolding completely_metrizable_space_def mcomplete_of_def mtopology_of_def
      by (metis Metric_space_mspace_mdist)
    show "embedding_map X (mtopology_of m') f"
      using Metric_space12.isometry_imp_embedding_map
      by (metis Metric_space12_def Metric_space_axioms Metric_space_mspace_mdist Xeq eqd fim 
             mtopology_of_def)
    show "(mtopology_of m') closure_of f ` topspace X = topspace (mtopology_of m')"
      by (simp add: Xeq m')
  qed
qed


subsection\<open>Contractions\<close>

lemma (in Metric_space) contraction_imp_unique_fixpoint:
  assumes "f x = x" "f y = y"
    and "f \<in> M \<rightarrow> M"
    and "k < 1"
    and "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d (f x) (f y) \<le> k * d x y"
    and "x \<in> M" "y \<in> M"
  shows "x = y"
  by (smt (verit, ccfv_SIG) mdist_pos_less mult_le_cancel_right1 assms)

text \<open>Banach Fixed-Point Theorem (aka, Contraction Mapping Principle)\<close>
lemma (in Metric_space) Banach_fixedpoint_thm:
  assumes mcomplete and "M \<noteq> {}" and fim: "f \<in> M \<rightarrow> M"    
    and "k < 1"
    and con: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d (f x) (f y) \<le> k * d x y"
  obtains x where "x \<in> M" "f x = x"
proof -
  obtain a where "a \<in> M"
    using \<open>M \<noteq> {}\<close> by blast
  show thesis
  proof (cases "\<forall>x \<in> M. f x = f a")
    case True
    then show ?thesis
      by (metis \<open>a \<in> M\<close> fim image_subset_iff image_subset_iff_funcset that)
  next
    case False
    then obtain b where "b \<in> M" and b: "f b \<noteq> f a"
      by blast
    have "k>0"
      using Lipschitz_coefficient_pos [where f=f]
      by (metis False \<open>a \<in> M\<close> con fim mdist_Self mspace_Self)
    define \<sigma> where "\<sigma> \<equiv> \<lambda>n. (f^^n) a"
    have f_iter: "\<sigma> n \<in> M" for n
      unfolding \<sigma>_def by (induction n) (use \<open>a \<in> M\<close> fim in auto)
    show ?thesis
    proof (cases "f a = a")
      case True
      then show ?thesis
        using \<open>a \<in> M\<close> that by blast
    next
      case False
      have "MCauchy \<sigma>"
      proof -
        show ?thesis
          unfolding MCauchy_def
        proof (intro conjI strip)
          show "range \<sigma> \<subseteq> M"
            using f_iter by blast
          fix \<epsilon>::real
          assume "\<epsilon>>0"
          with \<open>k < 1\<close> \<open>f a \<noteq> a\<close> \<open>a \<in> M\<close> fim have gt0: "((1 - k) * \<epsilon>) / d a (f a) > 0"
            by (fastforce simp: divide_simps Pi_iff)
          obtain N where "k^N < ((1-k) * \<epsilon>) / d a (f a)"
            using real_arch_pow_inv [OF gt0 \<open>k < 1\<close>] by blast
          then have N: "\<And>n. n \<ge> N \<Longrightarrow> k^n < ((1-k) * \<epsilon>) / d a (f a)"
            by (smt (verit) \<open>0 < k\<close> assms(4) power_decreasing)
          have "\<forall>n n'. n<n' \<longrightarrow> N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
          proof (intro exI strip)
            fix n n'
            assume "n<n'" "N \<le> n" "N \<le> n'"
            have "d (\<sigma> n) (\<sigma> n') \<le> (\<Sum>i=n..<n'. d (\<sigma> i) (\<sigma> (Suc i)))"
            proof -
              have "n < m \<Longrightarrow> d (\<sigma> n) (\<sigma> m) \<le> (\<Sum>i=n..<m. d (\<sigma> i) (\<sigma> (Suc i)))" for m
              proof (induction m)
                case 0
                then show ?case
                  by simp
              next
                case (Suc m)
                then consider "n<m" | "m=n"
                  by linarith
                then show ?case
                proof cases
                  case 1
                  have "d (\<sigma> n) (\<sigma> (Suc m)) \<le> d (\<sigma> n) (\<sigma> m) + d (\<sigma> m) (\<sigma> (Suc m))"
                    by (simp add: f_iter triangle)
                  also have "\<dots> \<le> (\<Sum>i=n..<m. d (\<sigma> i) (\<sigma> (Suc i))) + d (\<sigma> m) (\<sigma> (Suc m))"
                    using Suc 1 by linarith
                  also have "\<dots> = (\<Sum>i = n..<Suc m. d (\<sigma> i) (\<sigma> (Suc i)))"
                    using "1" by force
                  finally show ?thesis .
                qed auto
              qed
              with \<open>n < n'\<close> show ?thesis by blast
            qed
            also have "\<dots> \<le> (\<Sum>i=n..<n'. d a (f a) * k^i)"
            proof (rule sum_mono)
              fix i
              assume "i \<in> {n..<n'}"
              show "d (\<sigma> i) (\<sigma> (Suc i)) \<le> d a (f a) * k ^ i"
              proof (induction i)
                case 0
                then show ?case
                  by (auto simp: \<sigma>_def)
              next
                case (Suc i)
                have "d (\<sigma> (Suc i)) (\<sigma> (Suc (Suc i))) \<le> k * d (\<sigma> i) (\<sigma> (Suc i))"
                  using con \<sigma>_def f_iter fim by fastforce
                also have "\<dots> \<le> d a (f a) * k ^ Suc i"
                  using Suc \<open>0 < k\<close> by auto
                finally show ?case .
              qed
            qed
            also have "\<dots> = d a (f a) * (\<Sum>i=n..<n'. k^i)"
              by (simp add: sum_distrib_left)
            also have "\<dots> = d a (f a) * (\<Sum>i=0..<n'-n. k^(i+n))"
              using sum.shift_bounds_nat_ivl [of "power k" 0 n "n'-n"] \<open>n < n'\<close> by simp
            also have "\<dots> = d a (f a) * k^n * (\<Sum>i<n'-n. k^i)"
              by (simp add: power_add lessThan_atLeast0 flip: sum_distrib_right)
            also have "\<dots> = d a (f a) * (k ^ n - k ^ n') / (1 - k)"
              using \<open>k < 1\<close> \<open>n < n'\<close> apply (simp add: sum_gp_strict)
              by (simp add: algebra_simps flip: power_add)
            also have "\<dots> < \<epsilon>"
              using N \<open>k < 1\<close> \<open>0 < \<epsilon>\<close> \<open>0 < k\<close> \<open>N \<le> n\<close>
              apply (simp add: field_simps)
              by (smt (verit) nonneg pos_less_divide_eq zero_less_divide_iff zero_less_power)
            finally show "d (\<sigma> n) (\<sigma> n') < \<epsilon>" .
          qed 
          then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
            by (metis \<open>0 < \<epsilon>\<close> commute f_iter linorder_not_le local.mdist_zero nat_less_le)
        qed
      qed
      then obtain l where l: "limitin mtopology \<sigma> l sequentially"
        using \<open>mcomplete\<close> mcomplete_def by blast
      show ?thesis 
      proof
        show "l \<in> M"
          using l limitin_mspace by blast
        show "f l = l"
        proof (rule limitin_metric_unique)
          have "limitin mtopology (f \<circ> \<sigma>) (f l) sequentially"
          proof (rule continuous_map_limit)
            have "Lipschitz_continuous_map Self Self f"
              using con by (auto simp: Lipschitz_continuous_map_def fim)
            then show "continuous_map mtopology mtopology f"
              using Lipschitz_continuous_imp_continuous_map Self_def by force
          qed (use l in auto)
          moreover have "(f \<circ> \<sigma>) = (\<lambda>i. \<sigma>(i+1))"
            by (auto simp: \<sigma>_def)
          ultimately show "limitin mtopology (\<lambda>n. (f^^n)a) (f l) sequentially"
            using limitin_sequentially_offset_rev [of mtopology \<sigma> 1]
            by (simp add: \<sigma>_def)
        qed (use l in \<open>auto simp: \<sigma>_def\<close>)
      qed
    qed
  qed
qed


subsection\<open> The Baire Category Theorem\<close>

text \<open>Possibly relevant to the theorem "Baire" in Elementary Normed Spaces\<close>

lemma (in Metric_space) metric_Baire_category:
  assumes "mcomplete" "countable \<G>"
  and "\<And>T. T \<in> \<G> \<Longrightarrow> openin mtopology T \<and> mtopology closure_of T = M"
shows "mtopology closure_of \<Inter>\<G> = M"
proof (cases "\<G>={}")
  case False
  then obtain U :: "nat \<Rightarrow> 'a set" where U: "range U = \<G>"
    by (metis \<open>countable \<G>\<close> uncountable_def)
  with assms have u_open: "\<And>n. openin mtopology (U n)" and u_dense: "\<And>n. mtopology closure_of (U n) = M"
    by auto
  have "\<Inter>(range U) \<inter> W \<noteq> {}" if W: "openin mtopology W" "W \<noteq> {}" for W
  proof -
    have "W \<subseteq> M"
      using openin_mtopology W by blast
    have "\<exists>r' x'. 0 < r' \<and> r' < r/2 \<and> x' \<in> M \<and> mcball x' r' \<subseteq> mball x r \<inter> U n" 
      if "r>0" "x \<in> M" for x r n
    proof -
      obtain z where z: "z \<in> U n \<inter> mball x r"
        using u_dense [of n] \<open>r>0\<close> \<open>x \<in> M\<close>
        by (metis dense_intersects_open centre_in_mball_iff empty_iff openin_mball topspace_mtopology equals0I)
      then have "z \<in> M" by auto
      have "openin mtopology (U n \<inter> mball x r)"
        by (simp add: openin_Int u_open)
      with \<open>z \<in> M\<close> z obtain e where "e>0" and e: "mcball z e \<subseteq> U n \<inter> mball x r"
        by (meson openin_mtopology_mcball)
      define r' where "r' \<equiv> min e (r/4)"
      show ?thesis
      proof (intro exI conjI)
        show "0 < r'" "r' < r / 2" "z \<in> M"
          using \<open>e>0\<close> \<open>r>0\<close> \<open>z \<in> M\<close> by (auto simp: r'_def)
        show "mcball z r' \<subseteq> mball x r \<inter> U n"
          using Metric_space.mcball_subset_concentric e r'_def by auto
      qed
    qed
    then obtain nextr nextx 
      where nextr: "\<And>r x n. \<lbrakk>r>0; x\<in>M\<rbrakk> \<Longrightarrow> 0 < nextr r x n \<and> nextr r x n < r/2"
        and nextx: "\<And>r x n. \<lbrakk>r>0; x\<in>M\<rbrakk> \<Longrightarrow> nextx r x n \<in> M"
        and nextsub: "\<And>r x n. \<lbrakk>r>0; x\<in>M\<rbrakk> \<Longrightarrow> mcball (nextx r x n) (nextr r x n) \<subseteq> mball x r \<inter> U n"
      by metis
    obtain x0 where x0: "x0 \<in> U 0 \<inter> W"
      by (metis W dense_intersects_open topspace_mtopology all_not_in_conv u_dense)
    then have "x0 \<in> M"
      using \<open>W \<subseteq> M\<close> by fastforce
    obtain r0 where "0 < r0" "r0 < 1" and sub: "mcball x0 r0 \<subseteq> U 0 \<inter> W"
    proof -
      have "openin mtopology (U 0 \<inter> W)"
        using W u_open by blast
      then obtain r where "r>0" and r: "mball x0 r \<subseteq> U 0" "mball x0 r \<subseteq> W"
        by (meson Int_subset_iff openin_mtopology x0)
      define r0 where "r0 \<equiv> (min r 1) / 2"
      show thesis
      proof
        show "0 < r0" "r0 < 1"
          using \<open>r>0\<close> by (auto simp: r0_def)
        show "mcball x0 r0 \<subseteq> U 0 \<inter> W"
          using r \<open>0 < r0\<close> r0_def by auto
      qed
    qed
    define b where "b \<equiv> rec_nat (x0,r0) (\<lambda>n (x,r). (nextx r x n, nextr r x n))"
    have b0[simp]: "b 0 = (x0,r0)"
      by (simp add: b_def)
    have bSuc[simp]: "b (Suc n) = (let (x,r) = b n in (nextx r x n, nextr r x n))" for n
      by (simp add: b_def)
    define xf where "xf \<equiv> fst \<circ> b"
    define rf where "rf \<equiv> snd \<circ> b"
    have rfxf: "0 < rf n \<and> xf n \<in> M" for n
    proof (induction n)
      case 0
      with \<open>0 < r0\<close> \<open>x0 \<in> M\<close> show ?case 
        by (auto simp: rf_def xf_def)
    next
      case (Suc n)
      then show ?case
        by (auto simp: rf_def xf_def case_prod_unfold nextr nextx Let_def)
    qed
    have mcball_sub: "mcball (xf (Suc n)) (rf (Suc n)) \<subseteq> mball (xf n) (rf n) \<inter> U n" for n
      using rfxf nextsub by (auto simp: xf_def rf_def case_prod_unfold Let_def)
    have half: "rf (Suc n) < rf n / 2" for n
      using rfxf nextr by (auto simp: xf_def rf_def case_prod_unfold Let_def)
    then have "decseq rf"
      using rfxf by (smt (verit, ccfv_threshold) decseq_SucI field_sum_of_halves)
    have nested: "mball (xf n) (rf n) \<subseteq> mball (xf m) (rf m)" if "m \<le> n" for m n
      using that
    proof (induction n)
      case (Suc n)
      then show ?case
        by (metis mcball_sub order.trans inf.boundedE le_Suc_eq mball_subset_mcball order.refl)
    qed auto
    have "MCauchy xf"
      unfolding MCauchy_def
    proof (intro conjI strip)
      show "range xf \<subseteq> M"
        using rfxf by blast
      fix \<epsilon> :: real
      assume "\<epsilon>>0"
      then obtain N where N: "inverse (2^N) < \<epsilon>"
        using real_arch_pow_inv by (force simp flip: power_inverse)
      have "d (xf n) (xf n') < \<epsilon>" if "n \<le> n'" "N \<le> n" "N \<le> n'" for n n'
      proof -           
        have *: "rf n < inverse (2 ^ n)" for n
        proof (induction n)
          case 0
          then show ?case
            by (simp add: \<open>r0 < 1\<close> rf_def)
        next
          case (Suc n)
          with half show ?case
            by simp (smt (verit))
        qed
        have "rf n \<le> rf N"
          using \<open>decseq rf\<close> \<open>N \<le> n\<close> by (simp add: decseqD)
        moreover
        have "xf n' \<in> mball (xf n) (rf n)"
          using nested rfxf \<open>n \<le> n'\<close> by blast
        ultimately have "d (xf n) (xf n') < rf N"
          by auto
        also have "\<dots> < \<epsilon>"
          using "*" N order.strict_trans by blast
        finally show ?thesis .
      qed
      then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (xf n) (xf n') < \<epsilon>"
        by (metis commute linorder_le_cases)
    qed
    then obtain l where l: "limitin mtopology xf l sequentially"
      using \<open>mcomplete\<close> mcomplete_alt by blast
    have l_in: "l \<in> mcball (xf n) (rf n)" for n
    proof -
      have "\<forall>\<^sub>F m in sequentially. xf m \<in> mcball (xf n) (rf n)"
        unfolding eventually_sequentially
        by (meson nested rfxf centre_in_mball_iff mball_subset_mcball subset_iff)
      with l limitin_closedin show ?thesis
        by (metis closedin_mcball trivial_limit_sequentially)
    qed
    then have "\<And>n. l \<in> U n"
      using mcball_sub by blast
    moreover have "l \<in> W"
      using l_in[of 0] sub  by (auto simp: xf_def rf_def)
    ultimately show ?thesis by auto
  qed
  with U show ?thesis
    by (metis dense_intersects_open topspace_mtopology)
qed auto



lemma (in Metric_space) metric_Baire_category_alt:
  assumes "mcomplete" "countable \<G>"
    and empty: "\<And>T. T \<in> \<G> \<Longrightarrow> closedin mtopology T \<and> mtopology interior_of T = {}"
  shows "mtopology interior_of \<Union>\<G> = {}"
proof -
  have *: "mtopology closure_of \<Inter>((-)M ` \<G>) = M"
  proof (intro metric_Baire_category conjI \<open>mcomplete\<close>)
    show "countable ((-) M ` \<G>)"
      using \<open>countable \<G>\<close> by blast
    fix T
    assume "T \<in> (-) M ` \<G>"
    then obtain U where U: "U \<in> \<G>" "T = M-U" "U \<subseteq> M"
      using empty metric_closedin_iff_sequentially_closed by force
    with empty show "openin mtopology T" by blast
    show "mtopology closure_of T = M"
      using U by (simp add: closure_of_interior_of double_diff empty)
  qed
  with closure_of_eq show ?thesis
    by (fastforce simp: interior_of_closure_of split: if_split_asm)
qed


text \<open>Since all locally compact Hausdorff spaces are regular, the disjunction in the HOL Light version is redundant.\<close>
lemma Baire_category_aux:
  assumes "locally_compact_space X" "regular_space X" 
    and "countable \<G>"
    and empty: "\<And>G. G \<in> \<G> \<Longrightarrow> closedin X G \<and> X interior_of G = {}"
  shows "X interior_of \<Union>\<G> = {}"
proof (cases "\<G> = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  then obtain T :: "nat \<Rightarrow> 'a set" where T: "\<G> = range T"
    by (metis \<open>countable \<G>\<close> uncountable_def)
  with empty have Tempty: "\<And>n. X interior_of (T n) = {}"
    by auto
  show ?thesis
  proof (clarsimp simp: T interior_of_def)
    fix z U
    assume "z \<in> U" and opeA: "openin X U" and Asub: "U \<subseteq> \<Union> (range T)"
    with openin_subset have "z \<in> topspace X"
      by blast
    have "neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
      using assms locally_compact_regular_space_neighbourhood_base by auto
    then obtain V K where "openin X V" "compactin X K" "closedin X K" "z \<in> V" "V \<subseteq> K" "K \<subseteq> U"
      by (metis (no_types, lifting) \<open>z \<in> U\<close> neighbourhood_base_of opeA)
    have nb_closedin: "neighbourhood_base_of (closedin X) X"
      using \<open>regular_space X\<close> neighbourhood_base_of_closedin by auto
    have "\<exists>\<Phi>. \<forall>n. (\<Phi> n \<subseteq> K \<and> closedin X (\<Phi> n) \<and> X interior_of \<Phi> n \<noteq> {} \<and> disjnt (\<Phi> n) (T n)) \<and>
        \<Phi> (Suc n) \<subseteq> \<Phi> n"
    proof (rule dependent_nat_choice)
      show "\<exists>x\<subseteq>K. closedin X x \<and> X interior_of x \<noteq> {} \<and> disjnt x (T 0)"
      proof -
        have False if "V \<subseteq> T 0"
          using Tempty \<open>openin X V\<close> \<open>z \<in> V\<close> interior_of_maximal that by fastforce
        then obtain x where "openin X (V - T 0) \<and> x \<in> V - T 0"
          using T \<open>openin X V\<close> empty by blast
        with nb_closedin 
        obtain N C  where "openin X N" "closedin X C" "x \<in> N" "N \<subseteq> C" "C \<subseteq> V - T 0"
          unfolding neighbourhood_base_of by metis
        show ?thesis
        proof (intro exI conjI)
          show "C \<subseteq> K"
            using \<open>C \<subseteq> V - T 0\<close> \<open>V \<subseteq> K\<close> by auto
          show "X interior_of C \<noteq> {}"
            by (metis \<open>N \<subseteq> C\<close> \<open>openin X N\<close> \<open>x \<in> N\<close> empty_iff interior_of_eq_empty)
          show "disjnt C (T 0)"
            using \<open>C \<subseteq> V - T 0\<close> disjnt_iff by fastforce
        qed (use \<open>closedin X C\<close> in auto)
      qed
      show "\<exists>L. (L \<subseteq> K \<and> closedin X L \<and> X interior_of L \<noteq> {} \<and> disjnt L (T (Suc n))) \<and> L \<subseteq> C"
        if \<section>: "C \<subseteq> K \<and> closedin X C \<and> X interior_of C \<noteq> {} \<and> disjnt C (T n)"
        for C n
      proof -
        have False if "X interior_of C \<subseteq> T (Suc n)"
          by (metis Tempty interior_of_eq_empty \<section> openin_interior_of that)
        then obtain x where "openin X (X interior_of C - T (Suc n)) \<and> x \<in> X interior_of C - T (Suc n)"
          using T empty by fastforce
        with nb_closedin 
        obtain N D where "openin X N" "closedin X D" "x \<in> N" "N \<subseteq> D"  and D: "D \<subseteq> X interior_of C - T(Suc n)"
          unfolding neighbourhood_base_of by metis
        show ?thesis
        proof (intro conjI exI)
          show "D \<subseteq> K"
            using D interior_of_subset \<section> by fastforce
          show "X interior_of D \<noteq> {}"
            by (metis \<open>N \<subseteq> D\<close> \<open>openin X N\<close> \<open>x \<in> N\<close> empty_iff interior_of_eq_empty)
          show "disjnt D (T (Suc n))"
            using D disjnt_iff by fastforce
          show "D \<subseteq> C"
            using interior_of_subset [of X C] D by blast
        qed (use \<open>closedin X D\<close> in auto)
      qed
    qed
    then obtain \<Phi> where \<Phi>: "\<And>n. \<Phi> n \<subseteq> K \<and> closedin X (\<Phi> n) \<and> X interior_of \<Phi> n \<noteq> {} \<and> disjnt (\<Phi> n) (T n)"
      and "\<And>n. \<Phi> (Suc n) \<subseteq> \<Phi> n" by metis
    then have "decseq \<Phi>"
      by (simp add: decseq_SucI)
    moreover have "\<And>n. \<Phi> n \<noteq> {}"
      by (metis \<Phi> bot.extremum_uniqueI interior_of_subset)
    ultimately have "\<Inter>(range \<Phi>) \<noteq> {}"
      by (metis \<Phi> compact_space_imp_nest \<open>compactin X K\<close> compactin_subspace closedin_subset_topspace)
    moreover have "U \<subseteq> {y. \<exists>x. y \<in> T x}"
      using Asub by auto
    with T have "{a. \<forall>n.  a \<in> \<Phi> n} \<subseteq> {}"
      by (smt (verit) Asub \<Phi> Collect_empty_eq UN_iff \<open>K \<subseteq> U\<close> disjnt_iff subset_iff)
    ultimately show False
      by blast
  qed
qed


lemma Baire_category_alt:
  assumes "completely_metrizable_space X \<or> locally_compact_space X \<and> regular_space X" 
    and "countable \<G>"
    and "\<And>T. T \<in> \<G> \<Longrightarrow> closedin X T \<and> X interior_of T = {}"
  shows "X interior_of \<Union>\<G> = {}"
  using Baire_category_aux [of X \<G>] Metric_space.metric_Baire_category_alt
  by (metis assms completely_metrizable_space_def)


lemma Baire_category:
  assumes "completely_metrizable_space X \<or> locally_compact_space X \<and> regular_space X" 
    and "countable \<G>"
    and top: "\<And>T. T \<in> \<G> \<Longrightarrow> openin X T \<and> X closure_of T = topspace X"
  shows "X closure_of \<Inter>\<G> = topspace X"
proof (cases "\<G>={}")
  case False
  have *: "X interior_of \<Union>((-)(topspace X) ` \<G>) = {}"
    proof (intro Baire_category_alt conjI assms)
  show "countable ((-) (topspace X) ` \<G>)"
    using assms by blast
    fix T
    assume "T \<in> (-) (topspace X) ` \<G>"
    then obtain U where U: "U \<in> \<G>" "T = (topspace X) - U" "U \<subseteq> (topspace X)"
      by (meson top image_iff openin_subset)
    then show "closedin X T"
      by (simp add: closedin_diff top)
    show "X interior_of T = {}"
      using U top by (simp add: interior_of_closure_of double_diff)
  qed
  then show ?thesis
    by (simp add: closure_of_eq_topspace interior_of_complement)
qed auto


subsection\<open>Sierpinski-Hausdorff type results about countable closed unions\<close>

lemma locally_connected_not_countable_closed_union:
  assumes "topspace X \<noteq> {}" and csX: "connected_space X"
    and lcX: "locally_connected_space X"
    and X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and "countable \<U>" and pwU: "pairwise disjnt \<U>"
    and clo: "\<And>C. C \<in> \<U> \<Longrightarrow> closedin X C \<and> C \<noteq> {}"
    and UU_eq: "\<Union>\<U> = topspace X"
  shows "\<U> = {topspace X}"
proof -
  define \<V> where "\<V> \<equiv> (frontier_of) X ` \<U>"
  define B where "B \<equiv> \<Union>\<V>"
  then have Bsub: "B \<subseteq> topspace X"
    by (simp add: Sup_le_iff \<V>_def closedin_frontier_of closedin_subset)
  have allsub: "A \<subseteq> topspace X" if "A \<in> \<U>" for A
    by (meson clo closedin_def that)
  show ?thesis
  proof (rule ccontr)
    assume "\<U> \<noteq> {topspace X}"
    with assms have "\<exists>A\<in>\<U>. \<not> (closedin X A \<and> openin X A)"
      by (metis Union_empty connected_space_clopen_in singletonI subsetI subset_singleton_iff)
    then have "B \<noteq> {}"
      by (auto simp: B_def \<V>_def frontier_of_eq_empty allsub)
    moreover
    have "subtopology X B interior_of B = B"
      by (simp add: Bsub interior_of_openin openin_subtopology_refl)
    ultimately have int_B_nonempty: "subtopology X B interior_of B \<noteq> {}"
      by auto
    have "subtopology X B interior_of \<Union>\<V> = {}"
    proof (intro Baire_category_alt conjI)
      have "\<Union>\<U> \<subseteq> B \<union> \<Union>((interior_of) X ` \<U>)"
        using clo closure_of_closedin by (fastforce simp: B_def \<V>_def frontier_of_def)
      moreover have "B \<union> \<Union>((interior_of) X ` \<U>) \<subseteq> \<Union>\<U>"
        using allsub clo frontier_of_subset_eq interior_of_subset by (fastforce simp: B_def \<V>_def )
      moreover have "disjnt B (\<Union>((interior_of) X ` \<U>))"
        using pwU 
        apply (clarsimp simp: B_def \<V>_def frontier_of_def pairwise_def disjnt_iff)
        by (metis clo closure_of_eq interior_of_subset subsetD)
      ultimately have "B = topspace X - \<Union> ((interior_of) X ` \<U>)"
        by (auto simp: UU_eq disjnt_iff)
      then have "closedin X B"
        by fastforce
      with X show "completely_metrizable_space (subtopology X B) \<or> locally_compact_space (subtopology X B) \<and> regular_space (subtopology X B)"
        by (metis completely_metrizable_space_closedin locally_compact_Hausdorff_or_regular 
            locally_compact_space_closed_subset regular_space_subtopology)
      show "countable \<V>"
        by (simp add: \<V>_def \<open>countable \<U>\<close>)
      fix V
      assume "V \<in> \<V>"
      then obtain S where S: "S \<in> \<U>" "V = X frontier_of S"
        by (auto simp: \<V>_def)
      show "closedin (subtopology X B) V"
        by (metis B_def Sup_upper \<V>_def \<open>V \<in> \<V>\<close> closedin_frontier_of closedin_subset_topspace image_iff)
      have "subtopology X B interior_of (X frontier_of S) = {}"
      proof (clarsimp simp: interior_of_def openin_subtopology_alt)
        fix a U
        assume "a \<in> B" "a \<in> U" and opeU: "openin X U" and BUsub: "B \<inter> U \<subseteq> X frontier_of S"
        then have "a \<in> S"
          by (meson IntI \<open>S \<in> \<U>\<close> clo frontier_of_subset_closedin subsetD)
        then obtain W C where "openin X W" "connectedin X C" "a \<in> W" "W \<subseteq> C" "C \<subseteq> U"
          by (metis \<open>a \<in> U\<close> lcX locally_connected_space opeU)
        have "W \<inter> X frontier_of S \<noteq> {}"
          using \<open>B \<inter> U \<subseteq> X frontier_of S\<close> \<open>a \<in> B\<close> \<open>a \<in> U\<close> \<open>a \<in> W\<close> by auto
        with frontier_of_openin_straddle_Int
        obtain "W \<inter> S \<noteq> {}" "W - S \<noteq> {}" "W \<subseteq> topspace X"
          using \<open>openin X W\<close> by (metis openin_subset) 
        then obtain b where "b \<in> topspace X" "b \<in> W-S"
          by blast
        with UU_eq obtain T where "T \<in> \<U>" "T \<noteq> S" "W \<inter> T \<noteq> {}"
          by auto 
        then have "disjnt S T"
          by (metis \<open>S \<in> \<U>\<close> pairwise_def pwU)
        then have "C - T \<noteq> {}"
          by (meson Diff_eq_empty_iff \<open>W \<subseteq> C\<close> \<open>a \<in> S\<close> \<open>a \<in> W\<close> disjnt_iff subsetD)
        then have "C \<inter> X frontier_of T \<noteq> {}"
          using \<open>W \<inter> T \<noteq> {}\<close> \<open>W \<subseteq> C\<close> \<open>connectedin X C\<close> connectedin_Int_frontier_of by blast
        moreover have "C \<inter> X frontier_of T = {}"
        proof -
          have "X frontier_of S \<subseteq> S" "X frontier_of T \<subseteq> T"
            using frontier_of_subset_closedin \<open>S \<in> \<U>\<close> \<open>T \<in> \<U>\<close> clo by blast+
          moreover have "X frontier_of T \<union> B = B"
            using B_def \<V>_def \<open>T \<in> \<U>\<close> by blast
          ultimately show ?thesis
            using BUsub \<open>C \<subseteq> U\<close> \<open>disjnt S T\<close> unfolding disjnt_def by blast
        qed
        ultimately show False
          by simp
      qed
      with S show "subtopology X B interior_of V = {}"
        by meson
    qed
    then show False
      using B_def int_B_nonempty by blast
  qed
qed

lemma real_Sierpinski_lemma:
  fixes a b::real
  assumes "a \<le> b"
    and "countable \<U>" and pwU: "pairwise disjnt \<U>"
    and clo: "\<And>C. C \<in> \<U> \<Longrightarrow> closed C \<and> C \<noteq> {}"
    and "\<Union>\<U> = {a..b}"
  shows "\<U> = {{a..b}}"
proof -
  have "locally_connected_space (top_of_set {a..b})"
    by (simp add: locally_connected_real_interval)
  moreover
  have "completely_metrizable_space (top_of_set {a..b})"
    by (metis box_real(2) completely_metrizable_space_cbox)
  ultimately
  show ?thesis
    using locally_connected_not_countable_closed_union [of "subtopology euclidean {a..b}"] assms
    apply (simp add: closedin_subtopology)
    by (metis Union_upper inf.orderE)
qed


subsection\<open>The Tychonoff embedding\<close>

lemma completely_regular_space_cube_embedding_explicit:
  assumes "completely_regular_space X" "Hausdorff_space X"
  shows "embedding_map X
             (product_topology (\<lambda>f. top_of_set {0..1::real})
                (mspace (submetric (cfunspace X euclidean_metric)
                  {f. f \<in> topspace X \<rightarrow> {0..1}})) )
             (\<lambda>x. \<lambda>f \<in> mspace (submetric (cfunspace X euclidean_metric) {f. f \<in> topspace X \<rightarrow> {0..1}}).
              f x)"
proof -
  define K where "K \<equiv> mspace(submetric (cfunspace X euclidean_metric) {f. f \<in> topspace X \<rightarrow> {0..1::real}})"
  define e where "e \<equiv> \<lambda>x. \<lambda>f\<in>K. f x"
  have "e x \<noteq> e y" if xy: "x \<noteq> y" "x \<in> topspace X" "y \<in> topspace X" for x y
  proof -
    have "closedin X {x}"
      by (simp add: \<open>Hausdorff_space X\<close> closedin_Hausdorff_singleton \<open>x \<in> topspace X\<close>)
    then obtain f where contf: "continuous_map X euclideanreal f" 
      and f01: "f \<in> topspace X \<rightarrow> {0..1}" and fxy: "f y = 0" "f x = 1"
      using \<open>completely_regular_space X\<close> xy unfolding completely_regular_space_def Pi_iff continuous_map_in_subtopology image_subset_iff
      by (metis Diff_iff empty_iff insert_iff)
    then have "bounded (f ` topspace X)"
      by (metis bounded_closed_interval bounded_subset image_subset_iff_funcset)
    with contf f01 have "restrict f (topspace X) \<in> K"
      by (auto simp: K_def)
    with fxy xy show ?thesis 
      unfolding e_def by (metis restrict_apply' zero_neq_one)
  qed
  then have "inj_on e (topspace X)"
    by (meson inj_onI)
  then obtain e' where e': "\<And>x. x \<in> topspace X \<Longrightarrow> e' (e x) = x"
    by (metis inv_into_f_f)
  have "continuous_map (subtopology (product_topology (\<lambda>f. top_of_set {0..1}) K) (e ` topspace X)) X e'"
  proof (clarsimp simp add: continuous_map_atin limitin_atin openin_subtopology_alt e')
    fix x U
    assume "e x \<in> K \<rightarrow>\<^sub>E {0..1}" and "x \<in> topspace X" and "openin X U" and "x \<in> U"
    then obtain g where contg: "continuous_map X (top_of_set {0..1}) g" and "g x = 0" 
          and gim: "g \<in> (topspace X - U) \<rightarrow> {1::real}"
      using \<open>completely_regular_space X\<close> unfolding completely_regular_space_def 
      using Diff_iff openin_closedin_eq
      by (metis image_subset_iff_funcset)
    then have "bounded (g ` topspace X)"
      by (meson bounded_closed_interval bounded_subset continuous_map_in_subtopology
          image_subset_iff_funcset)
    moreover have "g \<in> topspace X \<rightarrow> {0..1}"
      using contg by (simp add: continuous_map_def)
    ultimately have g_in_K: "restrict g (topspace X) \<in> K"
      using contg by (force simp add: K_def continuous_map_in_subtopology)
    have "openin (top_of_set {0..1}) {0..<1::real}"
      using open_real_greaterThanLessThan[of "-1" 1] by (force simp: openin_open)
    moreover have "e x \<in> (\<Pi>\<^sub>E f\<in>K. if f = restrict g (topspace X) then {0..<1} else {0..1})"
      using \<open>e x \<in> K \<rightarrow>\<^sub>E {0..1}\<close> by (simp add: e_def \<open>g x = 0\<close> \<open>x \<in> topspace X\<close> PiE_iff)
    moreover have "e y = e x"
      if "y \<notin> U" and ey: "e y \<in> (\<Pi>\<^sub>E f\<in>K. if f = restrict g (topspace X) then {0..<1} else {0..1})"
           and y: "y \<in> topspace X" for y
    proof -
      have "e y (restrict g (topspace X)) \<in> {0..<1}"
        using ey by (smt (verit, ccfv_SIG) PiE_mem g_in_K)
    with gim g_in_K y \<open>y \<notin> U\<close> show ?thesis
      by (fastforce simp: e_def Pi_iff)
    qed
    ultimately
    show "\<exists>W. openin (product_topology (\<lambda>f. top_of_set {0..1}) K) W \<and> e x \<in> W \<and> e' ` (e ` topspace X \<inter> W - {e x}) \<subseteq> U"
      apply (rule_tac x="PiE K (\<lambda>f. if f = restrict g (topspace X) then {0..<1} else {0..1})" in exI)
      by (auto simp: openin_PiE_gen e')
  qed
  with e' have "embedding_map X (product_topology (\<lambda>f. top_of_set {0..1}) K) e"
    unfolding embedding_map_def homeomorphic_map_maps homeomorphic_maps_def
    by (fastforce simp: e_def K_def continuous_map_in_subtopology continuous_map_componentwise)
  then show ?thesis
    by (simp add: K_def e_def)
qed


lemma completely_regular_space_cube_embedding:
  fixes X :: "'a topology"
  assumes "completely_regular_space X" "Hausdorff_space X"
  obtains K:: "('a\<Rightarrow>real)set" and e
    where "embedding_map X (product_topology (\<lambda>f. top_of_set {0..1::real}) K) e"
  using completely_regular_space_cube_embedding_explicit [OF assms] by metis


subsection \<open>Urysohn and Tietze analogs for completely regular spaces\<close>

text\<open>"Urysohn and Tietze analogs for completely regular spaces if (()) set is 
assumed compact instead of closed. Note that Hausdorffness is *not* required: inside () proof 
we factor through the Kolmogorov quotient." -- John Harrison\<close>

lemma Urysohn_completely_regular_closed_compact:
  fixes a b::real
  assumes "a \<le> b" "completely_regular_space X" "closedin X S" "compactin X T" "disjnt S T"
  obtains f where "continuous_map X (subtopology euclidean {a..b}) f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
proof -
  obtain f where contf: "continuous_map X (subtopology euclideanreal {0..1}) f" 
    and f0: "f ` T \<subseteq> {0}" and f1: "f ` S \<subseteq> {1}"
  proof (cases "T={}")
    case True
    show thesis
    proof
      show "continuous_map X (top_of_set {0..1}) (\<lambda>x. 1::real)" "(\<lambda>x. 1::real) ` T \<subseteq> {0}" "(\<lambda>x. 1::real) ` S \<subseteq> {1}"
        using True by auto
    qed   
  next
    case False
    have "\<And>t. t \<in> T \<Longrightarrow> \<exists>f. continuous_map X (subtopology euclideanreal ({0..1})) f \<and> f t = 0 \<and> f ` S \<subseteq> {1}"
      using assms unfolding completely_regular_space_def
      by (meson DiffI compactin_subset_topspace disjnt_iff subset_eq)
    then obtain g where contg: "\<And>t. t \<in> T \<Longrightarrow> continuous_map X (subtopology euclideanreal {0..1}) (g t)"
                  and g0: "\<And>t. t \<in> T \<Longrightarrow> g t t = 0"
                  and g1: "\<And>t. t \<in> T \<Longrightarrow> g t ` S \<subseteq> {1}"
      by metis
    then have g01: "\<And>t. t \<in> T \<Longrightarrow> g t ` topspace X \<subseteq> {0..1}"
      by (meson continuous_map_in_subtopology image_subset_iff_funcset)
    define G where "G \<equiv> \<lambda>t. {x \<in> topspace X. g t x \<in> {..<1/2}}"
    have "Ball (G`T) (openin X)"
      using contg unfolding G_def continuous_map_in_subtopology
      by (smt (verit, best) Collect_cong openin_continuous_map_preimage image_iff open_lessThan open_openin)
    moreover have "T \<subseteq> \<Union>(G`T)"
      using \<open>compactin X T\<close> g0 compactin_subset_topspace by (force simp: G_def)
    ultimately have "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> G`T \<and> T \<subseteq> \<Union> \<F>"
      using \<open>compactin X T\<close> unfolding compactin_def by blast
    then obtain K where K: "finite K" "K \<subseteq> T" "T \<subseteq> \<Union>(G`K)"
      by (metis finite_subset_image)
    with False have "K \<noteq> {}"
      by fastforce
    define f where "f \<equiv> \<lambda>x. 2 * max 0 (Inf ((\<lambda>t. g t x) ` K) - 1/2)"
    have [simp]: "max 0 (x - 1/2) = 0 \<longleftrightarrow> x \<le> 1/2" for x::real
      by force
    have [simp]: "2 * max 0 (x - 1/2) = 1 \<longleftrightarrow> x = 1" for x::real
      by (simp add: max_def_raw)
    show thesis 
    proof
      have "g t s = 1" if "s \<in> S" "t \<in> K" for s t
        using \<open>K \<subseteq> T\<close> g1 that by auto
      then show "f ` S \<subseteq> {1}"
        using \<open>K \<noteq> {}\<close> by (simp add: f_def image_subset_iff)
      have "(INF t\<in>K. g t x) \<le> 1/2" if "x \<in> T" for x
      proof -
        obtain k where "k \<in> K" "g k x < 1/2"
          using K \<open>x \<in> T\<close> by (auto simp: G_def)
        then show ?thesis
          by (meson \<open>finite K\<close> cInf_le_finite dual_order.trans finite_imageI imageI less_le_not_le)
      qed
      then show "f ` T \<subseteq> {0}"
        by (force simp: f_def)
      have "\<And>t. t \<in> K \<Longrightarrow> continuous_map X euclideanreal (g t)"
        using \<open>K \<subseteq> T\<close> contg continuous_map_in_subtopology by blast
      moreover have "2 * max 0 ((INF t\<in>K. g t x) - 1/2) \<le> 1" if "x \<in> topspace X" for x
      proof -
        obtain k where "k \<in> K" "g k x \<le> 1"
          using K \<open>x \<in> topspace X\<close> \<open>K \<noteq> {}\<close> g01 by (fastforce simp: G_def)
        then have "(INF t\<in>K. g t x) \<le> 1"
          by (meson \<open>finite K\<close> cInf_le_finite dual_order.trans finite_imageI imageI)
        then show ?thesis
          by (simp add: max_def_raw)
      qed
      ultimately show "continuous_map X (top_of_set {0..1}) f"
        by (force simp: f_def continuous_map_in_subtopology intro!: \<open>finite K\<close> continuous_intros)
    qed
  qed
  define g where "g \<equiv> \<lambda>x. a + (b - a) * f x"
  show thesis
  proof
    have "a + (b - a) * f i \<le> b" if "i \<in> topspace X" for i
      using that contf \<open>a \<le> b\<close> affine_ineq [of "f i" a b]
      unfolding continuous_map_in_subtopology continuous_map_upper_lower_semicontinuous_le_gen Pi_iff 
      by (simp add: algebra_simps)
    then show "continuous_map X (top_of_set {a..b}) g"
      using contf \<open>a \<le> b\<close> unfolding g_def continuous_map_in_subtopology Pi_iff
      by (intro conjI continuous_intros; simp)
    show "g ` T \<subseteq> {a}" "g ` S \<subseteq> {b}"
      using f0 f1 by (auto simp: g_def)
  qed 
qed


lemma Urysohn_completely_regular_compact_closed:
  fixes a b::real
  assumes "a \<le> b" "completely_regular_space X" "compactin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X (subtopology euclidean {a..b}) f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
proof -
  obtain f where contf: "continuous_map X (subtopology euclidean {-b..-a}) f" and fim: "f ` T \<subseteq> {-a}" "f ` S \<subseteq> {-b}"
    by (meson Urysohn_completely_regular_closed_compact assms disjnt_sym neg_le_iff_le)
  show thesis
  proof
    show "continuous_map X (top_of_set {a..b}) (uminus \<circ> f)"
      using contf by (auto simp: continuous_map_in_subtopology o_def Pi_iff)
    show "(uminus o f) ` T \<subseteq> {a}" "(uminus o f) ` S \<subseteq> {b}"
      using fim by fastforce+
  qed
qed

lemma Urysohn_completely_regular_compact_closed_alt:
  fixes a b::real
  assumes "completely_regular_space X" "compactin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X euclideanreal f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
proof (cases a b rule: le_cases)
  case le
  then show ?thesis
    by (meson Urysohn_completely_regular_compact_closed assms continuous_map_into_fulltopology that)
next
  case ge
  then show ?thesis 
    using Urysohn_completely_regular_closed_compact assms
    by (metis Urysohn_completely_regular_closed_compact assms continuous_map_into_fulltopology disjnt_sym that)
qed


lemma Tietze_extension_comp_reg_aux:
  fixes T :: "real set"
  assumes "completely_regular_space X" "Hausdorff_space X" "compactin X S" 
    and T: "is_interval T" "T\<noteq>{}" 
    and contf: "continuous_map (subtopology X S) euclidean f" and fim: "f`S \<subseteq> T"
  obtains g where "continuous_map X euclidean g" "g ` topspace X \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain K:: "('a\<Rightarrow>real)set" and e
    where e0: "embedding_map X (product_topology (\<lambda>f. top_of_set {0..1::real}) K) e"
    using assms completely_regular_space_cube_embedding by blast
  define cube where "cube \<equiv> product_topology (\<lambda>f. top_of_set {0..1::real}) K"
  have e: "embedding_map X cube e"
    using e0 by (simp add: cube_def)
  obtain e' where  e': "homeomorphic_maps X (subtopology cube (e ` topspace X)) e e'"
    using e by (force simp: cube_def embedding_map_def homeomorphic_map_maps)
  then have conte: "continuous_map X (subtopology cube (e ` topspace X)) e"
     and conte': "continuous_map (subtopology cube (e ` topspace X)) X e'"
     and e'e: "\<forall>x\<in>topspace X. e' (e x) = x"
    by (auto simp: homeomorphic_maps_def)
  have "Hausdorff_space cube"
    unfolding cube_def
    using Hausdorff_space_euclidean Hausdorff_space_product_topology Hausdorff_space_subtopology by blast
  have "normal_space cube"
  proof (rule compact_Hausdorff_or_regular_imp_normal_space)
    show "compact_space cube"
      unfolding cube_def
      using compact_space_product_topology compact_space_subtopology compactin_euclidean_iff by blast
  qed (use \<open>Hausdorff_space cube\<close> in auto)
  moreover
  have comp: "compactin cube (e ` S)"
    by (meson \<open>compactin X S\<close> conte continuous_map_in_subtopology image_compactin)
  then have "closedin cube (e ` S)"
    by (intro compactin_imp_closedin \<open>Hausdorff_space cube\<close>)
  moreover
  have "continuous_map (subtopology cube (e ` S)) euclideanreal (f \<circ> e')"
  proof (intro continuous_map_compose)
    show "continuous_map (subtopology cube (e ` S)) (subtopology X S) e'"
      unfolding continuous_map_in_subtopology
    proof
      show "continuous_map (subtopology cube (e ` S)) X e'"
        by (meson \<open>compactin X S\<close> compactin_subset_topspace conte' continuous_map_from_subtopology_mono image_mono)
      show "e' \<in> topspace (subtopology cube (e ` S)) \<rightarrow> S"
        using \<open>compactin X S\<close> compactin_subset_topspace e'e by fastforce
    qed
  qed (simp add: contf)
  moreover
  have "(f \<circ> e') ` e ` S \<subseteq> T"
    using \<open>compactin X S\<close> compactin_subset_topspace e'e fim by fastforce
  ultimately
  obtain g where contg: "continuous_map cube euclidean g" and gsub: "g ` topspace cube \<subseteq> T" 
                and gf: "\<And>x. x \<in> e`S \<Longrightarrow> g x = (f \<circ> e') x"
    using Tietze_extension_realinterval T by metis
  show thesis
  proof
    show "continuous_map X euclideanreal (g \<circ> e)"
      by (meson contg conte continuous_map_compose continuous_map_in_subtopology)
    show "(g \<circ> e) ` topspace X \<subseteq> T"
      using gsub conte continuous_map_image_subset_topspace by fastforce
    fix x
    assume "x \<in> S"
    then show "(g \<circ> e) x = f x"
      using gf \<open>compactin X S\<close> compactin_subset_topspace e'e by fastforce
  qed
qed


lemma Tietze_extension_completely_regular:
  assumes "completely_regular_space X" "compactin X S" "is_interval T" "T \<noteq> {}" 
    and contf: "continuous_map (subtopology X S) euclidean f" and fim: "f`S \<subseteq> T"
  obtains g where "continuous_map X euclideanreal g" "g ` topspace X \<subseteq> T" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  define Q where "Q \<equiv> Kolmogorov_quotient X ` (topspace X)"
  obtain g where contg: "continuous_map (subtopology X (Kolmogorov_quotient X ` S)) euclidean g"
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g(Kolmogorov_quotient X x) = f x"
    using Kolmogorov_quotient_lift_exists 
    by (metis \<open>compactin X S\<close> contf compactin_subset_topspace open_openin t0_space_def t1_space)
  have "S \<subseteq> topspace X"
    by (simp add: \<open>compactin X S\<close> compactin_subset_topspace)
  then have [simp]: "Q \<inter> Kolmogorov_quotient X ` S = Kolmogorov_quotient X ` S"
    using Q_def by blast
  have creg: "completely_regular_space (subtopology X Q)"
    by (simp add: \<open>completely_regular_space X\<close> completely_regular_space_subtopology)
  then have "regular_space (subtopology X Q)"
    by (simp add: completely_regular_imp_regular_space)
  then have "Hausdorff_space (subtopology X Q)"
    using Q_def regular_t0_eq_Hausdorff_space t0_space_Kolmogorov_quotient by blast
  moreover
  have "compactin (subtopology X Q) (Kolmogorov_quotient X ` S)"
    by (metis Q_def \<open>compactin X S\<close> image_compactin quotient_imp_continuous_map quotient_map_Kolmogorov_quotient)
  ultimately obtain h where conth: "continuous_map (subtopology X Q) euclidean h" 
              and him: "h ` topspace (subtopology X Q) \<subseteq> T" 
              and hg: "\<And>x. x \<in> Kolmogorov_quotient X ` S \<Longrightarrow> h x = g x"
    using Tietze_extension_comp_reg_aux [of "subtopology X Q" "Kolmogorov_quotient X ` S" T g]
    apply (simp add: subtopology_subtopology creg contg assms)
    using fim gf by blast
  show thesis
  proof
    show "continuous_map X euclideanreal (h \<circ> Kolmogorov_quotient X)"
      by (metis Q_def conth continuous_map_compose quotient_imp_continuous_map quotient_map_Kolmogorov_quotient)
    show "(h \<circ> Kolmogorov_quotient X) ` topspace X \<subseteq> T"
      using Q_def continuous_map_Kolmogorov_quotient continuous_map_image_subset_topspace him by fastforce
    fix x
    assume "x \<in> S" then show "(h \<circ> Kolmogorov_quotient X) x = f x"
      by (simp add: gf hg)
  qed
qed

subsection\<open>Size bounds on connected or path-connected spaces\<close>

lemma connected_space_imp_card_ge_alt:
  assumes "connected_space X" "completely_regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "S \<subseteq> topspace X"
    using \<open>closedin X S\<close> closedin_subset by blast
  then obtain a where "a \<in> topspace X" "a \<notin> S"
    using \<open>S \<noteq> topspace X\<close> by blast
  have "(UNIV::real set) \<lesssim> {0..1::real}"
    using eqpoll_real_subset 
    by (meson atLeastAtMost_iff eqpoll_imp_lepoll eqpoll_sym less_eq_real_def zero_less_one)
  also have "\<dots> \<lesssim> topspace X"
  proof -
    obtain f where contf: "continuous_map X euclidean f"
      and fim: "f \<in> (topspace X) \<rightarrow> {0..1::real}"
      and f0: "f a = 0" and f1: "f ` S \<subseteq> {1}"
      using \<open>completely_regular_space X\<close>
      unfolding completely_regular_space_def
      by (metis Diff_iff \<open>a \<in> topspace X\<close> \<open>a \<notin> S\<close> \<open>closedin X S\<close> continuous_map_in_subtopology image_subset_iff_funcset)
    have "\<exists>y\<in>topspace X. x = f y" if "0 \<le> x" and "x \<le> 1" for x
    proof -
      have "connectedin euclidean (f ` topspace X)"
        using \<open>connected_space X\<close> connectedin_continuous_map_image connectedin_topspace contf by blast
      moreover have "\<exists>y. 0 = f y \<and> y \<in> topspace X"
        using \<open>a \<in> topspace X\<close> f0 by auto
      moreover have "\<exists>y. 1 = f y \<and> y \<in> topspace X"
        using \<open>S \<subseteq> topspace X\<close> \<open>S \<noteq> {}\<close> f1 by fastforce
      ultimately show ?thesis
        using that by (fastforce simp: is_interval_1 simp flip: is_interval_connected_1)
    qed
    then show ?thesis
      unfolding lepoll_iff using atLeastAtMost_iff by blast
  qed
  finally show ?thesis .
qed


lemma connected_space_imp_card_ge_gen:
  assumes "connected_space X" "normal_space X" "closedin X S" "closedin X T" "S \<noteq> {}" "T \<noteq> {}" "disjnt S T"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "(UNIV::real set) \<lesssim> {0..1::real}"
    by (metis atLeastAtMost_iff eqpoll_real_subset eqpoll_imp_lepoll eqpoll_sym less_le_not_le zero_less_one)
  also have "\<dots>\<lesssim> topspace X"
  proof -
    obtain f where contf: "continuous_map X euclidean f"
       and fim: "f \<in> (topspace X) \<rightarrow> {0..1::real}"
       and f0: "f ` S \<subseteq> {0}" and f1: "f ` T \<subseteq> {1}"
      using assms by (metis continuous_map_in_subtopology normal_space_iff_Urysohn image_subset_iff_funcset)
    have "\<exists>y\<in>topspace X. x = f y" if "0 \<le> x" and "x \<le> 1" for x
    proof -
      have "connectedin euclidean (f ` topspace X)"
        using \<open>connected_space X\<close> connectedin_continuous_map_image connectedin_topspace contf by blast
      moreover have "\<exists>y. 0 = f y \<and> y \<in> topspace X"
        using \<open>closedin X S\<close> \<open>S \<noteq> {}\<close> closedin_subset f0 by fastforce
      moreover have "\<exists>y. 1 = f y \<and> y \<in> topspace X"
        using \<open>closedin X T\<close> \<open>T \<noteq> {}\<close> closedin_subset f1 by fastforce
      ultimately show ?thesis
        using that by (fastforce simp: is_interval_1 simp flip: is_interval_connected_1)
    qed
    then show ?thesis
      unfolding lepoll_iff using atLeastAtMost_iff by blast
  qed
  finally show ?thesis .
qed

lemma connected_space_imp_card_ge:
  assumes "connected_space X" "normal_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then have "{a} \<noteq> topspace X"
    by force
  with connected_space_imp_card_ge_alt assms show ?thesis
    by (metis \<open>a \<in> topspace X\<close> closedin_t1_singleton insert_not_empty normal_imp_completely_regular_space_A)
qed

lemma connected_space_imp_infinite_gen:
   "\<lbrakk>connected_space X; t1_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
  by (metis connected_space_discrete_topology finite_t1_space_imp_discrete_topology)

lemma connected_space_imp_infinite:
   "\<lbrakk>connected_space X; Hausdorff_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
  by (simp add: Hausdorff_imp_t1_space connected_space_imp_infinite_gen)

lemma connected_space_imp_infinite_alt:
  assumes "connected_space X" "regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "infinite(topspace X)"
proof -
  have "S \<subseteq> topspace X"
    using \<open>closedin X S\<close> closedin_subset by blast
  then obtain a where a: "a \<in> topspace X" "a \<notin> S"
    using \<open>S \<noteq> topspace X\<close> by blast
  have "\<exists>\<Phi>. \<forall>n. (disjnt (\<Phi> n) S \<and> a \<in> \<Phi> n \<and> openin X (\<Phi> n)) \<and> \<Phi>(Suc n) \<subset> \<Phi> n"
  proof (rule dependent_nat_choice)
    show "\<exists>T. disjnt T S \<and> a \<in> T \<and> openin X T"
      by (metis Diff_iff a \<open>closedin X S\<close> closedin_def disjnt_iff)
    fix V n
    assume \<section>: "disjnt V S \<and> a \<in> V \<and> openin X V"
    then obtain U C where U: "openin X U" "closedin X C" "a \<in> U" "U \<subseteq> C" "C \<subseteq> V"
      using \<open>regular_space X\<close> by (metis neighbourhood_base_of neighbourhood_base_of_closedin)
    with assms have "U \<subset> V"
      by (metis "\<section>" \<open>S \<subseteq> topspace X\<close> connected_space_clopen_in disjnt_def empty_iff inf.absorb_iff2 inf.orderE psubsetI subset_trans)
    with U show "\<exists>U. (disjnt U S \<and> a \<in> U \<and> openin X U) \<and> U \<subset> V"
      using "\<section>" disjnt_subset1 by blast
  qed
  then obtain \<Phi> where \<Phi>: "\<And>n. disjnt (\<Phi> n) S \<and> a \<in> \<Phi> n \<and> openin X (\<Phi> n)"
    and \<Phi>sub: "\<And>n. \<Phi> (Suc n) \<subset> \<Phi> n" by metis
  then have "decseq \<Phi>"
    by (simp add: decseq_SucI psubset_eq)
  have "\<forall>n. \<exists>x. x \<in> \<Phi> n \<and> x \<notin> \<Phi>(Suc n)"
    by (meson \<Phi>sub psubsetE subsetI)
  then obtain f where fin: "\<And>n. f n \<in> \<Phi> n" and fout: "\<And>n. f n \<notin> \<Phi>(Suc n)"
    by metis
  have "range f \<subseteq> topspace X"
    by (meson \<Phi> fin image_subset_iff openin_subset subset_iff)
  moreover have "inj f"
    by (metis Suc_le_eq \<open>decseq \<Phi>\<close> decseq_def fin fout linorder_injI subsetD)
  ultimately show ?thesis
    using infinite_iff_countable_subset by blast
qed

lemma path_connected_space_imp_card_ge:
  assumes "path_connected_space X" "Hausdorff_space X" and nosing: "\<not> (\<exists>x. topspace X \<subseteq> {x})"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then obtain \<gamma> where \<gamma>: "pathin X \<gamma>" "\<gamma> 0 = a" "\<gamma> 1 = b"
    by (meson \<open>a \<in> topspace X\<close> \<open>b \<in> topspace X\<close> \<open>path_connected_space X\<close> path_connected_space_def)
  let ?Y = "subtopology X (\<gamma> ` (topspace (subtopology euclidean {0..1})))"
  have "(UNIV::real set) \<lesssim>  topspace ?Y"
  proof (intro compact_Hausdorff_or_regular_imp_normal_space connected_space_imp_card_ge)
    show "connected_space ?Y"
      using \<open>pathin X \<gamma>\<close> connectedin_def connectedin_path_image by auto
    show "Hausdorff_space ?Y \<or> regular_space ?Y"
      using Hausdorff_space_subtopology \<open>Hausdorff_space X\<close> by blast
    show "t1_space ?Y"
      using Hausdorff_imp_t1_space \<open>Hausdorff_space X\<close> t1_space_subtopology by blast
    show "compact_space ?Y"
      by (simp add: \<open>pathin X \<gamma>\<close> compact_space_subtopology compactin_path_image)
    have "a \<in> topspace ?Y" "b \<in> topspace ?Y"
      using \<gamma> pathin_subtopology by fastforce+
    with \<open>a \<noteq> b\<close> show "\<nexists>x. topspace ?Y \<subseteq> {x}"
      by blast
  qed
  also have "\<dots> \<lesssim> \<gamma> ` {0..1}"
    by (simp add: subset_imp_lepoll)
  also have "\<dots> \<lesssim> topspace X"
    by (meson \<gamma> path_image_subset_topspace subset_imp_lepoll image_subset_iff_funcset)
  finally show ?thesis .
qed

lemma connected_space_imp_uncountable:
  assumes "connected_space X" "regular_space X" "Hausdorff_space X" "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
proof
  assume coX: "countable (topspace X)"
  with \<open>regular_space X\<close> have "normal_space X"
    using countable_imp_Lindelof_space regular_Lindelof_imp_normal_space by blast
  then have "(UNIV::real set) \<lesssim> topspace X"
    by (simp add: Hausdorff_imp_t1_space assms connected_space_imp_card_ge)
  with coX show False
    using countable_lepoll uncountable_UNIV_real by blast
qed

lemma path_connected_space_imp_uncountable:
  assumes "path_connected_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
proof 
  assume coX: "countable (topspace X)"
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then obtain \<gamma> where "pathin X \<gamma>" "\<gamma> 0 = a" "\<gamma> 1 = b"
    by (meson \<open>a \<in> topspace X\<close> \<open>b \<in> topspace X\<close> \<open>path_connected_space X\<close> path_connected_space_def)
  then have "\<gamma> ` {0..1} \<lesssim> topspace X"
    by (meson path_image_subset_topspace subset_imp_lepoll image_subset_iff_funcset)
  define \<A> where "\<A> \<equiv> ((\<lambda>a. {x \<in> {0..1}. \<gamma> x \<in> {a}}) ` topspace X) - {{}}"
  have \<A>01: "\<A> = {{0..1}}"
  proof (rule real_Sierpinski_lemma)
    show "countable \<A>"
      using \<A>_def coX by blast
    show "disjoint \<A>"
      by (auto simp: \<A>_def disjnt_iff pairwise_def)
    show "\<Union>\<A> = {0..1}"
      using \<open>pathin X \<gamma>\<close> path_image_subset_topspace by (fastforce simp: \<A>_def Bex_def)
    fix C
    assume "C \<in> \<A>"
    then obtain a where "a \<in> topspace X" and C: "C = {x \<in> {0..1}. \<gamma> x \<in> {a}}" "C \<noteq> {}"
      by (auto simp: \<A>_def)
    then have "closedin X {a}"
      by (meson \<open>t1_space X\<close> closedin_t1_singleton)
    then have "closedin (top_of_set {0..1}) C"
      using C \<open>pathin X \<gamma>\<close> closedin_continuous_map_preimage pathin_def by fastforce
    then show "closed C \<and> C \<noteq> {}"
      using C closedin_closed_trans by blast
  qed auto
  then have "{0..1} \<in> \<A>"
    by blast
  then have "\<exists>a \<in> topspace X. {0..1} \<subseteq> {x. \<gamma> x = a}"
    using \<A>_def image_iff by auto
  then show False
    using \<open>\<gamma> 0 = a\<close> \<open>\<gamma> 1 = b\<close> \<open>a \<noteq> b\<close> atLeastAtMost_iff zero_less_one_class.zero_le_one by blast
qed


subsection\<open>Lavrentiev extension etc\<close>

lemma (in Metric_space) convergent_eq_zero_oscillation_gen:
  assumes "mcomplete" and fim: "f \<in> (topspace X \<inter> S) \<rightarrow> M"
  shows "(\<exists>l. limitin mtopology f l (atin_within X a S)) \<longleftrightarrow>
         M \<noteq> {} \<and>
         (a \<in> topspace X
            \<longrightarrow> (\<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and>
                           (\<forall>x \<in> (S \<inter> U) - {a}. \<forall>y \<in> (S \<inter> U) - {a}. d (f x) (f y) < \<epsilon>)))"
proof (cases "M = {}")
  case True
  with limitin_mspace show ?thesis
    by blast
next
  case False
  show ?thesis
  proof (cases "a \<in> topspace X")
    case True
    let ?R = "\<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
    show ?thesis
    proof (cases "a \<in> X derived_set_of S")
      case True
      have ?R
        if "limitin mtopology f l (atin_within X a S)" for l
      proof (intro strip)
        fix \<epsilon>::real
        assume "\<epsilon>>0"
        with that \<open>a \<in> topspace X\<close> 
        obtain U where U: "openin X U" "a \<in> U" "l \<in> M"
          and Uless: "\<forall>x\<in>U - {a}. x \<in> S \<longrightarrow> f x \<in> M \<and> d (f x) l < \<epsilon>/2"
          unfolding limitin_metric eventually_atin_within by (metis Diff_iff insertI1  half_gt_zero [OF \<open>\<epsilon>>0\<close>])
        show "\<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
        proof (intro exI strip conjI)
          fix x y
          assume x: "x \<in> S \<inter> U - {a}" and y: "y \<in> S \<inter> U - {a}"
          then have "d (f x) l < \<epsilon>/2" "d (f y) l < \<epsilon>/2" "f x \<in> M" "f y \<in> M"
            using Uless by auto
          then show "d (f x) (f y) < \<epsilon>"
            using triangle' \<open>l \<in> M\<close> by fastforce
        qed (auto simp add: U)
      qed
      moreover have "\<exists>l. limitin mtopology f l (atin_within X a S)" 
        if R [rule_format]: ?R
      proof -
        define F where "F \<equiv> \<lambda>U. mtopology closure_of f ` (S \<inter> U - {a})"
        define \<C> where "\<C> \<equiv> F ` {U. openin X U \<and> a \<in> U}"
        have \<C>_clo: "\<forall>C \<in> \<C>. closedin mtopology C"
          by (force simp add: \<C>_def F_def)
        moreover have sub_mcball: "\<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a \<epsilon>" if "\<epsilon>>0" for \<epsilon>
        proof -
          obtain U where U: "openin X U" "a \<in> U" 
            and Uless: "\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>"
            using R [OF \<open>\<epsilon>>0\<close>] by blast
          then obtain b where b: "b \<noteq> a" "b \<in> S" "b \<in> U"
            using True by (auto simp add: in_derived_set_of)
          have "U \<subseteq> topspace X"
            by (simp add: U(1) openin_subset)
          have "f b \<in> M"
            using b \<open>openin X U\<close> by (metis image_subset_iff_funcset Int_iff fim image_eqI openin_subset subsetD)
          moreover
          have "mtopology closure_of f ` ((S \<inter> U) - {a}) \<subseteq> mcball (f b) \<epsilon>"
          proof (rule closure_of_minimal)
            have "f y \<in> M" if "y \<in> S" and "y \<in> U" for y
              using \<open>U \<subseteq> topspace X\<close> fim that by (auto simp: Pi_iff)
            moreover
            have "d (f b) (f y) \<le> \<epsilon>" if "y \<in> S" "y \<in> U" "y \<noteq> a" for y
              using that Uless b by force
            ultimately show "f ` (S \<inter> U - {a}) \<subseteq> mcball (f b) \<epsilon>"
              by (force simp: \<open>f b \<in> M\<close>)
          qed auto
          ultimately show ?thesis
            using U by (auto simp add: \<C>_def F_def)
        qed
        moreover have "\<Inter>\<F> \<noteq> {}" if "finite \<F>" "\<F> \<subseteq> \<C>" for \<F>
        proof -
          obtain \<G> where sub: "\<G> \<subseteq> {U. openin X U \<and> a \<in> U}" and eq: "\<F> = F ` \<G>" and "finite \<G>"
            by (metis (no_types, lifting) \<C>_def \<open>\<F> \<subseteq> \<C>\<close> \<open>finite \<F>\<close> finite_subset_image)
          then have "U \<subseteq> topspace X" if "U \<in> \<G>" for U
            using openin_subset that by auto
          then have "T \<subseteq> mtopology closure_of T" 
            if "T \<in> (\<lambda>U. f ` (S \<inter> U - {a})) ` \<G>" for T
            using that fim by (fastforce simp add: intro!: closure_of_subset)
          moreover
          have ain: "a \<in> \<Inter> (insert (topspace X) \<G>)" "openin X (\<Inter> (insert (topspace X) \<G>))"
            using True in_derived_set_of sub \<open>finite \<G>\<close> by (fastforce intro!: openin_Inter)+
          then obtain y where "y \<noteq> a" "y \<in> S" and y: "y \<in> \<Inter> (insert (topspace X) \<G>)"
            by (meson \<open>a \<in> X derived_set_of S\<close> sub in_derived_set_of) 
          then have "f y \<in> \<Inter>\<F>"
            using eq that ain fim by (auto simp add: F_def image_subset_iff in_closure_of)
          then show ?thesis by blast
        qed
        ultimately have "\<Inter>\<C> \<noteq> {}"
          using \<open>mcomplete\<close> mcomplete_fip by metis
        then obtain b where "b \<in> \<Inter>\<C>"
          by auto
        then have "b \<in> M"
          using sub_mcball \<C>_clo mbounded_alt_pos mbounded_empty metric_closedin_iff_sequentially_closed by force
        have "limitin mtopology f b (atin_within X a S)"
        proof (clarsimp simp: limitin_metric \<open>b \<in> M\<close>)
          fix \<epsilon> :: real
          assume "\<epsilon> > 0"
          then obtain U where U: "openin X U" "a \<in> U" and subU: "U \<subseteq> topspace X"
            and Uless: "\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>/2"
            by (metis R half_gt_zero openin_subset) 
          then obtain x where x: "x \<in> S" "x \<in> U" "x \<noteq> a" and fx: "f x \<in> mball b (\<epsilon>/2)"
            using \<open>b \<in> \<Inter>\<C>\<close> 
            apply (simp add: \<C>_def F_def closure_of_def del: divide_const_simps)
            by (metis Diff_iff Int_iff centre_in_mball_iff in_mball openin_mball singletonI zero_less_numeral)
          moreover
          have "d (f y) b < \<epsilon>" if "y \<in> U" "y \<noteq> a" "y \<in> S" for y
          proof -
            have "d (f x) (f y) < \<epsilon>/2"
              using Uless that x by force
            moreover have "d b (f x)  < \<epsilon>/2"
              using fx by simp
            ultimately show ?thesis
              using triangle [of b "f x" "f y"] subU that \<open>b \<in> M\<close> commute fim fx by fastforce
          qed
          ultimately show "\<forall>\<^sub>F x in atin_within X a S. f x \<in> M \<and> d (f x) b < \<epsilon>"
            using fim U
            apply (simp add: eventually_atin_within del: divide_const_simps flip: image_subset_iff_funcset)
            by (smt (verit, del_insts) Diff_iff Int_iff imageI insertI1 openin_subset subsetD)
        qed
        then show ?thesis ..
      qed
      ultimately
      show ?thesis
        by (meson True \<open>M \<noteq> {}\<close> in_derived_set_of)
    next
      case False
      have "(\<exists>l. limitin mtopology f l (atin_within X a S))"
        by (metis \<open>M \<noteq> {}\<close> False derived_set_of_trivial_limit equals0I limitin_trivial topspace_mtopology)
      moreover have "\<forall>e>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < e)"
        by (metis Diff_iff False IntE True in_derived_set_of insert_iff)
      ultimately show ?thesis
        using limitin_mspace by blast
    qed
  next
    case False
    then show ?thesis
      by (metis derived_set_of_trivial_limit ex_in_conv in_derived_set_of limitin_mspace limitin_trivial topspace_mtopology)
  qed
qed

text \<open>The HOL Light proof uses some ugly tricks to share common parts of what are two separate proofs for the two cases\<close>
lemma (in Metric_space) gdelta_in_points_of_convergence_within:
  assumes "mcomplete"
    and f: "continuous_map (subtopology X S) mtopology f \<or> t1_space X \<and> f \<in> S \<rightarrow> M"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin mtopology f l (atin_within X x S)}"
proof -
  have fim: "f \<in> (topspace X \<inter> S) \<rightarrow> M"
    using continuous_map_image_subset_topspace f by force
  show ?thesis
  proof (cases "M={}")
    case True
    then show ?thesis
      by (smt (verit) Collect_cong empty_def empty_iff gdelta_in_empty limitin_mspace)
  next
    case False
    define A where "A \<equiv> {a \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)}"
    have "gdelta_in X A"
      using f 
    proof (elim disjE conjE)
      assume cm: "continuous_map (subtopology X S) mtopology f"
      define C where "C \<equiv> \<lambda>r. \<Union>{U. openin X U \<and> (\<forall>x \<in> S\<inter>U. \<forall>y \<in> S\<inter>U. d (f x) (f y) < r)}"
      define B where "B \<equiv> (\<Inter>n. C(inverse(Suc n)))"
      define D where "D \<equiv> (\<Inter> (C ` {0<..}))"
      have "D=B"
        unfolding B_def C_def D_def
        apply (intro Inter_eq_Inter_inverse_Suc Sup_subset_mono)
        by (smt (verit, ccfv_threshold) Collect_mono_iff)
      have "B \<subseteq> topspace X"
        using openin_subset by (force simp add: B_def C_def)
      have "(countable intersection_of openin X) B"
        unfolding B_def C_def 
        by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
      then have "gdelta_in X B"
        unfolding gdelta_in_def by (intro relative_to_subset_inc \<open>B \<subseteq> topspace X\<close>)
      moreover have "A=D"
      proof (intro equalityI subsetI)
        fix a
        assume x: "a \<in> A"
        then have "a \<in> topspace X"
          using A_def by blast
        show "a \<in> D"
        proof (clarsimp simp: D_def C_def \<open>a \<in> topspace X\<close>)
          fix \<epsilon>::real assume "\<epsilon> > 0"
          then obtain U where "openin X U" "a \<in> U" and U: "(\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
            using x by (force simp: A_def)
          show "\<exists>T. openin X T \<and> (\<forall>x\<in>S \<inter> T. \<forall>y\<in>S \<inter> T. d (f x) (f y) < \<epsilon>) \<and> a \<in> T"
          proof (cases "a \<in> S")
            case True
            then obtain V where "openin X V" "a \<in> V" and V: "\<forall>x. x \<in> S \<and> x \<in> V \<longrightarrow> f a \<in> M \<and> f x \<in> M \<and> d (f a) (f x) < \<epsilon>"
              using \<open>a \<in> topspace X\<close> \<open>\<epsilon> > 0\<close> cm
              by (force simp add: continuous_map_to_metric openin_subtopology_alt Ball_def)
            show ?thesis
            proof (intro exI conjI strip)
              show "openin X (U \<inter> V)"
                using \<open>openin X U\<close> \<open>openin X V\<close> by blast 
              show "a \<in> U \<inter> V"
                using \<open>a \<in> U\<close> \<open>a \<in> V\<close> by blast
              show "\<And>x y. \<lbrakk>x \<in> S \<inter> (U \<inter> V); y \<in> S \<inter> (U \<inter> V)\<rbrakk> \<Longrightarrow> d (f x) (f y) < \<epsilon>"
                by (metis DiffI Int_iff U V commute singletonD)
            qed
          next
            case False then show ?thesis
              using U \<open>a \<in> U\<close> \<open>openin X U\<close> by auto
          qed
        qed
      next
        fix x
        assume x: "x \<in> D"
        then have "x \<in> topspace X"
          using \<open>B \<subseteq> topspace X\<close> \<open>D=B\<close> by blast
        with x show "x \<in> A"
          apply (clarsimp simp: D_def C_def A_def)
          by (meson DiffD1 greaterThan_iff)
      qed
      ultimately show ?thesis
        by (simp add: \<open>D=B\<close>)
    next
      assume "t1_space X" "f \<in> S \<rightarrow> M"
      define C where "C \<equiv> \<lambda>r. \<Union>{U. openin X U \<and> 
                           (\<exists>b \<in> topspace X. \<forall>x \<in> S\<inter>U - {b}. \<forall>y \<in> S\<inter>U - {b}. d (f x) (f y) < r)}"
      define B where "B \<equiv> (\<Inter>n. C(inverse(Suc n)))"
      define D where "D \<equiv> (\<Inter> (C ` {0<..}))"
      have "D=B"
        unfolding B_def C_def D_def
        apply (intro Inter_eq_Inter_inverse_Suc Sup_subset_mono)
        by (smt (verit, ccfv_threshold) Collect_mono_iff)
      have "B \<subseteq> topspace X"
        using openin_subset by (force simp add: B_def C_def)
      have "(countable intersection_of openin X) B"
        unfolding B_def C_def 
        by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
      then have "gdelta_in X B"
        unfolding gdelta_in_def by (intro relative_to_subset_inc \<open>B \<subseteq> topspace X\<close>)
      moreover have "A=D"
      proof (intro equalityI subsetI)
        fix x
        assume x: "x \<in> D"
        then have "x \<in> topspace X"
          using \<open>B \<subseteq> topspace X\<close> \<open>D=B\<close> by blast
        show "x \<in> A"
        proof (clarsimp simp: A_def \<open>x \<in> topspace X\<close>)
          fix \<epsilon> :: real
          assume "\<epsilon>>0"
          then obtain U b where "openin X U" "b \<in> topspace X"
                  and U: "\<forall>x\<in>S \<inter> U - {b}. \<forall>y\<in>S \<inter> U - {b}. d (f x) (f y) < \<epsilon>" and "x \<in> U"
            using x by (auto simp: D_def C_def A_def Ball_def)
          then have "openin X (U-{b})"
            by (meson \<open>t1_space X\<close> t1_space_openin_delete_alt)
          then show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>xa\<in>S \<inter> U - {x}. \<forall>y\<in>S \<inter> U - {x}. d (f xa) (f y) < \<epsilon>)"
            using U \<open>openin X U\<close> \<open>x \<in> U\<close> by auto
        qed
      next
        show "\<And>x. x \<in> A \<Longrightarrow> x \<in> D"
          unfolding A_def D_def C_def
          by clarsimp meson
      qed
      ultimately show ?thesis
        by (simp add: \<open>D=B\<close>)
    qed
    then show ?thesis
      by (simp add: A_def convergent_eq_zero_oscillation_gen False fim \<open>mcomplete\<close> cong: conj_cong)
  qed
qed


lemma gdelta_in_points_of_convergence_within:
  assumes Y: "completely_metrizable_space Y"
    and f: "continuous_map (subtopology X S) Y f \<or> t1_space X \<and> f \<in> S \<rightarrow> topspace Y"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
  using assms
  unfolding completely_metrizable_space_def
  using Metric_space.gdelta_in_points_of_convergence_within Metric_space.topspace_mtopology by fastforce


lemma Lavrentiev_extension_gen:
  assumes "S \<subseteq> topspace X" and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" 
            "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
             "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  define U where "U \<equiv> {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
  have "S \<subseteq> U"
    using that contf limit_continuous_map_within subsetD [OF \<open>S \<subseteq> topspace X\<close>] 
    by (fastforce simp: U_def)
  then have "S \<subseteq> X closure_of S \<inter> U"
    by (simp add: \<open>S \<subseteq> topspace X\<close> closure_of_subset)
  moreover
  have "\<And>t. t \<in> X closure_of S \<inter> U - S \<Longrightarrow> \<exists>l. limitin Y f l (atin_within X t S)"
    using U_def by blast
  moreover have "regular_space Y"
    by (simp add: Y completely_metrizable_imp_metrizable_space metrizable_imp_regular_space)
  ultimately
  obtain g where g: "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using continuous_map_extension_pointwise_alt assms by blast 
  show thesis
  proof
    show "gdelta_in X U"
      by (simp add: U_def Y contf gdelta_in_points_of_convergence_within)
    show "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g"
      by (simp add: g)
  qed (use \<open>S \<subseteq> U\<close> gf in auto)
qed

lemma Lavrentiev_extension:
  assumes "S \<subseteq> topspace X" 
    and X: "metrizable_space X \<or> topspace X \<subseteq> X closure_of S" 
    and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" "U \<subseteq> X closure_of S"
            "continuous_map (subtopology X U) Y g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain U g where "gdelta_in X U" "S \<subseteq> U" 
    and contg: "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using Lavrentiev_extension_gen Y assms(1) contf by blast
  define V where "V \<equiv> X closure_of S \<inter> U"
  show thesis
  proof
    show "gdelta_in X V"
      by (metis V_def X \<open>gdelta_in X U\<close> closed_imp_gdelta_in closedin_closure_of closure_of_subset_topspace gdelta_in_Int gdelta_in_topspace subset_antisym)
    show "S \<subseteq> V"
      by (simp add: V_def \<open>S \<subseteq> U\<close> assms(1) closure_of_subset)
    show "continuous_map (subtopology X V) Y g"
      by (simp add: V_def contg)
  qed (auto simp: gf V_def)
qed

subsection\<open>Embedding in products and hence more about completely metrizable spaces\<close>

lemma (in Metric_space) gdelta_homeomorphic_space_closedin_product:
  assumes S: "\<And>i. i \<in> I \<Longrightarrow> openin mtopology (S i)"
  obtains T where "closedin (prod_topology mtopology (powertop_real I)) T"
                  "subtopology mtopology (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology mtopology (powertop_real I)) T"
proof (cases "I={}")
  case True
  then have top: "topspace (prod_topology mtopology (powertop_real I)) = (M \<times> {(\<lambda>x. undefined)})"
    by simp
  show ?thesis
  proof
    show "closedin (prod_topology mtopology (powertop_real I)) (M \<times> {(\<lambda>x. undefined)})"
      by (metis top closedin_topspace)
    have "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space mtopology"
      by (simp add: True product_topology_empty_discrete)
    also have "\<dots> homeomorphic_space (prod_topology mtopology (discrete_topology {\<lambda>x. undefined}))"
      by (meson homeomorphic_space_sym prod_topology_homeomorphic_space_left)
    finally
    show "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space subtopology (prod_topology mtopology (powertop_real I)) (M \<times> {(\<lambda>x. undefined)})"
      by (smt (verit, ccfv_SIG) True product_topology_empty_discrete subtopology_topspace top)
  qed   
next
  case False
  have SM: "\<And>i. i \<in> I \<Longrightarrow> S i \<subseteq> M"
    using assms openin_mtopology by blast
  then have "(\<Inter>i \<in> I. S i) \<subseteq> M"
    using False by blast
  define dd where "dd \<equiv> \<lambda>i. if i\<notin>I \<or> S i = M then \<lambda>u. 1 else (\<lambda>u. INF x \<in> M - S i. d u x)"
  have [simp]: "bdd_below (d u ` A)" for u A
    by (meson bdd_belowI2 nonneg)
  have cont_dd: "continuous_map (subtopology mtopology (S i)) euclidean (dd i)" if "i \<in> I" for i
  proof -
    have "dist (Inf (d x ` (M - S i))) (Inf (d y ` (M - S i))) \<le> d x y" 
      if "x \<in> S i" "x \<in> M" "y \<in> S i" "y \<in> M" "S i \<noteq> M" for x y
    proof -
      have [simp]: "\<not> M \<subseteq> S i"
        using SM \<open>S i \<noteq> M\<close> \<open>i \<in> I\<close> by auto
      have "\<And>u. \<lbrakk>u \<in> M; u \<notin> S i\<rbrakk> \<Longrightarrow> Inf (d x ` (M - S i)) \<le> d x y + d y u"
        apply (clarsimp simp add: cInf_le_iff_less)
        by (smt (verit) DiffI triangle \<open>x \<in> M\<close> \<open>y \<in> M\<close>)
      then have "Inf (d x ` (M - S i)) - d x y \<le> Inf (d y ` (M - S i))"
        by (force simp add: le_cInf_iff)
      moreover
      have "\<And>u. \<lbrakk>u \<in> M; u \<notin> S i\<rbrakk> \<Longrightarrow> Inf (d y ` (M - S i)) \<le> d x u + d x y"
        apply (clarsimp simp add: cInf_le_iff_less)
        by (smt (verit) DiffI triangle'' \<open>x \<in> M\<close> \<open>y \<in> M\<close>)
      then have "Inf (d y ` (M - S i)) - d x y \<le> Inf (d x ` (M - S i))"
        by (force simp add: le_cInf_iff)
      ultimately show ?thesis
        by (simp add: dist_real_def abs_le_iff)
    qed
    then have *: "Lipschitz_continuous_map (submetric Self (S i)) euclidean_metric (\<lambda>u. Inf (d u ` (M - S i)))"
      unfolding Lipschitz_continuous_map_def by (force intro!: exI [where x=1])
    then show ?thesis
      using Lipschitz_continuous_imp_continuous_map [OF *]
      by (simp add: dd_def Self_def mtopology_of_submetric )
  qed 
  have dd_pos: "0 < dd i x" if "x \<in> S i" for i x
  proof (clarsimp simp add: dd_def)
    assume "i \<in> I" and "S i \<noteq> M"
    have opeS: "openin mtopology (S i)"
      by (simp add: \<open>i \<in> I\<close> assms)
    then obtain r where "r>0" and r: "\<And>y. \<lbrakk>y \<in> M; d x y < r\<rbrakk> \<Longrightarrow> y \<in> S i"
      by (meson \<open>x \<in> S i\<close> in_mball openin_mtopology subsetD)
    then have "\<And>y. y \<in> M - S i \<Longrightarrow> d x y \<ge> r"
      by (meson Diff_iff linorder_not_le)
    then have "Inf (d x ` (M - S i)) \<ge> r"
      by (meson Diff_eq_empty_iff SM \<open>S i \<noteq> M\<close> \<open>i \<in> I\<close> cINF_greatest set_eq_subset)
    with \<open>r>0\<close> show "0 < Inf (d x ` (M - S i))" by simp
  qed
  define f where "f \<equiv> \<lambda>x. (x, \<lambda>i\<in>I. inverse(dd i x))"
  define T where "T \<equiv> f ` (\<Inter>i \<in> I. S i)"
  show ?thesis
  proof
    show "closedin (prod_topology mtopology (powertop_real I)) T"
      unfolding closure_of_subset_eq [symmetric]
    proof
      show "T \<subseteq> topspace (prod_topology mtopology (powertop_real I))"
        using False SM by (auto simp: T_def f_def)

      have "(x,ds) \<in> T"
        if \<section>: "\<And>U. \<lbrakk>(x, ds) \<in> U; openin (prod_topology mtopology (powertop_real I)) U\<rbrakk> \<Longrightarrow> \<exists>y\<in>T. y \<in> U"
          and "x \<in> M" and ds: "ds \<in> I \<rightarrow>\<^sub>E UNIV" for x ds
      proof -
        have ope: "\<exists>x. x \<in> \<Inter>(S ` I) \<and> f x \<in> U \<times> V"
          if "x \<in> U" and "ds \<in> V" and "openin mtopology U" and "openin (powertop_real I) V" for U V
          using \<section> [of "U\<times>V"] that by (force simp add: T_def openin_prod_Times_iff)
        have x_in_INT: "x \<in> \<Inter>(S ` I)"
        proof clarify
          fix i
          assume "i \<in> I"
          show "x \<in> S i"
          proof (rule ccontr)
            assume "x \<notin> S i"
            have "openin (powertop_real I) {z \<in> topspace (powertop_real I). z i \<in> {ds i - 1 <..< ds i + 1}}"
            proof (rule openin_continuous_map_preimage)
              show "continuous_map (powertop_real I) euclidean (\<lambda>x. x i)"
                by (metis \<open>i \<in> I\<close> continuous_map_product_projection)
            qed auto
            then obtain y where "y \<in> S i" "y \<in> M" and dxy: "d x y < inverse (\<bar>ds i\<bar> + 1)"
                          and intvl: "inverse (dd i y) \<in> {ds i - 1 <..< ds i + 1}"
              using ope [of "mball x (inverse(abs(ds i) + 1))" "{z \<in> topspace(powertop_real I). z i \<in> {ds i - 1<..<ds i + 1}}"]
                    \<open>x \<in> M\<close> \<open>ds \<in> I \<rightarrow>\<^sub>E UNIV\<close> \<open>i \<in> I\<close>
              by (fastforce simp add: f_def)
            have "\<not> M \<subseteq> S i"
              using \<open>x \<notin> S i\<close> \<open>x \<in> M\<close> by blast
            have "inverse (\<bar>ds i\<bar> + 1) \<le> dd i y"
              using intvl \<open>y \<in> S i\<close> dd_pos [of y i]
              by (smt (verit, ccfv_threshold) greaterThanLessThan_iff inverse_inverse_eq le_imp_inverse_le)
            also have "\<dots> \<le> d x y"
              using \<open>i \<in> I\<close> \<open>\<not> M \<subseteq> S i\<close> \<open>x \<notin> S i\<close> \<open>x \<in> M\<close>
              apply (simp add: dd_def cInf_le_iff_less)
              using commute by force
            finally show False
              using dxy by linarith
          qed
        qed
        moreover have "ds = (\<lambda>i\<in>I. inverse (dd i x))"
        proof (rule PiE_ext [OF ds])
          fix i
          assume "i \<in> I"
          define e where "e \<equiv> \<bar>ds i - inverse (dd i x)\<bar>"
          { assume con: "e > 0"
            have "continuous_map (subtopology mtopology (S i)) euclidean (\<lambda>x. inverse (dd i x))" 
              using dd_pos cont_dd \<open>i \<in> I\<close> 
              by (fastforce simp:  intro!: continuous_map_real_inverse)
             then have "openin (subtopology mtopology (S i))
                         {z \<in> topspace (subtopology mtopology (S i)). 
                          inverse (dd i z) \<in> {inverse(dd i x) - e/2<..<inverse(dd i x) + e/2}}"
               using openin_continuous_map_preimage open_greaterThanLessThan open_openin by blast
             then obtain U where "openin mtopology U"
                  and U: "{z \<in> S i. inverse (dd i x) - e/2 < inverse (dd i z) \<and>
                           inverse (dd i z) < inverse (dd i x) + e/2}
                         = U \<inter> S i"
               using SM \<open>i \<in> I\<close>  by (auto simp: openin_subtopology)
             have "x \<in> U"
               using U x_in_INT \<open>i \<in> I\<close> con by fastforce
             have "ds \<in> {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
               by (simp add: con ds)
             moreover
             have  "openin (powertop_real I) {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
             proof (rule openin_continuous_map_preimage)
               show "continuous_map (powertop_real I) euclidean (\<lambda>x. x i)"
                 by (metis \<open>i \<in> I\<close> continuous_map_product_projection)
             qed auto
             ultimately obtain y where "y \<in> \<Inter>(S ` I) \<and> f y \<in> U \<times> {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
               using ope \<open>x \<in> U\<close> \<open>openin mtopology U\<close> \<open>x \<in> U\<close>
               by presburger 
             with \<open>i \<in> I\<close> U 
             have False unfolding set_eq_iff f_def e_def by simp (smt (verit) field_sum_of_halves)
          }
          then show "ds i = (\<lambda>i\<in>I. inverse (dd i x)) i"
            using \<open>i \<in> I\<close> by (force simp: e_def)
        qed auto
        ultimately show ?thesis
          by (auto simp: T_def f_def)
      qed
      then show "prod_topology mtopology (powertop_real I) closure_of T \<subseteq> T"
        by (auto simp: closure_of_def)
    qed
    have eq: "(\<Inter>(S ` I) \<times> (I \<rightarrow>\<^sub>E UNIV) \<inter> f ` (M \<inter> \<Inter>(S ` I))) = (f ` \<Inter>(S ` I))"
      using False SM by (force simp: f_def image_iff)
    have "continuous_map (subtopology mtopology (\<Inter>(S ` I))) euclidean (dd i)" if "i \<in> I" for i
      by (meson INT_lower cont_dd continuous_map_from_subtopology_mono that)
    then have "continuous_map (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I) (\<lambda>x. \<lambda>i\<in>I. inverse (dd i x))"
      using dd_pos by (fastforce simp: continuous_map_componentwise intro!: continuous_map_real_inverse)
    then have "embedding_map (subtopology mtopology (\<Inter>(S ` I))) (prod_topology (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I)) f"
      by (simp add: embedding_map_graph f_def)
    moreover have "subtopology (prod_topology (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I))
                     (f ` topspace (subtopology mtopology (\<Inter>(S ` I)))) =
                   subtopology (prod_topology mtopology (powertop_real I)) T"
      by (simp add: prod_topology_subtopology subtopology_subtopology T_def eq)
    ultimately
    show "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space subtopology (prod_topology mtopology (powertop_real I)) T"
      by (metis embedding_map_imp_homeomorphic_space)
  qed
qed


lemma gdelta_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "\<And>i. i \<in> I \<Longrightarrow> openin X (S i)"
  obtains T where "closedin (prod_topology X (powertop_real I)) T"
                  "subtopology X (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology X (powertop_real I)) T"
  using Metric_space.gdelta_homeomorphic_space_closedin_product
  by (metis assms metrizable_space_def)

lemma open_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "openin X S"
  obtains T where "closedin (prod_topology X euclideanreal) T"
    "subtopology X S homeomorphic_space
                   subtopology (prod_topology X euclideanreal) T"
proof -
  obtain T where cloT: "closedin (prod_topology X (powertop_real {()})) T"
    and homT: "subtopology X S homeomorphic_space
                   subtopology (prod_topology X (powertop_real {()})) T"
    using gdelta_homeomorphic_space_closedin_product [of X "{()}" "\<lambda>i. S"] assms
    by auto
  have "prod_topology X (powertop_real {()}) homeomorphic_space prod_topology X euclideanreal"
    by (meson homeomorphic_space_prod_topology homeomorphic_space_refl homeomorphic_space_singleton_product)
  then obtain f where f: "homeomorphic_map (prod_topology X (powertop_real {()})) (prod_topology X euclideanreal) f"
    unfolding homeomorphic_space by metis
  show thesis
  proof
    show "closedin (prod_topology X euclideanreal) (f ` T)"
      using cloT f homeomorphic_map_closedness_eq by blast
    moreover have "T = topspace (subtopology (prod_topology X (powertop_real {()})) T)"
      by (metis cloT closedin_subset topspace_subtopology_subset)
    ultimately show "subtopology X S homeomorphic_space subtopology (prod_topology X euclideanreal) (f ` T)"
      by (smt (verit, best) closedin_subset f homT homeomorphic_map_subtopologies homeomorphic_space 
          homeomorphic_space_trans topspace_subtopology topspace_subtopology_subset)
  qed
qed

lemma completely_metrizable_space_gdelta_in_alt:
  assumes X: "completely_metrizable_space X" 
    and S: "(countable intersection_of openin X) S"
  shows "completely_metrizable_space (subtopology X S)"
proof -
  obtain \<U> where "countable \<U>" "S = \<Inter>\<U>" and ope: "\<And>U. U \<in> \<U> \<Longrightarrow> openin X U"
    using S by (force simp add: intersection_of_def)
  then have \<U>: "completely_metrizable_space (powertop_real \<U>)"
    by (simp add: completely_metrizable_space_euclidean completely_metrizable_space_product_topology)
  obtain C where "closedin (prod_topology X (powertop_real \<U>)) C"
                and sub: "subtopology X (\<Inter>\<U>) homeomorphic_space
                   subtopology (prod_topology X (powertop_real \<U>)) C"
    by (metis gdelta_homeomorphic_space_closedin_product  X completely_metrizable_imp_metrizable_space ope INF_identity_eq)
  moreover have "completely_metrizable_space (prod_topology X (powertop_real \<U>))"
    by (simp add: completely_metrizable_space_prod_topology X \<U>)
  ultimately have "completely_metrizable_space (subtopology (prod_topology X (powertop_real \<U>)) C)"
    using completely_metrizable_space_closedin by blast
  then show ?thesis
    using \<open>S = \<Inter>\<U>\<close> sub homeomorphic_completely_metrizable_space by blast
qed

lemma completely_metrizable_space_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; gdelta_in X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
  by (simp add: completely_metrizable_space_gdelta_in_alt gdelta_in_alt)

lemma completely_metrizable_space_openin:
   "\<lbrakk>completely_metrizable_space X; openin X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
  by (simp add: completely_metrizable_space_gdelta_in open_imp_gdelta_in)


lemma (in Metric_space) locally_compact_imp_completely_metrizable_space:
  assumes "locally_compact_space mtopology"
  shows "completely_metrizable_space mtopology"
proof -
  obtain f :: "['a,'a] \<Rightarrow> real" and m' where
    "mcomplete_of m'" and fim: "f \<in> M \<rightarrow> mspace m'"
    and clo: "mtopology_of m' closure_of f ` M = mspace m'"
    and d: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
    by (metis metric_completion)
  then have "embedding_map mtopology (mtopology_of m') f"
    unfolding mtopology_of_def
    by (metis Metric_space12.isometry_imp_embedding_map Metric_space12_mspace_mdist mdist_metric mspace_metric)
  then have hom: "mtopology homeomorphic_space subtopology (mtopology_of m') (f ` M)"
    by (metis embedding_map_imp_homeomorphic_space topspace_mtopology)
  have "locally_compact_space (subtopology (mtopology_of m') (f ` M))"
    using assms hom homeomorphic_locally_compact_space by blast
  moreover have "Hausdorff_space (mtopology_of m')"
    by (simp add: Metric_space.Hausdorff_space_mtopology mtopology_of_def)
  ultimately have "openin (mtopology_of m') (f ` M)"
    by (simp add: clo dense_locally_compact_openin_Hausdorff_space fim image_subset_iff_funcset)
  then
  have "completely_metrizable_space (subtopology (mtopology_of m') (f ` M))"
    using \<open>mcomplete_of m'\<close> unfolding mcomplete_of_def mtopology_of_def
    by (metis Metric_space.completely_metrizable_space_mtopology Metric_space_mspace_mdist completely_metrizable_space_openin )
  then show ?thesis
    using hom homeomorphic_completely_metrizable_space by blast
qed

lemma locally_compact_imp_completely_metrizable_space:
  assumes "metrizable_space X" and "locally_compact_space X"
  shows "completely_metrizable_space X"
  by (metis Metric_space.locally_compact_imp_completely_metrizable_space assms metrizable_space_def)


lemma completely_metrizable_space_imp_gdelta_in:
  assumes X: "metrizable_space X" and "S \<subseteq> topspace X" 
    and XS: "completely_metrizable_space (subtopology X S)"
  shows "gdelta_in X S"
proof -
  obtain U f where "gdelta_in X U" "S \<subseteq> U" and U: "U \<subseteq> X closure_of S"
            and contf: "continuous_map (subtopology X U) (subtopology X S) f" 
            and fid: "\<And>x. x \<in> S \<Longrightarrow> f x = x"
    using Lavrentiev_extension[of S X "subtopology X S" id] assms by auto
  then have "f ` topspace (subtopology X U) \<subseteq> topspace (subtopology X S)"
    using continuous_map_image_subset_topspace by blast
  then have "f`U \<subseteq> S"
    by (metis \<open>gdelta_in X U\<close> \<open>S \<subseteq> topspace X\<close> gdelta_in_subset topspace_subtopology_subset)
  moreover 
  have "Hausdorff_space (subtopology X U)"
    by (simp add: Hausdorff_space_subtopology X metrizable_imp_Hausdorff_space)
  then have "\<And>x. x \<in> U \<Longrightarrow> f x = x"
    using U fid contf forall_in_closure_of_eq [of _ "subtopology X U" S "subtopology X U" f id]
    by (metis \<open>S \<subseteq> U\<close> closure_of_subtopology_open continuous_map_id continuous_map_in_subtopology id_apply inf.orderE subtopology_subtopology)
  ultimately have "U \<subseteq> S"
    by auto
  then show ?thesis
    using \<open>S \<subseteq> U\<close> \<open>gdelta_in X U\<close> by auto
qed

lemma completely_metrizable_space_eq_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; S \<subseteq> topspace X\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S) \<longleftrightarrow> gdelta_in X S"
  using completely_metrizable_imp_metrizable_space completely_metrizable_space_gdelta_in completely_metrizable_space_imp_gdelta_in by blast

lemma gdelta_in_eq_completely_metrizable_space:
   "completely_metrizable_space X
    \<Longrightarrow> gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> completely_metrizable_space (subtopology X S)"
  by (metis completely_metrizable_space_eq_gdelta_in gdelta_in_alt)

subsection\<open> Theorems from Kuratowski\<close>

text\<open>Kuratowski, Remark on an Invariance Theorem, \emph{Fundamenta Mathematicae} \textbf{37} (1950), pp. 251-252. 
 The idea is that in suitable spaces, to show "number of components of the complement" (without 
 distinguishing orders of infinity) is a homeomorphic invariant, it 
 suffices to show it for closed subsets. Kuratowski states the main result 
 for a "locally connected continuum", and seems clearly to be implicitly   
 assuming that means metrizable. We call out the general topological       
 hypotheses more explicitly, which do not however include connectedness.   \<close>

lemma separation_by_closed_intermediates_count:
  assumes X: "hereditarily normal_space X"
    and "finite \<U>"
    and pwU: "pairwise (separatedin X) \<U>"
    and nonempty: "{} \<notin> \<U>"
    and UU: "\<Union>\<U> = topspace X - S"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. \<V> \<approx> \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
proof -
  obtain F where F: "\<And>S. S \<in> \<U> \<Longrightarrow> openin X (F S) \<and> S \<subseteq> F S"
    and pwF: "pairwise (\<lambda>S T. disjnt (F S) (F T)) \<U>"
    using assms by (smt (verit, best) Diff_subset Sup_le_iff hereditarily_normal_separation_pairwise)
  show thesis
  proof
    show "closedin X (topspace X - \<Union>(F ` \<U>))"
      using F by blast
    show "topspace X - \<Union>(F ` \<U>) \<subseteq> S"
      using UU F by auto
    show "\<exists>\<V>. \<V> \<approx> \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - C"
      if "closedin X C" "C \<subseteq> S" and C: "topspace X - \<Union>(F ` \<U>) \<subseteq> C" for C
    proof (intro exI conjI strip)
      have "inj_on (\<lambda>S. F S - C) \<U>"
        using pwF F
        unfolding inj_on_def pairwise_def disjnt_iff
        by (metis Diff_iff UU UnionI nonempty subset_empty subset_eq \<open>C \<subseteq> S\<close>)
      then show "(\<lambda>S. F S - C) ` \<U> \<approx> \<U>"
        by simp
      show "pairwise (separatedin X) ((\<lambda>S. F S - C) ` \<U>)"
        using \<open>closedin X C\<close> F pwF by (force simp: pairwise_def openin_diff separatedin_open_sets disjnt_iff)
      show "{} \<notin> (\<lambda>S. F S - C) ` \<U>"
        using nonempty UU \<open>C \<subseteq> S\<close> F
        by clarify (metis DiffD2 Diff_eq_empty_iff F UnionI subset_empty subset_eq)
      show "(\<Union>S\<in>\<U>. F S - C) = topspace X - C"
        using UU F C openin_subset by fastforce
    qed
  qed
qed

lemma separation_by_closed_intermediates_gen:
  assumes X: "hereditarily normal_space X"
    and discon: "\<not> connectedin X (topspace X - S)"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk> \<Longrightarrow> \<not> connectedin X (topspace X - D)"
proof -
  obtain C1 C2 where Ueq: "C1 \<union> C2 = topspace X - S" and "C1 \<noteq> {}" "C2 \<noteq> {}" 
    and sep: "separatedin X C1 C2" and "C1 \<noteq> C2"
    by (metis Diff_subset connectedin_eq_not_separated discon separatedin_refl)
  then obtain C where "closedin X C" "C \<subseteq> S"
    and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. \<V> \<approx> {C1,C2} \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
    using separation_by_closed_intermediates_count [of X "{C1,C2}" S] X
    apply (simp add: pairwise_insert separatedin_sym)
    by metis
  have "\<not> connectedin X (topspace X - D)"
    if D: "closedin X D" "C \<subseteq> D" "D \<subseteq> S" for D 
  proof -
    obtain V1 V2 where *: "pairwise (separatedin X) {V1,V2}" "{} \<notin> {V1,V2}" 
                          "\<Union>{V1,V2} = topspace X - D" "V1\<noteq>V2"
      by (metis C [OF D] \<open>C1 \<noteq> C2\<close> eqpoll_doubleton_iff)
    then have "disjnt V1 V2"
      by (metis pairwise_insert separatedin_imp_disjoint singleton_iff)
      with * show ?thesis
        by (auto simp add: connectedin_eq_not_separated pairwise_insert)
    qed
  then show thesis
    using \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> that by auto
qed

lemma separation_by_closed_intermediates_eq_count:
  fixes n::nat
  assumes lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
  shows "(\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>\<U>.  \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D)))"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (smt (verit, best) hnX separation_by_closed_intermediates_count eqpoll_iff_finite_card eqpoll_trans)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "n=0")
    case True
    with R show ?thesis
      by fastforce
  next
    case False
    obtain C where "closedin X C" "C \<subseteq> S"
             and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
      using R by force
    then have "C \<subseteq> topspace X"
      by (simp add: closedin_subset)
    define \<U> where "\<U> \<equiv> {D \<in> connected_components_of (subtopology X (topspace X - C)). D-S \<noteq> {}}"
    have ope\<U>: "openin X U" if "U \<in> \<U>" for U
      using that  \<open>closedin X C\<close> lcX locally_connected_space_open_connected_components 
      by (fastforce simp add: closedin_def \<U>_def)
    have "{} \<notin> \<U>"
      by (auto simp: \<U>_def)
    have "pairwise disjnt \<U>"
      using connected_components_of_disjoint by (fastforce simp add: pairwise_def \<U>_def)
    show ?lhs
    proof (rule ccontr)
      assume con: "\<nexists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
      have card\<U>: "finite \<U> \<and> card \<U> < n"
      proof (rule ccontr)
        assume "\<not> (finite \<U> \<and> card \<U> < n)"
        then obtain \<V> where "\<V> \<subseteq> \<U>" "finite \<V>" "card \<V> = n"
          by (metis infinite_arbitrarily_large linorder_not_less obtain_subset_with_card_n)
        then obtain T where "T \<in> \<V>"
          using False by force
        define \<W> where "\<W> \<equiv> insert (topspace X - S - \<Union>(\<V> - {T})) ((\<lambda>D. D - S) ` (\<V> - {T}))"
        have "\<Union>\<W> = topspace X - S"
          using \<open>\<And>U. U \<in> \<U> \<Longrightarrow> openin X U\<close> \<open>\<V> \<subseteq> \<U>\<close> topspace_def by (fastforce simp: \<W>_def)
        moreover have "{} \<notin> \<W>"
        proof -
          obtain a where "a \<in> T" "a \<notin> S"
            using \<U>_def \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> by blast
          then have "a \<in> topspace X"
            using \<open>T \<in> \<V>\<close> ope\<U> \<open>\<V> \<subseteq> \<U>\<close> openin_subset by blast
          moreover have "a \<notin> \<Union>(\<V> - {T})"
            using diff_Union_pairwise_disjoint [of \<V> "{T}"] \<open>disjoint \<U>\<close> pairwise_subset \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> \<open>a \<in> T\<close> 
            by auto
          ultimately have "topspace X - S - \<Union>(\<V> - {T}) \<noteq> {}"
            using \<open>a \<notin> S\<close> by blast
          moreover have "\<And>V. V \<in> \<V> - {T} \<Longrightarrow> V - S \<noteq> {}"
            using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> by blast
          ultimately show ?thesis
            by (metis (no_types, lifting) \<W>_def image_iff insert_iff)
        qed
        moreover have "disjoint \<V>"
          using \<open>\<V> \<subseteq> \<U>\<close> \<open>disjoint \<U>\<close> pairwise_subset by blast
        then have inj: "inj_on (\<lambda>D. D - S) (\<V> - {T})"
          unfolding inj_on_def using \<open>\<V> \<subseteq> \<U>\<close> disjointD \<U>_def inf_commute by blast
        have "finite \<W>" "card \<W> = n"
          using \<open>{} \<notin> \<W>\<close> \<open>n \<noteq> 0\<close> \<open>T \<in> \<V>\<close>
          by (auto simp add: \<W>_def \<open>finite \<V>\<close> card_insert_if card_image inj \<open>card \<V> = n\<close>)
        moreover have "pairwise (separatedin X) \<W>"
        proof -
          have "disjoint \<W>"
            using \<open>disjoint \<V>\<close> by (auto simp: \<W>_def pairwise_def disjnt_iff)
          have "pairwise (separatedin (subtopology X (topspace X - S))) \<W>"
          proof (intro pairwiseI)
            fix A B
            assume \<section>: "A \<in> \<W>" "B \<in> \<W>" "A \<noteq> B"
            then have "disjnt A B"
              by (meson \<open>disjoint \<W>\<close> pairwiseD)
            have "closedin (subtopology X (topspace X - C)) (\<Union>(\<V> - {T}))"
              using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> closedin_connected_components_of \<open>finite \<V>\<close>
              by (force simp add: intro!: closedin_Union)
            with \<open>C \<subseteq> S\<close> have "openin (subtopology X (topspace X - S)) (topspace X - S - \<Union>(\<V> - {T}))"
              by (fastforce simp add: openin_closedin_eq closedin_subtopology Int_absorb1)
            moreover have "\<And>V. V \<in> \<V> \<and> V\<noteq>T \<Longrightarrow> openin (subtopology X (topspace X - S)) (V - S)"
              using \<open>\<V> \<subseteq> \<U>\<close> ope\<U>
              by (metis IntD2 Int_Diff inf.orderE openin_subset openin_subtopology) 
            ultimately have "openin (subtopology X (topspace X - S)) A" "openin (subtopology X (topspace X - S)) B"
              using \<section> \<W>_def by blast+
            with \<open>disjnt A B\<close> show "separatedin (subtopology X (topspace X - S)) A B"
              using separatedin_open_sets by blast
          qed
          then show ?thesis
            by (simp add: pairwise_def separatedin_subtopology)
        qed
        ultimately show False
          by (metis con eqpoll_iff_finite_card)
      qed
      obtain \<V> where "\<V> \<approx> {..<n} " "{} \<notin> \<V>"
                and pw\<V>: "pairwise (separatedin X) \<V>" and UV: "\<Union>\<V> = topspace X - (topspace X - \<Union>\<U>)"
      proof -
        have "closedin X (topspace X - \<Union>\<U>)"
          using ope\<U> by blast
        moreover have "C \<subseteq> topspace X - \<Union>\<U>"
          using \<open>C \<subseteq> topspace X\<close> connected_components_of_subset by (fastforce simp: \<U>_def)
        moreover have "topspace X - \<Union>\<U> \<subseteq> S"
          using Union_connected_components_of [of "subtopology X (topspace X - C)"] \<open>C \<subseteq> S\<close>
          by (auto simp: \<U>_def)
        ultimately show thesis
          by (metis C that)
      qed
      have "\<V> \<lesssim> \<U>"
      proof (rule lepoll_relational_full)
        have "\<Union>\<V> = \<Union>\<U>"
          by (simp add: Sup_le_iff UV double_diff ope\<U> openin_subset)
        then show "\<exists>U. U \<in> \<U> \<and> \<not> disjnt U V" if "V \<in> \<V>" for V
          using that
          by (metis \<open>{} \<notin> \<V>\<close> disjnt_Union1 disjnt_self_iff_empty)
        show "C1 = C2"
          if "T \<in> \<U>" and "C1 \<in> \<V>" and "C2 \<in> \<V>" and "\<not> disjnt T C1" and "\<not> disjnt T C2" for T C1 C2
        proof (cases "C1=C2")
          case False
          then have "connectedin X T"
            using \<U>_def connectedin_connected_components_of connectedin_subtopology \<open>T \<in> \<U>\<close> by blast
          have "T \<subseteq> C1 \<union> \<Union>(\<V> - {C1})"
            using \<open>\<Union>\<V> = \<Union>\<U>\<close> \<open>T \<in> \<U>\<close> by auto
          with \<open>connectedin X T\<close>
          have "\<not> separatedin X C1 (\<Union>(\<V> - {C1}))"
            unfolding connectedin_eq_not_separated_subset
            by (smt (verit) that False disjnt_def UnionI disjnt_iff insertE insert_Diff)
          with that show ?thesis
            by (metis (no_types, lifting) \<open>\<V> \<approx> {..<n}\<close> eqpoll_iff_finite_card finite_Diff pairwiseD pairwise_alt pw\<V> separatedin_Union(1) separatedin_def)
        qed auto
      qed
      then show False
        by (metis \<open>\<V> \<approx> {..<n}\<close> card\<U> eqpoll_iff_finite_card leD lepoll_iff_card_le)
    qed
  qed
qed

lemma separation_by_closed_intermediates_eq_gen:
  assumes "locally_connected_space X" "hereditarily normal_space X"
  shows "\<not> connectedin X (topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S \<longrightarrow> \<not> connectedin X (topspace X - D)))"
    (is "?lhs = ?rhs")
proof -
  have *: "(\<exists>\<U>::'a set set. \<U> \<approx> {..<Suc (Suc 0)} \<and> P \<U>) \<longleftrightarrow> (\<exists>A B. A\<noteq>B \<and> P{A,B})" for P
    by (metis One_nat_def eqpoll_doubleton_iff lessThan_Suc lessThan_empty_iff zero_neq_one)
  have *: "(\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - D)))"
    using separation_by_closed_intermediates_eq_count [OF assms, of "Suc(Suc 0)" S]
    apply (simp add: * pairwise_insert separatedin_sym cong: conj_cong)
    apply (simp add: eq_sym_conv conj_ac)
    done
  with separatedin_refl
  show ?thesis
    apply (simp add: connectedin_eq_not_separated)
    by (smt (verit, best) separatedin_refl)
qed



lemma lepoll_connnected_components_connectedin:
  assumes "\<And>C. C \<in> \<U> \<Longrightarrow> connectedin X C"  "\<Union>\<U> = topspace X"
  shows "connected_components_of X \<lesssim> \<U>"
proof -
  have "connected_components_of X \<lesssim> \<U> - {{}}"
  proof (rule lepoll_relational_full)
    show "\<exists>U. U \<in> \<U> - {{}} \<and> U \<subseteq> V"
      if "V \<in> connected_components_of X" for V 
      using that unfolding connected_components_of_def image_iff
      by (metis Union_iff assms connected_component_of_maximal empty_iff insert_Diff_single insert_iff)
    show "V = V'"
      if "U \<in> \<U> - {{}}" "V \<in> connected_components_of X" "V' \<in> connected_components_of X" "U \<subseteq> V" "U \<subseteq> V'"
      for U V V'
      by (metis DiffD2 disjointD insertCI le_inf_iff pairwise_disjoint_connected_components_of subset_empty that)
  qed
  also have "\<dots> \<lesssim> \<U>"
    by (simp add: subset_imp_lepoll)
  finally show ?thesis .
qed

lemma lepoll_connected_components_alt:
  "{..<n::nat} \<lesssim> connected_components_of X \<longleftrightarrow>
    n = 0 \<or> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "n=0")
next
  case False
  show ?thesis 
  proof
    assume L: ?lhs 
    with False show ?rhs
    proof (induction n rule: less_induct)
      case (less n)
      show ?case
      proof (cases "n\<le>1")
        case True
        with less.prems have "topspace X \<noteq> {}" "n=1"
          by (fastforce simp add: connected_components_of_def)+
        then have "{} \<notin> {topspace X}"
          by blast
        with \<open>n=1\<close> show ?thesis
          by (simp add: eqpoll_iff_finite_card card_Suc_eq flip: ex_simps)
      next
        case False
        then have "n-1 \<noteq> 0"
          by linarith
        have n1_lesspoll: "{..<n-1} \<prec> {..<n}"
          using False lesspoll_iff_finite_card by fastforce
        also have "\<dots> \<lesssim> connected_components_of X"
          using less by blast
        finally have "{..<n-1} \<lesssim> connected_components_of X"
          using lesspoll_imp_lepoll by blast 
        then obtain \<U> where Ueq: "\<U> \<approx> {..<n-1}" and "{} \<notin> \<U>" 
          and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
          by (meson \<open>n - 1 \<noteq> 0\<close> diff_less gr0I less zero_less_one)
        show ?thesis
        proof (cases "\<forall>C \<in> \<U>. connectedin X C")
          case True
          then show ?thesis
            using lepoll_connnected_components_connectedin [of \<U> X] less.prems
            by (metis UU Ueq lepoll_antisym lepoll_trans lepoll_trans2 lesspoll_def n1_lesspoll)
          next
            case False
            with UU obtain C A B where ABC: "C \<in> \<U>" "A \<union> B = C" "A \<noteq> {}" "B \<noteq> {}" and sep: "separatedin X A B"
              by (fastforce simp add: connectedin_eq_not_separated)
            define \<V> where "\<V> \<equiv> insert A (insert B (\<U> - {C}))"
            have "\<V> \<approx> {..<n}"
            proof -
              have "A \<noteq> B"
                using \<open>B \<noteq> {}\<close> sep by auto
              moreover obtain "A \<notin> \<U>" "B \<notin> \<U>"
                using pwU unfolding pairwise_def
                by (metis ABC sep separatedin_Un(1) separatedin_refl separatedin_sym)
              moreover have "card \<U> = n-1" "finite \<U>"
                using Ueq eqpoll_iff_finite_card by blast+
              ultimately
              have "card (insert A (insert B (\<U> - {C}))) = n"
                using \<open>C \<in> \<U>\<close> by (auto simp add: card_insert_if)
              then show ?thesis
                using \<V>_def \<open>finite \<U>\<close> eqpoll_iff_finite_card by blast
            qed
            moreover have "{} \<notin> \<V>"
              using ABC \<V>_def \<open>{} \<notin> \<U>\<close> by blast
            moreover have "\<Union>\<V> = topspace X"
              using ABC UU \<V>_def by auto
            moreover have "pairwise (separatedin X) \<V>"
              using pwU sep ABC unfolding  \<V>_def
              apply (simp add: separatedin_sym pairwise_def)
              by (metis member_remove remove_def separatedin_Un(1))
            ultimately show ?thesis
              by blast
          qed
      qed
    qed
  next
    assume ?rhs
    then obtain \<U> where "\<U> \<approx> {..<n}" "{} \<notin> \<U>" and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
      using False by force
    have "card (connected_components_of X) \<ge> n" if "finite (connected_components_of X)"
    proof -
      have "\<U> \<lesssim> connected_components_of X"
      proof (rule lepoll_relational_full)
        show "\<exists>T. T \<in> connected_components_of X \<and> \<not> disjnt T C" if "C \<in> \<U>" for C 
          by (metis that UU Union_connected_components_of Union_iff \<open>{} \<notin> \<U>\<close> disjnt_iff equals0I)
        show "(C1::'a set) = C2"
          if "T \<in> connected_components_of X" and "C1 \<in> \<U>" "C2 \<in> \<U>" "\<not> disjnt T C1" "\<not> disjnt T C2" for T C1 C2
        proof (rule ccontr)
          assume "C1 \<noteq> C2"
          then have "connectedin X T"
            by (simp add: connectedin_connected_components_of that(1))
          moreover have "\<not> separatedin X C1 (\<Union>(\<U> - {C1}))"
            using \<open>connectedin X T\<close> pwU unfolding pairwise_def
            by (smt (verit) Sup_upper UU Union_connected_components_of \<open>C1 \<noteq> C2\<close> complete_lattice_class.Sup_insert connectedin_subset_separated_union disjnt_subset2 disjnt_sym insert_Diff separatedin_imp_disjoint that)
          ultimately show False
            using \<open>\<U> \<approx> {..<n}\<close>
            apply (simp add: connectedin_eq_not_separated_subset eqpoll_iff_finite_card)
            by (metis Sup_upper UU finite_Diff pairwise_alt pwU separatedin_Union(1) that(2))
        qed
      qed
      then show ?thesis
        by (metis \<open>\<U> \<approx> {..<n}\<close> eqpoll_iff_finite_card lepoll_iff_card_le that)
    qed
    then show ?lhs
      by (metis card_lessThan finite_lepoll_infinite finite_lessThan lepoll_iff_card_le)
  qed
qed auto


subsection\<open>A perfect set in common cases must have at least the cardinality of the continuum\<close>

lemma (in Metric_space) lepoll_perfect_set:
  assumes "mcomplete"
    and "mtopology derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
proof -
  have "S \<subseteq> M"
    using assms(2) derived_set_of_infinite_mball by blast
  have "(UNIV::real set) \<lesssim> (UNIV::nat set set)"
    using eqpoll_imp_lepoll eqpoll_sym nat_sets_eqpoll_reals by blast
  also have "\<dots> \<lesssim> S"
  proof -
    have "\<exists>y z \<delta>. y \<in> S \<and> z \<in> S \<and> 0 < \<delta> \<and> \<delta> < \<epsilon>/2 \<and>
                  mcball y \<delta> \<subseteq> mcball x \<epsilon> \<and> mcball z \<delta> \<subseteq> mcball x \<epsilon> \<and> disjnt (mcball y \<delta>) (mcball z \<delta>)"
      if "x \<in> S" "0 < \<epsilon>" for x \<epsilon>
    proof -
      define S' where "S' \<equiv> S \<inter> mball x (\<epsilon>/4)"
      have "infinite S'"
        using derived_set_of_infinite_mball [of S] assms that S'_def
        by (smt (verit, ccfv_SIG) mem_Collect_eq zero_less_divide_iff)
      then have "\<And>x y z. \<not> (S' \<subseteq> {x,y,z})"
        using finite_subset by auto
      then obtain l r where lr: "l \<in> S'" "r \<in> S'" "l\<noteq>r" "l\<noteq>x" "r\<noteq>x"
        by (metis insert_iff subsetI)
      show ?thesis
      proof (intro exI conjI)
        show "l \<in> S" "r \<in> S" "d l r / 3 > 0"
          using lr by (auto simp: S'_def)
        show "d l r / 3 < \<epsilon>/2" "mcball l (d l r / 3) \<subseteq> mcball x \<epsilon>" "mcball r (d l r / 3) \<subseteq> mcball x \<epsilon>"
          using lr by (clarsimp simp: S'_def, smt (verit) commute triangle'')+
        show "disjnt (mcball l (d l r / 3)) (mcball r (d l r / 3))"
          using lr by (simp add: S'_def disjnt_iff) (smt (verit, best) mdist_pos_less triangle')
      qed
    qed
    then obtain l r \<delta> 
        where lrS: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> l x \<epsilon> \<in> S \<and> r x \<epsilon> \<in> S"
          and \<delta>: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> 0 < \<delta> x \<epsilon> \<and> \<delta> x \<epsilon> < \<epsilon>/2"
          and "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow>  mcball (l x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> mcball (r x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> 
                  disjnt (mcball (l x \<epsilon>) (\<delta> x \<epsilon>)) (mcball (r x \<epsilon>) (\<delta> x \<epsilon>))"
      by metis
    then have lr_mcball: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> mcball (l x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> mcball (r x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> "
          and lr_disjnt: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> disjnt (mcball (l x \<epsilon>) (\<delta> x \<epsilon>)) (mcball (r x \<epsilon>) (\<delta> x \<epsilon>))"
      by metis+
    obtain a where "a \<in> S"
      using \<open>S \<noteq> {}\<close> by blast
    define xe where "xe \<equiv> 
           \<lambda>B. rec_nat (a,1) (\<lambda>n (x,\<gamma>). ((if n\<in>B then r else l) x \<gamma>, \<delta> x \<gamma>))"
    have [simp]: "xe b 0 = (a,1)" for b
      by (simp add: xe_def)
    have "xe B (Suc n) = (let (x,\<gamma>) = xe B n in ((if n\<in>B then r else l) x \<gamma>, \<delta> x \<gamma>))" for B n
      by (simp add: xe_def)
    define x where "x \<equiv> \<lambda>B n. fst (xe B n)"
    define \<gamma> where "\<gamma> \<equiv> \<lambda>B n. snd (xe B n)"
    have [simp]: "x B 0 = a" "\<gamma> B 0 = 1" for B
      by (simp_all add: x_def \<gamma>_def xe_def)
    have x_Suc[simp]: "x B (Suc n) = ((if n\<in>B then r else l) (x B n) (\<gamma> B n))" 
     and \<gamma>_Suc[simp]: "\<gamma> B (Suc n) = \<delta> (x B n) (\<gamma> B n)" for B n
      by (simp_all add: x_def \<gamma>_def xe_def split: prod.split)
    interpret Submetric M d S
    proof qed (use \<open>S \<subseteq> M\<close> in metis)
    have "closedin mtopology S"
      by (metis assms(2) closure_of closure_of_eq inf.absorb_iff2 subset subset_Un_eq subset_refl topspace_mtopology)
    with \<open>mcomplete\<close>
    have "sub.mcomplete"
      by (metis closedin_mcomplete_imp_mcomplete)
    have *: "x B n \<in> S \<and> \<gamma> B n > 0" for B n
      by (induction n) (auto simp: \<open>a \<in> S\<close> lrS \<delta>)
    with subset have E: "x B n \<in> M" for B n
      by blast
    have \<gamma>_le: "\<gamma> B n \<le> (1/2)^n" for B n
    proof(induction n)
      case 0 then show ?case by auto
    next
      case (Suc n)
      then show ?case
        by simp (smt (verit) "*" \<delta> field_sum_of_halves)
    qed
    { fix B
      have "\<And>n. sub.mcball (x B (Suc n)) (\<gamma> B (Suc n)) \<subseteq> sub.mcball (x B n) (\<gamma> B n)"
        by (smt (verit, best) "*" Int_iff \<gamma>_Suc x_Suc in_mono lr_mcball mcball_submetric_eq subsetI)
      then have mon: "monotone (\<le>) (\<lambda>x y. y \<subseteq> x) (\<lambda>n. sub.mcball (x B n) (\<gamma> B n))"
        by (simp add: decseq_SucI)
      have "\<exists>n a. sub.mcball (x B n) (\<gamma> B n) \<subseteq> sub.mcball a \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        obtain n where "(1/2)^n < \<epsilon>"
          using \<open>0 < \<epsilon>\<close> real_arch_pow_inv by force
        with \<gamma>_le have \<epsilon>: "\<gamma> B n \<le> \<epsilon>"
          by (smt (verit))
        show ?thesis
        proof (intro exI)
          show "sub.mcball (x B n) (\<gamma> B n) \<subseteq> sub.mcball (x B n) \<epsilon>"
            by (simp add: \<epsilon> sub.mcball_subset_concentric)
        qed
      qed
      then have "\<exists>l. l \<in> S \<and> (\<Inter>n. sub.mcball (x B n) (\<gamma> B n)) = {l}"
        using \<open>sub.mcomplete\<close> mon 
        unfolding sub.mcomplete_nest_sing
        apply (drule_tac x="\<lambda>n. sub.mcball (x B n) (\<gamma> B n)" in spec)
        by (meson * order.asym sub.closedin_mcball sub.mcball_eq_empty)
    }
    then obtain z where z: "\<And>B. z B \<in> S \<and> (\<Inter>n. sub.mcball (x B n) (\<gamma> B n)) = {z B}"
      by metis
    show ?thesis
      unfolding lepoll_def
    proof (intro exI conjI)
      show "inj z"
      proof (rule inj_onCI)
        fix B C
        assume eq: "z B = z C" and "B \<noteq> C"
        then have ne: "sym_diff B C \<noteq> {}"
          by blast
        define n where "n \<equiv> LEAST k. k \<in> (sym_diff B C)"
        with ne have n: "n \<in> sym_diff B C"
          by (metis Inf_nat_def1 LeastI)
        then have non: "n \<in> B \<longleftrightarrow> n \<notin> C"
          by blast
        have H: "z C \<in> sub.mcball (x B (Suc n)) (\<gamma> B (Suc n)) \<and> z C \<in> sub.mcball (x C (Suc n)) (\<gamma> C (Suc n))"
          using z [of B] z [of C] apply (simp add: lrS set_eq_iff non *)
          by (smt (verit, best) \<gamma>_Suc eq non x_Suc)
        have "k \<in> B \<longleftrightarrow> k \<in> C" if "k<n" for k
          using that unfolding n_def by (meson DiffI UnCI not_less_Least)
        moreover have "(\<forall>m. m < p \<longrightarrow> (m \<in> B \<longleftrightarrow> m \<in> C)) \<Longrightarrow> x B p = x C p \<and> \<gamma> B p = \<gamma> C p" for p
          by (induction p) auto
        ultimately have "x B n = x C n" "\<gamma> B n = \<gamma> C n"
           by blast+
        then show False
          using lr_disjnt * H non
          by (smt (verit) IntD2 \<gamma>_Suc disjnt_iff mcball_submetric_eq x_Suc)
      qed
      show "range z \<subseteq> S"
        using z by blast
    qed
  qed
  finally show ?thesis .
qed

lemma lepoll_perfect_set_aux:
  assumes lcX: "locally_compact_space X" and hsX: "Hausdorff_space X"
    and eq: "X derived_set_of topspace X = topspace X" and "topspace X \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "(UNIV::real set) \<lesssim> (UNIV::nat set set)"
    using eqpoll_imp_lepoll eqpoll_sym nat_sets_eqpoll_reals by blast
  also have "\<dots> \<lesssim> topspace X"
  proof -
    obtain z where z: "z \<in> topspace X"
      using assms by blast
    then obtain U K where "openin X U" "compactin X K" "U \<noteq> {}" "U \<subseteq> K"
      by (metis emptyE lcX locally_compact_space_def)
    then have "closedin X K"
      by (simp add: compactin_imp_closedin hsX)
    have intK_ne: "X interior_of K \<noteq> {}"
        using \<open>U \<noteq> {}\<close> \<open>U \<subseteq> K\<close> \<open>openin X U\<close> interior_of_eq_empty by blast
    have "\<exists>D E. closedin X D \<and> D \<subseteq> K \<and> X interior_of D \<noteq> {} \<and>
                closedin X E \<and> E \<subseteq> K \<and> X interior_of E \<noteq> {} \<and>
                disjnt D E \<and> D \<subseteq> C \<and> E \<subseteq> C"
      if "closedin X C" "C \<subseteq> K" and C: "X interior_of C \<noteq> {}" for C
    proof -
      obtain z where z: "z \<in> X interior_of C" "z \<in> topspace X"
        using C interior_of_subset_topspace by fastforce 
      obtain x y where "x \<in> X interior_of C" "y \<in> X interior_of C" "x\<noteq>y"
        by (metis z eq in_derived_set_of openin_interior_of)
      then have "x \<in> topspace X" "y \<in> topspace X"
        using interior_of_subset_topspace by force+
      with hsX obtain V W where "openin X V" "openin X W" "x \<in> V" "y \<in> W" "disjnt V W"
        by (metis Hausdorff_space_def \<open>x \<noteq> y\<close>)
      have *: "\<And>W x. openin X W \<and> x \<in> W
            \<Longrightarrow> \<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
        using lcX hsX locally_compact_Hausdorff_imp_regular_space neighbourhood_base_of_closedin neighbourhood_base_of
        by metis
      obtain M D where MD: "openin X M" "closedin X D" "y \<in> M" "M \<subseteq> D" "D \<subseteq> X interior_of C \<inter> W"
        using * [of "X interior_of C \<inter> W" y]
        using \<open>openin X W\<close> \<open>y \<in> W\<close> \<open>y \<in> X interior_of C\<close> by fastforce
      obtain N E where NE: "openin X N" "closedin X E" "x \<in> N" "N \<subseteq> E" "E \<subseteq> X interior_of C \<inter> V"
        using * [of "X interior_of C \<inter> V" x]
        using \<open>openin X V\<close> \<open>x \<in> V\<close> \<open>x \<in> X interior_of C\<close> by fastforce
      show ?thesis
      proof (intro exI conjI)
        show "X interior_of D \<noteq> {}" "X interior_of E \<noteq> {}"
          using MD NE by (fastforce simp: interior_of_def)+
        show "disjnt D E"
          by (meson MD(5) NE(5) \<open>disjnt V W\<close> disjnt_subset1 disjnt_sym le_inf_iff)
      qed (use MD NE \<open>C \<subseteq> K\<close> interior_of_subset in force)+
    qed
    then obtain L R where
     LR: "\<And>C. \<lbrakk>closedin X C; C \<subseteq> K; X interior_of C \<noteq> {}\<rbrakk>
      \<Longrightarrow> closedin X (L C) \<and> (L C) \<subseteq> K \<and> X interior_of (L C) \<noteq> {} \<and>
                closedin X (R C) \<and> (R C) \<subseteq> K \<and> X interior_of (R C) \<noteq> {}"
     and disjLR: "\<And>C. \<lbrakk>closedin X C; C \<subseteq> K; X interior_of C \<noteq> {}\<rbrakk>
      \<Longrightarrow> disjnt (L C) (R C) \<and> (L C) \<subseteq> C \<and> (R C) \<subseteq> C"
      by metis
    define d where "d \<equiv> \<lambda>B. rec_nat K (\<lambda>n. if n \<in> B then R else L)"
    have d0[simp]: "d B 0 = K" for B
      by (simp add: d_def)
    have [simp]: "d B (Suc n) = (if n \<in> B then R else L) (d B n)" for B n
      by (simp add: d_def)
    have d_correct: "closedin X (d B n) \<and> d B n \<subseteq> K \<and> X interior_of (d B n) \<noteq> {}" for B n
    proof (induction n)
      case 0
      then show ?case by (auto simp: \<open>closedin X K\<close> intK_ne)
    next
      case (Suc n) with LR show ?case by auto
    qed
    have "(\<Inter>n. d B n) \<noteq> {}" for B
    proof (rule compact_space_imp_nest)
      show "compact_space (subtopology X K)"
        by (simp add: \<open>compactin X K\<close> compact_space_subtopology)
      show "closedin (subtopology X K) (d B n)" for n :: nat
        by (simp add: closedin_subset_topspace d_correct)
      show "d B n \<noteq> {}" for n :: nat
        by (metis d_correct interior_of_empty)
      show "antimono (d B)"
      proof (rule antimonoI [OF transitive_stepwise_le])
        fix n
        show "d B (Suc n) \<subseteq> d B n"
        by (simp add: d_correct disjLR)
      qed auto
    qed
    then obtain x where x: "\<And>B. x B \<in> (\<Inter>n. d B n)"
      unfolding set_eq_iff by (metis empty_iff)
    show ?thesis
      unfolding lepoll_def
    proof (intro exI conjI)
      show "inj x"
      proof (rule inj_onCI)
        fix B C
        assume eq: "x B = x C" and "B\<noteq>C"
        then have ne: "sym_diff B C \<noteq> {}"
          by blast
        define n where "n \<equiv> LEAST k. k \<in> (sym_diff B C)"
        with ne have n: "n \<in> sym_diff B C"
          by (metis Inf_nat_def1 LeastI)
        then have non: "n \<in> B \<longleftrightarrow> n \<notin> C"
          by blast
        have "k \<in> B \<longleftrightarrow> k \<in> C" if "k<n" for k
          using that unfolding n_def by (meson DiffI UnCI not_less_Least)
        moreover have "(\<forall>m. m < p \<longrightarrow> (m \<in> B \<longleftrightarrow> m \<in> C)) \<Longrightarrow> d B p = d C p" for p
          by (induction p) auto
        ultimately have "d B n = d C n"
          by blast
        then have "disjnt (d B (Suc n)) (d C (Suc n))"
          by (simp add: d_correct disjLR disjnt_sym non)
        then show False
          by (metis InterE disjnt_iff eq rangeI x)
      qed
      show "range x \<subseteq> topspace X"
        using x d0 \<open>compactin X K\<close> compactin_subset_topspace d_correct by fastforce
    qed
  qed
  finally show ?thesis .
qed

lemma lepoll_perfect_set:
  assumes X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and S: "X derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
  using X
proof
  assume "completely_metrizable_space X"
  with assms show "(UNIV::real set) \<lesssim> S"
    by (metis Metric_space.lepoll_perfect_set completely_metrizable_space_def)
next
  assume "locally_compact_space X \<and> Hausdorff_space X"
  then show "(UNIV::real set) \<lesssim> S"
    using lepoll_perfect_set_aux [of "subtopology X S"]
    by (metis Hausdorff_space_subtopology S closedin_derived_set_of closedin_subset derived_set_of_subtopology 
        locally_compact_space_closed_subset subtopology_topspace topspace_subtopology topspace_subtopology_subset)
qed




lemma Kuratowski_aux1:
  assumes "\<And>S T. R S T \<Longrightarrow> R T S"
  shows "(\<forall>S T n. R S T \<longrightarrow> (f S \<approx> {..<n::nat} \<longleftrightarrow> f T \<approx> {..<n::nat})) \<longleftrightarrow>
         (\<forall>n S T. R S T \<longrightarrow> {..<n::nat} \<lesssim> f S \<longrightarrow> {..<n::nat} \<lesssim> f T)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (meson eqpoll_iff_finite_card eqpoll_sym finite_lepoll_infinite finite_lessThan lepoll_trans2)
next
  assume ?rhs then show ?lhs
    by (smt (verit, best) lepoll_iff_finite_card  assms eqpoll_iff_finite_card finite_lepoll_infinite 
        finite_lessThan le_Suc_eq lepoll_antisym lepoll_iff_card_le not_less_eq_eq)
qed

lemma Kuratowski_aux2:
   "pairwise (separatedin (subtopology X (topspace X - S))) \<U> \<and> {} \<notin> \<U> \<and>
     \<Union>\<U> = topspace(subtopology X (topspace X - S)) \<longleftrightarrow>
     pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
  by (auto simp: pairwise_def separatedin_subtopology)

proposition Kuratowski_component_number_invariance_aux:
  assumes "compact_space X" and HsX: "Hausdorff_space X" 
    and lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
    and hom: "(subtopology X S) homeomorphic_space (subtopology X T)"
    and leXS: "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))"
  assumes \<section>: "\<And>S T.
              \<lbrakk>closedin X S; closedin X T; (subtopology X S) homeomorphic_space (subtopology X T);
              {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))\<rbrakk>
              \<Longrightarrow> {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
  shows "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
proof (cases "n=0")
  case False
  obtain f g where homf: "homeomorphic_map (subtopology X S) (subtopology X T) f" 
      and homg: "homeomorphic_map (subtopology X T) (subtopology X S) g"
    and gf: "\<And>x. x \<in> topspace (subtopology X S) \<Longrightarrow> g(f x) = x" 
    and fg: "\<And>y. y \<in> topspace (subtopology X T) \<Longrightarrow> f(g y) = y"
    and f: "f \<in> topspace (subtopology X S) \<rightarrow> topspace (subtopology X T)" 
    and g: "g \<in> topspace (subtopology X T) \<rightarrow> topspace (subtopology X S)"
    using homeomorphic_space_unfold hom by metis
  obtain C where "closedin X C" "C \<subseteq> S"
     and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
           \<Longrightarrow> \<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
    using separation_by_closed_intermediates_eq_count [of X n S] assms
    by (smt (verit, ccfv_threshold) False Kuratowski_aux2 lepoll_connected_components_alt)
  have "\<exists>C. closedin X C \<and> C \<subseteq> T \<and>
          (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> T
               \<longrightarrow> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and>
                        {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D))"
  proof (intro exI, intro conjI strip)
    have "compactin X (f ` C)"
      by (meson \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> assms(1) closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homf)
    then show "closedin X (f ` C)"
      using \<open>Hausdorff_space X\<close> compactin_imp_closedin by blast
    show "f ` C \<subseteq> T"
      by (meson \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> closedin_imp_subset closedin_subset_topspace homeomorphic_map_closedness_eq homf)
    fix D'
    assume D': "closedin X D' \<and> f ` C \<subseteq> D' \<and> D' \<subseteq> T"
    define D where "D \<equiv> g ` D'"
    have "compactin X D"
      unfolding D_def
      by (meson D' \<open>compact_space X\<close> closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homg)
    then have "closedin X D"
      by (simp add: assms(2) compactin_imp_closedin)
    moreover have "C \<subseteq> D"
      using D' D_def \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> closedin_subset gf image_iff by fastforce
    moreover have "D \<subseteq> S"
      by (metis D' D_def assms(1) closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homg)
    ultimately obtain \<U> where "\<U> \<approx> {..<n}" "pairwise (separatedin X) \<U>" "{} \<notin> \<U>" "\<Union>\<U> = topspace X - D"
      using C by meson
    moreover have "(subtopology X D) homeomorphic_space (subtopology X D')"
      unfolding homeomorphic_space_def
    proof (intro exI)
      have "subtopology X D = subtopology (subtopology X S) D"
        by (simp add: \<open>D \<subseteq> S\<close> inf.absorb2 subtopology_subtopology)
      moreover have "subtopology X D' = subtopology (subtopology X T) D'"
        by (simp add: D' inf.absorb2 subtopology_subtopology)
      moreover have "homeomorphic_maps (subtopology X T) (subtopology X S) g f"
        by (simp add: fg gf homeomorphic_maps_map homf homg)
      ultimately
      have "homeomorphic_maps (subtopology X D') (subtopology X D) g f"
        by (metis D' D_def \<open>closedin X D\<close> closedin_subset homeomorphic_maps_subtopologies topspace_subtopology Int_absorb1)
      then show "homeomorphic_maps (subtopology X D) (subtopology X D') f g"
        using homeomorphic_maps_sym by blast
    qed
    ultimately show "\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union> \<U> = topspace X - D'"
      by (smt (verit, ccfv_SIG) \<section> D' False \<open>closedin X D\<close> Kuratowski_aux2 lepoll_connected_components_alt)
  qed
  then have "\<exists>\<U>. \<U> \<approx> {..<n} \<and>
         pairwise (separatedin (subtopology X (topspace X - T))) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - T"
    using separation_by_closed_intermediates_eq_count [of X n T] Kuratowski_aux2 lcX hnX by auto
  with False show ?thesis
    using lepoll_connected_components_alt by fastforce
qed auto


theorem Kuratowski_component_number_invariance:
  assumes "compact_space X" "Hausdorff_space X" "locally_connected_space X" "hereditarily normal_space X"
  shows "((\<forall>S T n.
              closedin X S \<and> closedin X T \<and>
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})) \<longleftrightarrow>
           (\<forall>S T n.
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})))"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  then show ?rhs
    apply (subst (asm) Kuratowski_aux1, use homeomorphic_space_sym in blast)
    apply (subst Kuratowski_aux1, use homeomorphic_space_sym in blast)
    apply (blast intro: Kuratowski_component_number_invariance_aux assms)
    done
qed blast

end
