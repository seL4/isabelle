(*  Title:      HOL/Analysis/Arcwise_Connected.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Urysohn lemma and its Consequences\<close>

theory Urysohn
imports Abstract_Topological_Spaces Abstract_Metric_Spaces Infinite_Sum Arcwise_Connected
begin

subsection \<open>Urysohn lemma and Tietze's theorem\<close>

lemma Urysohn_lemma:
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
  ultimately have fim: "f ` topspace X \<subseteq> {0..1}"
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
      using that r G [of s r] by (force simp add: dest: closure_of_subset openin_subset)
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
            using ** f_le1 in_closure_of r by (fastforce simp add: True G'_def)
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
    by (force simp add: Met_TC.continuous_map_to_metric dist_real_def continuous_map_in_subtopology fim simp flip: Met_TC.mtopology_is_euclideanreal)
  define g where "g \<equiv> \<lambda>x. a + (b - a) * f x"
  show thesis
  proof
    have "continuous_map X euclideanreal g"
      using contf \<open>a \<le> b\<close> unfolding g_def by (auto simp: continuous_intros continuous_map_in_subtopology)
    moreover have "g ` (topspace X) \<subseteq> {a..b}"
      using mult_left_le [of "f _" "b-a"] contf \<open>a \<le> b\<close>   
      by (simp add: g_def add.commute continuous_map_in_subtopology image_subset_iff le_diff_eq)
    ultimately show "continuous_map X (top_of_set {a..b}) g"
      by (meson continuous_map_in_subtopology)
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
        by (force simp add: U_def V_def disjnt_iff)
    qed
  qed
qed

lemma Tietze_extension_closed_real_interval:
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
      by (simp add: abs_le_iff continuous_map_def minus_le_iff)
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


lemma Tietze_extension_realinterval:
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
    then have him01: "h ` topspace X \<subseteq> {0..1}"
      by (meson continuous_map_in_subtopology)
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

subsection \<open>random metric space stuff\<close>


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
      and fim: "f ` topspace X \<subseteq> {0..1}" and f0: "f a = 0" and f1: "f ` C \<subseteq> {1}"
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
    using assms
    unfolding completely_regular_space_def regular_space_def continuous_map_in_subtopology
    by (meson "*")
qed


lemma locally_compact_regular_imp_completely_regular_space:
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
    using \<open>M \<subseteq> topspace X\<close> by (force simp add: continuous_map_in_subtopology image_subset_iff)
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
      topspace (prod_topology X Y) = {} \<or>
      completely_regular_space X \<and> completely_regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_prod_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "topspace(prod_topology X Y) = {}")
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


lemma completely_regular_space_product_topology:
   "completely_regular_space (product_topology X I) \<longleftrightarrow>
    (\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {} \<or> (\<forall>i \<in> I. completely_regular_space (X i))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_product_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "(\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {}")
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

lemma kc_space_one_point_compactification_gen:
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

lemma istopology_Alexandroff_open: "istopology (Alexandroff_open X)"
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
    by (force simp add: topspace_def openin_Alexandroff_compactification)
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
    by (fastforce simp add: compactin_subtopology closedin_Alexandroff_I closedin_subtopology)
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


lemma regular_space_one_point_compactification:
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
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_locally_compact_space homeomorphic_regular_space 
      by fastforce
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

lemma Hausdorff_space_one_point_compactification_asymmetric_prod:
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
      then have "kc_space X"
        using kc_space_retraction_map_image [of "prod_topology X (subtopology X (topspace X - {a}))" X fst]
        by (metis Diff_subset R True insert_Diff retraction_map_fst topspace_subtopology_subset)
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
          by (force simp add: closure_of_def)
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

end
