(*  Title:      HOL/Analysis/Vitali_Covering_Theorem.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section  \<open>Vitali Covering Theorem and an Application to Negligibility\<close>

theory Vitali_Covering_Theorem
imports
  "HOL-Combinatorics.Permutations"
  Equivalence_Lebesgue_Henstock_Integration
begin

lemma stretch_Galois:
  fixes x :: "real^'n"
  shows "(\<And>k. m k \<noteq> 0) \<Longrightarrow> ((y = (\<chi> k. m k * x$k)) \<longleftrightarrow> (\<chi> k. y$k / m k) = x)"
  by auto

lemma lambda_swap_Galois:
   "(x = (\<chi> i. y $ Transposition.transpose m n i) \<longleftrightarrow> (\<chi> i. x $ Transposition.transpose m n i) = y)"
  by (auto; simp add: pointfree_idE vec_eq_iff)

lemma lambda_add_Galois:
  fixes x :: "real^'n"
  shows "m \<noteq> n \<Longrightarrow> (x = (\<chi> i. if i = m then y$m + y$n else y$i) \<longleftrightarrow> (\<chi> i. if i = m then x$m - x$n else x$i) = y)"
  by (safe; simp add: vec_eq_iff)


lemma Vitali_covering_lemma_cballs_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "\<And>i. i \<in> K \<Longrightarrow> \<exists>j. j \<in> C \<and>
                        \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                        cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
proof (cases "K = {}")
  case True
  with that show ?thesis
    by auto
next
  case False
  then have "B > 0"
    using assms less_le_trans by auto
  have rgt0[simp]: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i"
    using assms by auto
  let ?djnt = "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j)))"
  have "\<exists>C. \<forall>n. (C n \<subseteq> K \<and>
             (\<forall>i \<in> C n. B/2 ^ n \<le> r i) \<and> ?djnt (C n) \<and>
             (\<forall>i \<in> K. B/2 ^ n < r i
                 \<longrightarrow> (\<exists>j. j \<in> C n \<and>
                         \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                         cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)))) \<and> (C n \<subseteq> C(Suc n))"
  proof (rule dependent_nat_choice, safe)
    fix C n
    define D where "D \<equiv> {i \<in> K. B/2 ^ Suc n < r i \<and> (\<forall>j\<in>C. disjnt (cball(a i)(r i)) (cball (a j) (r j)))}"
    let ?cover_ar = "\<lambda>i j. \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                             cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
    assume "C \<subseteq> K"
      and Ble: "\<forall>i\<in>C. B/2 ^ n \<le> r i"
      and djntC: "?djnt C"
      and cov_n: "\<forall>i\<in>K. B/2 ^ n < r i \<longrightarrow> (\<exists>j. j \<in> C \<and> ?cover_ar i j)"
    have *: "\<forall>C\<in>chains {C. C \<subseteq> D \<and> ?djnt C}. \<Union>C \<in> {C. C \<subseteq> D \<and> ?djnt C}"
    proof (clarsimp simp: chains_def)
      fix C
      assume C: "C \<subseteq> {C. C \<subseteq> D \<and> ?djnt C}" and "chain\<^sub>\<subseteq> C"
      show "\<Union>C \<subseteq> D \<and> ?djnt (\<Union>C)"
        unfolding pairwise_def
      proof (intro ballI conjI impI)
        show "\<Union>C \<subseteq> D"
          using C by blast
      next
        fix x y
        assume "x \<in> \<Union>C" and "y \<in> \<Union>C" and "x \<noteq> y"
        then obtain X Y where XY: "x \<in> X" "X \<in> C" "y \<in> Y" "Y \<in> C"
          by blast
        then consider "X \<subseteq> Y" | "Y \<subseteq> X"
          by (meson \<open>chain\<^sub>\<subseteq> C\<close> chain_subset_def)
        then show "disjnt (cball (a x) (r x)) (cball (a y) (r y))"
        proof cases
          case 1
          with C XY \<open>x \<noteq> y\<close> show ?thesis
            unfolding pairwise_def by blast
        next
          case 2
          with C XY \<open>x \<noteq> y\<close> show ?thesis
            unfolding pairwise_def by blast
        qed
      qed
    qed
    obtain E where "E \<subseteq> D" and djntE: "?djnt E" and maximalE: "\<And>X. \<lbrakk>X \<subseteq> D; ?djnt X; E \<subseteq> X\<rbrakk> \<Longrightarrow> X = E"
      using Zorn_Lemma [OF *] by safe blast
    show "\<exists>L. (L \<subseteq> K \<and>
               (\<forall>i\<in>L. B/2 ^ Suc n \<le> r i) \<and> ?djnt L \<and>
               (\<forall>i\<in>K. B/2 ^ Suc n < r i \<longrightarrow> (\<exists>j. j \<in> L \<and> ?cover_ar i j))) \<and> C \<subseteq> L"
    proof (intro exI conjI ballI)
      show "C \<union> E \<subseteq> K"
        using D_def \<open>C \<subseteq> K\<close> \<open>E \<subseteq> D\<close> by blast
      show "B/2 ^ Suc n \<le> r i" if i: "i \<in> C \<union> E" for i
        using i
      proof
        assume "i \<in> C"
        have "B/2 ^ Suc n \<le> B/2 ^ n"
          using \<open>B > 0\<close> by (simp add: field_split_simps)
        also have "\<dots> \<le> r i"
          using Ble \<open>i \<in> C\<close> by blast
        finally show ?thesis .
      qed (use D_def \<open>E \<subseteq> D\<close> in auto)
      show "?djnt (C \<union> E)"
        using D_def \<open>C \<subseteq> K\<close> \<open>E \<subseteq> D\<close> djntC djntE
        unfolding pairwise_def disjnt_def by blast
    next
      fix i
      assume "i \<in> K"
      show "B/2 ^ Suc n < r i \<longrightarrow> (\<exists>j. j \<in> C \<union> E \<and> ?cover_ar i j)"
      proof (cases "r i \<le> B/2^n")
        case False
        then show ?thesis
          using cov_n \<open>i \<in> K\<close> by auto
      next
        case True
        have "cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
          if less: "B/2 ^ Suc n < r i" and j: "j \<in> C \<union> E"
            and nondis: "\<not> disjnt (cball (a i) (r i)) (cball (a j) (r j))" for j
        proof -
          obtain x where x: "dist (a i) x \<le> r i" "dist (a j) x \<le> r j"
            using nondis by (force simp: disjnt_def)
          have "dist (a i) (a j) \<le> dist (a i) x + dist x (a j)"
            by (simp add: dist_triangle)
          also have "\<dots> \<le> r i + r j"
            by (metis add_mono_thms_linordered_semiring(1) dist_commute x)
          finally have aij: "dist (a i) (a j) + r i < 5 * r j" if "r i < 2 * r j"
            using that by auto
          show ?thesis
            using j
          proof
            assume "j \<in> C"
            have "B/2^n < 2 * r j"
              using Ble True \<open>j \<in> C\<close> less by auto
            with aij True show "cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
              by (simp add: cball_subset_ball_iff)
          next
            assume "j \<in> E"
            then have "B/2 ^ n < 2 * r j"
              using D_def \<open>E \<subseteq> D\<close> by auto
            with True have "r i < 2 * r j"
              by auto
            with aij show "cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
              by (simp add: cball_subset_ball_iff)
          qed
        qed
      moreover have "\<exists>j. j \<in> C \<union> E \<and> \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j))"
        if "B/2 ^ Suc n < r i"
      proof (rule classical)
        assume NON: "\<not> ?thesis"
        show ?thesis
        proof (cases "i \<in> D")
          case True
          have "insert i E = E"
          proof (rule maximalE)
            show "insert i E \<subseteq> D"
              by (simp add: True \<open>E \<subseteq> D\<close>)
            show "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) (insert i E)"
              using False NON by (auto simp: pairwise_insert djntE disjnt_sym)
          qed auto
          then show ?thesis
            using \<open>i \<in> K\<close> assms by fastforce
        next
          case False
          with that show ?thesis
            by (auto simp: D_def disjnt_def \<open>i \<in> K\<close>)
        qed
      qed
      ultimately
      show "B/2 ^ Suc n < r i \<longrightarrow>
            (\<exists>j. j \<in> C \<union> E \<and>
                 \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                 cball (a i) (r i) \<subseteq> ball (a j) (5 * r j))"
        by blast
      qed
    qed auto
  qed (use assms in force)
  then obtain F where FK: "\<And>n. F n \<subseteq> K"
               and Fle: "\<And>n i. i \<in> F n \<Longrightarrow> B/2 ^ n \<le> r i"
               and Fdjnt:  "\<And>n. ?djnt (F n)"
               and FF:  "\<And>n i. \<lbrakk>i \<in> K; B/2 ^ n < r i\<rbrakk>
                        \<Longrightarrow> \<exists>j. j \<in> F n \<and> \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                                cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
               and inc:  "\<And>n. F n \<subseteq> F(Suc n)"
    by (force simp: all_conj_distrib)
  show thesis
  proof
    have *: "countable I"
      if "I \<subseteq> K" and pw: "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) I" for I
    proof -
      show ?thesis
      proof (rule countable_image_inj_on [of "\<lambda>i. cball(a i)(r i)"])
        show "countable ((\<lambda>i. cball (a i) (r i)) ` I)"
        proof (rule countable_disjoint_nonempty_interior_subsets)
          show "disjoint ((\<lambda>i. cball (a i) (r i)) ` I)"
            by (auto simp: dest: pairwiseD [OF pw] intro: pairwise_imageI)
          show "\<And>S. \<lbrakk>S \<in> (\<lambda>i. cball (a i) (r i)) ` I; interior S = {}\<rbrakk> \<Longrightarrow> S = {}"
            using \<open>I \<subseteq> K\<close>
            by (auto simp: not_less [symmetric])
        qed
      next
        have "\<And>x y. \<lbrakk>x \<in> I; y \<in> I; a x = a y; r x = r y\<rbrakk> \<Longrightarrow> x = y"
          using pw \<open>I \<subseteq> K\<close> assms
          apply (clarsimp simp: pairwise_def disjnt_def)
          by (metis assms centre_in_cball subsetD empty_iff inf.idem less_eq_real_def)
        then show "inj_on (\<lambda>i. cball (a i) (r i)) I"
          using \<open>I \<subseteq> K\<close> by (fastforce simp: inj_on_def cball_eq_cball_iff dest: assms)
      qed
    qed
    show "(Union(range F)) \<subseteq> K"
      using FK by blast
    moreover show "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) (Union(range F))"
    proof (rule pairwise_chain_Union)
      show "chain\<^sub>\<subseteq> (range F)"
        unfolding chain_subset_def by clarify (meson inc lift_Suc_mono_le linear subsetCE)
    qed (use Fdjnt in blast)
    ultimately show "countable (Union(range F))"
      by (blast intro: *)
  next
    fix i assume "i \<in> K"
    then obtain n where "(1/2) ^ n < r i / B"
      using  \<open>B > 0\<close> assms real_arch_pow_inv by fastforce
    then have B2: "B/2 ^ n < r i"
      using \<open>B > 0\<close> by (simp add: field_split_simps)
    have "0 < r i" "r i \<le> B"
      by (auto simp: \<open>i \<in> K\<close> assms)
    show "\<exists>j. j \<in> (Union(range F)) \<and>
          \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
          cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
      using FF [OF \<open>i \<in> K\<close> B2] by auto
  qed
qed

subsection\<open>Vitali covering theorem\<close>

lemma Vitali_covering_lemma_cballs:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<subseteq> (\<Union>i\<in>K. cball (a i) (r i))"
      and r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "S \<subseteq> (\<Union>i\<in>C. cball (a i) (5 * r i))"
proof -
  obtain C where C: "countable C" "C \<subseteq> K"
                    "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
           and cov: "\<And>i. i \<in> K \<Longrightarrow> \<exists>j. j \<in> C \<and> \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                        cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
    by (rule Vitali_covering_lemma_cballs_balls [OF r, where a=a]) (blast intro: that)+
  show ?thesis
  proof
    have "(\<Union>i\<in>K. cball (a i) (r i)) \<subseteq> (\<Union>i\<in>C. cball (a i) (5 * r i))"
      using cov subset_iff by fastforce
    with S show "S \<subseteq> (\<Union>i\<in>C. cball (a i) (5 * r i))"
      by blast
  qed (use C in auto)
qed

lemma Vitali_covering_lemma_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<subseteq> (\<Union>i\<in>K. ball (a i) (r i))"
      and r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
     "S \<subseteq> (\<Union>i\<in>C. ball (a i) (5 * r i))"
proof -
  obtain C where C: "countable C" "C \<subseteq> K"
           and pw:  "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
           and cov: "\<And>i. i \<in> K \<Longrightarrow> \<exists>j. j \<in> C \<and> \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                        cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
    by (rule Vitali_covering_lemma_cballs_balls [OF r, where a=a]) (blast intro: that)+
  show ?thesis
  proof
    have "(\<Union>i\<in>K. ball (a i) (r i)) \<subseteq> (\<Union>i\<in>C. ball (a i) (5 * r i))"
      using cov subset_iff
      by clarsimp (meson less_imp_le mem_ball mem_cball subset_eq)
    with S show "S \<subseteq> (\<Union>i\<in>C. ball (a i) (5 * r i))"
      by blast
    show "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
      using pw
      by (clarsimp simp: pairwise_def) (meson ball_subset_cball disjnt_subset1 disjnt_subset2)
  qed (use C in auto)
qed


theorem Vitali_covering_theorem_cballs:
  fixes a :: "'a \<Rightarrow> 'n::euclidean_space"
  assumes r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i"
      and S: "\<And>x d. \<lbrakk>x \<in> S; 0 < d\<rbrakk>
                     \<Longrightarrow> \<exists>i. i \<in> K \<and> x \<in> cball (a i) (r i) \<and> r i < d"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "negligible(S - (\<Union>i \<in> C. cball (a i) (r i)))"
proof -
  let ?\<mu> = "measure lebesgue"
  have *: "\<exists>C. countable C \<and> C \<subseteq> K \<and>
            pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C \<and>
            negligible(S - (\<Union>i \<in> C. cball (a i) (r i)))"
    if r01: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> 1"
       and Sd: "\<And>x d. \<lbrakk>x \<in> S; 0 < d\<rbrakk> \<Longrightarrow> \<exists>i. i \<in> K \<and> x \<in> cball (a i) (r i) \<and> r i < d"
     for K r and a :: "'a \<Rightarrow> 'n"
  proof -
    obtain C where C: "countable C" "C \<subseteq> K"
      and pwC: "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
      and cov: "\<And>i. i \<in> K \<Longrightarrow> \<exists>j. j \<in> C \<and> \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                        cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
      by (rule Vitali_covering_lemma_cballs_balls [of K r 1 a]) (auto simp: r01)
    have ar_injective: "\<And>x y. \<lbrakk>x \<in> C; y \<in> C; a x = a y; r x = r y\<rbrakk> \<Longrightarrow> x = y"
      using \<open>C \<subseteq> K\<close> pwC cov
      by (force simp: pairwise_def disjnt_def)
    show ?thesis
    proof (intro exI conjI)
      show "negligible (S - (\<Union>i\<in>C. cball (a i) (r i)))"
      proof (clarsimp simp: negligible_on_intervals [of "S-T" for T])
        fix l u
        show "negligible ((S - (\<Union>i\<in>C. cball (a i) (r i))) \<inter> cbox l u)"
          unfolding negligible_outer_le
        proof (intro allI impI)
          fix e::real
          assume "e > 0"
          define D where "D \<equiv> {i \<in> C. \<not> disjnt (ball(a i) (5 * r i)) (cbox l u)}"
          then have "D \<subseteq> C"
            by auto
          have "countable D"
            unfolding D_def using \<open>countable C\<close> by simp
          have UD: "(\<Union>i\<in>D. cball (a i) (r i)) \<in> lmeasurable"
          proof (rule fmeasurableI2)
            show "cbox (l - 6 *\<^sub>R One) (u + 6 *\<^sub>R One) \<in> lmeasurable"
              by blast
            have "y \<in> cbox (l - 6 *\<^sub>R One) (u + 6 *\<^sub>R One)"
              if "i \<in> C" and x: "x \<in> cbox l u" and ai: "dist (a i) y \<le> r i" "dist (a i) x < 5 * r i"
              for i x y
            proof -
              have d6: "dist y x < 6 * r i"
                using dist_triangle3 [of y x "a i"] that by linarith
              show ?thesis
              proof (clarsimp simp: mem_box algebra_simps)
                fix j::'n
                assume j: "j \<in> Basis"
                then have xyj: "\<bar>x \<bullet> j - y \<bullet> j\<bar> \<le> dist y x"
                  by (metis Basis_le_norm dist_commute dist_norm inner_diff_left)
                have "l \<bullet> j \<le> x \<bullet> j"
                  using \<open>j \<in> Basis\<close> mem_box \<open>x \<in> cbox l u\<close> by blast
                also have "\<dots> \<le> y \<bullet> j + 6 * r i"
                  using d6 xyj by (auto simp: algebra_simps)
                also have "\<dots> \<le> y \<bullet> j + 6"
                  using r01 [of i] \<open>C \<subseteq> K\<close> \<open>i \<in> C\<close> by auto
                finally have l: "l \<bullet> j \<le> y \<bullet> j + 6" .
                have "y \<bullet> j \<le> x \<bullet> j + 6 * r i"
                  using d6 xyj by (auto simp: algebra_simps)
                also have "\<dots> \<le> u \<bullet> j + 6 * r i"
                  using j  x by (auto simp: mem_box)
                also have "\<dots> \<le> u \<bullet> j + 6"
                  using r01 [of i] \<open>C \<subseteq> K\<close> \<open>i \<in> C\<close> by auto
                finally have u: "y \<bullet> j \<le> u \<bullet> j + 6" .
                show "l \<bullet> j \<le> y \<bullet> j + 6 \<and> y \<bullet> j \<le> u \<bullet> j + 6"
                  using l u by blast
              qed
            qed
            then show "(\<Union>i\<in>D. cball (a i) (r i)) \<subseteq> cbox (l - 6 *\<^sub>R One) (u + 6 *\<^sub>R One)"
              by (force simp: D_def disjnt_def)
            show "(\<Union>i\<in>D. cball (a i) (r i)) \<in> sets lebesgue"
              using \<open>countable D\<close> by auto
          qed
          obtain D1 where "D1 \<subseteq> D" "finite D1"
            and measD1: "?\<mu> (\<Union>i\<in>D. cball (a i) (r i)) - e / 5 ^ DIM('n) < ?\<mu> (\<Union>i\<in>D1. cball (a i) (r i))"
          proof (rule measure_countable_Union_approachable [where e = "e / 5 ^ (DIM('n))"])
            show "countable ((\<lambda>i. cball (a i) (r i)) ` D)"
              using \<open>countable D\<close> by auto
            show "\<And>d. d \<in> (\<lambda>i. cball (a i) (r i)) ` D \<Longrightarrow> d \<in> lmeasurable"
              by auto
            show "\<And>D'. \<lbrakk>D' \<subseteq> (\<lambda>i. cball (a i) (r i)) ` D; finite D'\<rbrakk> \<Longrightarrow> ?\<mu> (\<Union>D') \<le> ?\<mu> (\<Union>i\<in>D. cball (a i) (r i))"
              by (fastforce simp add: intro!: measure_mono_fmeasurable UD)
          qed (use \<open>e > 0\<close> in \<open>auto dest: finite_subset_image\<close>)
          show "\<exists>T. (S - (\<Union>i\<in>C. cball (a i) (r i))) \<inter>
                    cbox l u \<subseteq> T \<and> T \<in> lmeasurable \<and> ?\<mu> T \<le> e"
          proof (intro exI conjI)
            show "(S - (\<Union>i\<in>C. cball (a i) (r i))) \<inter> cbox l u \<subseteq> (\<Union>i\<in>D - D1. ball (a i) (5 * r i))"
            proof clarify
              fix x
              assume x: "x \<in> cbox l u" "x \<in> S" "x \<notin> (\<Union>i\<in>C. cball (a i) (r i))"
              have "closed (\<Union>i\<in>D1. cball (a i) (r i))"
                using \<open>finite D1\<close> by blast
              moreover have "x \<notin> (\<Union>j\<in>D1. cball (a j) (r j))"
                using x \<open>D1 \<subseteq> D\<close> unfolding D_def by blast
              ultimately obtain q where "q > 0" and q: "ball x q \<subseteq> - (\<Union>i\<in>D1. cball (a i) (r i))"
                by (metis (no_types, lifting) ComplI open_contains_ball closed_def)
              obtain i where "i \<in> K" and xi: "x \<in> cball (a i) (r i)" and ri: "r i < q/2"
                using Sd [OF \<open>x \<in> S\<close>] \<open>q > 0\<close> half_gt_zero by blast
              then obtain j where "j \<in> C"
                             and nondisj: "\<not> disjnt (cball (a i) (r i)) (cball (a j) (r j))"
                             and sub5j:  "cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
                using cov [OF \<open>i \<in> K\<close>] by metis
              show "x \<in> (\<Union>i\<in>D - D1. ball (a i) (5 * r i))"
              proof
                show "j \<in> D - D1"
                proof
                  show "j \<in> D"
                    using \<open>j \<in> C\<close> sub5j \<open>x \<in> cbox l u\<close> xi by (auto simp: D_def disjnt_def)
                  obtain y where yi: "dist (a i) y \<le> r i" and yj: "dist (a j) y \<le> r j"
                    using disjnt_def nondisj by fastforce
                  have "dist x y \<le> r i + r i"
                    by (metis add_mono dist_commute dist_triangle_le mem_cball xi yi)
                  also have "\<dots> < q"
                    using ri by linarith
                  finally have "y \<in> ball x q"
                    by simp
                  with yj q show "j \<notin> D1"
                    by (auto simp: disjoint_UN_iff)
                qed
                show "x \<in> ball (a j) (5 * r j)"
                  using xi sub5j by blast
              qed
            qed
            have 3: "?\<mu> (\<Union>i\<in>D2. ball (a i) (5 * r i)) \<le> e"
              if D2: "D2 \<subseteq> D - D1" and "finite D2" for D2
            proof -
              have rgt0: "0 < r i" if "i \<in> D2" for i
                using \<open>C \<subseteq> K\<close> D_def \<open>i \<in> D2\<close> D2 r01
                by (simp add: subset_iff)
              then have inj: "inj_on (\<lambda>i. ball (a i) (5 * r i)) D2"
                using \<open>C \<subseteq> K\<close> D2 by (fastforce simp: inj_on_def D_def ball_eq_ball_iff intro: ar_injective)
              have "?\<mu> (\<Union>i\<in>D2. ball (a i) (5 * r i)) \<le> sum (?\<mu>) ((\<lambda>i. ball (a i) (5 * r i)) ` D2)"
                using that by (force intro: measure_Union_le)
              also have "\<dots>  = (\<Sum>i\<in>D2. ?\<mu> (ball (a i) (5 * r i)))"
                by (simp add: comm_monoid_add_class.sum.reindex [OF inj])
              also have "\<dots> = (\<Sum>i\<in>D2. 5 ^ DIM('n) * ?\<mu> (ball (a i) (r i)))"
              proof (rule sum.cong [OF refl])
                fix i assume "i \<in> D2"
                thus "?\<mu> (ball (a i) (5 * r i)) = 5 ^ DIM('n) * ?\<mu> (ball (a i) (r i))"
                  using content_ball_conv_unit_ball[of "5 * r i" "a i"]
                        content_ball_conv_unit_ball[of "r i" "a i"] rgt0[of i] by auto
              qed
              also have "\<dots> = (\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) * 5 ^ DIM('n)"
                by (simp add: sum_distrib_left mult.commute)
              finally have "?\<mu> (\<Union>i\<in>D2. ball (a i) (5 * r i)) \<le> (\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) * 5 ^ DIM('n)" .
              moreover have "(\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) \<le> e / 5 ^ DIM('n)"
              proof -
                have D12_dis: "((\<Union>x\<in>D1. cball (a x) (r x)) \<inter> (\<Union>x\<in>D2. cball (a x) (r x))) \<le> {}"
                proof clarify
                  fix w d1 d2
                  assume "d1 \<in> D1" "w d1 d2 \<in> cball (a d1) (r d1)" "d2 \<in> D2" "w d1 d2 \<in> cball (a d2) (r d2)"
                  then show "w d1 d2 \<in> {}"
                    by (metis DiffE disjnt_iff subsetCE D2 \<open>D1 \<subseteq> D\<close> \<open>D \<subseteq> C\<close> pairwiseD [OF pwC, of d1 d2])
                qed
                have inj: "inj_on (\<lambda>i. cball (a i) (r i)) D2"
                  using rgt0 D2 \<open>D \<subseteq> C\<close> by (force simp: inj_on_def cball_eq_cball_iff intro!: ar_injective)
                have ds: "disjoint ((\<lambda>i. cball (a i) (r i)) ` D2)"
                  using D2 \<open>D \<subseteq> C\<close> by (auto intro: pairwiseI pairwiseD [OF pwC])
                have "(\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) = (\<Sum>i\<in>D2. ?\<mu> (cball (a i) (r i)))"
                  by (simp add: content_cball_conv_ball)
                also have "\<dots> = sum ?\<mu> ((\<lambda>i. cball (a i) (r i)) ` D2)"
                  by (simp add: comm_monoid_add_class.sum.reindex [OF inj])
                also have "\<dots> = ?\<mu> (\<Union>i\<in>D2. cball (a i) (r i))"
                  by (auto intro: measure_Union' [symmetric] ds simp add: \<open>finite D2\<close>)
                finally have "?\<mu> (\<Union>i\<in>D1. cball (a i) (r i)) + (\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) =
                              ?\<mu> (\<Union>i\<in>D1. cball (a i) (r i)) + ?\<mu> (\<Union>i\<in>D2. cball (a i) (r i))"
                  by simp
                also have "\<dots> = ?\<mu> (\<Union>i \<in> D1 \<union> D2. cball (a i) (r i))"
                  using D12_dis by (simp add: measure_Un3 \<open>finite D1\<close> \<open>finite D2\<close> fmeasurable.finite_UN)
                also have "\<dots> \<le> ?\<mu> (\<Union>i\<in>D. cball (a i) (r i))"
                  using D2 \<open>D1 \<subseteq> D\<close> by (fastforce intro!: measure_mono_fmeasurable [OF _ _ UD] \<open>finite D1\<close> \<open>finite D2\<close>)
                finally have "?\<mu> (\<Union>i\<in>D1. cball (a i) (r i)) + (\<Sum>i\<in>D2. ?\<mu> (ball (a i) (r i))) \<le> ?\<mu> (\<Union>i\<in>D. cball (a i) (r i))" .
                with measD1 show ?thesis
                  by simp
              qed
                ultimately show ?thesis
                  by (simp add: field_split_simps)
            qed
            have co: "countable (D - D1)"
              by (simp add: \<open>countable D\<close>)
            show "(\<Union>i\<in>D - D1. ball (a i) (5 * r i)) \<in> lmeasurable"
              using \<open>e > 0\<close> by (auto simp: fmeasurable_UN_bound [OF co _ 3])
            show "?\<mu> (\<Union>i\<in>D - D1. ball (a i) (5 * r i)) \<le> e"
              using \<open>e > 0\<close> by (auto simp: measure_UN_bound [OF co _ 3])
          qed
        qed
      qed
    qed (use C pwC in auto)
  qed
  define K' where "K' \<equiv> {i \<in> K. r i \<le> 1}"
  have 1: "\<And>i. i \<in> K' \<Longrightarrow> 0 < r i \<and> r i \<le> 1"
    using K'_def r by auto
  have 2: "\<exists>i. i \<in> K' \<and> x \<in> cball (a i) (r i) \<and> r i < d"
    if "x \<in> S \<and> 0 < d" for x d
    using that by (auto simp: K'_def dest!: S [where d = "min d 1"])
  have "K' \<subseteq> K"
    using K'_def by auto
  then show thesis
    using * [OF 1 2] that by fastforce
qed


theorem Vitali_covering_theorem_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "\<And>x d. \<lbrakk>x \<in> S; 0 < d\<rbrakk> \<Longrightarrow> \<exists>i. i \<in> K \<and> x \<in> ball (a i) (r i) \<and> r i < d"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
     "negligible(S - (\<Union>i \<in> C. ball (a i) (r i)))"
proof -
  have 1: "\<exists>i. i \<in> {i \<in> K. 0 < r i} \<and> x \<in> cball (a i) (r i) \<and> r i < d"
         if xd: "x \<in> S" "d > 0" for x d
    by (metis (mono_tags, lifting) assms ball_eq_empty less_eq_real_def mem_Collect_eq mem_ball mem_cball not_le xd(1) xd(2))
  obtain C where C: "countable C" "C \<subseteq> K"
             and pw: "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
             and neg: "negligible(S - (\<Union>i \<in> C. cball (a i) (r i)))"
    by (rule Vitali_covering_theorem_cballs [of "{i \<in> K. 0 < r i}" r S a, OF _ 1]) auto
  show thesis
  proof
    show "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
      apply (rule pairwise_mono [OF pw])
      apply (auto simp: disjnt_def)
      by (meson disjoint_iff_not_equal less_imp_le mem_cball)
    have "negligible (\<Union>i\<in>C. sphere (a i) (r i))"
      by (auto intro: negligible_sphere \<open>countable C\<close>)
    then have "negligible (S - (\<Union>i \<in> C. cball(a i)(r i)) \<union> (\<Union>i \<in> C. sphere (a i) (r i)))"
      by (rule negligible_Un [OF neg])
    then show "negligible (S - (\<Union>i\<in>C. ball (a i) (r i)))"
      by (rule negligible_subset) force
  qed (use C in auto)
qed


lemma negligible_eq_zero_density_alt:
     "negligible S \<longleftrightarrow>
      (\<forall>x \<in> S. \<forall>e > 0.
        \<exists>d U. 0 < d \<and> d \<le> e \<and> S \<inter> ball x d \<subseteq> U \<and>
              U \<in> lmeasurable \<and> measure lebesgue U < e * measure lebesgue (ball x d))"
     (is "_ = (\<forall>x \<in> S. \<forall>e > 0. ?Q x e)")
proof (intro iffI ballI allI impI)
  fix x and e :: real
  assume "negligible S" and "x \<in> S" and "e > 0"
  then
  show "\<exists>d U. 0 < d \<and> d \<le> e \<and> S \<inter> ball x d \<subseteq> U \<and> U \<in> lmeasurable \<and>
              measure lebesgue U < e * measure lebesgue (ball x d)"
    apply (rule_tac x=e in exI)
    apply (rule_tac x="S \<inter> ball x e" in exI)
    apply (auto simp: negligible_imp_measurable negligible_Int negligible_imp_measure0 zero_less_measure_iff
                intro: mult_pos_pos content_ball_pos)
    done
next
  assume R [rule_format]: "\<forall>x \<in> S. \<forall>e > 0. ?Q x e"
  let ?\<mu> = "measure lebesgue"
  have "\<exists>U. openin (top_of_set S) U \<and> z \<in> U \<and> negligible U"
    if "z \<in> S" for z
  proof (intro exI conjI)
    show "openin (top_of_set S) (S \<inter> ball z 1)"
      by (simp add: openin_open_Int)
    show "z \<in> S \<inter> ball z 1"
      using \<open>z \<in> S\<close> by auto
    show "negligible (S \<inter> ball z 1)"
    proof (clarsimp simp: negligible_outer_le)
      fix e :: "real"
      assume "e > 0"
      let ?K = "{(x,d). x \<in> S \<and> 0 < d \<and> ball x d \<subseteq> ball z 1 \<and>
                     (\<exists>U. S \<inter> ball x d \<subseteq> U \<and> U \<in> lmeasurable \<and>
                         ?\<mu> U < e / ?\<mu> (ball z 1) * ?\<mu> (ball x d))}"
      obtain C where "countable C" and Csub: "C \<subseteq> ?K"
        and pwC: "pairwise (\<lambda>i j. disjnt (ball (fst i) (snd i)) (ball (fst j) (snd j))) C"
        and negC: "negligible((S \<inter> ball z 1) - (\<Union>i \<in> C. ball (fst i) (snd i)))"
      proof (rule Vitali_covering_theorem_balls [of "S \<inter> ball z 1" ?K fst snd])
        fix x and d :: "real"
        assume x: "x \<in> S \<inter> ball z 1" and "d > 0"
        obtain k where "k > 0" and k: "ball x k \<subseteq> ball z 1"
          by (meson Int_iff open_ball openE x)
        let ?\<epsilon> = "min (e / ?\<mu> (ball z 1) / 2) (min (d / 2) k)"
        obtain r U where r: "r > 0" "r \<le> ?\<epsilon>" and U: "S \<inter> ball x r \<subseteq> U" "U \<in> lmeasurable"
          and mU: "?\<mu> U < ?\<epsilon> * ?\<mu> (ball x r)"
          using R [of x ?\<epsilon>] \<open>d > 0\<close> \<open>e > 0\<close> \<open>k > 0\<close> x by (auto simp: content_ball_pos)
        show "\<exists>i. i \<in> ?K \<and> x \<in> ball (fst i) (snd i) \<and> snd i < d"
        proof (rule exI [of _ "(x,r)"], simp, intro conjI exI)
          have "ball x r \<subseteq> ball x k"
            using r by (simp add: ball_subset_ball_iff)
          also have "\<dots> \<subseteq> ball z 1"
            using ball_subset_ball_iff k by auto
          finally show "ball x r \<subseteq> ball z 1" .
          have "?\<epsilon> * ?\<mu> (ball x r) \<le> e * content (ball x r) / content (ball z 1)"
            using r \<open>e > 0\<close> by (simp add: ord_class.min_def field_split_simps content_ball_pos)
          with mU show "?\<mu> U < e * content (ball x r) / content (ball z 1)"
            by auto
        qed (use r U x in auto)
      qed
      have "\<exists>U. case p of (x,d) \<Rightarrow> S \<inter> ball x d \<subseteq> U \<and>
                        U \<in> lmeasurable \<and> ?\<mu> U < e / ?\<mu> (ball z 1) * ?\<mu> (ball x d)"
        if "p \<in> C" for p
        using that Csub unfolding case_prod_unfold by blast
      then obtain U where U:
                "\<And>p. p \<in> C \<Longrightarrow>
                       case p of (x,d) \<Rightarrow> S \<inter> ball x d \<subseteq> U p \<and>
                        U p \<in> lmeasurable \<and> ?\<mu> (U p) < e / ?\<mu> (ball z 1) * ?\<mu> (ball x d)"
        by (rule that [OF someI_ex])
      let ?T = "((S \<inter> ball z 1) - (\<Union>(x,d)\<in>C. ball x d)) \<union> \<Union>(U ` C)"
      show "\<exists>T. S \<inter> ball z 1 \<subseteq> T \<and> T \<in> lmeasurable \<and> ?\<mu> T \<le> e"
      proof (intro exI conjI)
        show "S \<inter> ball z 1 \<subseteq> ?T"
          using U by fastforce
        { have Um: "U i \<in> lmeasurable" if "i \<in> C" for i
            using that U by blast
          have lee: "?\<mu> (\<Union>i\<in>I. U i) \<le> e" if "I \<subseteq> C" "finite I" for I
          proof -
            have "?\<mu> (\<Union>(x,d)\<in>I. ball x d) \<le> ?\<mu> (ball z 1)"
              apply (rule measure_mono_fmeasurable)
              using \<open>I \<subseteq> C\<close> \<open>finite I\<close> Csub by (force simp: prod.case_eq_if sets.finite_UN)+
            then have le1: "(?\<mu> (\<Union>(x,d)\<in>I. ball x d) / ?\<mu> (ball z 1)) \<le> 1"
              by (simp add: content_ball_pos)
            have "?\<mu> (\<Union>i\<in>I. U i) \<le> (\<Sum>i\<in>I. ?\<mu> (U i))"
              using that U by (blast intro: measure_UNION_le)
            also have "\<dots> \<le> (\<Sum>(x,r)\<in>I. e / ?\<mu> (ball z 1) * ?\<mu> (ball x r))"
              by (rule sum_mono) (use \<open>I \<subseteq> C\<close> U in force)
            also have "\<dots> = (e / ?\<mu> (ball z 1)) * (\<Sum>(x,r)\<in>I. ?\<mu> (ball x r))"
              by (simp add: case_prod_app prod.case_distrib sum_distrib_left)
            also have "\<dots> = e * (?\<mu> (\<Union>(x,r)\<in>I. ball x r) / ?\<mu> (ball z 1))"
              apply (subst measure_UNION')
              using that pwC by (auto simp: case_prod_unfold elim: pairwise_mono)
            also have "\<dots> \<le> e"
              by (metis mult.commute mult.left_neutral mult_le_cancel_iff1 \<open>e > 0\<close> le1)
            finally show ?thesis .
          qed
          have "\<Union>(U ` C) \<in> lmeasurable" "?\<mu> (\<Union>(U ` C)) \<le> e"
            using \<open>e > 0\<close> Um lee
            by(auto intro!: fmeasurable_UN_bound [OF \<open>countable C\<close>] measure_UN_bound [OF \<open>countable C\<close>])
        }
        moreover have "?\<mu> ?T = ?\<mu> (\<Union>(U ` C))"
        proof (rule measure_negligible_symdiff [OF \<open>\<Union>(U ` C) \<in> lmeasurable\<close>])
          show "negligible((\<Union>(U ` C) - ?T) \<union> (?T - \<Union>(U ` C)))"
            by (force intro!: negligible_subset [OF negC])
        qed
        ultimately show "?T \<in> lmeasurable"  "?\<mu> ?T \<le> e"
          by (simp_all add: fmeasurable.Un negC negligible_imp_measurable split_def)
      qed
    qed
  qed
  with locally_negligible_alt show "negligible S"
    by metis
qed

proposition negligible_eq_zero_density:
   "negligible S \<longleftrightarrow>
    (\<forall>x\<in>S. \<forall>r>0. \<forall>e>0. \<exists>d. 0 < d \<and> d \<le> r \<and>
                   (\<exists>U. S \<inter> ball x d \<subseteq> U \<and> U \<in> lmeasurable \<and> measure lebesgue U < e * measure lebesgue (ball x d)))"
proof -
  let ?Q = "\<lambda>x d e. \<exists>U. S \<inter> ball x d \<subseteq> U \<and> U \<in> lmeasurable \<and> measure lebesgue U < e * content (ball x d)"
  have "(\<forall>e>0. \<exists>d>0. d \<le> e \<and> ?Q x d e) = (\<forall>r>0. \<forall>e>0. \<exists>d>0. d \<le> r \<and> ?Q x d e)"
    if "x \<in> S" for x
  proof (intro iffI allI impI)
    fix r :: "real" and e :: "real"
    assume L [rule_format]: "\<forall>e>0. \<exists>d>0. d \<le> e \<and> ?Q x d e" and "r > 0" "e > 0"
    show "\<exists>d>0. d \<le> r \<and> ?Q x d e"
      using L [of "min r e"] apply (rule ex_forward)
      using \<open>r > 0\<close> \<open>e > 0\<close>  by (auto intro: less_le_trans elim!: ex_forward simp: content_ball_pos)
  qed auto
  then show ?thesis
    by (force simp: negligible_eq_zero_density_alt)
qed

end
