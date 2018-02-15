(*  Title:      HOL/Analysis/Continuous_Extension.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Continuous extensions of functions: Urysohn's lemma, Dugundji extension theorem, Tietze\<close>

theory Continuous_Extension
imports Starlike
begin

subsection\<open>Partitions of unity subordinate to locally finite open coverings\<close>

text\<open>A difference from HOL Light: all summations over infinite sets equal zero,
   so the "support" must be made explicit in the summation below!\<close>

proposition subordinate_partition_of_unity:
  fixes S :: "'a :: euclidean_space set"
  assumes "S \<subseteq> \<Union>\<C>" and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
      and fin: "\<And>x. x \<in> S \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. U \<inter> V \<noteq> {}}"
  obtains F :: "['a set, 'a] \<Rightarrow> real"
    where "\<And>U. U \<in> \<C> \<Longrightarrow> continuous_on S (F U) \<and> (\<forall>x \<in> S. 0 \<le> F U x)"
      and "\<And>x U. \<lbrakk>U \<in> \<C>; x \<in> S; x \<notin> U\<rbrakk> \<Longrightarrow> F U x = 0"
      and "\<And>x. x \<in> S \<Longrightarrow> supp_sum (\<lambda>W. F W x) \<C> = 1"
      and "\<And>x. x \<in> S \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. \<exists>x\<in>V. F U x \<noteq> 0}"
proof (cases "\<exists>W. W \<in> \<C> \<and> S \<subseteq> W")
  case True
    then obtain W where "W \<in> \<C>" "S \<subseteq> W" by metis
    then show ?thesis
      apply (rule_tac F = "\<lambda>V x. if V = W then 1 else 0" in that)
      apply (auto simp: continuous_on_const supp_sum_def support_on_def)
      done
next
  case False
    have nonneg: "0 \<le> supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>" for x
      by (simp add: supp_sum_def sum_nonneg)
    have sd_pos: "0 < setdist {x} (S - V)" if "V \<in> \<C>" "x \<in> S" "x \<in> V" for V x
    proof -
      have "closedin (subtopology euclidean S) (S - V)"
        by (simp add: Diff_Diff_Int Diff_subset closedin_def opC openin_open_Int \<open>V \<in> \<C>\<close>)
      with that False setdist_eq_0_closedin [of S "S-V" x] setdist_pos_le [of "{x}" "S - V"]
        show ?thesis
          by (simp add: order_class.order.order_iff_strict)
    qed
    have ss_pos: "0 < supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>" if "x \<in> S" for x
    proof -
      obtain U where "U \<in> \<C>" "x \<in> U" using \<open>x \<in> S\<close> \<open>S \<subseteq> \<Union>\<C>\<close>
        by blast
      obtain V where "open V" "x \<in> V" "finite {U \<in> \<C>. U \<inter> V \<noteq> {}}"
        using \<open>x \<in> S\<close> fin by blast
      then have *: "finite {A \<in> \<C>. \<not> S \<subseteq> A \<and> x \<notin> closure (S - A)}"
        using closure_def that by (blast intro: rev_finite_subset)
      have "x \<notin> closure (S - U)"
        by (metis \<open>U \<in> \<C>\<close> \<open>x \<in> U\<close> less_irrefl sd_pos setdist_eq_0_sing_1 that)
      then show ?thesis
        apply (simp add: setdist_eq_0_sing_1 supp_sum_def support_on_def)
        apply (rule ordered_comm_monoid_add_class.sum_pos2 [OF *, of U])
        using \<open>U \<in> \<C>\<close> \<open>x \<in> U\<close> False
        apply (auto simp: setdist_pos_le sd_pos that)
        done
    qed
    define F where
      "F \<equiv> \<lambda>W x. if x \<in> S then setdist {x} (S - W) / supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>
                 else 0"
    show ?thesis
    proof (rule_tac F = F in that)
      have "continuous_on S (F U)" if "U \<in> \<C>" for U
      proof -
        have *: "continuous_on S (\<lambda>x. supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>)"
        proof (clarsimp simp add: continuous_on_eq_continuous_within)
          fix x assume "x \<in> S"
          then obtain X where "open X" and x: "x \<in> S \<inter> X" and finX: "finite {U \<in> \<C>. U \<inter> X \<noteq> {}}"
            using assms by blast
          then have OSX: "openin (subtopology euclidean S) (S \<inter> X)" by blast
          have sumeq: "\<And>x. x \<in> S \<inter> X \<Longrightarrow>
                     (\<Sum>V | V \<in> \<C> \<and> V \<inter> X \<noteq> {}. setdist {x} (S - V))
                     = supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>"
            apply (simp add: supp_sum_def)
            apply (rule sum.mono_neutral_right [OF finX])
            apply (auto simp: setdist_eq_0_sing_1 support_on_def subset_iff)
            apply (meson DiffI closure_subset disjoint_iff_not_equal subsetCE)
            done
          show "continuous (at x within S) (\<lambda>x. supp_sum (\<lambda>V. setdist {x} (S - V)) \<C>)"
            apply (rule continuous_transform_within_openin
                     [where f = "\<lambda>x. (sum (\<lambda>V. setdist {x} (S - V)) {V \<in> \<C>. V \<inter> X \<noteq> {}})"
                        and S ="S \<inter> X"])
            apply (rule continuous_intros continuous_at_setdist continuous_at_imp_continuous_at_within OSX x)+
            apply (simp add: sumeq)
            done
        qed
        show ?thesis
          apply (simp add: F_def)
          apply (rule continuous_intros *)+
          using ss_pos apply force
          done
      qed
      moreover have "\<lbrakk>U \<in> \<C>; x \<in> S\<rbrakk> \<Longrightarrow> 0 \<le> F U x" for U x
        using nonneg [of x] by (simp add: F_def divide_simps setdist_pos_le)
      ultimately show "\<And>U. U \<in> \<C> \<Longrightarrow> continuous_on S (F U) \<and> (\<forall>x\<in>S. 0 \<le> F U x)"
        by metis
    next
      show "\<And>x U. \<lbrakk>U \<in> \<C>; x \<in> S; x \<notin> U\<rbrakk> \<Longrightarrow> F U x = 0"
        by (simp add: setdist_eq_0_sing_1 closure_def F_def)
    next
      show "supp_sum (\<lambda>W. F W x) \<C> = 1" if "x \<in> S" for x
        using that ss_pos [OF that]
        by (simp add: F_def divide_simps supp_sum_divide_distrib [symmetric])
    next
      show "\<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. \<exists>x\<in>V. F U x \<noteq> 0}" if "x \<in> S" for x
        using fin [OF that] that
        by (fastforce simp: setdist_eq_0_sing_1 closure_def F_def elim!: rev_finite_subset)
    qed
qed


subsection\<open>Urysohn's lemma (for Euclidean spaces, where the proof is easy using distances)\<close>

lemma Urysohn_both_ne:
  assumes US: "closedin (subtopology euclidean U) S"
      and UT: "closedin (subtopology euclidean U) T"
      and "S \<inter> T = {}" "S \<noteq> {}" "T \<noteq> {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
proof -
  have S0: "\<And>x. x \<in> U \<Longrightarrow> setdist {x} S = 0 \<longleftrightarrow> x \<in> S"
    using \<open>S \<noteq> {}\<close>  US setdist_eq_0_closedin  by auto
  have T0: "\<And>x. x \<in> U \<Longrightarrow> setdist {x} T = 0 \<longleftrightarrow> x \<in> T"
    using \<open>T \<noteq> {}\<close>  UT setdist_eq_0_closedin  by auto
  have sdpos: "0 < setdist {x} S + setdist {x} T" if "x \<in> U" for x
  proof -
    have "~ (setdist {x} S = 0 \<and> setdist {x} T = 0)"
      using assms by (metis IntI empty_iff setdist_eq_0_closedin that)
    then show ?thesis
      by (metis add.left_neutral add.right_neutral add_pos_pos linorder_neqE_linordered_idom not_le setdist_pos_le)
  qed
  define f where "f \<equiv> \<lambda>x. a + (setdist {x} S / (setdist {x} S + setdist {x} T)) *\<^sub>R (b - a)"
  show ?thesis
  proof (rule_tac f = f in that)
    show "continuous_on U f"
      using sdpos unfolding f_def
      by (intro continuous_intros | force)+
    show "f x \<in> closed_segment a b" if "x \<in> U" for x
        unfolding f_def
      apply (simp add: closed_segment_def)
      apply (rule_tac x="(setdist {x} S / (setdist {x} S + setdist {x} T))" in exI)
      using sdpos that apply (simp add: algebra_simps)
      done
    show "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
      using S0 \<open>a \<noteq> b\<close> f_def sdpos by force
    show "(f x = b \<longleftrightarrow> x \<in> T)" if "x \<in> U" for x
    proof -
      have "f x = b \<longleftrightarrow> (setdist {x} S / (setdist {x} S + setdist {x} T)) = 1"
        unfolding f_def
        apply (rule iffI)
         apply (metis  \<open>a \<noteq> b\<close> add_diff_cancel_left' eq_iff_diff_eq_0 pth_1 real_vector.scale_right_imp_eq, force)
        done
      also have "...  \<longleftrightarrow> setdist {x} T = 0 \<and> setdist {x} S \<noteq> 0"
        using sdpos that
        by (simp add: divide_simps) linarith
      also have "...  \<longleftrightarrow> x \<in> T"
        using \<open>S \<noteq> {}\<close> \<open>T \<noteq> {}\<close> \<open>S \<inter> T = {}\<close> that
        by (force simp: S0 T0)
      finally show ?thesis .
    qed
  qed
qed

proposition Urysohn_local_strong:
  assumes US: "closedin (subtopology euclidean U) S"
      and UT: "closedin (subtopology euclidean U) T"
      and "S \<inter> T = {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
proof (cases "S = {}")
  case True show ?thesis
  proof (cases "T = {}")
    case True show ?thesis
    proof (rule_tac f = "\<lambda>x. midpoint a b" in that)
      show "continuous_on U (\<lambda>x. midpoint a b)"
        by (intro continuous_intros)
      show "midpoint a b \<in> closed_segment a b"
        using csegment_midpoint_subset by blast
      show "(midpoint a b = a) = (x \<in> S)" for x
        using \<open>S = {}\<close> \<open>a \<noteq> b\<close> by simp
      show "(midpoint a b = b) = (x \<in> T)" for x
        using \<open>T = {}\<close> \<open>a \<noteq> b\<close> by simp
    qed
  next
    case False
    show ?thesis
    proof (cases "T = U")
      case True with \<open>S = {}\<close> \<open>a \<noteq> b\<close> show ?thesis
        by (rule_tac f = "\<lambda>x. b" in that) (auto simp: continuous_on_const)
    next
      case False
      with UT closedin_subset obtain c where c: "c \<in> U" "c \<notin> T"
        by fastforce
      obtain f where f: "continuous_on U f"
                "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment (midpoint a b) b"
                "\<And>x. x \<in> U \<Longrightarrow> (f x = midpoint a b \<longleftrightarrow> x = c)"
                "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
        apply (rule Urysohn_both_ne [of U "{c}" T "midpoint a b" "b"])
        using c \<open>T \<noteq> {}\<close> assms apply simp_all
        done
      show ?thesis
        apply (rule_tac f=f in that)
        using \<open>S = {}\<close> \<open>T \<noteq> {}\<close> f csegment_midpoint_subset notin_segment_midpoint [OF \<open>a \<noteq> b\<close>]
        apply force+
        done
    qed
  qed
next
  case False
  show ?thesis
  proof (cases "T = {}")
    case True show ?thesis
    proof (cases "S = U")
      case True with \<open>T = {}\<close> \<open>a \<noteq> b\<close> show ?thesis
        by (rule_tac f = "\<lambda>x. a" in that) (auto simp: continuous_on_const)
    next
      case False
      with US closedin_subset obtain c where c: "c \<in> U" "c \<notin> S"
        by fastforce
      obtain f where f: "continuous_on U f"
                "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a (midpoint a b)"
                "\<And>x. x \<in> U \<Longrightarrow> (f x = midpoint a b \<longleftrightarrow> x = c)"
                "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
        apply (rule Urysohn_both_ne [of U S "{c}" a "midpoint a b"])
        using c \<open>S \<noteq> {}\<close> assms apply simp_all
        apply (metis midpoint_eq_endpoint)
        done
      show ?thesis
        apply (rule_tac f=f in that)
        using \<open>S \<noteq> {}\<close> \<open>T = {}\<close> f  \<open>a \<noteq> b\<close>
        apply simp_all
        apply (metis (no_types) closed_segment_commute csegment_midpoint_subset midpoint_sym subset_iff)
        apply (metis closed_segment_commute midpoint_sym notin_segment_midpoint)
        done
    qed
  next
    case False
    show ?thesis
      using Urysohn_both_ne [OF US UT \<open>S \<inter> T = {}\<close> \<open>S \<noteq> {}\<close> \<open>T \<noteq> {}\<close> \<open>a \<noteq> b\<close>] that
      by blast
  qed
qed

lemma Urysohn_local:
  assumes US: "closedin (subtopology euclidean U) S"
      and UT: "closedin (subtopology euclidean U) T"
      and "S \<inter> T = {}"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> S \<Longrightarrow> f x = a"
          "\<And>x. x \<in> T \<Longrightarrow> f x = b"
proof (cases "a = b")
  case True then show ?thesis
    by (rule_tac f = "\<lambda>x. b" in that) (auto simp: continuous_on_const)
next
  case False
  then show ?thesis
    apply (rule Urysohn_local_strong [OF assms])
    apply (erule that, assumption)
    apply (meson US closedin_singleton closedin_trans)
    apply (meson UT closedin_singleton closedin_trans)
    done
qed

lemma Urysohn_strong:
  assumes US: "closed S"
      and UT: "closed T"
      and "S \<inter> T = {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on UNIV f"
          "\<And>x. f x \<in> closed_segment a b"
          "\<And>x. f x = a \<longleftrightarrow> x \<in> S"
          "\<And>x. f x = b \<longleftrightarrow> x \<in> T"
using assms by (auto intro: Urysohn_local_strong [of UNIV S T])

proposition Urysohn:
  assumes US: "closed S"
      and UT: "closed T"
      and "S \<inter> T = {}"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on UNIV f"
          "\<And>x. f x \<in> closed_segment a b"
          "\<And>x. x \<in> S \<Longrightarrow> f x = a"
          "\<And>x. x \<in> T \<Longrightarrow> f x = b"
using assms by (auto intro: Urysohn_local [of UNIV S T a b])


subsection\<open> The Dugundji extension theorem, and Tietze variants as corollaries.\<close>

text\<open>J. Dugundji. An extension of Tietze's theorem. Pacific J. Math. Volume 1, Number 3 (1951), 353-367.
http://projecteuclid.org/euclid.pjm/1103052106\<close>

theorem Dugundji:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes "convex C" "C \<noteq> {}"
      and cloin: "closedin (subtopology euclidean U) S"
      and contf: "continuous_on S f" and "f ` S \<subseteq> C"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C"
                  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (cases "S = {}")
  case True then show thesis
    apply (rule_tac g="\<lambda>x. SOME y. y \<in> C" in that)
      apply (rule continuous_intros)
     apply (meson all_not_in_conv \<open>C \<noteq> {}\<close> image_subsetI someI_ex, simp)
    done
next
  case False
  then have sd_pos: "\<And>x. \<lbrakk>x \<in> U; x \<notin> S\<rbrakk> \<Longrightarrow> 0 < setdist {x} S"
    using setdist_eq_0_closedin [OF cloin] le_less setdist_pos_le by fastforce
  define \<B> where "\<B> = {ball x (setdist {x} S / 2) |x. x \<in> U - S}"
  have [simp]: "\<And>T. T \<in> \<B> \<Longrightarrow> open T"
    by (auto simp: \<B>_def)
  have USS: "U - S \<subseteq> \<Union>\<B>"
    by (auto simp: sd_pos \<B>_def)
  obtain \<C> where USsub: "U - S \<subseteq> \<Union>\<C>"
       and nbrhd: "\<And>U. U \<in> \<C> \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<B> \<and> U \<subseteq> T)"
       and fin: "\<And>x. x \<in> U - S
                     \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U. U \<in> \<C> \<and> U \<inter> V \<noteq> {}}"
    using paracompact [OF USS] by auto
  have "\<exists>v a. v \<in> U \<and> v \<notin> S \<and> a \<in> S \<and>
              T \<subseteq> ball v (setdist {v} S / 2) \<and>
              dist v a \<le> 2 * setdist {v} S" if "T \<in> \<C>" for T
  proof -
    obtain v where v: "T \<subseteq> ball v (setdist {v} S / 2)" "v \<in> U" "v \<notin> S"
      using \<open>T \<in> \<C>\<close> nbrhd by (force simp: \<B>_def)
    then obtain a where "a \<in> S" "dist v a < 2 * setdist {v} S"
      using setdist_ltE [of "{v}" S "2 * setdist {v} S"]
      using False sd_pos by force
    with v show ?thesis
      apply (rule_tac x=v in exI)
      apply (rule_tac x=a in exI, auto)
      done
  qed
  then obtain \<V> \<A> where
    VA: "\<And>T. T \<in> \<C> \<Longrightarrow> \<V> T \<in> U \<and> \<V> T \<notin> S \<and> \<A> T \<in> S \<and>
              T \<subseteq> ball (\<V> T) (setdist {\<V> T} S / 2) \<and>
              dist (\<V> T) (\<A> T) \<le> 2 * setdist {\<V> T} S"
    by metis
  have sdle: "setdist {\<V> T} S \<le> 2 * setdist {v} S" if "T \<in> \<C>" "v \<in> T" for T v
    using setdist_Lipschitz [of "\<V> T" S v] VA [OF \<open>T \<in> \<C>\<close>] \<open>v \<in> T\<close> by auto
  have d6: "dist a (\<A> T) \<le> 6 * dist a v" if "T \<in> \<C>" "v \<in> T" "a \<in> S" for T v a
  proof -
    have "dist (\<V> T) v < setdist {\<V> T} S / 2"
      using that VA mem_ball by blast
    also have "... \<le> setdist {v} S"
      using sdle [OF \<open>T \<in> \<C>\<close> \<open>v \<in> T\<close>] by simp
    also have vS: "setdist {v} S \<le> dist a v"
      by (simp add: setdist_le_dist setdist_sym \<open>a \<in> S\<close>)
    finally have VTV: "dist (\<V> T) v < dist a v" .
    have VTS: "setdist {\<V> T} S \<le> 2 * dist a v"
      using sdle that vS by force
    have "dist a (\<A> T) \<le> dist a v + dist v (\<V> T) + dist (\<V> T) (\<A> T)"
      by (metis add.commute add_le_cancel_left dist_commute dist_triangle2 dist_triangle_le)
    also have "... \<le> dist a v + dist a v + dist (\<V> T) (\<A> T)"
      using VTV by (simp add: dist_commute)
    also have "... \<le> 2 * dist a v + 2 * setdist {\<V> T} S"
      using VA [OF \<open>T \<in> \<C>\<close>] by auto
    finally show ?thesis
      using VTS by linarith
  qed
  obtain H :: "['a set, 'a] \<Rightarrow> real"
    where Hcont: "\<And>Z. Z \<in> \<C> \<Longrightarrow> continuous_on (U-S) (H Z)"
      and Hge0: "\<And>Z x. \<lbrakk>Z \<in> \<C>; x \<in> U-S\<rbrakk> \<Longrightarrow> 0 \<le> H Z x"
      and Heq0: "\<And>x Z. \<lbrakk>Z \<in> \<C>; x \<in> U-S; x \<notin> Z\<rbrakk> \<Longrightarrow> H Z x = 0"
      and H1: "\<And>x. x \<in> U-S \<Longrightarrow> supp_sum (\<lambda>W. H W x) \<C> = 1"
      and Hfin: "\<And>x. x \<in> U-S \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. \<exists>x\<in>V. H U x \<noteq> 0}"
    apply (rule subordinate_partition_of_unity [OF USsub _ fin])
    using nbrhd by auto
  define g where "g \<equiv> \<lambda>x. if x \<in> S then f x else supp_sum (\<lambda>T. H T x *\<^sub>R f(\<A> T)) \<C>"
  show ?thesis
  proof (rule that)
    show "continuous_on U g"
    proof (clarsimp simp: continuous_on_eq_continuous_within)
      fix a assume "a \<in> U"
      show "continuous (at a within U) g"
      proof (cases "a \<in> S")
        case True show ?thesis
        proof (clarsimp simp add: continuous_within_topological)
          fix W
          assume "open W" "g a \<in> W"
          then obtain e where "0 < e" and e: "ball (f a) e \<subseteq> W"
            using openE True g_def by auto
          have "continuous (at a within S) f"
            using True contf continuous_on_eq_continuous_within by blast
          then obtain d where "0 < d"
                        and d: "\<And>x. \<lbrakk>x \<in> S; dist x a < d\<rbrakk> \<Longrightarrow> dist (f x) (f a) < e"
            using continuous_within_eps_delta \<open>0 < e\<close> by force
          have "g y \<in> ball (f a) e" if "y \<in> U" and y: "y \<in> ball a (d / 6)" for y
          proof (cases "y \<in> S")
            case True
            then have "dist (f a) (f y) < e"
              by (metis ball_divide_subset_numeral dist_commute in_mono mem_ball y d)
            then show ?thesis
              by (simp add: True g_def)
          next
            case False
            have *: "dist (f (\<A> T)) (f a) < e" if "T \<in> \<C>" "H T y \<noteq> 0" for T
            proof -
              have "y \<in> T"
                using Heq0 that False \<open>y \<in> U\<close> by blast
              have "dist (\<A> T) a < d"
                using d6 [OF \<open>T \<in> \<C>\<close> \<open>y \<in> T\<close> \<open>a \<in> S\<close>] y
                by (simp add: dist_commute mult.commute)
              then show ?thesis
                using VA [OF \<open>T \<in> \<C>\<close>] by (auto simp: d)
            qed
            have "supp_sum (\<lambda>T. H T y *\<^sub>R f (\<A> T)) \<C> \<in> ball (f a) e"
              apply (rule convex_supp_sum [OF convex_ball])
              apply (simp_all add: False H1 Hge0 \<open>y \<in> U\<close>)
              by (metis dist_commute *)
            then show ?thesis
              by (simp add: False g_def)
          qed
          then show "\<exists>A. open A \<and> a \<in> A \<and> (\<forall>y\<in>U. y \<in> A \<longrightarrow> g y \<in> W)"
            apply (rule_tac x = "ball a (d / 6)" in exI)
            using e \<open>0 < d\<close> by fastforce
        qed
      next
        case False
        obtain N where N: "open N" "a \<in> N"
                   and finN: "finite {U \<in> \<C>. \<exists>a\<in>N. H U a \<noteq> 0}"
          using Hfin False \<open>a \<in> U\<close> by auto
        have oUS: "openin (subtopology euclidean U) (U - S)"
          using cloin by (simp add: openin_diff)
        have HcontU: "continuous (at a within U) (H T)" if "T \<in> \<C>" for T
          using Hcont [OF \<open>T \<in> \<C>\<close>] False  \<open>a \<in> U\<close> \<open>T \<in> \<C>\<close>
          apply (simp add: continuous_on_eq_continuous_within continuous_within)
          apply (rule Lim_transform_within_set)
          using oUS
            apply (force simp: eventually_at openin_contains_ball dist_commute dest!: bspec)+
          done
        show ?thesis
        proof (rule continuous_transform_within_openin [OF _ oUS])
          show "continuous (at a within U) (\<lambda>x. supp_sum (\<lambda>T. H T x *\<^sub>R f (\<A> T)) \<C>)"
          proof (rule continuous_transform_within_openin)
            show "continuous (at a within U)
                    (\<lambda>x. \<Sum>T\<in>{U \<in> \<C>. \<exists>x\<in>N. H U x \<noteq> 0}. H T x *\<^sub>R f (\<A> T))"
              by (force intro: continuous_intros HcontU)+
          next
            show "openin (subtopology euclidean U) ((U - S) \<inter> N)"
              using N oUS openin_trans by blast
          next
            show "a \<in> (U - S) \<inter> N" using False \<open>a \<in> U\<close> N by blast
          next
            show "\<And>x. x \<in> (U - S) \<inter> N \<Longrightarrow>
                         (\<Sum>T \<in> {U \<in> \<C>. \<exists>x\<in>N. H U x \<noteq> 0}. H T x *\<^sub>R f (\<A> T))
                         = supp_sum (\<lambda>T. H T x *\<^sub>R f (\<A> T)) \<C>"
              by (auto simp: supp_sum_def support_on_def
                       intro: sum.mono_neutral_right [OF finN])
          qed
        next
          show "a \<in> U - S" using False \<open>a \<in> U\<close> by blast
        next
          show "\<And>x. x \<in> U - S \<Longrightarrow> supp_sum (\<lambda>T. H T x *\<^sub>R f (\<A> T)) \<C> = g x"
            by (simp add: g_def)
        qed
      qed
    qed
    show "g ` U \<subseteq> C"
      using \<open>f ` S \<subseteq> C\<close> VA
      by (fastforce simp: g_def Hge0 intro!: convex_supp_sum [OF \<open>convex C\<close>] H1)
    show "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
      by (simp add: g_def)
  qed
qed


corollary Tietze:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
      and "0 \<le> B"
      and "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> B"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
                  "\<And>x. x \<in> U \<Longrightarrow> norm(g x) \<le> B"
using assms
by (auto simp: image_subset_iff intro: Dugundji [of "cball 0 B" U S f])

corollary Tietze_closed_interval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
      and "cbox a b \<noteq> {}"
      and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> cbox a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
                  "\<And>x. x \<in> U \<Longrightarrow> g x \<in> cbox a b"
apply (rule Dugundji [of "cbox a b" U S f])
using assms by auto

corollary Tietze_closed_interval_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
      and "a \<le> b"
      and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> cbox a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
                  "\<And>x. x \<in> U \<Longrightarrow> g x \<in> cbox a b"
apply (rule Dugundji [of "cbox a b" U S f])
using assms by (auto simp: image_subset_iff)

corollary Tietze_open_interval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
      and "box a b \<noteq> {}"
      and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> box a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
                  "\<And>x. x \<in> U \<Longrightarrow> g x \<in> box a b"
apply (rule Dugundji [of "box a b" U S f])
using assms by auto

corollary Tietze_open_interval_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
      and "a < b"
      and no: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> box a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
                  "\<And>x. x \<in> U \<Longrightarrow> g x \<in> box a b"
apply (rule Dugundji [of "box a b" U S f])
using assms by (auto simp: image_subset_iff)

corollary Tietze_unbounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on S f"
      and "closedin (subtopology euclidean U) S"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
apply (rule Dugundji [of UNIV U S f])
using assms by auto

end
