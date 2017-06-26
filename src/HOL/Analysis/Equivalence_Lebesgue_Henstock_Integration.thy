(*  Title:      HOL/Analysis/Equivalence_Lebesgue_Henstock_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
*)

theory Equivalence_Lebesgue_Henstock_Integration
  imports Lebesgue_Measure Henstock_Kurzweil_Integration Complete_Measure Set_Integral
begin

lemma le_left_mono: "x \<le> y \<Longrightarrow> y \<le> a \<longrightarrow> x \<le> (a::'a::preorder)"
  by (auto intro: order_trans)

lemma ball_trans:
  assumes "y \<in> ball z q" "r + q \<le> s" shows "ball y r \<subseteq> ball z s"
proof safe
  fix x assume x: "x \<in> ball y r"
  have "dist z x \<le> dist z y + dist y x"
    by (rule dist_triangle)
  also have "\<dots> < s"
    using assms x by auto
  finally show "x \<in> ball z s"
    by simp
qed

lemma has_integral_implies_lebesgue_measurable_cbox:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "(f has_integral I) (cbox x y)"
  shows "f \<in> lebesgue_on (cbox x y) \<rightarrow>\<^sub>M borel"
proof (rule cld_measure.borel_measurable_cld)
  let ?L = "lebesgue_on (cbox x y)"
  let ?\<mu> = "emeasure ?L"
  let ?\<mu>' = "outer_measure_of ?L"
  interpret L: finite_measure ?L
  proof
    show "?\<mu> (space ?L) \<noteq> \<infinity>"
      by (simp add: emeasure_restrict_space space_restrict_space emeasure_lborel_cbox_eq)
  qed

  show "cld_measure ?L"
  proof
    fix B A assume "B \<subseteq> A" "A \<in> null_sets ?L"
    then show "B \<in> sets ?L"
      using null_sets_completion_subset[OF \<open>B \<subseteq> A\<close>, of lborel]
      by (auto simp add: null_sets_restrict_space sets_restrict_space_iff intro: )
  next
    fix A assume "A \<subseteq> space ?L" "\<And>B. B \<in> sets ?L \<Longrightarrow> ?\<mu> B < \<infinity> \<Longrightarrow> A \<inter> B \<in> sets ?L"
    from this(1) this(2)[of "space ?L"] show "A \<in> sets ?L"
      by (auto simp: Int_absorb2 less_top[symmetric])
  qed auto
  then interpret cld_measure ?L
    .

  have content_eq_L: "A \<in> sets borel \<Longrightarrow> A \<subseteq> cbox x y \<Longrightarrow> content A = measure ?L A" for A
    by (subst measure_restrict_space) (auto simp: measure_def)

  fix E and a b :: real assume "E \<in> sets ?L" "a < b" "0 < ?\<mu> E" "?\<mu> E < \<infinity>"
  then obtain M :: real where "?\<mu> E = M" "0 < M"
    by (cases "?\<mu> E") auto
  define e where "e = M / (4 + 2 / (b - a))"
  from \<open>a < b\<close> \<open>0<M\<close> have "0 < e"
    by (auto intro!: divide_pos_pos simp: field_simps e_def)

  have "e < M / (3 + 2 / (b - a))"
    using \<open>a < b\<close> \<open>0 < M\<close>
    unfolding e_def by (intro divide_strict_left_mono add_strict_right_mono mult_pos_pos) (auto simp: field_simps)
  then have "2 * e < (b - a) * (M - e * 3)"
    using \<open>0<M\<close> \<open>0 < e\<close> \<open>a < b\<close> by (simp add: field_simps)

  have e_less_M: "e < M / 1"
    unfolding e_def using \<open>a < b\<close> \<open>0<M\<close> by (intro divide_strict_left_mono) (auto simp: field_simps)

  obtain d
    where "gauge d"
      and integral_f: "\<forall>p. p tagged_division_of cbox x y \<and> d fine p \<longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - I) < e"
    using \<open>0<e\<close> f unfolding has_integral by auto

  define C where "C X m = X \<inter> {x. ball x (1/Suc m) \<subseteq> d x}" for X m
  have "incseq (C X)" for X
    unfolding C_def [abs_def]
    by (intro monoI Collect_mono conj_mono imp_refl le_left_mono subset_ball divide_left_mono Int_mono) auto

  { fix X assume "X \<subseteq> space ?L" and eq: "?\<mu>' X = ?\<mu> E"
    have "(SUP m. outer_measure_of ?L (C X m)) = outer_measure_of ?L (\<Union>m. C X m)"
      using \<open>X \<subseteq> space ?L\<close> by (intro SUP_outer_measure_of_incseq \<open>incseq (C X)\<close>) (auto simp: C_def)
    also have "(\<Union>m. C X m) = X"
    proof -
      { fix x
        obtain e where "0 < e" "ball x e \<subseteq> d x"
          using gaugeD[OF \<open>gauge d\<close>, of x] unfolding open_contains_ball by auto
        moreover
        obtain n where "1 / (1 + real n) < e"
          using reals_Archimedean[OF \<open>0<e\<close>] by (auto simp: inverse_eq_divide)
        then have "ball x (1 / (1 + real n)) \<subseteq> ball x e"
          by (intro subset_ball) auto
        ultimately have "\<exists>n. ball x (1 / (1 + real n)) \<subseteq> d x"
          by blast }
      then show ?thesis
        by (auto simp: C_def)
    qed
    finally have "(SUP m. outer_measure_of ?L (C X m)) = ?\<mu> E"
      using eq by auto
    also have "\<dots> > M - e"
      using \<open>0 < M\<close> \<open>?\<mu> E = M\<close> \<open>0<e\<close> by (auto intro!: ennreal_lessI)
    finally have "\<exists>m. M - e < outer_measure_of ?L (C X m)"
      unfolding less_SUP_iff by auto }
  note C = this

  let ?E = "{x\<in>E. f x \<le> a}" and ?F = "{x\<in>E. b \<le> f x}"

  have "\<not> (?\<mu>' ?E = ?\<mu> E \<and> ?\<mu>' ?F = ?\<mu> E)"
  proof
    assume eq: "?\<mu>' ?E = ?\<mu> E \<and> ?\<mu>' ?F = ?\<mu> E"
    with C[of ?E] C[of ?F] \<open>E \<in> sets ?L\<close>[THEN sets.sets_into_space] obtain ma mb
      where "M - e < outer_measure_of ?L (C ?E ma)" "M - e < outer_measure_of ?L (C ?F mb)"
      by auto
    moreover define m where "m = max ma mb"
    ultimately have M_minus_e: "M - e < outer_measure_of ?L (C ?E m)" "M - e < outer_measure_of ?L (C ?F m)"
      using
        incseqD[OF \<open>incseq (C ?E)\<close>, of ma m, THEN outer_measure_of_mono]
        incseqD[OF \<open>incseq (C ?F)\<close>, of mb m, THEN outer_measure_of_mono]
      by (auto intro: less_le_trans)
    define d' where "d' x = d x \<inter> ball x (1 / (3 * Suc m))" for x
    have "gauge d'"
      unfolding d'_def by (intro gauge_Int \<open>gauge d\<close> gauge_ball) auto
    then obtain p where p: "p tagged_division_of cbox x y" "d' fine p"
      by (rule fine_division_exists)
    then have "d fine p"
      unfolding d'_def[abs_def] fine_def by auto

    define s where "s = {(x::'a, k). k \<inter> (C ?E m) \<noteq> {} \<and> k \<inter> (C ?F m) \<noteq> {}}"
    define T where "T E k = (SOME x. x \<in> k \<inter> C E m)" for E k
    let ?A = "(\<lambda>(x, k). (T ?E k, k)) ` (p \<inter> s) \<union> (p - s)"
    let ?B = "(\<lambda>(x, k). (T ?F k, k)) ` (p \<inter> s) \<union> (p - s)"

    { fix X assume X_eq: "X = ?E \<or> X = ?F"
      let ?T = "(\<lambda>(x, k). (T X k, k))"
      let ?p = "?T ` (p \<inter> s) \<union> (p - s)"

      have in_s: "(x, k) \<in> s \<Longrightarrow> T X k \<in> k \<inter> C X m" for x k
        using someI_ex[of "\<lambda>x. x \<in> k \<inter> C X m"] X_eq unfolding ex_in_conv by (auto simp: T_def s_def)

      { fix x k assume "(x, k) \<in> p" "(x, k) \<in> s"
        have k: "k \<subseteq> ball x (1 / (3 * Suc m))"
          using \<open>d' fine p\<close>[THEN fineD, OF \<open>(x, k) \<in> p\<close>] by (auto simp: d'_def)
        then have "x \<in> ball (T X k) (1 / (3 * Suc m))"
          using in_s[OF \<open>(x, k) \<in> s\<close>] by (auto simp: C_def subset_eq dist_commute)
        then have "ball x (1 / (3 * Suc m)) \<subseteq> ball (T X k) (1 / Suc m)"
          by (rule ball_trans) (auto simp: divide_simps)
        with k in_s[OF \<open>(x, k) \<in> s\<close>] have "k \<subseteq> d (T X k)"
          by (auto simp: C_def) }
      then have "d fine ?p"
        using \<open>d fine p\<close> by (auto intro!: fineI)
      moreover
      have "?p tagged_division_of cbox x y"
      proof (rule tagged_division_ofI)
        show "finite ?p"
          using p(1) by auto
      next
        fix z k assume *: "(z, k) \<in> ?p"
        then consider "(z, k) \<in> p" "(z, k) \<notin> s"
          | x' where "(x', k) \<in> p" "(x', k) \<in> s" "z = T X k"
          by (auto simp: T_def)
        then have "z \<in> k \<and> k \<subseteq> cbox x y \<and> (\<exists>a b. k = cbox a b)"
          using p(1) by cases (auto dest: in_s)
        then show "z \<in> k" "k \<subseteq> cbox x y" "\<exists>a b. k = cbox a b"
          by auto
      next
        fix z k z' k' assume "(z, k) \<in> ?p" "(z', k') \<in> ?p" "(z, k) \<noteq> (z', k')"
        with tagged_division_ofD(5)[OF p(1), of _ k _ k']
        show "interior k \<inter> interior k' = {}"
          by (auto simp: T_def dest: in_s)
      next
        have "{k. \<exists>x. (x, k) \<in> ?p} = {k. \<exists>x. (x, k) \<in> p}"
          by (auto simp: T_def image_iff Bex_def)
        then show "\<Union>{k. \<exists>x. (x, k) \<in> ?p} = cbox x y"
          using p(1) by auto
      qed
      ultimately have I: "norm ((\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) - I) < e"
        using integral_f by auto

      have "(\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) =
        (\<Sum>(x, k)\<in>?T ` (p \<inter> s). content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p - s. content k *\<^sub>R f x)"
        using p(1)[THEN tagged_division_ofD(1)]
        by (safe intro!: sum.union_inter_neutral) (auto simp: s_def T_def)
      also have "(\<Sum>(x, k)\<in>?T ` (p \<inter> s). content k *\<^sub>R f x) = (\<Sum>(x, k)\<in>p \<inter> s. content k *\<^sub>R f (T X k))"
      proof (subst sum.reindex_nontrivial, safe)
        fix x1 x2 k assume 1: "(x1, k) \<in> p" "(x1, k) \<in> s" and 2: "(x2, k) \<in> p" "(x2, k) \<in> s"
          and eq: "content k *\<^sub>R f (T X k) \<noteq> 0"
        with tagged_division_ofD(5)[OF p(1), of x1 k x2 k] tagged_division_ofD(4)[OF p(1), of x1 k]
        show "x1 = x2"
          by (auto simp: content_eq_0_interior)
      qed (use p in \<open>auto intro!: sum.cong\<close>)
      finally have eq: "(\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) =
        (\<Sum>(x, k)\<in>p \<inter> s. content k *\<^sub>R f (T X k)) + (\<Sum>(x, k)\<in>p - s. content k *\<^sub>R f x)" .

      have in_T: "(x, k) \<in> s \<Longrightarrow> T X k \<in> X" for x k
        using in_s[of x k] by (auto simp: C_def)

      note I eq in_T }
    note parts = this

    have p_in_L: "(x, k) \<in> p \<Longrightarrow> k \<in> sets ?L" for x k
      using tagged_division_ofD(3, 4)[OF p(1), of x k] by (auto simp: sets_restrict_space)

    have [simp]: "finite p"
      using tagged_division_ofD(1)[OF p(1)] .

    have "(M - 3*e) * (b - a) \<le> (\<Sum>(x, k)\<in>p \<inter> s. content k) * (b - a)"
    proof (intro mult_right_mono)
      have fin: "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) < \<infinity>" for X
        using \<open>?\<mu> E < \<infinity>\<close> by (rule le_less_trans[rotated]) (auto intro!: emeasure_mono \<open>E \<in> sets ?L\<close>)
      have sets: "(E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) \<in> sets ?L" for X
        using tagged_division_ofD(1)[OF p(1)] by (intro sets.Diff \<open>E \<in> sets ?L\<close> sets.finite_Union sets.Int) (auto intro: p_in_L)
      { fix X assume "X \<subseteq> E" "M - e < ?\<mu>' (C X m)"
        have "M - e \<le> ?\<mu>' (C X m)"
          by (rule less_imp_le) fact
        also have "\<dots> \<le> ?\<mu>' (E - (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}))"
        proof (intro outer_measure_of_mono subsetI)
          fix v assume "v \<in> C X m"
          then have "v \<in> cbox x y" "v \<in> E"
            using \<open>E \<subseteq> space ?L\<close> \<open>X \<subseteq> E\<close> by (auto simp: space_restrict_space C_def)
          then obtain z k where "(z, k) \<in> p" "v \<in> k"
            using tagged_division_ofD(6)[OF p(1), symmetric] by auto
          then show "v \<in> E - E \<inter> (\<Union>{k\<in>snd`p. k \<inter> C X m = {}})"
            using \<open>v \<in> C X m\<close> \<open>v \<in> E\<close> by auto
        qed
        also have "\<dots> = ?\<mu> E - ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}})"
          using \<open>E \<in> sets ?L\<close> fin[of X] sets[of X] by (auto intro!: emeasure_Diff)
        finally have "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) \<le> e"
          using \<open>0 < e\<close> e_less_M apply (cases "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}})")
          by (auto simp add: \<open>?\<mu> E = M\<close> ennreal_minus ennreal_le_iff2)
        note this }
      note upper_bound = this

      have "?\<mu> (E \<inter> \<Union>(snd`(p - s))) =
        ?\<mu> ((E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?E m = {}}) \<union> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?F m = {}}))"
        by (intro arg_cong[where f="?\<mu>"]) (auto simp: s_def image_def Bex_def)
      also have "\<dots> \<le> ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?E m = {}}) + ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?F m = {}})"
        using sets[of ?E] sets[of ?F] M_minus_e by (intro emeasure_subadditive) auto
      also have "\<dots> \<le> e + ennreal e"
        using upper_bound[of ?E] upper_bound[of ?F] M_minus_e by (intro add_mono) auto
      finally have "?\<mu> E - 2*e \<le> ?\<mu> (E - (E \<inter> \<Union>(snd`(p - s))))"
        using \<open>0 < e\<close> \<open>E \<in> sets ?L\<close> tagged_division_ofD(1)[OF p(1)]
        by (subst emeasure_Diff)
           (auto simp: ennreal_plus[symmetric] top_unique simp del: ennreal_plus
                 intro!: sets.Int sets.finite_UN ennreal_mono_minus intro: p_in_L)
      also have "\<dots> \<le> ?\<mu> (\<Union>x\<in>p \<inter> s. snd x)"
      proof (safe intro!: emeasure_mono subsetI)
        fix v assume "v \<in> E" and not: "v \<notin> (\<Union>x\<in>p \<inter> s. snd x)"
        then have "v \<in> cbox x y"
          using \<open>E \<subseteq> space ?L\<close> by (auto simp: space_restrict_space)
        then obtain z k where "(z, k) \<in> p" "v \<in> k"
          using tagged_division_ofD(6)[OF p(1), symmetric] by auto
        with not show "v \<in> UNION (p - s) snd"
          by (auto intro!: bexI[of _ "(z, k)"] elim: ballE[of _ _ "(z, k)"])
      qed (auto intro!: sets.Int sets.finite_UN ennreal_mono_minus intro: p_in_L)
      also have "\<dots> = measure ?L (\<Union>x\<in>p \<inter> s. snd x)"
        by (auto intro!: emeasure_eq_ennreal_measure)
      finally have "M - 2 * e \<le> measure ?L (\<Union>x\<in>p \<inter> s. snd x)"
        unfolding \<open>?\<mu> E = M\<close> using \<open>0 < e\<close> by (simp add: ennreal_minus)
      also have "measure ?L (\<Union>x\<in>p \<inter> s. snd x) = content (\<Union>x\<in>p \<inter> s. snd x)"
        using tagged_division_ofD(1,3,4) [OF p(1)]
        by (intro content_eq_L[symmetric])
           (fastforce intro!: sets.finite_UN UN_least del: subsetI)+
      also have "content (\<Union>x\<in>p \<inter> s. snd x) \<le> (\<Sum>k\<in>p \<inter> s. content (snd k))"
        using p(1) by (auto simp: emeasure_lborel_cbox_eq intro!: measure_subadditive_finite
                            dest!: p(1)[THEN tagged_division_ofD(4)])
      finally show "M - 3 * e \<le> (\<Sum>(x, y)\<in>p \<inter> s. content y)"
        using \<open>0 < e\<close> by (simp add: split_beta)
    qed (use \<open>a < b\<close> in auto)
    also have "\<dots> = (\<Sum>(x, k)\<in>p \<inter> s. content k * (b - a))"
      by (simp add: sum_distrib_right split_beta')
    also have "\<dots> \<le> (\<Sum>(x, k)\<in>p \<inter> s. content k * (f (T ?F k) - f (T ?E k)))"
      using parts(3) by (auto intro!: sum_mono mult_left_mono diff_mono)
    also have "\<dots> = (\<Sum>(x, k)\<in>p \<inter> s. content k * f (T ?F k)) - (\<Sum>(x, k)\<in>p \<inter> s. content k * f (T ?E k))"
      by (auto intro!: sum.cong simp: field_simps sum_subtractf[symmetric])
    also have "\<dots> = (\<Sum>(x, k)\<in>?B. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>?A. content k *\<^sub>R f x)"
      by (subst (1 2) parts) auto
    also have "\<dots> \<le> norm ((\<Sum>(x, k)\<in>?B. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>?A. content k *\<^sub>R f x))"
      by auto
    also have "\<dots> \<le> e + e"
      using parts(1)[of ?E] parts(1)[of ?F] by (intro norm_diff_triangle_le[of _ I]) auto
    finally show False
      using \<open>2 * e < (b - a) * (M - e * 3)\<close> by (auto simp: field_simps)
  qed
  moreover have "?\<mu>' ?E \<le> ?\<mu> E" "?\<mu>' ?F \<le> ?\<mu> E"
    unfolding outer_measure_of_eq[OF \<open>E \<in> sets ?L\<close>, symmetric] by (auto intro!: outer_measure_of_mono)
  ultimately show "min (?\<mu>' ?E) (?\<mu>' ?F) < ?\<mu> E"
    unfolding min_less_iff_disj by (auto simp: less_le)
qed

lemma has_integral_implies_lebesgue_measurable_real:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "(f has_integral I) \<Omega>"
  shows "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
proof -
  define B :: "nat \<Rightarrow> 'a set" where "B n = cbox (- real n *\<^sub>R One) (real n *\<^sub>R One)" for n
  show "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
  proof (rule measurable_piecewise_restrict)
    have "(\<Union>n. box (- real n *\<^sub>R One) (real n *\<^sub>R One)) \<subseteq> UNION UNIV B"
      unfolding B_def by (intro UN_mono box_subset_cbox order_refl)
    then show "countable (range B)" "space lebesgue \<subseteq> UNION UNIV B"
      by (auto simp: B_def UN_box_eq_UNIV)
  next
    fix \<Omega>' assume "\<Omega>' \<in> range B"
    then obtain n where \<Omega>': "\<Omega>' = B n" by auto
    then show "\<Omega>' \<inter> space lebesgue \<in> sets lebesgue"
      by (auto simp: B_def)

    have "f integrable_on \<Omega>"
      using f by auto
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on \<Omega>"
      by (auto simp: integrable_on_def cong: has_integral_cong)
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on (\<Omega> \<union> B n)"
      by (rule integrable_on_superset[rotated 2]) auto
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on B n"
      unfolding B_def by (rule integrable_on_subcbox) auto
    then show "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue_on \<Omega>' \<rightarrow>\<^sub>M borel"
      unfolding B_def \<Omega>' by (auto intro: has_integral_implies_lebesgue_measurable_cbox simp: integrable_on_def)
  qed
qed

lemma has_integral_implies_lebesgue_measurable:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "(f has_integral I) \<Omega>"
  shows "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
proof (intro borel_measurable_euclidean_space[where 'c='b, THEN iffD2] ballI)
  fix i :: "'b" assume "i \<in> Basis"
  have "(\<lambda>x. (f x \<bullet> i) * indicator \<Omega> x) \<in> borel_measurable (completion lborel)"
    using has_integral_linear[OF f bounded_linear_inner_left, of i]
    by (intro has_integral_implies_lebesgue_measurable_real) (auto simp: comp_def)
  then show "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x \<bullet> i) \<in> borel_measurable (completion lborel)"
    by (simp add: ac_simps)
qed

subsection \<open>Equivalence Lebesgue integral on @{const lborel} and HK-integral\<close>

lemma has_integral_measure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and finite: "emeasure lborel A < \<infinity>"
  shows "((\<lambda>x. 1) has_integral measure lborel A) A"
proof -
  { fix l u :: 'a
    have "((\<lambda>x. 1) has_integral measure lborel (box l u)) (box l u)"
    proof cases
      assume "\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b"
      then show ?thesis
        apply simp
        apply (subst has_integral_restrict[symmetric, OF box_subset_cbox])
        apply (subst has_integral_spike_interior_eq[where g="\<lambda>_. 1"])
        using has_integral_const[of "1::real" l u]
        apply (simp_all add: inner_diff_left[symmetric] content_cbox_cases)
        done
    next
      assume "\<not> (\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b)"
      then have "box l u = {}"
        unfolding box_eq_empty by (auto simp: not_le intro: less_imp_le)
      then show ?thesis
        by simp
    qed }
  note has_integral_box = this

  { fix a b :: 'a let ?M = "\<lambda>A. measure lborel (A \<inter> box a b)"
    have "Int_stable  (range (\<lambda>(a, b). box a b))"
      by (auto simp: Int_stable_def box_Int_box)
    moreover have "(range (\<lambda>(a, b). box a b)) \<subseteq> Pow UNIV"
      by auto
    moreover have "A \<in> sigma_sets UNIV (range (\<lambda>(a, b). box a b))"
       using A unfolding borel_eq_box by simp
    ultimately have "((\<lambda>x. 1) has_integral ?M A) (A \<inter> box a b)"
    proof (induction rule: sigma_sets_induct_disjoint)
      case (basic A) then show ?case
        by (auto simp: box_Int_box has_integral_box)
    next
      case empty then show ?case
        by simp
    next
      case (compl A)
      then have [measurable]: "A \<in> sets borel"
        by (simp add: borel_eq_box)

      have "((\<lambda>x. 1) has_integral ?M (box a b)) (box a b)"
        by (simp add: has_integral_box)
      moreover have "((\<lambda>x. if x \<in> A \<inter> box a b then 1 else 0) has_integral ?M A) (box a b)"
        by (subst has_integral_restrict) (auto intro: compl)
      ultimately have "((\<lambda>x. 1 - (if x \<in> A \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_diff)
      then have "((\<lambda>x. (if x \<in> (UNIV - A) \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_cong[THEN iffD1, rotated 1]) auto
      then have "((\<lambda>x. 1) has_integral ?M (box a b) - ?M A) ((UNIV - A) \<inter> box a b)"
        by (subst (asm) has_integral_restrict) auto
      also have "?M (box a b) - ?M A = ?M (UNIV - A)"
        by (subst measure_Diff[symmetric]) (auto simp: emeasure_lborel_box_eq Diff_Int_distrib2)
      finally show ?case .
    next
      case (union F)
      then have [measurable]: "\<And>i. F i \<in> sets borel"
        by (simp add: borel_eq_box subset_eq)
      have "((\<lambda>x. if x \<in> UNION UNIV F \<inter> box a b then 1 else 0) has_integral ?M (\<Union>i. F i)) (box a b)"
      proof (rule has_integral_monotone_convergence_increasing)
        let ?f = "\<lambda>k x. \<Sum>i<k. if x \<in> F i \<inter> box a b then 1 else 0 :: real"
        show "\<And>k. (?f k has_integral (\<Sum>i<k. ?M (F i))) (box a b)"
          using union.IH by (auto intro!: has_integral_sum simp del: Int_iff)
        show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
          by (intro sum_mono2) auto
        from union(1) have *: "\<And>x i j. x \<in> F i \<Longrightarrow> x \<in> F j \<longleftrightarrow> j = i"
          by (auto simp add: disjoint_family_on_def)
        show "\<And>x. (\<lambda>k. ?f k x) \<longlonglongrightarrow> (if x \<in> UNION UNIV F \<inter> box a b then 1 else 0)"
          apply (auto simp: * sum.If_cases Iio_Int_singleton)
          apply (rule_tac k="Suc xa" in LIMSEQ_offset)
          apply simp
          done
        have *: "emeasure lborel ((\<Union>x. F x) \<inter> box a b) \<le> emeasure lborel (box a b)"
          by (intro emeasure_mono) auto

        with union(1) show "(\<lambda>k. \<Sum>i<k. ?M (F i)) \<longlonglongrightarrow> ?M (\<Union>i. F i)"
          unfolding sums_def[symmetric] UN_extend_simps
          by (intro measure_UNION) (auto simp: disjoint_family_on_def emeasure_lborel_box_eq top_unique)
      qed
      then show ?case
        by (subst (asm) has_integral_restrict) auto
    qed }
  note * = this

  show ?thesis
  proof (rule has_integral_monotone_convergence_increasing)
    let ?B = "\<lambda>n::nat. box (- real n *\<^sub>R One) (real n *\<^sub>R One) :: 'a set"
    let ?f = "\<lambda>n::nat. \<lambda>x. if x \<in> A \<inter> ?B n then 1 else 0 :: real"
    let ?M = "\<lambda>n. measure lborel (A \<inter> ?B n)"

    show "\<And>n::nat. (?f n has_integral ?M n) A"
      using * by (subst has_integral_restrict) simp_all
    show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
      by (auto simp: box_def)
    { fix x assume "x \<in> A"
      moreover have "(\<lambda>k. indicator (A \<inter> ?B k) x :: real) \<longlonglongrightarrow> indicator (\<Union>k::nat. A \<inter> ?B k) x"
        by (intro LIMSEQ_indicator_incseq) (auto simp: incseq_def box_def)
      ultimately show "(\<lambda>k. if x \<in> A \<inter> ?B k then 1 else 0::real) \<longlonglongrightarrow> 1"
        by (simp add: indicator_def UN_box_eq_UNIV) }

    have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> emeasure lborel (\<Union>n::nat. A \<inter> ?B n)"
      by (intro Lim_emeasure_incseq) (auto simp: incseq_def box_def)
    also have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) = (\<lambda>n. measure lborel (A \<inter> ?B n))"
    proof (intro ext emeasure_eq_ennreal_measure)
      fix n have "emeasure lborel (A \<inter> ?B n) \<le> emeasure lborel (?B n)"
        by (intro emeasure_mono) auto
      then show "emeasure lborel (A \<inter> ?B n) \<noteq> top"
        by (auto simp: top_unique)
    qed
    finally show "(\<lambda>n. measure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> measure lborel A"
      using emeasure_eq_ennreal_measure[of lborel A] finite
      by (simp add: UN_box_eq_UNIV less_top)
  qed
qed

lemma nn_integral_has_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
  shows "(f has_integral r) UNIV"
using f proof (induct f arbitrary: r rule: borel_measurable_induct_real)
  case (set A)
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (intro has_integral_measure_lborel) (auto simp: ennreal_indicator)
  with set show ?case
    by (simp add: ennreal_indicator measure_def) (simp add: indicator_def)
next
  case (mult g c)
  then have "ennreal c * (\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal r"
    by (subst nn_integral_cmult[symmetric]) (auto simp: ennreal_mult)
  with \<open>0 \<le> r\<close> \<open>0 \<le> c\<close>
  obtain r' where "(c = 0 \<and> r = 0) \<or> (0 \<le> r' \<and> (\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel) = ennreal r' \<and> r = c * r')"
    by (cases "\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel" rule: ennreal_cases)
       (auto split: if_split_asm simp: ennreal_mult_top ennreal_mult[symmetric])
  with mult show ?case
    by (auto intro!: has_integral_cmult_real)
next
  case (add g h)
  then have "(\<integral>\<^sup>+ x. h x + g x \<partial>lborel) = (\<integral>\<^sup>+ x. h x \<partial>lborel) + (\<integral>\<^sup>+ x. g x \<partial>lborel)"
    by (simp add: nn_integral_add)
  with add obtain a b where "0 \<le> a" "0 \<le> b" "(\<integral>\<^sup>+ x. h x \<partial>lborel) = ennreal a" "(\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal b" "r = a + b"
    by (cases "\<integral>\<^sup>+ x. h x \<partial>lborel" "\<integral>\<^sup>+ x. g x \<partial>lborel" rule: ennreal2_cases)
       (auto simp: add_top nn_integral_add top_add ennreal_plus[symmetric] simp del: ennreal_plus)
  with add show ?case
    by (auto intro!: has_integral_add)
next
  case (seq U)
  note seq(1)[measurable] and f[measurable]

  { fix i x
    have "U i x \<le> f x"
      using seq(5)
      apply (rule LIMSEQ_le_const)
      using seq(4)
      apply (auto intro!: exI[of _ i] simp: incseq_def le_fun_def)
      done }
  note U_le_f = this

  { fix i
    have "(\<integral>\<^sup>+x. U i x \<partial>lborel) \<le> (\<integral>\<^sup>+x. f x \<partial>lborel)"
      using seq(2) f(2) U_le_f by (intro nn_integral_mono) simp
    then obtain p where "(\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p" "p \<le> r" "0 \<le> p"
      using seq(6) \<open>0\<le>r\<close> by (cases "\<integral>\<^sup>+x. U i x \<partial>lborel" rule: ennreal_cases) (auto simp: top_unique)
    moreover note seq
    ultimately have "\<exists>p. (\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p \<and> 0 \<le> p \<and> p \<le> r \<and> (U i has_integral p) UNIV"
      by auto }
  then obtain p where p: "\<And>i. (\<integral>\<^sup>+x. ennreal (U i x) \<partial>lborel) = ennreal (p i)"
    and bnd: "\<And>i. p i \<le> r" "\<And>i. 0 \<le> p i"
    and U_int: "\<And>i.(U i has_integral (p i)) UNIV" by metis

  have int_eq: "\<And>i. integral UNIV (U i) = p i" using U_int by (rule integral_unique)

  have *: "f integrable_on UNIV \<and> (\<lambda>k. integral UNIV (U k)) \<longlonglongrightarrow> integral UNIV f"
  proof (rule monotone_convergence_increasing)
    show "\<forall>k. U k integrable_on UNIV" using U_int by auto
    show "\<forall>k. \<forall>x\<in>UNIV. U k x \<le> U (Suc k) x" using \<open>incseq U\<close> by (auto simp: incseq_def le_fun_def)
    then show "bounded {integral UNIV (U k) |k. True}"
      using bnd int_eq by (auto simp: bounded_real intro!: exI[of _ r])
    show "\<forall>x\<in>UNIV. (\<lambda>k. U k x) \<longlonglongrightarrow> f x"
      using seq by auto
  qed
  moreover have "(\<lambda>i. (\<integral>\<^sup>+x. U i x \<partial>lborel)) \<longlonglongrightarrow> (\<integral>\<^sup>+x. f x \<partial>lborel)"
    using seq f(2) U_le_f by (intro nn_integral_dominated_convergence[where w=f]) auto
  ultimately have "integral UNIV f = r"
    by (auto simp add: bnd int_eq p seq intro: LIMSEQ_unique)
  with * show ?case
    by (simp add: has_integral_integral)
qed

lemma nn_integral_lborel_eq_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "(\<integral>\<^sup>+x. f x \<partial>lborel) = integral UNIV f"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    using nn_integral_has_integral[OF f(1,2) r] by (simp add: integral_unique)
qed

lemma nn_integral_integrable_on:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "f integrable_on UNIV"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    by (intro has_integral_integrable[where i=r] nn_integral_has_integral[where r=r] f)
qed

lemma nn_integral_has_integral_lborel:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel" and nonneg: "\<And>x. 0 \<le> f x"
  assumes I: "(f has_integral I) UNIV"
  shows "integral\<^sup>N lborel f = I"
proof -
  from f_borel have "(\<lambda>x. ennreal (f x)) \<in> borel_measurable lborel" by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess F . note F = this
  let ?B = "\<lambda>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One) :: 'a set"

  note F(1)[THEN borel_measurable_simple_function, measurable]

  have "0 \<le> I"
    using I by (rule has_integral_nonneg) (simp add: nonneg)

  have F_le_f: "enn2real (F i x) \<le> f x" for i x
    using F(3,4)[where x=x] nonneg SUP_upper[of i UNIV "\<lambda>i. F i x"]
    by (cases "F i x" rule: ennreal_cases) auto
  let ?F = "\<lambda>i x. F i x * indicator (?B i) x"
  have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (SUP i. integral\<^sup>N lborel (\<lambda>x. ?F i x))"
  proof (subst nn_integral_monotone_convergence_SUP[symmetric])
    { fix x
      obtain j where j: "x \<in> ?B j"
        using UN_box_eq_UNIV by auto

      have "ennreal (f x) = (SUP i. F i x)"
        using F(4)[of x] nonneg[of x] by (simp add: max_def)
      also have "\<dots> = (SUP i. ?F i x)"
      proof (rule SUP_eq)
        fix i show "\<exists>j\<in>UNIV. F i x \<le> ?F j x"
          using j F(2)
          by (intro bexI[of _ "max i j"])
             (auto split: split_max split_indicator simp: incseq_def le_fun_def box_def)
      qed (auto intro!: F split: split_indicator)
      finally have "ennreal (f x) =  (SUP i. ?F i x)" . }
    then show "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+ x. (SUP i. ?F i x) \<partial>lborel)"
      by simp
  qed (insert F, auto simp: incseq_def le_fun_def box_def split: split_indicator)
  also have "\<dots> \<le> ennreal I"
  proof (rule SUP_least)
    fix i :: nat
    have finite_F: "(\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel) < \<infinity>"
    proof (rule nn_integral_bound_simple_function)
      have "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} \<le>
        emeasure lborel (?B i)"
        by (intro emeasure_mono)  (auto split: split_indicator)
      then show "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} < \<infinity>"
        by (auto simp: less_top[symmetric] top_unique)
    qed (auto split: split_indicator
              intro!: F simple_function_compose1[where g="enn2real"] simple_function_ennreal)

    have int_F: "(\<lambda>x. enn2real (F i x) * indicator (?B i) x) integrable_on UNIV"
      using F(4) finite_F
      by (intro nn_integral_integrable_on) (auto split: split_indicator simp: enn2real_nonneg)

    have "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) =
      (\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel)"
      using F(3,4)
      by (intro nn_integral_cong) (auto simp: image_iff eq_commute split: split_indicator)
    also have "\<dots> = ennreal (integral UNIV (\<lambda>x. enn2real (F i x) * indicator (?B i) x))"
      using F
      by (intro nn_integral_lborel_eq_integral[OF _ _ finite_F])
         (auto split: split_indicator intro: enn2real_nonneg)
    also have "\<dots> \<le> ennreal I"
      by (auto intro!: has_integral_le[OF integrable_integral[OF int_F] I] nonneg F_le_f
               simp: \<open>0 \<le> I\<close> split: split_indicator )
    finally show "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) \<le> ennreal I" .
  qed
  finally have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) < \<infinity>"
    by (auto simp: less_top[symmetric] top_unique)
  from nn_integral_lborel_eq_integral[OF assms(1,2) this] I show ?thesis
    by (simp add: integral_unique)
qed

lemma has_integral_iff_emeasure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and [simp]: "0 \<le> r"
  shows "((\<lambda>x. 1) has_integral r) A \<longleftrightarrow> emeasure lborel A = ennreal r"
proof (cases "emeasure lborel A = \<infinity>")
  case emeasure_A: True
  have "\<not> (\<lambda>x. 1::real) integrable_on A"
  proof
    assume int: "(\<lambda>x. 1::real) integrable_on A"
    then have "(indicator A::'a \<Rightarrow> real) integrable_on UNIV"
      unfolding indicator_def[abs_def] integrable_restrict_UNIV .
    then obtain r where "((indicator A::'a\<Rightarrow>real) has_integral r) UNIV"
      by auto
    from nn_integral_has_integral_lborel[OF _ _ this] emeasure_A show False
      by (simp add: ennreal_indicator)
  qed
  with emeasure_A show ?thesis
    by auto
next
  case False
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (simp add: has_integral_measure_lborel less_top)
  with False show ?thesis
    by (auto simp: emeasure_eq_ennreal_measure has_integral_unique)
qed

lemma ennreal_max_0: "ennreal (max 0 x) = ennreal x"
  by (auto simp: max_def ennreal_neg)

lemma has_integral_integral_real:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  from integrableE[OF f] obtain r q
    where "0 \<le> r" "0 \<le> q"
      and r: "(\<integral>\<^sup>+ x. ennreal (max 0 (f x)) \<partial>lborel) = ennreal r"
      and q: "(\<integral>\<^sup>+ x. ennreal (max 0 (- f x)) \<partial>lborel) = ennreal q"
      and f: "f \<in> borel_measurable lborel" and eq: "integral\<^sup>L lborel f = r - q"
    unfolding ennreal_max_0 by auto
  then have "((\<lambda>x. max 0 (f x)) has_integral r) UNIV" "((\<lambda>x. max 0 (- f x)) has_integral q) UNIV"
    using nn_integral_has_integral[OF _ _ r] nn_integral_has_integral[OF _ _ q] by auto
  note has_integral_diff[OF this]
  moreover have "(\<lambda>x. max 0 (f x) - max 0 (- f x)) = f"
    by auto
  ultimately show ?thesis
    by (simp add: eq)
qed

lemma has_integral_AE:
  assumes ae: "AE x in lborel. x \<in> \<Omega> \<longrightarrow> f x = g x"
  shows "(f has_integral x) \<Omega> = (g has_integral x) \<Omega>"
proof -
  from ae obtain N
    where N: "N \<in> sets borel" "emeasure lborel N = 0" "{x. \<not> (x \<in> \<Omega> \<longrightarrow> f x = g x)} \<subseteq> N"
    by (auto elim!: AE_E)
  then have not_N: "AE x in lborel. x \<notin> N"
    by (simp add: AE_iff_measurable)
  show ?thesis
  proof (rule has_integral_spike_eq[symmetric])
    show "\<And>x. x\<in>\<Omega> - N \<Longrightarrow> f x = g x" using N(3) by auto
    show "negligible N"
      unfolding negligible_def
    proof (intro allI)
      fix a b :: "'a"
      let ?F = "\<lambda>x::'a. if x \<in> cbox a b then indicator N x else 0 :: real"
      have "integrable lborel ?F = integrable lborel (\<lambda>x::'a. 0::real)"
        using not_N N(1) by (intro integrable_cong_AE) auto
      moreover have "(LINT x|lborel. ?F x) = (LINT x::'a|lborel. 0::real)"
        using not_N N(1) by (intro integral_cong_AE) auto
      ultimately have "(?F has_integral 0) UNIV"
        using has_integral_integral_real[of ?F] by simp
      then show "(indicator N has_integral (0::real)) (cbox a b)"
        unfolding has_integral_restrict_UNIV .
    qed
  qed
qed

lemma nn_integral_has_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg: "\<And>x. 0 \<le> f x" and I: "(f has_integral I) \<Omega>"
  shows "integral\<^sup>N lborel (\<lambda>x. indicator \<Omega> x * f x) = I"
proof -
  from I have "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
    by (rule has_integral_implies_lebesgue_measurable)
  then obtain f' :: "'a \<Rightarrow> real"
    where [measurable]: "f' \<in> borel \<rightarrow>\<^sub>M borel" and eq: "AE x in lborel. indicator \<Omega> x * f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)

  from I have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV"
    using nonneg by (simp add: indicator_def if_distrib[of "\<lambda>x. x * f y" for y] cong: if_cong)
  also have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV \<longleftrightarrow> ((\<lambda>x. abs (f' x)) has_integral I) UNIV"
    using eq by (intro has_integral_AE) auto
  finally have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = I"
    by (rule nn_integral_has_integral_lborel[rotated 2]) auto
  also have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = integral\<^sup>N lborel (\<lambda>x. abs (indicator \<Omega> x * f x))"
    using eq by (intro nn_integral_cong_AE) auto
  finally show ?thesis
    using nonneg by auto
qed

lemma has_integral_iff_nn_integral_lebesgue:
  assumes f: "\<And>x. 0 \<le> f x"
  shows "(f has_integral r) UNIV \<longleftrightarrow> (f \<in> lebesgue \<rightarrow>\<^sub>M borel \<and> integral\<^sup>N lebesgue f = r \<and> 0 \<le> r)" (is "?I = ?N")
proof
  assume ?I
  have "0 \<le> r"
    using has_integral_nonneg[OF \<open>?I\<close>] f by auto
  then show ?N
    using nn_integral_has_integral_lebesgue[OF f \<open>?I\<close>]
      has_integral_implies_lebesgue_measurable[OF \<open>?I\<close>]
    by (auto simp: nn_integral_completion)
next
  assume ?N
  then obtain f' where f': "f' \<in> borel \<rightarrow>\<^sub>M borel" "AE x in lborel. f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)
  moreover have "(\<integral>\<^sup>+ x. ennreal \<bar>f' x\<bar> \<partial>lborel) = (\<integral>\<^sup>+ x. ennreal \<bar>f x\<bar> \<partial>lborel)"
    using f' by (intro nn_integral_cong_AE) auto
  moreover have "((\<lambda>x. \<bar>f' x\<bar>) has_integral r) UNIV \<longleftrightarrow> ((\<lambda>x. \<bar>f x\<bar>) has_integral r) UNIV"
    using f' by (intro has_integral_AE) auto
  moreover note nn_integral_has_integral[of "\<lambda>x. \<bar>f' x\<bar>" r] \<open>?N\<close>
  ultimately show ?I
    using f by (auto simp: nn_integral_completion)
qed

context
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
begin

lemma has_integral_integral_lborel:
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  have "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    using f by (intro has_integral_sum finite_Basis ballI has_integral_scaleR_left has_integral_integral_real) auto
  also have eq_f: "(\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) = f"
    by (simp add: fun_eq_iff euclidean_representation)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lborel f"
    using f by (subst (2) eq_f[symmetric]) simp
  finally show ?thesis .
qed

lemma integrable_on_lborel: "integrable lborel f \<Longrightarrow> f integrable_on UNIV"
  using has_integral_integral_lborel by auto

lemma integral_lborel: "integrable lborel f \<Longrightarrow> integral UNIV f = (\<integral>x. f x \<partial>lborel)"
  using has_integral_integral_lborel by auto

end

context
begin

private lemma has_integral_integral_lebesgue_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lebesgue f"
  shows "(f has_integral (integral\<^sup>L lebesgue f)) UNIV"
proof -
  obtain f' where f': "f' \<in> borel \<rightarrow>\<^sub>M borel" "AE x in lborel. f x = f' x"
    using completion_ex_borel_measurable_real[OF borel_measurable_integrable[OF f]] by auto
  moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>lborel) = (\<integral>\<^sup>+ x. ennreal (norm (f' x)) \<partial>lborel)"
    using f' by (intro nn_integral_cong_AE) auto
  ultimately have "integrable lborel f'"
    using f by (auto simp: integrable_iff_bounded nn_integral_completion cong: nn_integral_cong_AE)
  note has_integral_integral_real[OF this]
  moreover have "integral\<^sup>L lebesgue f = integral\<^sup>L lebesgue f'"
    using f' f by (intro integral_cong_AE) (auto intro: AE_completion measurable_completion)
  moreover have "integral\<^sup>L lebesgue f' = integral\<^sup>L lborel f'"
    using f' by (simp add: integral_completion)
  moreover have "(f' has_integral integral\<^sup>L lborel f') UNIV \<longleftrightarrow> (f has_integral integral\<^sup>L lborel f') UNIV"
    using f' by (intro has_integral_AE) auto
  ultimately show ?thesis
    by auto
qed

lemma has_integral_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "integrable lebesgue f"
  shows "(f has_integral (integral\<^sup>L lebesgue f)) UNIV"
proof -
  have "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lebesgue (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    using f by (intro has_integral_sum finite_Basis ballI has_integral_scaleR_left has_integral_integral_lebesgue_real) auto
  also have eq_f: "(\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) = f"
    by (simp add: fun_eq_iff euclidean_representation)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lebesgue (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lebesgue f"
    using f by (subst (2) eq_f[symmetric]) simp
  finally show ?thesis .
qed

lemma integrable_on_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "integrable lebesgue f \<Longrightarrow> f integrable_on UNIV"
  using has_integral_integral_lebesgue by auto

lemma integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "integrable lebesgue f \<Longrightarrow> integral UNIV f = (\<integral>x. f x \<partial>lebesgue)"
  using has_integral_integral_lebesgue by auto

end

subsection \<open>Absolute integrability (this is the same as Lebesgue integrability)\<close>

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

lemma set_integral_reflect:
  fixes S and f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "(LBINT x : S. f x) = (LBINT x : {x. - x \<in> S}. f (- x))"
  by (subst lborel_integral_real_affine[where c="-1" and t=0])
     (auto intro!: Bochner_Integration.integral_cong split: split_indicator)

lemma borel_integrable_atLeastAtMost':
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes f: "continuous_on {a..b} f"
  shows "set_integrable lborel {a..b} f" (is "integrable _ ?f")
  by (intro borel_integrable_compact compact_Icc f)

lemma integral_FTC_atLeastAtMost:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
    and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    and f: "continuous_on {a .. b} f"
  shows "integral\<^sup>L lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) = F b - F a"
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have "(?f has_integral (\<integral>x. ?f x \<partial>lborel)) UNIV"
    using borel_integrable_atLeastAtMost'[OF f] by (rule has_integral_integral_lborel)
  moreover
  have "(f has_integral F b - F a) {a .. b}"
    by (intro fundamental_theorem_of_calculus ballI assms) auto
  then have "(?f has_integral F b - F a) {a .. b}"
    by (subst has_integral_cong[where g=f]) auto
  then have "(?f has_integral F b - F a) UNIV"
    by (intro has_integral_on_superset[where T=UNIV and S="{a..b}"]) auto
  ultimately show "integral\<^sup>L lborel ?f = F b - F a"
    by (rule has_integral_unique)
qed

lemma set_borel_integral_eq_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "set_integrable lborel S f"
  shows "f integrable_on S" "LINT x : S | lborel. f x = integral S f"
proof -
  let ?f = "\<lambda>x. indicator S x *\<^sub>R f x"
  have "(?f has_integral LINT x : S | lborel. f x) UNIV"
    by (rule has_integral_integral_lborel) fact
  hence 1: "(f has_integral (set_lebesgue_integral lborel S f)) S"
    apply (subst has_integral_restrict_UNIV [symmetric])
    apply (rule has_integral_eq)
    by auto
  thus "f integrable_on S"
    by (auto simp add: integrable_on_def)
  with 1 have "(f has_integral (integral S f)) S"
    by (intro integrable_integral, auto simp add: integrable_on_def)
  thus "LINT x : S | lborel. f x = integral S f"
    by (intro has_integral_unique [OF 1])
qed

lemma has_integral_set_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "set_integrable lebesgue S f"
  shows "(f has_integral (LINT x:S|lebesgue. f x)) S"
  using has_integral_integral_lebesgue[OF f]
  by (simp_all add: indicator_def if_distrib[of "\<lambda>x. x *\<^sub>R f _"] has_integral_restrict_UNIV cong: if_cong)

lemma set_lebesgue_integral_eq_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "set_integrable lebesgue S f"
  shows "f integrable_on S" "LINT x:S | lebesgue. f x = integral S f"
  using has_integral_set_lebesgue[OF f] by (auto simp: integral_unique integrable_on_def)

lemma lmeasurable_iff_has_integral:
  "S \<in> lmeasurable \<longleftrightarrow> ((indicator S) has_integral measure lebesgue S) UNIV"
  by (subst has_integral_iff_nn_integral_lebesgue)
     (auto simp: ennreal_indicator emeasure_eq_measure2 borel_measurable_indicator_iff intro!: fmeasurableI)

abbreviation
  absolutely_integrable_on :: "('a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr "absolutely'_integrable'_on" 46)
  where "f absolutely_integrable_on s \<equiv> set_integrable lebesgue s f"


lemma absolutely_integrable_on_def:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and> (\<lambda>x. norm (f x)) integrable_on s"
proof safe
  assume f: "f absolutely_integrable_on s"
  then have nf: "integrable lebesgue (\<lambda>x. norm (indicator s x *\<^sub>R f x))"
    by (intro integrable_norm)
  note integrable_on_lebesgue[OF f] integrable_on_lebesgue[OF nf]
  moreover have
    "(\<lambda>x. indicator s x *\<^sub>R f x) = (\<lambda>x. if x \<in> s then f x else 0)"
    "(\<lambda>x. norm (indicator s x *\<^sub>R f x)) = (\<lambda>x. if x \<in> s then norm (f x) else 0)"
    by auto
  ultimately show "f integrable_on s" "(\<lambda>x. norm (f x)) integrable_on s"
    by (simp_all add: integrable_restrict_UNIV)
next
  assume f: "f integrable_on s" and nf: "(\<lambda>x. norm (f x)) integrable_on s"
  show "f absolutely_integrable_on s"
  proof (rule integrableI_bounded)
    show "(\<lambda>x. indicator s x *\<^sub>R f x) \<in> borel_measurable lebesgue"
      using f has_integral_implies_lebesgue_measurable[of f _ s] by (auto simp: integrable_on_def)
    show "(\<integral>\<^sup>+ x. ennreal (norm (indicator s x *\<^sub>R f x)) \<partial>lebesgue) < \<infinity>"
      using nf nn_integral_has_integral_lebesgue[of "\<lambda>x. norm (f x)" _ s]
      by (auto simp: integrable_on_def nn_integral_completion)
  qed
qed
  
lemma absolutely_integrable_on_null [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "content (cbox a b) = 0 \<Longrightarrow> f absolutely_integrable_on (cbox a b)"
  by (auto simp: absolutely_integrable_on_def)

lemma absolutely_integrable_on_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f absolutely_integrable_on box a b \<longleftrightarrow>
         f absolutely_integrable_on cbox a b"
  by (auto simp: integrable_on_open_interval absolutely_integrable_on_def)

lemma absolutely_integrable_restrict_UNIV:
  "(\<lambda>x. if x \<in> s then f x else 0) absolutely_integrable_on UNIV \<longleftrightarrow> f absolutely_integrable_on s"
  by (intro arg_cong2[where f=integrable]) auto

lemma absolutely_integrable_onI:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f integrable_on s \<Longrightarrow> (\<lambda>x. norm (f x)) integrable_on s \<Longrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def by auto

lemma nonnegative_absolutely_integrable_1:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on A" and "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x"
  shows "f absolutely_integrable_on A"
  apply (rule absolutely_integrable_onI [OF f])
  using assms by (simp add: integrable_eq)

lemma absolutely_integrable_on_iff_nonneg:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x" shows "f absolutely_integrable_on S \<longleftrightarrow> f integrable_on S"
proof -
  { assume "f integrable_on S"
    then have "(\<lambda>x. if x \<in> S then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have "(\<lambda>x. if x \<in> S then f x else 0) absolutely_integrable_on UNIV"
      using \<open>f integrable_on S\<close> absolutely_integrable_restrict_UNIV assms nonnegative_absolutely_integrable_1 by blast
    then have "f absolutely_integrable_on S"
      using absolutely_integrable_restrict_UNIV by blast
  }
  then show ?thesis        
    unfolding absolutely_integrable_on_def by auto
qed

lemma lmeasurable_iff_integrable_on: "S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. 1::real) integrable_on S"
  by (subst absolutely_integrable_on_iff_nonneg[symmetric])
     (simp_all add: lmeasurable_iff_integrable)

lemma lmeasure_integral_UNIV: "S \<in> lmeasurable \<Longrightarrow> measure lebesgue S = integral UNIV (indicator S)"
  by (simp add: lmeasurable_iff_has_integral integral_unique)

lemma lmeasure_integral: "S \<in> lmeasurable \<Longrightarrow> measure lebesgue S = integral S (\<lambda>x. 1::real)"
  by (auto simp add: lmeasure_integral_UNIV indicator_def[abs_def] lmeasurable_iff_integrable_on)

lemma
  assumes \<D>: "\<D> division_of S"
  shows lmeasurable_division: "S \<in> lmeasurable" (is ?l)
    and content_division: "(\<Sum>k\<in>\<D>. measure lebesgue k) = measure lebesgue S" (is ?m)
proof -
  { fix d1 d2 assume *: "d1 \<in> \<D>" "d2 \<in> \<D>" "d1 \<noteq> d2"
    then obtain a b c d where "d1 = cbox a b" "d2 = cbox c d"
      using division_ofD(4)[OF \<D>] by blast
    with division_ofD(5)[OF \<D> *]
    have "d1 \<in> sets lborel" "d2 \<in> sets lborel" "d1 \<inter> d2 \<subseteq> (cbox a b - box a b) \<union> (cbox c d - box c d)"
      by auto
    moreover have "(cbox a b - box a b) \<union> (cbox c d - box c d) \<in> null_sets lborel"
      by (intro null_sets.Un null_sets_cbox_Diff_box)
    ultimately have "d1 \<inter> d2 \<in> null_sets lborel"
      by (blast intro: null_sets_subset) }
  then show ?l ?m
    unfolding division_ofD(6)[OF \<D>, symmetric]
    using division_ofD(1,4)[OF \<D>]
    by (auto intro!: measure_Union_AE[symmetric] simp: completion.AE_iff_null_sets Int_def[symmetric] pairwise_def null_sets_def)
qed

text \<open>This should be an abbreviation for negligible.\<close>
lemma negligible_iff_null_sets: "negligible S \<longleftrightarrow> S \<in> null_sets lebesgue"
proof
  assume "negligible S"
  then have "(indicator S has_integral (0::real)) UNIV"
    by (auto simp: negligible)
  then show "S \<in> null_sets lebesgue"
    by (subst (asm) has_integral_iff_nn_integral_lebesgue)
        (auto simp: borel_measurable_indicator_iff nn_integral_0_iff_AE AE_iff_null_sets indicator_eq_0_iff)
next
  assume S: "S \<in> null_sets lebesgue"
  show "negligible S"
    unfolding negligible_def
  proof (safe intro!: has_integral_iff_nn_integral_lebesgue[THEN iffD2]
                      has_integral_restrict_UNIV[where s="cbox _ _", THEN iffD1])
    fix a b
    show "(\<lambda>x. if x \<in> cbox a b then indicator S x else 0) \<in> lebesgue \<rightarrow>\<^sub>M borel"
      using S by (auto intro!: measurable_If)
    then show "(\<integral>\<^sup>+ x. ennreal (if x \<in> cbox a b then indicator S x else 0) \<partial>lebesgue) = ennreal 0"
      using S[THEN AE_not_in] by (auto intro!: nn_integral_0_iff_AE[THEN iffD2])
  qed auto
qed

lemma starlike_negligible:
  assumes "closed S"
      and eq1: "\<And>c x. \<lbrakk>(a + c *\<^sub>R x) \<in> S; 0 \<le> c; a + x \<in> S\<rbrakk> \<Longrightarrow> c = 1"
    shows "negligible S"
proof -
  have "negligible (op + (-a) ` S)"
  proof (subst negligible_on_intervals, intro allI)
    fix u v
    show "negligible (op + (- a) ` S \<inter> cbox u v)"
      unfolding negligible_iff_null_sets
      apply (rule starlike_negligible_compact)
       apply (simp add: assms closed_translation closed_Int_compact, clarify)
      by (metis eq1 minus_add_cancel)
  qed
  then show ?thesis
    by (rule negligible_translation_rev)
qed

lemma starlike_negligible_strong:
  assumes "closed S"
      and star: "\<And>c x. \<lbrakk>0 \<le> c; c < 1; a+x \<in> S\<rbrakk> \<Longrightarrow> a + c *\<^sub>R x \<notin> S"
    shows "negligible S"
proof -
  show ?thesis
  proof (rule starlike_negligible [OF \<open>closed S\<close>, of a])
    fix c x
    assume cx: "a + c *\<^sub>R x \<in> S" "0 \<le> c" "a + x \<in> S"
    with star have "~ (c < 1)" by auto
    moreover have "~ (c > 1)"
      using star [of "1/c" "c *\<^sub>R x"] cx by force
    ultimately show "c = 1" by arith
  qed
qed

subsection\<open>Applications\<close>

lemma negligible_hyperplane:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0" shows "negligible {x. a \<bullet> x = b}"
proof -
  obtain x where x: "a \<bullet> x \<noteq> b"
    using assms
    apply auto
     apply (metis inner_eq_zero_iff inner_zero_right)
    using inner_zero_right by fastforce
  show ?thesis
    apply (rule starlike_negligible [OF closed_hyperplane, of x])
    using x apply (auto simp: algebra_simps)
    done
qed

lemma negligible_lowdim:
  fixes S :: "'N :: euclidean_space set"
  assumes "dim S < DIM('N)"
    shows "negligible S"
proof -
  obtain a where "a \<noteq> 0" and a: "span S \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane [OF assms] by blast
  have "negligible (span S)"
    using \<open>a \<noteq> 0\<close> a negligible_hyperplane by (blast intro: negligible_subset)
  then show ?thesis
    using span_inc by (blast intro: negligible_subset)
qed

proposition negligible_convex_frontier:
  fixes S :: "'N :: euclidean_space set"
  assumes "convex S"
    shows "negligible(frontier S)"
proof -
  have nf: "negligible(frontier S)" if "convex S" "0 \<in> S" for S :: "'N set"
  proof -
    obtain B where "B \<subseteq> S" and indB: "independent B"
               and spanB: "S \<subseteq> span B" and cardB: "card B = dim S"
      by (metis basis_exists)
    consider "dim S < DIM('N)" | "dim S = DIM('N)"
      using dim_subset_UNIV le_eq_less_or_eq by blast
    then show ?thesis
    proof cases
      case 1
      show ?thesis
        by (rule negligible_subset [of "closure S"])
           (simp_all add: Diff_subset frontier_def negligible_lowdim 1)
    next
      case 2
      obtain a where a: "a \<in> interior S"
        apply (rule interior_simplex_nonempty [OF indB])
          apply (simp add: indB independent_finite)
         apply (simp add: cardB 2)
        apply (metis \<open>B \<subseteq> S\<close> \<open>0 \<in> S\<close> \<open>convex S\<close> insert_absorb insert_subset interior_mono subset_hull)
        done
      show ?thesis
      proof (rule starlike_negligible_strong [where a=a])
        fix c::real and x
        have eq: "a + c *\<^sub>R x = (a + x) - (1 - c) *\<^sub>R ((a + x) - a)"
          by (simp add: algebra_simps)
        assume "0 \<le> c" "c < 1" "a + x \<in> frontier S"
        then show "a + c *\<^sub>R x \<notin> frontier S"
          apply (clarsimp simp: frontier_def)
          apply (subst eq)
          apply (rule mem_interior_closure_convex_shrink [OF \<open>convex S\<close> a, of _ "1-c"], auto)
          done
      qed auto
    qed
  qed
  show ?thesis
  proof (cases "S = {}")
    case True then show ?thesis by auto
  next
    case False
    then obtain a where "a \<in> S" by auto
    show ?thesis
      using nf [of "(\<lambda>x. -a + x) ` S"]
      by (metis \<open>a \<in> S\<close> add.left_inverse assms convex_translation_eq frontier_translation
                image_eqI negligible_translation_rev)
  qed
qed

corollary negligible_sphere: "negligible (sphere a e)"
  using frontier_cball negligible_convex_frontier convex_cball
  by (blast intro: negligible_subset)


lemma non_negligible_UNIV [simp]: "\<not> negligible UNIV"
  unfolding negligible_iff_null_sets by (auto simp: null_sets_def emeasure_lborel_UNIV)

lemma negligible_interval:
  "negligible (cbox a b) \<longleftrightarrow> box a b = {}" "negligible (box a b) \<longleftrightarrow> box a b = {}"
   by (auto simp: negligible_iff_null_sets null_sets_def prod_nonneg inner_diff_left box_eq_empty
                  not_le emeasure_lborel_cbox_eq emeasure_lborel_box_eq
            intro: eq_refl antisym less_imp_le)

subsection \<open>Negligibility of a Lipschitz image of a negligible set\<close>

lemma measure_eq_0_null_sets: "S \<in> null_sets M \<Longrightarrow> measure M S = 0"
  by (auto simp: measure_def null_sets_def)

text\<open>The bound will be eliminated by a sort of onion argument\<close>
lemma locally_Lipschitz_negl_bounded:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "0 < B" "bounded S" "negligible S"
      and lips: "\<And>x. x \<in> S
                      \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and>
                              (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
  shows "negligible (f ` S)"
  unfolding negligible_iff_null_sets
proof (clarsimp simp: completion.null_sets_outer)
  fix e::real
  assume "0 < e"
  have "S \<in> lmeasurable"
    using \<open>negligible S\<close> by (simp add: negligible_iff_null_sets fmeasurableI_null_sets)
  have e22: "0 < e / 2 / (2 * B * real DIM('M)) ^ DIM('N)"
    using \<open>0 < e\<close> \<open>0 < B\<close> by (simp add: divide_simps)
  obtain T
    where "open T" "S \<subseteq> T" "T \<in> lmeasurable"
      and "measure lebesgue T \<le> measure lebesgue S + e / 2 / (2 * B * DIM('M)) ^ DIM('N)"
    by (rule lmeasurable_outer_open [OF \<open>S \<in> lmeasurable\<close> e22])
  then have T: "measure lebesgue T \<le> e / 2 / (2 * B * DIM('M)) ^ DIM('N)"
    using \<open>negligible S\<close> by (simp add: negligible_iff_null_sets measure_eq_0_null_sets)
  have "\<exists>r. 0 < r \<and> r \<le> 1/2 \<and>
            (x \<in> S \<longrightarrow> (\<forall>y. norm(y - x) < r
                       \<longrightarrow> y \<in> T \<and> (y \<in> S \<longrightarrow> norm(f y - f x) \<le> B * norm(y - x))))"
        for x
  proof (cases "x \<in> S")
    case True
    obtain U where "open U" "x \<in> U" and U: "\<And>y. y \<in> S \<inter> U \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
      using lips [OF \<open>x \<in> S\<close>] by auto
    have "x \<in> T \<inter> U"
      using \<open>S \<subseteq> T\<close> \<open>x \<in> U\<close> \<open>x \<in> S\<close> by auto
    then obtain \<epsilon> where "0 < \<epsilon>" "ball x \<epsilon> \<subseteq> T \<inter> U"
      by (metis \<open>open T\<close> \<open>open U\<close> openE open_Int)
    then show ?thesis
      apply (rule_tac x="min (1/2) \<epsilon>" in exI)
      apply (simp del: divide_const_simps)
      apply (intro allI impI conjI)
       apply (metis dist_commute dist_norm mem_ball subsetCE)
      by (metis Int_iff subsetCE U dist_norm mem_ball norm_minus_commute)
  next
    case False
    then show ?thesis
      by (rule_tac x="1/4" in exI) auto
  qed
  then obtain R where R12: "\<And>x. 0 < R x \<and> R x \<le> 1/2"
                and RT: "\<And>x y. \<lbrakk>x \<in> S; norm(y - x) < R x\<rbrakk> \<Longrightarrow> y \<in> T"
                and RB: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; norm(y - x) < R x\<rbrakk> \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
    by metis+
  then have gaugeR: "gauge (\<lambda>x. ball x (R x))"
    by (simp add: gauge_def)
  obtain c where c: "S \<subseteq> cbox (-c *\<^sub>R One) (c *\<^sub>R One)" "box (-c *\<^sub>R One:: 'M) (c *\<^sub>R One) \<noteq> {}"
  proof -
    obtain B where B: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
      using \<open>bounded S\<close> bounded_iff by blast
    show ?thesis
      apply (rule_tac c = "abs B + 1" in that)
      using norm_bound_Basis_le Basis_le_norm
       apply (fastforce simp: box_eq_empty mem_box dest!: B intro: order_trans)+
      done
  qed
  obtain \<D> where "countable \<D>"
     and Dsub: "\<Union>\<D> \<subseteq> cbox (-c *\<^sub>R One) (c *\<^sub>R One)"
     and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
     and pw:   "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
     and Ksub: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> (\<lambda>x. ball x (R x)) x"
     and exN:  "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (2*c) / 2^n"
     and "S \<subseteq> \<Union>\<D>"
    using covering_lemma [OF c gaugeR]  by force
  have "\<exists>u v z. K = cbox u v \<and> box u v \<noteq> {} \<and> z \<in> S \<and> z \<in> cbox u v \<and>
                cbox u v \<subseteq> ball z (R z)" if "K \<in> \<D>" for K
  proof -
    obtain u v where "K = cbox u v"
      using \<open>K \<in> \<D>\<close> cbox by blast
    with that show ?thesis
      apply (rule_tac x=u in exI)
      apply (rule_tac x=v in exI)
      apply (metis Int_iff interior_cbox cbox Ksub)
      done
  qed
  then obtain uf vf zf
    where uvz: "\<And>K. K \<in> \<D> \<Longrightarrow>
                K = cbox (uf K) (vf K) \<and> box (uf K) (vf K) \<noteq> {} \<and> zf K \<in> S \<and>
                zf K \<in> cbox (uf K) (vf K) \<and> cbox (uf K) (vf K) \<subseteq> ball (zf K) (R (zf K))"
    by metis
  define prj1 where "prj1 \<equiv> \<lambda>x::'M. x \<bullet> (SOME i. i \<in> Basis)"
  define fbx where "fbx \<equiv> \<lambda>D. cbox (f(zf D) - (B * DIM('M) * (prj1(vf D - uf D))) *\<^sub>R One::'N)
                                    (f(zf D) + (B * DIM('M) * prj1(vf D - uf D)) *\<^sub>R One)"
  have vu_pos: "0 < prj1 (vf X - uf X)" if "X \<in> \<D>" for X
    using uvz [OF that] by (simp add: prj1_def box_ne_empty SOME_Basis inner_diff_left)
  have prj1_idem: "prj1 (vf X - uf X) = (vf X - uf X) \<bullet> i" if  "X \<in> \<D>" "i \<in> Basis" for X i
  proof -
    have "cbox (uf X) (vf X) \<in> \<D>"
      using uvz \<open>X \<in> \<D>\<close> by auto
    with exN obtain n where "\<And>i. i \<in> Basis \<Longrightarrow> vf X \<bullet> i - uf X \<bullet> i = (2*c) / 2^n"
      by blast
    then show ?thesis
      by (simp add: \<open>i \<in> Basis\<close> SOME_Basis inner_diff prj1_def)
  qed
  have countbl: "countable (fbx ` \<D>)"
    using \<open>countable \<D>\<close> by blast
  have "(\<Sum>k\<in>fbx`\<D>'. measure lebesgue k) \<le> e / 2" if "\<D>' \<subseteq> \<D>" "finite \<D>'" for \<D>'
  proof -
    have BM_ge0: "0 \<le> B * (DIM('M) * prj1 (vf X - uf X))" if "X \<in> \<D>'" for X
      using \<open>0 < B\<close> \<open>\<D>' \<subseteq> \<D>\<close> that vu_pos by fastforce
    have "{} \<notin> \<D>'"
      using cbox \<open>\<D>' \<subseteq> \<D>\<close> interior_empty by blast
    have "(\<Sum>k\<in>fbx`\<D>'. measure lebesgue k) \<le> sum (measure lebesgue o fbx) \<D>'"
      by (rule sum_image_le [OF \<open>finite \<D>'\<close>]) (force simp: fbx_def)
    also have "\<dots> \<le> (\<Sum>X\<in>\<D>'. (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X)"
    proof (rule sum_mono)
      fix X assume "X \<in> \<D>'"
      then have "X \<in> \<D>" using \<open>\<D>' \<subseteq> \<D>\<close> by blast
      then have ufvf: "cbox (uf X) (vf X) = X"
        using uvz by blast
      have "prj1 (vf X - uf X) ^ DIM('M) = (\<Prod>i::'M \<in> Basis. prj1 (vf X - uf X))"
        by (rule prod_constant [symmetric])
      also have "\<dots> = (\<Prod>i\<in>Basis. vf X \<bullet> i - uf X \<bullet> i)"
        using prj1_idem [OF \<open>X \<in> \<D>\<close>] by (auto simp: algebra_simps intro: prod.cong)
      finally have prj1_eq: "prj1 (vf X - uf X) ^ DIM('M) = (\<Prod>i\<in>Basis. vf X \<bullet> i - uf X \<bullet> i)" .
      have "uf X \<in> cbox (uf X) (vf X)" "vf X \<in> cbox (uf X) (vf X)"
        using uvz [OF \<open>X \<in> \<D>\<close>] by (force simp: mem_box)+
      moreover have "cbox (uf X) (vf X) \<subseteq> ball (zf X) (1/2)"
        by (meson R12 order_trans subset_ball uvz [OF \<open>X \<in> \<D>\<close>])
      ultimately have "uf X \<in> ball (zf X) (1/2)"  "vf X \<in> ball (zf X) (1/2)"
        by auto
      then have "dist (vf X) (uf X) \<le> 1"
        unfolding mem_ball
        by (metis dist_commute dist_triangle_half_l dual_order.order_iff_strict)
      then have 1: "prj1 (vf X - uf X) \<le> 1"
        unfolding prj1_def dist_norm using Basis_le_norm SOME_Basis order_trans by fastforce
      have 0: "0 \<le> prj1 (vf X - uf X)"
        using \<open>X \<in> \<D>\<close> prj1_def vu_pos by fastforce
      have "(measure lebesgue \<circ> fbx) X \<le> (2 * B * DIM('M)) ^ DIM('N) * content (cbox (uf X) (vf X))"
        apply (simp add: fbx_def content_cbox_cases algebra_simps BM_ge0 \<open>X \<in> \<D>'\<close> prod_constant)
        apply (simp add: power_mult_distrib \<open>0 < B\<close> prj1_eq [symmetric])
        using MleN 0 1 uvz \<open>X \<in> \<D>\<close>
        apply (fastforce simp add: box_ne_empty power_decreasing)
        done
      also have "\<dots> = (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X"
        by (subst (3) ufvf[symmetric]) simp
      finally show "(measure lebesgue \<circ> fbx) X \<le> (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X" .
    qed
    also have "\<dots> = (2 * B * DIM('M)) ^ DIM('N) * sum (measure lebesgue) \<D>'"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> e / 2"
    proof -
      have div: "\<D>' division_of \<Union>\<D>'"
        apply (auto simp: \<open>finite \<D>'\<close> \<open>{} \<notin> \<D>'\<close> division_of_def)
        using cbox that apply blast
        using pairwise_subset [OF pw \<open>\<D>' \<subseteq> \<D>\<close>] unfolding pairwise_def apply force+
        done
      have le_meaT: "measure lebesgue (\<Union>\<D>') \<le> measure lebesgue T"
      proof (rule measure_mono_fmeasurable [OF _ _ \<open>T : lmeasurable\<close>])
        show "(\<Union>\<D>') \<in> sets lebesgue"
          using div lmeasurable_division by auto
        have "\<Union>\<D>' \<subseteq> \<Union>\<D>"
          using \<open>\<D>' \<subseteq> \<D>\<close> by blast
        also have "... \<subseteq> T"
        proof (clarify)
          fix x D
          assume "x \<in> D" "D \<in> \<D>"
          show "x \<in> T"
            using Ksub [OF \<open>D \<in> \<D>\<close>]
            by (metis \<open>x \<in> D\<close> Int_iff dist_norm mem_ball norm_minus_commute subsetD RT)
        qed
        finally show "\<Union>\<D>' \<subseteq> T" .
      qed
      have "sum (measure lebesgue) \<D>' = sum content \<D>'"
        using  \<open>\<D>' \<subseteq> \<D>\<close> cbox by (force intro: sum.cong)
      then have "(2 * B * DIM('M)) ^ DIM('N) * sum (measure lebesgue) \<D>' =
                 (2 * B * real DIM('M)) ^ DIM('N) * measure lebesgue (\<Union>\<D>')"
        using content_division [OF div] by auto
      also have "\<dots> \<le> (2 * B * real DIM('M)) ^ DIM('N) * measure lebesgue T"
        apply (rule mult_left_mono [OF le_meaT])
        using \<open>0 < B\<close>
        apply (simp add: algebra_simps)
        done
      also have "\<dots> \<le> e / 2"
        using T \<open>0 < B\<close> by (simp add: field_simps)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  then have e2: "sum (measure lebesgue) \<G> \<le> e / 2" if "\<G> \<subseteq> fbx ` \<D>" "finite \<G>" for \<G>
    by (metis finite_subset_image that)
  show "\<exists>W\<in>lmeasurable. f ` S \<subseteq> W \<and> measure lebesgue W < e"
  proof (intro bexI conjI)
    have "\<exists>X\<in>\<D>. f y \<in> fbx X" if "y \<in> S" for y
    proof -
      obtain X where "y \<in> X" "X \<in> \<D>"
        using \<open>S \<subseteq> \<Union>\<D>\<close> \<open>y \<in> S\<close> by auto
      then have y: "y \<in> ball(zf X) (R(zf X))"
        using uvz by fastforce
      have conj_le_eq: "z - b \<le> y \<and> y \<le> z + b \<longleftrightarrow> abs(y - z) \<le> b" for z y b::real
        by auto
      have yin: "y \<in> cbox (uf X) (vf X)" and zin: "(zf X) \<in> cbox (uf X) (vf X)"
        using uvz \<open>X \<in> \<D>\<close> \<open>y \<in> X\<close> by auto
      have "norm (y - zf X) \<le> (\<Sum>i\<in>Basis. \<bar>(y - zf X) \<bullet> i\<bar>)"
        by (rule norm_le_l1)
      also have "\<dots> \<le> real DIM('M) * prj1 (vf X - uf X)"
      proof (rule sum_bounded_above)
        fix j::'M assume j: "j \<in> Basis"
        show "\<bar>(y - zf X) \<bullet> j\<bar> \<le> prj1 (vf X - uf X)"
          using yin zin j
          by (fastforce simp add: mem_box prj1_idem [OF \<open>X \<in> \<D>\<close> j] inner_diff_left)
      qed
      finally have nole: "norm (y - zf X) \<le> DIM('M) * prj1 (vf X - uf X)"
        by simp
      have fle: "\<bar>f y \<bullet> i - f(zf X) \<bullet> i\<bar> \<le> B * DIM('M) * prj1 (vf X - uf X)" if "i \<in> Basis" for i
      proof -
        have "\<bar>f y \<bullet> i - f (zf X) \<bullet> i\<bar> = \<bar>(f y - f (zf X)) \<bullet> i\<bar>"
          by (simp add: algebra_simps)
        also have "\<dots> \<le> norm (f y - f (zf X))"
          by (simp add: Basis_le_norm that)
        also have "\<dots> \<le> B * norm(y - zf X)"
          by (metis uvz RB \<open>X \<in> \<D>\<close> dist_commute dist_norm mem_ball \<open>y \<in> S\<close> y)
        also have "\<dots> \<le> B * real DIM('M) * prj1 (vf X - uf X)"
          using \<open>0 < B\<close> by (simp add: nole)
        finally show ?thesis .
      qed
      show ?thesis
        by (rule_tac x=X in bexI)
           (auto simp: fbx_def prj1_idem mem_box conj_le_eq inner_add inner_diff fle \<open>X \<in> \<D>\<close>)
    qed
    then show "f ` S \<subseteq> (\<Union>D\<in>\<D>. fbx D)" by auto
  next
    have 1: "\<And>D. D \<in> \<D> \<Longrightarrow> fbx D \<in> lmeasurable"
      by (auto simp: fbx_def)
    have 2: "I' \<subseteq> \<D> \<Longrightarrow> finite I' \<Longrightarrow> measure lebesgue (\<Union>D\<in>I'. fbx D) \<le> e/2" for I'
      by (rule order_trans[OF measure_Union_le e2]) (auto simp: fbx_def)
    have 3: "0 \<le> e/2"
      using \<open>0<e\<close> by auto
    show "(\<Union>D\<in>\<D>. fbx D) \<in> lmeasurable"
      by (intro fmeasurable_UN_bound[OF \<open>countable \<D>\<close> 1 2 3])
    have "measure lebesgue (\<Union>D\<in>\<D>. fbx D) \<le> e/2"
      by (intro measure_UN_bound[OF \<open>countable \<D>\<close> 1 2 3])
    then show "measure lebesgue (\<Union>D\<in>\<D>. fbx D) < e"
      using \<open>0 < e\<close> by linarith
  qed
qed

proposition negligible_locally_Lipschitz_image:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "negligible S"
      and lips: "\<And>x. x \<in> S
                      \<Longrightarrow> \<exists>T B. open T \<and> x \<in> T \<and>
                              (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
    shows "negligible (f ` S)"
proof -
  let ?S = "\<lambda>n. ({x \<in> S. norm x \<le> n \<and>
                          (\<exists>T. open T \<and> x \<in> T \<and>
                               (\<forall>y\<in>S \<inter> T. norm (f y - f x) \<le> (real n + 1) * norm (y - x)))})"
  have negfn: "f ` ?S n \<in> null_sets lebesgue" for n::nat
    unfolding negligible_iff_null_sets[symmetric]
    apply (rule_tac B = "real n + 1" in locally_Lipschitz_negl_bounded)
    by (auto simp: MleN bounded_iff intro: negligible_subset [OF \<open>negligible S\<close>])
  have "S = (\<Union>n. ?S n)"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> S"
    with lips obtain T B where T: "open T" "x \<in> T"
                           and B: "\<And>y. y \<in> S \<inter> T \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
      by metis+
    have no: "norm (f y - f x) \<le> (nat \<lceil>max B (norm x)\<rceil> + 1) * norm (y - x)" if "y \<in> S \<inter> T" for y
    proof -
      have "B * norm(y - x) \<le> (nat \<lceil>max B (norm x)\<rceil> + 1) * norm (y - x)"
        by (meson max.cobounded1 mult_right_mono nat_ceiling_le_eq nat_le_iff_add norm_ge_zero order_trans)
      then show ?thesis
        using B order_trans that by blast
    qed
    have "x \<in> ?S (nat (ceiling (max B (norm x))))"
      apply (simp add: \<open>x \<in> S \<close>, rule)
      using real_nat_ceiling_ge max.bounded_iff apply blast
      using T no
      apply (force simp: algebra_simps)
      done
    then show "x \<in> (\<Union>n. ?S n)" by force
  qed auto
  then show ?thesis
    by (rule ssubst) (auto simp: image_Union negligible_iff_null_sets intro: negfn)
qed

corollary negligible_differentiable_image_negligible:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "negligible S"
      and diff_f: "f differentiable_on S"
    shows "negligible (f ` S)"
proof -
  have "\<exists>T B. open T \<and> x \<in> T \<and> (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
        if "x \<in> S" for x
  proof -
    obtain f' where "linear f'"
      and f': "\<And>e. e>0 \<Longrightarrow>
                  \<exists>d>0. \<forall>y\<in>S. norm (y - x) < d \<longrightarrow>
                              norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)"
      using diff_f \<open>x \<in> S\<close>
      by (auto simp: linear_linear differentiable_on_def differentiable_def has_derivative_within_alt)
    obtain B where "B > 0" and B: "\<forall>x. norm (f' x) \<le> B * norm x"
      using linear_bounded_pos \<open>linear f'\<close> by blast
    obtain d where "d>0"
              and d: "\<And>y. \<lbrakk>y \<in> S; norm (y - x) < d\<rbrakk> \<Longrightarrow>
                          norm (f y - f x - f' (y - x)) \<le> norm (y - x)"
      using f' [of 1] by (force simp:)
    have *: "norm (f y - f x) \<le> (B + 1) * norm (y - x)"
              if "y \<in> S" "norm (y - x) < d" for y
    proof -
      have "norm (f y - f x) -B *  norm (y - x) \<le> norm (f y - f x) - norm (f' (y - x))"
        by (simp add: B)
      also have "\<dots> \<le> norm (f y - f x - f' (y - x))"
        by (rule norm_triangle_ineq2)
      also have "... \<le> norm (y - x)"
        by (rule d [OF that])
      finally show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      apply (rule_tac x="ball x d" in exI)
      apply (rule_tac x="B+1" in exI)
      using \<open>d>0\<close>
      apply (auto simp: dist_norm norm_minus_commute intro!: *)
      done
  qed
  with negligible_locally_Lipschitz_image assms show ?thesis by metis
qed

corollary negligible_differentiable_image_lowdim:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MlessN: "DIM('M) < DIM('N)" and diff_f: "f differentiable_on S"
    shows "negligible (f ` S)"
proof -
  have "x \<le> DIM('M) \<Longrightarrow> x \<le> DIM('N)" for x
    using MlessN by linarith
  obtain lift :: "'M * real \<Rightarrow> 'N" and drop :: "'N \<Rightarrow> 'M * real" and j :: 'N
    where "linear lift" "linear drop" and dropl [simp]: "\<And>z. drop (lift z) = z"
      and "j \<in> Basis" and j: "\<And>x. lift(x,0) \<bullet> j = 0"
    using lowerdim_embeddings [OF MlessN] by metis
  have "negligible {x. x\<bullet>j = 0}"
    by (metis \<open>j \<in> Basis\<close> negligible_standard_hyperplane)
  then have neg0S: "negligible ((\<lambda>x. lift (x, 0)) ` S)"
    apply (rule negligible_subset)
    by (simp add: image_subsetI j)
  have diff_f': "f \<circ> fst \<circ> drop differentiable_on (\<lambda>x. lift (x, 0)) ` S"
    using diff_f
    apply (clarsimp simp add: differentiable_on_def)
    apply (intro differentiable_chain_within linear_imp_differentiable [OF \<open>linear drop\<close>]
             linear_imp_differentiable [OF fst_linear])
    apply (force simp: image_comp o_def)
    done
  have "f = (f o fst o drop o (\<lambda>x. lift (x, 0)))"
    by (simp add: o_def)
  then show ?thesis
    apply (rule ssubst)
    apply (subst image_comp [symmetric])
    apply (metis negligible_differentiable_image_negligible order_refl diff_f' neg0S)
    done
qed

lemma set_integral_norm_bound:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "set_integrable M k f \<Longrightarrow> norm (LINT x:k|M. f x) \<le> LINT x:k|M. norm (f x)"
  using integral_norm_bound[of M "\<lambda>x. indicator k x *\<^sub>R f x"] by simp

lemma set_integral_finite_UN_AE:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I"
    and ae: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> AE x in M. (x \<in> A i \<and> x \<in> A j) \<longrightarrow> i = j"
    and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
    and f: "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f"
  shows "LINT x:(\<Union>i\<in>I. A i)|M. f x = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using \<open>finite I\<close> order_refl[of I]
proof (induction I rule: finite_subset_induct')
  case (insert i I')
  have "AE x in M. (\<forall>j\<in>I'. x \<in> A i \<longrightarrow> x \<notin> A j)"
  proof (intro AE_ball_countable[THEN iffD2] ballI)
    fix j assume "j \<in> I'"
    with \<open>I' \<subseteq> I\<close> \<open>i \<notin> I'\<close> have "i \<noteq> j" "j \<in> I"
      by auto
    then show "AE x in M. x \<in> A i \<longrightarrow> x \<notin> A j"
      using ae[of i j] \<open>i \<in> I\<close> by auto
  qed (use \<open>finite I'\<close> in \<open>rule countable_finite\<close>)
  then have "AE x\<in>A i in M. \<forall>xa\<in>I'. x \<notin> A xa "
    by auto
  with insert.hyps insert.IH[symmetric]
  show ?case
    by (auto intro!: set_integral_Un_AE sets.finite_UN f set_integrable_UN)
qed simp

lemma set_integrable_norm:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f: "set_integrable M k f" shows "set_integrable M k (\<lambda>x. norm (f x))"
  using integrable_norm[OF f] by simp

lemma absolutely_integrable_bounded_variation:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f absolutely_integrable_on UNIV"
  obtains B where "\<forall>d. d division_of (\<Union>d) \<longrightarrow> sum (\<lambda>k. norm (integral k f)) d \<le> B"
proof (rule that[of "integral UNIV (\<lambda>x. norm (f x))"]; safe)
  fix d :: "'a set set" assume d: "d division_of \<Union>d"
  have *: "k \<in> d \<Longrightarrow> f absolutely_integrable_on k" for k
    using f[THEN set_integrable_subset, of k] division_ofD(2,4)[OF d, of k] by auto
  note d' = division_ofD[OF d]

  have "(\<Sum>k\<in>d. norm (integral k f)) = (\<Sum>k\<in>d. norm (LINT x:k|lebesgue. f x))"
    by (intro sum.cong refl arg_cong[where f=norm] set_lebesgue_integral_eq_integral(2)[symmetric] *)
  also have "\<dots> \<le> (\<Sum>k\<in>d. LINT x:k|lebesgue. norm (f x))"
    by (intro sum_mono set_integral_norm_bound *)
  also have "\<dots> = (\<Sum>k\<in>d. integral k (\<lambda>x. norm (f x)))"
    by (intro sum.cong refl set_lebesgue_integral_eq_integral(2) set_integrable_norm *)
  also have "\<dots> \<le> integral (\<Union>d) (\<lambda>x. norm (f x))"
    using integrable_on_subdivision[OF d] assms f unfolding absolutely_integrable_on_def
    by (subst integral_combine_division_topdown[OF _ d]) auto
  also have "\<dots> \<le> integral UNIV (\<lambda>x. norm (f x))"
    using integrable_on_subdivision[OF d] assms unfolding absolutely_integrable_on_def
    by (intro integral_subset_le) auto
  finally show "(\<Sum>k\<in>d. norm (integral k f)) \<le> integral UNIV (\<lambda>x. norm (f x))" .
qed

lemma helplemma:
  assumes "sum (\<lambda>x. norm (f x - g x)) s < e"
    and "finite s"
  shows "\<bar>sum (\<lambda>x. norm(f x)) s - sum (\<lambda>x. norm(g x)) s\<bar> < e"
  unfolding sum_subtractf[symmetric]
  apply (rule le_less_trans[OF sum_abs])
  apply (rule le_less_trans[OF _ assms(1)])
  apply (rule sum_mono)
  apply (rule norm_triangle_ineq3)
  done

lemma bounded_variation_absolutely_integrable_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "f integrable_on cbox a b"
    and *: "\<forall>d. d division_of (cbox a b) \<longrightarrow> sum (\<lambda>k. norm(integral k f)) d \<le> B"
  shows "f absolutely_integrable_on cbox a b"
proof -
  let ?f = "\<lambda>d. \<Sum>k\<in>d. norm (integral k f)" and ?D = "{d. d division_of (cbox a b)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval[of a b]) auto
  have D_2: "bdd_above (?f`?D)"
    by (metis * mem_Collect_eq bdd_aboveI2)
  note D = D_1 D_2
  let ?S = "SUP x:?D. ?f x"
  show ?thesis
    apply (rule absolutely_integrable_onI [OF f has_integral_integrable])
    apply (subst has_integral[of _ ?S])
    apply safe
  proof goal_cases
    case e: (1 e)
    then have "?S - e / 2 < ?S" by simp
    then obtain d where d: "d division_of (cbox a b)" "?S - e / 2 < (\<Sum>k\<in>d. norm (integral k f))"
      unfolding less_cSUP_iff[OF D] by auto
    note d' = division_ofD[OF this(1)]

    have "\<forall>x. \<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
    proof
      fix x
      have "\<exists>da>0. \<forall>xa\<in>\<Union>{i \<in> d. x \<notin> i}. da \<le> dist x xa"
        apply (rule separate_point_closed)
        apply (rule closed_Union)
        apply (rule finite_subset[OF _ d'(1)])
        using d'(4)
        apply auto
        done
      then show "\<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
        by force
    qed
    from choice[OF this] guess k .. note k=conjunctD2[OF this[rule_format],rule_format]

    have "e/2 > 0"
      using e by auto
    from henstock_lemma[OF assms(1) this] guess g . note g=this[rule_format]
    let ?g = "\<lambda>x. g x \<inter> ball x (k x)"
    show ?case
      apply (rule_tac x="?g" in exI)
      apply safe
    proof -
      show "gauge ?g"
        using g(1) k(1)
        unfolding gauge_def
        by auto
      fix p
      assume "p tagged_division_of (cbox a b)" and "?g fine p"
      note p = this(1) conjunctD2[OF this(2)[unfolded fine_Int]]
      note p' = tagged_division_ofD[OF p(1)]
      define p' where "p' = {(x,k) | x k. \<exists>i l. x \<in> i \<and> i \<in> d \<and> (x,l) \<in> p \<and> k = i \<inter> l}"
      have gp': "g fine p'"
        using p(2)
        unfolding p'_def fine_def
        by auto
      have p'': "p' tagged_division_of (cbox a b)"
        apply (rule tagged_division_ofI)
      proof -
        show "finite p'"
          apply (rule finite_subset[of _ "(\<lambda>(k,(x,l)). (x,k \<inter> l)) `
            {(k,xl) | k xl. k \<in> d \<and> xl \<in> p}"])
          unfolding p'_def
          defer
          apply (rule finite_imageI,rule finite_product_dependent[OF d'(1) p'(1)])
          apply safe
          unfolding image_iff
          apply (rule_tac x="(i,x,l)" in bexI)
          apply auto
          done
        fix x k
        assume "(x, k) \<in> p'"
        then have "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l"
          unfolding p'_def by auto
        then guess i l by (elim exE) note il=conjunctD4[OF this]
        show "x \<in> k" and "k \<subseteq> cbox a b"
          using p'(2-3)[OF il(3)] il by auto
        show "\<exists>a b. k = cbox a b"
          unfolding il using p'(4)[OF il(3)] d'(4)[OF il(2)]
          apply safe
          unfolding Int_interval
          apply auto
          done
      next
        fix x1 k1
        assume "(x1, k1) \<in> p'"
        then have "\<exists>i l. x1 \<in> i \<and> i \<in> d \<and> (x1, l) \<in> p \<and> k1 = i \<inter> l"
          unfolding p'_def by auto
        then guess i1 l1 by (elim exE) note il1=conjunctD4[OF this]
        fix x2 k2
        assume "(x2,k2)\<in>p'"
        then have "\<exists>i l. x2 \<in> i \<and> i \<in> d \<and> (x2, l) \<in> p \<and> k2 = i \<inter> l"
          unfolding p'_def by auto
        then guess i2 l2 by (elim exE) note il2=conjunctD4[OF this]
        assume "(x1, k1) \<noteq> (x2, k2)"
        then have "interior i1 \<inter> interior i2 = {} \<or> interior l1 \<inter> interior l2 = {}"
          using d'(5)[OF il1(2) il2(2)] p'(5)[OF il1(3) il2(3)]
          unfolding il1 il2
          by auto
        then show "interior k1 \<inter> interior k2 = {}"
          unfolding il1 il2 by auto
      next
        have *: "\<forall>(x, X) \<in> p'. X \<subseteq> cbox a b"
          unfolding p'_def using d' by auto
        show "\<Union>{k. \<exists>x. (x, k) \<in> p'} = cbox a b"
          apply rule
          apply (rule Union_least)
          unfolding mem_Collect_eq
          apply (erule exE)
          apply (drule *[rule_format])
          apply safe
        proof -
          fix y
          assume y: "y \<in> cbox a b"
          then have "\<exists>x l. (x, l) \<in> p \<and> y\<in>l"
            unfolding p'(6)[symmetric] by auto
          then guess x l by (elim exE) note xl=conjunctD2[OF this]
          then have "\<exists>k. k \<in> d \<and> y \<in> k"
            using y unfolding d'(6)[symmetric] by auto
          then guess i .. note i = conjunctD2[OF this]
          have "x \<in> i"
            using fineD[OF p(3) xl(1)]
            using k(2)[OF i(1), of x]
            using i(2) xl(2)
            by auto
          then show "y \<in> \<Union>{k. \<exists>x. (x, k) \<in> p'}"
            unfolding p'_def Union_iff
            apply (rule_tac x="i \<inter> l" in bexI)
            using i xl
            apply auto
            done
        qed
      qed

      then have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x - integral k f)) < e / 2"
        apply -
        apply (rule g(2)[rule_format])
        unfolding tagged_division_of_def
        apply safe
        apply (rule gp')
        done
      then have **: "\<bar>(\<Sum>(x,k)\<in>p'. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p'. norm (integral k f))\<bar> < e / 2"
        unfolding split_def
        using p''
        by (force intro!: helplemma)

      have p'alt: "p' = {(x,(i \<inter> l)) | x i l. (x,l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}}"
      proof (safe, goal_cases)
        case prems: (2 _ _ x i l)
        have "x \<in> i"
          using fineD[OF p(3) prems(1)] k(2)[OF prems(2), of x] prems(4-)
          by auto
        then have "(x, i \<inter> l) \<in> p'"
          unfolding p'_def
          using prems
          apply safe
          apply (rule_tac x=x in exI)
          apply (rule_tac x="i \<inter> l" in exI)
          apply safe
          using prems
          apply auto
          done
        then show ?case
          using prems(3) by auto
      next
        fix x k
        assume "(x, k) \<in> p'"
        then have "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l"
          unfolding p'_def by auto
        then guess i l by (elim exE) note il=conjunctD4[OF this]
        then show "\<exists>y i l. (x, k) = (y, i \<inter> l) \<and> (y, l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}"
          apply (rule_tac x=x in exI)
          apply (rule_tac x=i in exI)
          apply (rule_tac x=l in exI)
          using p'(2)[OF il(3)]
          apply auto
          done
      qed
      have sum_p': "(\<Sum>(x, k)\<in>p'. norm (integral k f)) = (\<Sum>k\<in>snd ` p'. norm (integral k f))"
        apply (subst sum.over_tagged_division_lemma[OF p'',of "\<lambda>k. norm (integral k f)"])
        unfolding norm_eq_zero
         apply (rule integral_null)
        apply (simp add: content_eq_0_interior)
        apply rule
        done
      note snd_p = division_ofD[OF division_of_tagged_division[OF p(1)]]

      have *: "\<And>sni sni' sf sf'. \<bar>sf' - sni'\<bar> < e / 2 \<longrightarrow> ?S - e / 2 < sni \<and> sni' \<le> ?S \<and>
        sni \<le> sni' \<and> sf' = sf \<longrightarrow> \<bar>sf - ?S\<bar> < e"
        by arith
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format,OF **])
        apply safe
        apply(rule d(2))
      proof goal_cases
        case 1
        show ?case
          by (auto simp: sum_p' division_of_tagged_division[OF p''] D intro!: cSUP_upper)
      next
        case 2
        have *: "{k \<inter> l | k l. k \<in> d \<and> l \<in> snd ` p} =
          (\<lambda>(k,l). k \<inter> l) ` {(k,l)|k l. k \<in> d \<and> l \<in> snd ` p}"
          by auto
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. \<Sum>l\<in>snd ` p. norm (integral (i \<inter> l) f))"
        proof (rule sum_mono, goal_cases)
          case k: (1 k)
          from d'(4)[OF this] guess u v by (elim exE) note uv=this
          define d' where "d' = {cbox u v \<inter> l |l. l \<in> snd ` p \<and>  cbox u v \<inter> l \<noteq> {}}"
          note uvab = d'(2)[OF k[unfolded uv]]
          have "d' division_of cbox u v"
            apply (subst d'_def)
            apply (rule division_inter_1)
            apply (rule division_of_tagged_division[OF p(1)])
            apply (rule uvab)
            done
          then have "norm (integral k f) \<le> sum (\<lambda>k. norm (integral k f)) d'"
            unfolding uv
            apply (subst integral_combine_division_topdown[of _ _ d'])
            apply (rule integrable_on_subcbox[OF assms(1) uvab])
            apply assumption
            apply (rule sum_norm_le)
            apply auto
            done
          also have "\<dots> = (\<Sum>k\<in>{k \<inter> l |l. l \<in> snd ` p}. norm (integral k f))"
            apply (rule sum.mono_neutral_left)
            apply (subst Setcompr_eq_image)
            apply (rule finite_imageI)+
            apply fact
            unfolding d'_def uv
            apply blast
          proof (rule, goal_cases)
            case prems: (1 i)
            then have "i \<in> {cbox u v \<inter> l |l. l \<in> snd ` p}"
              by auto
            from this[unfolded mem_Collect_eq] guess l .. note l=this
            then have "cbox u v \<inter> l = {}"
              using prems by auto
            then show ?case
              using l by auto
          qed
          also have "\<dots> = (\<Sum>l\<in>snd ` p. norm (integral (k \<inter> l) f))"
            unfolding Setcompr_eq_image
            apply (rule sum.reindex_nontrivial [unfolded o_def])
            apply (rule finite_imageI)
            apply (rule p')
          proof goal_cases
            case prems: (1 l y)
            have "interior (k \<inter> l) \<subseteq> interior (l \<inter> y)"
              apply (subst(2) interior_Int)
              apply (rule Int_greatest)
              defer
              apply (subst prems(4))
              apply auto
              done
            then have *: "interior (k \<inter> l) = {}"
              using snd_p(5)[OF prems(1-3)] by auto
            from d'(4)[OF k] snd_p(4)[OF prems(1)] guess u1 v1 u2 v2 by (elim exE) note uv=this
            show ?case
              using *
              unfolding uv Int_interval content_eq_0_interior[symmetric]
              by auto
          qed
          finally show ?case .
        qed
        also have "\<dots> = (\<Sum>(i,l)\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (i\<inter>l) f))"
          apply (subst sum_sum_product[symmetric])
          apply fact
          using p'(1)
          apply auto
          done
        also have "\<dots> = (\<Sum>x\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (case_prod op \<inter> x) f))"
          unfolding split_def ..
        also have "\<dots> = (\<Sum>k\<in>{i \<inter> l |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral k f))"
          unfolding *
          apply (rule sum.reindex_nontrivial [symmetric, unfolded o_def])
          apply (rule finite_product_dependent)
          apply fact
          apply (rule finite_imageI)
          apply (rule p')
          unfolding split_paired_all mem_Collect_eq split_conv o_def
        proof -
          note * = division_ofD(4,5)[OF division_of_tagged_division,OF p(1)]
          fix l1 l2 k1 k2
          assume as:
            "(l1, k1) \<noteq> (l2, k2)"
            "l1 \<inter> k1 = l2 \<inter> k2"
            "\<exists>i l. (l1, k1) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
            "\<exists>i l. (l2, k2) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
          then have "l1 \<in> d" and "k1 \<in> snd ` p"
            by auto from d'(4)[OF this(1)] *(1)[OF this(2)]
          guess u1 v1 u2 v2 by (elim exE) note uv=this
          have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
            using as by auto
          then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
            apply -
            apply (erule disjE)
            apply (rule disjI2)
            apply (rule d'(5))
            prefer 4
            apply (rule disjI1)
            apply (rule *)
            using as
            apply auto
            done
          moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
            using as(2) by auto
          ultimately have "interior(l1 \<inter> k1) = {}"
            by auto
          then show "norm (integral (l1 \<inter> k1) f) = 0"
            unfolding uv Int_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed
        also have "\<dots> = (\<Sum>(x, k)\<in>p'. norm (integral k f))"
          unfolding sum_p'
          apply (rule sum.mono_neutral_right)
          apply (subst *)
          apply (rule finite_imageI[OF finite_product_dependent])
          apply fact
          apply (rule finite_imageI[OF p'(1)])
          apply safe
        proof goal_cases
          case (2 i ia l a b)
          then have "ia \<inter> b = {}"
            unfolding p'alt image_iff Bex_def not_ex
            apply (erule_tac x="(a, ia \<inter> b)" in allE)
            apply auto
            done
          then show ?case
            by auto
        next
          case (1 x a b)
          then show ?case
            unfolding p'_def
            apply safe
            apply (rule_tac x=i in exI)
            apply (rule_tac x=l in exI)
            unfolding snd_conv image_iff
            apply safe
            apply (rule_tac x="(a,l)" in bexI)
            apply auto
            done
        qed
        finally show ?case .
      next
        case 3
        let ?S = "{(x, i \<inter> l) |x i l. (x, l) \<in> p \<and> i \<in> d}"
        have Sigma_alt: "\<And>s t. s \<times> t = {(i, j) |i j. i \<in> s \<and> j \<in> t}"
          by auto
        have *: "?S = (\<lambda>(xl,i). (fst xl, snd xl \<inter> i)) ` (p \<times> d)"
          apply safe
          unfolding image_iff
          apply (rule_tac x="((x,l),i)" in bexI)
          apply auto
          done
        note pdfin = finite_cartesian_product[OF p'(1) d'(1)]
        have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x, k)\<in>?S. \<bar>content k\<bar> * norm (f x))"
          unfolding norm_scaleR
          apply (rule sum.mono_neutral_left)
          apply (subst *)
          apply (rule finite_imageI)
          apply fact
          unfolding p'alt
          apply blast
          apply safe
          apply (rule_tac x=x in exI)
          apply (rule_tac x=i in exI)
          apply (rule_tac x=l in exI)
          apply auto
          done
        also have "\<dots> = (\<Sum>((x,l),i)\<in>p \<times> d. \<bar>content (l \<inter> i)\<bar> * norm (f x))"
          unfolding *
          apply (subst sum.reindex_nontrivial)
          apply fact
          unfolding split_paired_all
          unfolding o_def split_def snd_conv fst_conv mem_Sigma_iff prod.inject
          apply (elim conjE)
        proof -
          fix x1 l1 k1 x2 l2 k2
          assume as: "(x1, l1) \<in> p" "(x2, l2) \<in> p" "k1 \<in> d" "k2 \<in> d"
            "x1 = x2" "l1 \<inter> k1 = l2 \<inter> k2" "\<not> ((x1 = x2 \<and> l1 = l2) \<and> k1 = k2)"
          from d'(4)[OF as(3)] p'(4)[OF as(1)] guess u1 v1 u2 v2 by (elim exE) note uv=this
          from as have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
            by auto
          then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
            apply -
            apply (erule disjE)
            apply (rule disjI2)
            defer
            apply (rule disjI1)
            apply (rule d'(5)[OF as(3-4)])
            apply assumption
            apply (rule p'(5)[OF as(1-2)])
            apply auto
            done
          moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
            unfolding  as ..
          ultimately have "interior (l1 \<inter> k1) = {}"
            by auto
          then show "\<bar>content (l1 \<inter> k1)\<bar> * norm (f x1) = 0"
            unfolding uv Int_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed safe
        also have "\<dots> = (\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x))"
          unfolding Sigma_alt
          apply (subst sum_sum_product[symmetric])
          apply (rule p')
          apply rule
          apply (rule d')
          apply (rule sum.cong)
          apply (rule refl)
          unfolding split_paired_all split_conv
        proof -
          fix x l
          assume as: "(x, l) \<in> p"
          note xl = p'(2-4)[OF this]
          from this(3) guess u v by (elim exE) note uv=this
          have "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar>) = (\<Sum>k\<in>d. content (k \<inter> cbox u v))"
            apply (rule sum.cong)
            apply (rule refl)
            apply (drule d'(4))
            apply safe
            apply (subst Int_commute)
            unfolding Int_interval uv
            apply (subst abs_of_nonneg)
            apply auto
            done
          also have "\<dots> = sum content {k \<inter> cbox u v| k. k \<in> d}"
            unfolding Setcompr_eq_image
            apply (rule sum.reindex_nontrivial [unfolded o_def, symmetric])
            apply (rule d')
          proof goal_cases
            case prems: (1 k y)
            from d'(4)[OF this(1)] d'(4)[OF this(2)]
            guess u1 v1 u2 v2 by (elim exE) note uv=this
            have "{} = interior ((k \<inter> y) \<inter> cbox u v)"
              apply (subst interior_Int)
              using d'(5)[OF prems(1-3)]
              apply auto
              done
            also have "\<dots> = interior (y \<inter> (k \<inter> cbox u v))"
              by auto
            also have "\<dots> = interior (k \<inter> cbox u v)"
              unfolding prems(4) by auto
            finally show ?case
              unfolding uv Int_interval content_eq_0_interior ..
          qed
          also have "\<dots> = sum content {cbox u v \<inter> k |k. k \<in> d \<and> cbox u v \<inter> k \<noteq> {}}"
            apply (rule sum.mono_neutral_right)
            unfolding Setcompr_eq_image
            apply (rule finite_imageI)
            apply (rule d')
            apply blast
            apply safe
            apply (rule_tac x=k in exI)
          proof goal_cases
            case prems: (1 i k)
            from d'(4)[OF this(1)] guess a b by (elim exE) note ab=this
            have "interior (k \<inter> cbox u v) \<noteq> {}"
              using prems(2)
              unfolding ab Int_interval content_eq_0_interior
              by auto
            then show ?case
              using prems(1)
              using interior_subset[of "k \<inter> cbox u v"]
              by auto
          qed
          finally show "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar> * norm (f x)) = content l *\<^sub>R norm (f x)"
            unfolding sum_distrib_right[symmetric] real_scaleR_def
            apply (subst(asm) additive_content_division[OF division_inter_1[OF d(1)]])
            using xl(2)[unfolded uv]
            unfolding uv
            apply auto
            done
        qed
        finally show ?case .
      qed
    qed
  qed
qed

lemma bounded_variation_absolutely_integrable:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on UNIV"
    and "\<forall>d. d division_of (\<Union>d) \<longrightarrow> sum (\<lambda>k. norm (integral k f)) d \<le> B"
  shows "f absolutely_integrable_on UNIV"
proof (rule absolutely_integrable_onI, fact)
  let ?f = "\<lambda>d. \<Sum>k\<in>d. norm (integral k f)" and ?D = "{d. d division_of  (\<Union>d)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval) auto
  have D_2: "bdd_above (?f`?D)"
    by (intro bdd_aboveI2[where M=B] assms(2)[rule_format]) simp
  note D = D_1 D_2
  let ?S = "SUP d:?D. ?f d"
  have f_int: "\<And>a b. f absolutely_integrable_on cbox a b"
    apply (rule bounded_variation_absolutely_integrable_interval[where B=B])
    apply (rule integrable_on_subcbox[OF assms(1)])
    defer
    apply safe
    apply (rule assms(2)[rule_format])
    apply auto
    done
  have "((\<lambda>x. norm (f x)) has_integral ?S) UNIV"
    apply (subst has_integral_alt')
    apply safe
  proof goal_cases
    case (1 a b)
    show ?case
      using f_int[of a b] unfolding absolutely_integrable_on_def by auto
  next
    case prems: (2 e)
    have "\<exists>y\<in>sum (\<lambda>k. norm (integral k f)) ` {d. d division_of \<Union>d}. \<not> y \<le> ?S - e"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "?S \<le> ?S - e"
        by (intro cSUP_least[OF D(1)]) auto
      then show False
        using prems by auto
    qed
    then obtain K where *: "\<exists>x\<in>{d. d division_of \<Union>d}. K = (\<Sum>k\<in>x. norm (integral k f))"
      "SUPREMUM {d. d division_of \<Union>d} (sum (\<lambda>k. norm (integral k f))) - e < K"
      by (auto simp add: image_iff not_le)
    from this(1) obtain d where "d division_of \<Union>d"
      and "K = (\<Sum>k\<in>d. norm (integral k f))"
      by auto
    note d = this(1) *(2)[unfolded this(2)]
    note d'=division_ofD[OF this(1)]
    have "bounded (\<Union>d)"
      by (rule elementary_bounded,fact)
    from this[unfolded bounded_pos] obtain K where
       K: "0 < K" "\<forall>x\<in>\<Union>d. norm x \<le> K" by auto
    show ?case
      apply (rule_tac x="K + 1" in exI)
      apply safe
    proof -
      fix a b :: 'n
      assume ab: "ball 0 (K + 1) \<subseteq> cbox a b"
      have *: "\<forall>s s1. ?S - e < s1 \<and> s1 \<le> s \<and> s < ?S + e \<longrightarrow> \<bar>s - ?S\<bar> < e"
        by arith
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format])
        apply safe
        apply (rule d(2))
      proof goal_cases
        case 1
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> sum (\<lambda>k. integral k (\<lambda>x. norm (f x))) d"
          apply (intro sum_mono)
          subgoal for k
            using d'(4)[of k] f_int
            by (auto simp: absolutely_integrable_on_def integral_norm_bound_integral)
          done
        also have "\<dots> = integral (\<Union>d) (\<lambda>x. norm (f x))"
          apply (rule integral_combine_division_bottomup[symmetric])
          apply (rule d)
          unfolding forall_in_division[OF d(1)]
          using f_int unfolding absolutely_integrable_on_def
          apply auto
          done
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)"
        proof -
          have "\<Union>d \<subseteq> cbox a b"
            apply rule
            apply (drule K(2)[rule_format])
            apply (rule ab[unfolded subset_eq,rule_format])
            apply (auto simp add: dist_norm)
            done
          then show ?thesis
            apply -
            apply (subst if_P)
            apply rule
            apply (rule integral_subset_le)
            defer
            apply (rule integrable_on_subdivision[of _ _ _ "cbox a b"])
            apply (rule d)
            using f_int[of a b] unfolding absolutely_integrable_on_def
            apply auto
            done
        qed
        finally show ?case .
      next
        note f' = f_int[of a b, unfolded absolutely_integrable_on_def]
        note f = f'[THEN conjunct1] f'[THEN conjunct2]
        note * = this(2)[unfolded has_integral_integral has_integral[of "\<lambda>x. norm (f x)"],rule_format]
        have "e/2>0"
          using \<open>e > 0\<close> by auto
        from * [OF this] obtain d1 where
          d1: "gauge d1" "\<forall>p. p tagged_division_of (cbox a b) \<and> d1 fine p \<longrightarrow>
            norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm (f x))) < e / 2"
          by auto
        from henstock_lemma [OF f(1) \<open>e/2>0\<close>] obtain d2 where
          d2: "gauge d2" "\<forall>p. p tagged_partial_division_of (cbox a b) \<and> d2 fine p \<longrightarrow>
            (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x - integral k f)) < e / 2" .
         obtain p where
          p: "p tagged_division_of (cbox a b)" "d1 fine p" "d2 fine p"
          by (rule fine_division_exists [OF gauge_Int [OF d1(1) d2(1)], of a b])
            (auto simp add: fine_Int)
        have *: "\<And>sf sf' si di. sf' = sf \<longrightarrow> si \<le> ?S \<longrightarrow> \<bar>sf - si\<bar> < e / 2 \<longrightarrow>
          \<bar>sf' - di\<bar> < e / 2 \<longrightarrow> di < ?S + e"
          by arith
        show "integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) < ?S + e"
          apply (subst if_P)
          apply rule
        proof (rule *[rule_format])
          show "\<bar>(\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p. norm (integral k f))\<bar> < e / 2"
            unfolding split_def
            apply (rule helplemma)
            using d2(2)[rule_format,of p]
            using p(1,3)
            unfolding tagged_division_of_def split_def
            apply auto
            done
          show "\<bar>(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm(f x))\<bar> < e / 2"
            using d1(2)[rule_format,OF conjI[OF p(1,2)]]
            by (simp only: real_norm_def)
          show "(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) = (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x))"
            apply (rule sum.cong)
            apply (rule refl)
            unfolding split_paired_all split_conv
            apply (drule tagged_division_ofD(4)[OF p(1)])
            unfolding norm_scaleR
            apply (subst abs_of_nonneg)
            apply auto
            done
          show "(\<Sum>(x, k)\<in>p. norm (integral k f)) \<le> ?S"
            using partial_division_of_tagged_division[of p "cbox a b"] p(1)
            apply (subst sum.over_tagged_division_lemma[OF p(1)])
            apply (simp add: content_eq_0_interior)
            apply (intro cSUP_upper2[OF D(2), of "snd ` p"])
            apply (auto simp: tagged_partial_division_of_def)
            done
        qed
      qed
    qed (insert K, auto)
  qed
  then show "(\<lambda>x. norm (f x)) integrable_on UNIV"
    by blast
qed

lemma absolutely_integrable_add[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> g absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. f x + g x) absolutely_integrable_on s"
  by (rule set_integral_add)

lemma absolutely_integrable_diff[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> g absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. f x - g x) absolutely_integrable_on s"
  by (rule set_integral_diff)

lemma absolutely_integrable_linear:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and h :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) absolutely_integrable_on s"
  using integrable_bounded_linear[of h lebesgue "\<lambda>x. indicator s x *\<^sub>R f x"]
  by (simp add: linear_simps[of h])

lemma absolutely_integrable_sum:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "finite t" and "\<And>a. a \<in> t \<Longrightarrow> (f a) absolutely_integrable_on s"
  shows "(\<lambda>x. sum (\<lambda>a. f a x) t) absolutely_integrable_on s"
  using assms(1,2) by induct auto

lemma absolutely_integrable_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes le: "\<forall>x\<in>s. norm (f x) \<le> g x" and f: "f integrable_on s" and g: "g integrable_on s"
  shows "f absolutely_integrable_on s"
proof (rule Bochner_Integration.integrable_bound)
  show "g absolutely_integrable_on s"
    unfolding absolutely_integrable_on_def
  proof
    show "(\<lambda>x. norm (g x)) integrable_on s"
      using le norm_ge_zero[of "f _"]
      by (intro integrable_spike_finite[OF _ _ g, of "{}"])
         (auto intro!: abs_of_nonneg intro: order_trans simp del: norm_ge_zero)
  qed fact
  show "set_borel_measurable lebesgue s f"
    using f by (auto intro: has_integral_implies_lebesgue_measurable simp: integrable_on_def)
qed (use le in \<open>auto intro!: always_eventually split: split_indicator\<close>)

subsection \<open>Componentwise\<close>

proposition absolutely_integrable_componentwise_iff:
  shows "f absolutely_integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) absolutely_integrable_on A)"
proof -
  have *: "(\<lambda>x. norm (f x)) integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. norm (f x \<bullet> b)) integrable_on A)"
          if "f integrable_on A"
  proof -
    have 1: "\<And>i. \<lbrakk>(\<lambda>x. norm (f x)) integrable_on A; i \<in> Basis\<rbrakk>
                 \<Longrightarrow> (\<lambda>x. f x \<bullet> i) absolutely_integrable_on A"
      apply (rule absolutely_integrable_integrable_bound [where g = "\<lambda>x. norm(f x)"])
      using Basis_le_norm integrable_component that apply fastforce+
      done
    have 2: "\<forall>i\<in>Basis. (\<lambda>x. \<bar>f x \<bullet> i\<bar>) integrable_on A \<Longrightarrow> f absolutely_integrable_on A"
      apply (rule absolutely_integrable_integrable_bound [where g = "\<lambda>x. \<Sum>i\<in>Basis. norm (f x \<bullet> i)"])
      using norm_le_l1 that apply (force intro: integrable_sum)+
      done
    show ?thesis
      apply auto
       apply (metis (full_types) absolutely_integrable_on_def set_integrable_abs 1)
      apply (metis (full_types) absolutely_integrable_on_def 2)
      done
  qed
  show ?thesis
    unfolding absolutely_integrable_on_def
    by (simp add:  integrable_componentwise_iff [symmetric] ball_conj_distrib * cong: conj_cong)
qed

lemma absolutely_integrable_componentwise:
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) absolutely_integrable_on A) \<Longrightarrow> f absolutely_integrable_on A"
  by (simp add: absolutely_integrable_componentwise_iff)

lemma absolutely_integrable_component:
  "f absolutely_integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (b :: 'b :: euclidean_space)) absolutely_integrable_on A"
  by (drule absolutely_integrable_linear[OF _ bounded_linear_inner_left[of b]]) (simp add: o_def)


lemma absolutely_integrable_scaleR_left:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
    assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on S"
proof -
  have "(\<lambda>x. c *\<^sub>R x) o f absolutely_integrable_on S"
    apply (rule absolutely_integrable_linear [OF assms])
    by (simp add: bounded_linear_scaleR_right)
  then show ?thesis by simp
qed

lemma absolutely_integrable_scaleR_right:
  assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. f x *\<^sub>R c) absolutely_integrable_on S"
  using assms by blast

lemma absolutely_integrable_norm:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f absolutely_integrable_on S"
  shows "(norm o f) absolutely_integrable_on S"
  using assms unfolding absolutely_integrable_on_def by auto
    
lemma absolutely_integrable_abs:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) absolutely_integrable_on S"
        (is "?g absolutely_integrable_on S")
proof -
  have eq: "?g =
        (\<lambda>x. \<Sum>i\<in>Basis. ((\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0) \<circ>
               (\<lambda>x. norm(\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f) x)"
    by (simp add: sum.delta)
  have *: "(\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0) \<circ>
           (\<lambda>x. norm (\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f 
           absolutely_integrable_on S" 
        if "i \<in> Basis" for i
  proof -
    have "bounded_linear (\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0)"
      by (simp add: linear_linear algebra_simps linearI)
    moreover have "(\<lambda>x. norm (\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f 
                   absolutely_integrable_on S"
      unfolding o_def
      apply (rule absolutely_integrable_norm [unfolded o_def])
      using assms \<open>i \<in> Basis\<close>
      apply (auto simp: algebra_simps dest: absolutely_integrable_component[where b=i])
      done
    ultimately show ?thesis
      by (subst comp_assoc) (blast intro: absolutely_integrable_linear)
  qed
  show ?thesis
    apply (rule ssubst [OF eq])
    apply (rule absolutely_integrable_sum)
     apply (force simp: intro!: *)+
    done
qed

lemma abs_absolutely_integrableI_1:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on A" and "(\<lambda>x. \<bar>f x\<bar>) integrable_on A"
  shows "f absolutely_integrable_on A"
  by (rule absolutely_integrable_integrable_bound [OF _ assms]) auto

  
lemma abs_absolutely_integrableI:
  assumes f: "f integrable_on S" and fcomp: "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) integrable_on S"
  shows "f absolutely_integrable_on S"
proof -
  have "(\<lambda>x. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on S" if "i \<in> Basis" for i
  proof -
    have "(\<lambda>x. \<bar>f x \<bullet> i\<bar>) integrable_on S" 
      using assms integrable_component [OF fcomp, where y=i] that by simp
    then have "(\<lambda>x. f x \<bullet> i) absolutely_integrable_on S"
      apply -
      apply (rule abs_absolutely_integrableI_1, auto)
      by (simp add: f integrable_component)
    then show ?thesis
      by (rule absolutely_integrable_scaleR_right)
  qed
  then have "(\<lambda>x. \<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on S"
    by (simp add: absolutely_integrable_sum)
  then show ?thesis
    by (simp add: euclidean_representation)
qed

    
lemma absolutely_integrable_abs_iff:
   "f absolutely_integrable_on S \<longleftrightarrow>
    f integrable_on S \<and> (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) integrable_on S"
    (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using absolutely_integrable_abs absolutely_integrable_on_def by blast
next
  assume ?rhs 
  moreover
  have "(\<lambda>x. if x \<in> S then \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i else 0) = (\<lambda>x. \<Sum>i\<in>Basis. \<bar>(if x \<in> S then f x else 0) \<bullet> i\<bar> *\<^sub>R i)"
    by force
  ultimately show ?lhs
    by (simp only: absolutely_integrable_restrict_UNIV [of S, symmetric] integrable_restrict_UNIV [of S, symmetric] abs_absolutely_integrableI)
qed

lemma absolutely_integrable_max:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. \<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i)
            absolutely_integrable_on S"
proof -
  have "(\<lambda>x. \<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = 
        (\<lambda>x. (1/2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i)))"
  proof (rule ext)
    fix x
    have "(\<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. ((f x \<bullet> i + g x \<bullet> i + \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) / 2) *\<^sub>R i)"
      by (force intro: sum.cong)
    also have "... = (1 / 2) *\<^sub>R (\<Sum>i\<in>Basis. (f x \<bullet> i + g x \<bullet> i + \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) *\<^sub>R i)"
      by (simp add: scaleR_right.sum)
    also have "... = (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))"
      by (simp add: sum.distrib algebra_simps euclidean_representation)
    finally
    show "(\<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) =
         (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))" .
  qed
  moreover have "(\<lambda>x. (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))) 
                 absolutely_integrable_on S"
    apply (intro absolutely_integrable_add absolutely_integrable_scaleR_left assms)
    using absolutely_integrable_abs [OF absolutely_integrable_diff [OF assms]]
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis by metis
qed
  
corollary absolutely_integrable_max_1:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. max (f x) (g x)) absolutely_integrable_on S"
  using absolutely_integrable_max [OF assms] by simp

lemma absolutely_integrable_min:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. \<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i)
            absolutely_integrable_on S"
proof -
  have "(\<lambda>x. \<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = 
        (\<lambda>x. (1/2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i)))"
  proof (rule ext)
    fix x
    have "(\<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. ((f x \<bullet> i + g x \<bullet> i - \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) / 2) *\<^sub>R i)"
      by (force intro: sum.cong)
    also have "... = (1 / 2) *\<^sub>R (\<Sum>i\<in>Basis. (f x \<bullet> i + g x \<bullet> i - \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) *\<^sub>R i)"
      by (simp add: scaleR_right.sum)
    also have "... = (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))"
      by (simp add: sum.distrib sum_subtractf algebra_simps euclidean_representation)
    finally
    show "(\<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) =
         (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))" .
  qed
  moreover have "(\<lambda>x. (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))) 
                 absolutely_integrable_on S"
    apply (intro absolutely_integrable_add absolutely_integrable_diff absolutely_integrable_scaleR_left assms)
    using absolutely_integrable_abs [OF absolutely_integrable_diff [OF assms]]
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis by metis
qed
  
corollary absolutely_integrable_min_1:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. min (f x) (g x)) absolutely_integrable_on S"
  using absolutely_integrable_min [OF assms] by simp

lemma nonnegative_absolutely_integrable:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A" and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> 0 \<le> f x \<bullet> b"
  shows "f absolutely_integrable_on A"
proof -
  have "(\<lambda>x. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on A" if "i \<in> Basis" for i
  proof -
    have "(\<lambda>x. f x \<bullet> i) integrable_on A" 
      by (simp add: assms(1) integrable_component)
    then have "(\<lambda>x. f x \<bullet> i) absolutely_integrable_on A"
      by (metis that comp nonnegative_absolutely_integrable_1)
    then show ?thesis
      by (rule absolutely_integrable_scaleR_right)
  qed
  then have "(\<lambda>x. \<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on A"
    by (simp add: absolutely_integrable_sum)
  then show ?thesis
    by (simp add: euclidean_representation)
qed

  
lemma absolutely_integrable_component_ubound:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "f integrable_on A" and g: "g absolutely_integrable_on A"
      and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> f x \<bullet> b \<le> g x \<bullet> b"
  shows "f absolutely_integrable_on A"
proof -
  have "(\<lambda>x. g x - (g x - f x)) absolutely_integrable_on A"
    apply (rule absolutely_integrable_diff [OF g nonnegative_absolutely_integrable])
    using Henstock_Kurzweil_Integration.integrable_diff absolutely_integrable_on_def f g apply blast
    by (simp add: comp inner_diff_left)
  then show ?thesis
    by simp
qed


lemma absolutely_integrable_component_lbound:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "f absolutely_integrable_on A" and g: "g integrable_on A"
      and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> f x \<bullet> b \<le> g x \<bullet> b"
  shows "g absolutely_integrable_on A"
proof -
  have "(\<lambda>x. f x + (g x - f x)) absolutely_integrable_on A"
    apply (rule absolutely_integrable_add [OF f nonnegative_absolutely_integrable])
    using Henstock_Kurzweil_Integration.integrable_diff absolutely_integrable_on_def f g apply blast
    by (simp add: comp inner_diff_left)
  then show ?thesis
    by simp
qed

subsection \<open>Dominated convergence\<close>

lemma dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. (f k) integrable_on s" and h: "h integrable_on s"
    and le: "\<And>k. \<forall>x \<in> s. norm (f k x) \<le> h x"
    and conv: "\<forall>x \<in> s. (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  shows "g integrable_on s" "(\<lambda>k. integral s (f k)) \<longlonglongrightarrow> integral s g"
proof -
  have 3: "h absolutely_integrable_on s"
    unfolding absolutely_integrable_on_def
  proof
    show "(\<lambda>x. norm (h x)) integrable_on s"
    proof (intro integrable_spike_finite[OF _ _ h, of "{}"] ballI)
      fix x assume "x \<in> s - {}" then show "norm (h x) = h x"
        by (metis Diff_empty abs_of_nonneg bot_set_def le norm_ge_zero order_trans real_norm_def)
    qed auto
  qed fact
  have 2: "set_borel_measurable lebesgue s (f k)" for k
    using f by (auto intro: has_integral_implies_lebesgue_measurable simp: integrable_on_def)
  then have 1: "set_borel_measurable lebesgue s g"
    by (rule borel_measurable_LIMSEQ_metric) (use conv in \<open>auto split: split_indicator\<close>)
  have 4: "AE x in lebesgue. (\<lambda>i. indicator s x *\<^sub>R f i x) \<longlonglongrightarrow> indicator s x *\<^sub>R g x"
    "AE x in lebesgue. norm (indicator s x *\<^sub>R f k x) \<le> indicator s x *\<^sub>R h x" for k
    using conv le by (auto intro!: always_eventually split: split_indicator)

  have g: "g absolutely_integrable_on s"
    using 1 2 3 4 by (rule integrable_dominated_convergence)
  then show "g integrable_on s"
    by (auto simp: absolutely_integrable_on_def)
  have "(\<lambda>k. (LINT x:s|lebesgue. f k x)) \<longlonglongrightarrow> (LINT x:s|lebesgue. g x)"
    using 1 2 3 4 by (rule integral_dominated_convergence)
  then show "(\<lambda>k. integral s (f k)) \<longlonglongrightarrow> integral s g"
    using g absolutely_integrable_integrable_bound[OF le f h]
    by (subst (asm) (1 2) set_lebesgue_integral_eq_integral) auto
qed

lemma has_integral_dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<And>k. (f k has_integral y k) s" "h integrable_on s"
    "\<And>k. \<forall>x\<in>s. norm (f k x) \<le> h x" "\<forall>x\<in>s. (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
    and x: "y \<longlonglongrightarrow> x"
  shows "(g has_integral x) s"
proof -
  have int_f: "\<And>k. (f k) integrable_on s"
    using assms by (auto simp: integrable_on_def)
  have "(g has_integral (integral s g)) s"
    by (intro integrable_integral dominated_convergence[OF int_f assms(2)]) fact+
  moreover have "integral s g = x"
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral s (f i)) \<longlonglongrightarrow> x"
      using integral_unique[OF assms(1)] x by simp
    show "(\<lambda>i. integral s (f i)) \<longlonglongrightarrow> integral s g"
      by (intro dominated_convergence[OF int_f assms(2)]) fact+
  qed
  ultimately show ?thesis
    by simp
qed

subsection \<open>Fundamental Theorem of Calculus for the Lebesgue integral\<close>

text \<open>

For the positive integral we replace continuity with Borel-measurability.

\<close>

lemma                                                                                          
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. x \<in> {a..b} \<Longrightarrow> DERIV F x :> f x" "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> f x" and "a \<le> b"
  shows nn_integral_FTC_Icc: "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?nn)
    and has_bochner_integral_FTC_Icc_nonneg:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_nonneg: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
    and integrable_FTC_Icc_nonneg: "integrable lborel (\<lambda>x. f x * indicator {a .. b} x)" (is ?int)
proof -
  have *: "(\<lambda>x. f x * indicator {a..b} x) \<in> borel_measurable borel" "\<And>x. 0 \<le> f x * indicator {a..b} x"
    using f(2) by (auto split: split_indicator)

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b\<Longrightarrow> F x \<le> F y" for x y
    using f by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)

  have "(f has_integral F b - F a) {a..b}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric]
             intro: has_field_derivative_subset[OF f(1)] \<open>a \<le> b\<close>)
  then have i: "((\<lambda>x. f x * indicator {a .. b} x) has_integral F b - F a) UNIV"
    unfolding indicator_def if_distrib[where f="\<lambda>x. a * x" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  then have nn: "(\<integral>\<^sup>+x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a"
    by (rule nn_integral_has_integral_lborel[OF *])
  then show ?has
    by (rule has_bochner_integral_nn_integral[rotated 3]) (simp_all add: * F_mono \<open>a \<le> b\<close>)
  then show ?eq ?int
    unfolding has_bochner_integral_iff by auto
  show ?nn
    by (subst nn[symmetric])
       (auto intro!: nn_integral_cong simp add: ennreal_mult f split: split_indicator)
qed

lemma
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
  assumes "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
  assumes cont: "continuous_on {a .. b} f"
  shows has_bochner_integral_FTC_Icc:
      "has_bochner_integral lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) (F b - F a)" (is ?has)
    and integral_FTC_Icc: "(\<integral>x. indicator {a .. b} x *\<^sub>R f x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have int: "integrable lborel ?f"
    using borel_integrable_compact[OF _ cont] by auto
  have "(f has_integral F b - F a) {a..b}"
    using assms(1,2) by (intro fundamental_theorem_of_calculus) auto
  moreover
  have "(f has_integral integral\<^sup>L lborel ?f) {a..b}"
    using has_integral_integral_lborel[OF int]
    unfolding indicator_def if_distrib[where f="\<lambda>x. x *\<^sub>R a" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  ultimately show ?eq
    by (auto dest: has_integral_unique)
  then show ?has
    using int by (auto simp: has_bochner_integral_iff)
qed

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes deriv: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F x :> f x"
  assumes cont: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows has_bochner_integral_FTC_Icc_real:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_real: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  have 1: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
    using deriv by (auto intro: DERIV_subset)
  have 2: "continuous_on {a .. b} f"
    using cont by (intro continuous_at_imp_continuous_on) auto
  show ?has ?eq
    using has_bochner_integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2] integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2]
    by (auto simp: mult.commute)
qed

lemma nn_integral_FTC_atLeast:
  fixes f :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> DERIV F x :> f x"
  assumes nonneg: "\<And>x. a \<le> x \<Longrightarrow> 0 \<le> f x"
  assumes lim: "(F \<longlongrightarrow> T) at_top"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a ..} x \<partial>lborel) = T - F a"
proof -
  let ?f = "\<lambda>(i::nat) (x::real). ennreal (f x) * indicator {a..a + real i} x"
  let ?fR = "\<lambda>x. ennreal (f x) * indicator {a ..} x"

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> F x \<le> F y" for x y
    using f nonneg by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)
  then have F_le_T: "a \<le> x \<Longrightarrow> F x \<le> T" for x
    by (intro tendsto_lowerbound[OF lim])
       (auto simp: trivial_limit_at_top_linorder eventually_at_top_linorder)

  have "(SUP i::nat. ?f i x) = ?fR x" for x
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    from reals_Archimedean2[of "x - a"] guess n ..
    then have "eventually (\<lambda>n. ?f n x = ?fR x) sequentially"
      by (auto intro!: eventually_sequentiallyI[where c=n] split: split_indicator)
    then show "(\<lambda>n. ?f n x) \<longlonglongrightarrow> ?fR x"
      by (rule Lim_eventually)
  qed (auto simp: nonneg incseq_def le_fun_def split: split_indicator)
  then have "integral\<^sup>N lborel ?fR = (\<integral>\<^sup>+ x. (SUP i::nat. ?f i x) \<partial>lborel)"
    by simp
  also have "\<dots> = (SUP i::nat. (\<integral>\<^sup>+ x. ?f i x \<partial>lborel))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f"
      using nonneg by (auto simp: incseq_def le_fun_def split: split_indicator)
    show "\<And>i. (?f i) \<in> borel_measurable lborel"
      using f_borel by auto
  qed
  also have "\<dots> = (SUP i::nat. ennreal (F (a + real i) - F a))"
    by (subst nn_integral_FTC_Icc[OF f_borel f nonneg]) auto
  also have "\<dots> = T - F a"
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    have "(\<lambda>x. F (a + real x)) \<longlonglongrightarrow> T"
      apply (rule filterlim_compose[OF lim filterlim_tendsto_add_at_top])
      apply (rule LIMSEQ_const_iff[THEN iffD2, OF refl])
      apply (rule filterlim_real_sequentially)
      done
    then show "(\<lambda>n. ennreal (F (a + real n) - F a)) \<longlonglongrightarrow> ennreal (T - F a)"
      by (simp add: F_mono F_le_T tendsto_diff)
  qed (auto simp: incseq_def intro!: ennreal_le_iff[THEN iffD2] F_mono)
  finally show ?thesis .
qed

lemma integral_power:
  "a \<le> b \<Longrightarrow> (\<integral>x. x^k * indicator {a..b} x \<partial>lborel) = (b^Suc k - a^Suc k) / Suc k"
proof (subst integral_FTC_Icc_real)
  fix x show "DERIV (\<lambda>x. x^Suc k / Suc k) x :> x^k"
    by (intro derivative_eq_intros) auto
qed (auto simp: field_simps simp del: of_nat_Suc)

subsection \<open>Integration by parts\<close>

lemma integral_by_parts_integrable:
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows  "integrable lborel (\<lambda>x.((F x) * (g x) + (f x) * (G x)) * indicator {a .. b} x)"
  by (auto intro!: borel_integrable_atLeastAtMost continuous_intros) (auto intro!: DERIV_isCont)

lemma integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows "(\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
proof-
  have 0: "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) = F b * G b - F a * G a"
    by (rule integral_FTC_Icc_real, auto intro!: derivative_eq_intros continuous_intros)
      (auto intro!: DERIV_isCont)

  have "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) =
    (\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel) + \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
    apply (subst Bochner_Integration.integral_add[symmetric])
    apply (auto intro!: borel_integrable_atLeastAtMost continuous_intros)
    by (auto intro!: DERIV_isCont Bochner_Integration.integral_cong split: split_indicator)

  thus ?thesis using 0 by auto
qed

lemma integral_by_parts':
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes "!!x. DERIV F x :> f x"
  assumes "!!x. DERIV G x :> g x"
  shows "(\<integral>x. indicator {a .. b} x *\<^sub>R (F x * g x) \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. indicator {a .. b} x *\<^sub>R (f x * G x) \<partial>lborel"
  using integral_by_parts[OF assms] by (simp add: ac_simps)

lemma has_bochner_integral_even_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes even: "\<And>x. f (- x) = f x"
  shows "has_bochner_integral lborel f (2 *\<^sub>R x)"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator even f)
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by (simp add: scaleR_2)
qed

lemma has_bochner_integral_odd_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes odd: "\<And>x. f (- x) = - f x"
  shows "has_bochner_integral lborel f 0"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. - indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator odd f)
  from has_bochner_integral_minus[OF this]
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) (- x)"
    by simp
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + - x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + - x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by simp
qed

lemma has_integral_0_closure_imp_0:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "continuous_on (closure S) f"
    and nonneg_interior: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
    and pos: "0 < emeasure lborel S"
    and finite: "emeasure lborel S < \<infinity>"
    and regular: "emeasure lborel (closure S) = emeasure lborel S"
    and opn: "open S"
  assumes int: "(f has_integral 0) (closure S)"
  assumes x: "x \<in> closure S"
  shows "f x = 0"
proof -
  have zero: "emeasure lborel (frontier S) = 0"
    using finite closure_subset regular
    unfolding frontier_def
    by (subst emeasure_Diff) (auto simp: frontier_def interior_open \<open>open S\<close> )
  have nonneg: "0 \<le> f x" if "x \<in> closure S" for x
    using continuous_ge_on_closure[OF f that nonneg_interior] by simp
  have "0 = integral (closure S) f"
    by (blast intro: int sym)
  also
  note intl = has_integral_integrable[OF int]
  have af: "f absolutely_integrable_on (closure S)"
    using nonneg
    by (intro absolutely_integrable_onI intl integrable_eq[OF _ intl]) simp
  then have "integral (closure S) f = set_lebesgue_integral lebesgue (closure S) f"
    by (intro set_lebesgue_integral_eq_integral(2)[symmetric])
  also have "\<dots> = 0 \<longleftrightarrow> (AE x in lebesgue. indicator (closure S) x *\<^sub>R f x = 0)"
    by (rule integral_nonneg_eq_0_iff_AE[OF af]) (use nonneg in \<open>auto simp: indicator_def\<close>)
  also have "\<dots> \<longleftrightarrow> (AE x in lebesgue. x \<in> {x. x \<in> closure S \<longrightarrow> f x = 0})"
    by (auto simp: indicator_def)
  finally have "(AE x in lebesgue. x \<in> {x. x \<in> closure S \<longrightarrow> f x = 0})" by simp
  moreover have "(AE x in lebesgue. x \<in> - frontier S)"
    using zero
    by (auto simp: eventually_ae_filter null_sets_def intro!: exI[where x="frontier S"])
  ultimately have ae: "AE x \<in> S in lebesgue. x \<in> {x \<in> closure S. f x = 0}" (is ?th)
    by eventually_elim (use closure_subset in \<open>auto simp: \<close>)
  have "closed {0::real}" by simp
  with continuous_on_closed_vimage[OF closed_closure, of S f] f
  have "closed (f -` {0} \<inter> closure S)" by blast
  then have "closed {x \<in> closure S. f x = 0}" by (auto simp: vimage_def Int_def conj_commute)
  with \<open>open S\<close> have "x \<in> {x \<in> closure S. f x = 0}" if "x \<in> S" for x using ae that
    by (rule mem_closed_if_AE_lebesgue_open)
  then have "f x = 0" if "x \<in> S" for x using that by auto
  from continuous_constant_on_closure[OF f this \<open>x \<in> closure S\<close>]
  show "f x = 0" .
qed

lemma has_integral_0_cbox_imp_0:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "continuous_on (cbox a b) f"
    and nonneg_interior: "\<And>x. x \<in> box a b \<Longrightarrow> 0 \<le> f x"
  assumes int: "(f has_integral 0) (cbox a b)"
  assumes ne: "box a b \<noteq> {}"
  assumes x: "x \<in> cbox a b"
  shows "f x = 0"
proof -
  have "0 < emeasure lborel (box a b)"
    using ne x unfolding emeasure_lborel_box_eq
    by (force intro!: prod_pos simp: mem_box algebra_simps)
  then show ?thesis using assms
    by (intro has_integral_0_closure_imp_0[of "box a b" f x])
      (auto simp: emeasure_lborel_box_eq emeasure_lborel_cbox_eq algebra_simps mem_box)
qed

end
