theory Equivalence_Lebesgue_Henstock_Integration
  imports Lebesgue_Measure Henstock_Kurzweil_Integration Complete_Measure
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

abbreviation lebesgue :: "'a::euclidean_space measure"
  where "lebesgue \<equiv> completion lborel"

abbreviation lebesgue_on :: "'a set \<Rightarrow> 'a::euclidean_space measure"
  where "lebesgue_on \<Omega> \<equiv> restrict_space (completion lborel) \<Omega>"

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
      unfolding d'_def by (intro gauge_inter \<open>gauge d\<close> gauge_ball) auto
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
        by (safe intro!: setsum.union_inter_neutral) (auto simp: s_def T_def)
      also have "(\<Sum>(x, k)\<in>?T ` (p \<inter> s). content k *\<^sub>R f x) = (\<Sum>(x, k)\<in>p \<inter> s. content k *\<^sub>R f (T X k))"
      proof (subst setsum.reindex_nontrivial, safe)
        fix x1 x2 k assume 1: "(x1, k) \<in> p" "(x1, k) \<in> s" and 2: "(x2, k) \<in> p" "(x2, k) \<in> s"
          and eq: "content k *\<^sub>R f (T X k) \<noteq> 0"
        with tagged_division_ofD(5)[OF p(1), of x1 k x2 k] tagged_division_ofD(4)[OF p(1), of x1 k]
        show "x1 = x2"
          by (auto simp: content_eq_0_interior)
      qed (use p in \<open>auto intro!: setsum.cong\<close>)
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
      by (simp add: setsum_distrib_right split_beta')
    also have "\<dots> \<le> (\<Sum>(x, k)\<in>p \<inter> s. content k * (f (T ?F k) - f (T ?E k)))"
      using parts(3) by (auto intro!: setsum_mono mult_left_mono diff_mono)
    also have "\<dots> = (\<Sum>(x, k)\<in>p \<inter> s. content k * f (T ?F k)) - (\<Sum>(x, k)\<in>p \<inter> s. content k * f (T ?E k))"
      by (auto intro!: setsum.cong simp: field_simps setsum_subtractf[symmetric])
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
        by (rule has_integral_sub)
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
          using union.IH by (auto intro!: has_integral_setsum simp del: Int_iff)
        show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
          by (intro setsum_mono2) auto
        from union(1) have *: "\<And>x i j. x \<in> F i \<Longrightarrow> x \<in> F j \<longleftrightarrow> j = i"
          by (auto simp add: disjoint_family_on_def)
        show "\<And>x. (\<lambda>k. ?f k x) \<longlonglongrightarrow> (if x \<in> UNION UNIV F \<inter> box a b then 1 else 0)"
          apply (auto simp: * setsum.If_cases Iio_Int_singleton)
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
      unfolding indicator_def[abs_def] integrable_restrict_univ .
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

lemma has_integral_integral_real:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
using f proof induct
  case (base A c) then show ?case
    by (auto intro!: has_integral_mult_left simp: )
       (simp add: emeasure_eq_ennreal_measure indicator_def has_integral_measure_lborel)
next
  case (add f g) then show ?case
    by (auto intro!: has_integral_add)
next
  case (lim f s)
  show ?case
  proof (rule has_integral_dominated_convergence)
    show "\<And>i. (s i has_integral integral\<^sup>L lborel (s i)) UNIV" by fact
    show "(\<lambda>x. norm (2 * f x)) integrable_on UNIV"
      using \<open>integrable lborel f\<close>
      by (intro nn_integral_integrable_on)
         (auto simp: integrable_iff_bounded abs_mult  nn_integral_cmult ennreal_mult ennreal_mult_less_top)
    show "\<And>k. \<forall>x\<in>UNIV. norm (s k x) \<le> norm (2 * f x)"
      using lim by (auto simp add: abs_mult)
    show "\<forall>x\<in>UNIV. (\<lambda>k. s k x) \<longlonglongrightarrow> f x"
      using lim by auto
    show "(\<lambda>k. integral\<^sup>L lborel (s k)) \<longlonglongrightarrow> integral\<^sup>L lborel f"
      using lim lim(1)[THEN borel_measurable_integrable]
      by (intro integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"]) auto
  qed
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
    show "\<forall>x\<in>\<Omega> - N. f x = g x" using N(3) by auto
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
        unfolding has_integral_restrict_univ .
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
    using f by (intro has_integral_setsum finite_Basis ballI has_integral_scaleR_left has_integral_integral_real) auto
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
    by (intro tendsto_le_const[OF _ lim])
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

end
