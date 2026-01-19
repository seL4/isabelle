section "Affine Sets"

theory Affine
imports Linear_Algebra
begin

lemma if_smult: "(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)"
  by simp

lemma sum_delta_notmem:
  assumes "x \<notin> s"
  shows "sum (\<lambda>y. if (y = x) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (y = x) then P y else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P y else Q y) s = sum Q s"
  by (smt (verit, best) assms sum.cong)+

lemma span_substd_basis:
  assumes d: "d \<subseteq> Basis"
  shows "span d = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  (is "_ = ?B")
proof -
  have "d \<subseteq> ?B"
    using d by (auto simp: inner_Basis)
  moreover have s: "subspace ?B"
    using subspace_substandard[of "\<lambda>i. i \<notin> d"] .
  ultimately have "span d \<subseteq> ?B"
    using span_mono[of d "?B"] span_eq_iff[of "?B"] by blast
  moreover have *: "card d \<le> dim (span d)"
    by (simp add: d dim_eq_card_independent independent_substdbasis)
  moreover from * have "dim ?B \<le> dim (span d)"
    using dim_substandard[OF assms] by auto
  ultimately show ?thesis
    by (simp add: s subspace_dim_equal)
qed

lemma basis_to_substdbasis_subspace_isomorphism:
  fixes B :: "'a::euclidean_space set"
  assumes "independent B"
  shows "\<exists>f d::'a set. card d = card B \<and> linear f \<and> f ` B = d \<and>
    f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} \<and> inj_on f (span B) \<and> d \<subseteq> Basis"
proof -
  have B: "card B = dim B"
    using dim_unique[of B B "card B"] assms span_superset[of B] by auto
  have "dim B \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV[of B] by simp
  from obtain_subset_with_card_n[OF this] 
  obtain d :: "'a set" where d: "d \<subseteq> Basis" and t: "card d = dim B"
    by auto
  let ?t = "{x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` B = d \<and> f ` span B = ?t \<and> inj_on f (span B)"
  proof (intro basis_to_basis_subspace_isomorphism subspace_span subspace_substandard span_superset)
    show "d \<subseteq> {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
      using d inner_not_same_Basis by blast
  qed (auto simp: span_substd_basis independent_substdbasis dim_substandard d t B assms)
  with t \<open>card B = dim B\<close> d show ?thesis by auto
qed

subsection \<open>Affine set and affine hull\<close>

definition\<^marker>\<open>tag important\<close> affine :: "'a::real_vector set \<Rightarrow> bool"
  where "affine S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> S)"

lemma affine_alt: "affine S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> S)"
  unfolding affine_def by (metis eq_diff_eq)

lemma affine_empty [iff]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing [iff]: "affine {x}"
  unfolding affine_alt by (auto simp: scaleR_left_distrib [symmetric])

lemma affine_UNIV [iff]: "affine UNIV"
  unfolding affine_def by auto

lemma affine_Inter [intro]: "(\<And>S. S\<in>\<F> \<Longrightarrow> affine S) \<Longrightarrow> affine (\<Inter>\<F>)"
  unfolding affine_def by auto

lemma affine_Int[intro]: "affine S \<Longrightarrow> affine T \<Longrightarrow> affine (S \<inter> T)"
  unfolding affine_def by auto

lemma affine_scaling: "affine S \<Longrightarrow> affine ((*\<^sub>R) c ` S)"
  apply (clarsimp simp: affine_def)
  apply (rule_tac x="u *\<^sub>R x + v *\<^sub>R y" in image_eqI)
  apply (auto simp: algebra_simps)
  done

lemma affine_affine_hull [simp]: "affine(affine hull S)"
  unfolding hull_def
  using affine_Inter[of "{T. affine T \<and> S \<subseteq> T}"] by auto

lemma affine_hull_eq[simp]: "(affine hull s = s) \<longleftrightarrow> affine s"
  by (metis affine_affine_hull hull_same)

lemma affine_hyperplane: "affine {x. a \<bullet> x = b}"
  by (simp add: affine_def algebra_simps) (metis distrib_right mult.left_neutral)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some explicit formulations\<close>

text "Formalized by Lars Schewe."

lemma affine:
  fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow>
         (\<forall>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> V \<and> sum u S = 1 \<longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V)"
proof -
  have "u *\<^sub>R x + v *\<^sub>R y \<in> V" if "x \<in> V" "y \<in> V" "u + v = (1::real)"
    and *: "\<And>S u. \<lbrakk>finite S; S \<noteq> {}; S \<subseteq> V; sum u S = 1\<rbrakk> \<Longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V" for x y u v
  proof (cases "x = y")
    case True
    then show ?thesis
      using that by (metis scaleR_add_left scaleR_one)
  next
    case False
    then show ?thesis
      using that *[of "{x,y}" "\<lambda>w. if w = x then u else v"] by auto
  qed
  moreover have "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
                if *: "\<And>x y u v. \<lbrakk>x\<in>V; y\<in>V; u + v = 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
                  and "finite S" "S \<noteq> {}" "S \<subseteq> V" "sum u S = 1" for S u
  proof -
    define n where "n = card S"
    consider "card S = 0" | "card S = 1" | "card S = 2" | "card S > 2" by linarith
    then show "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
    proof cases
      assume "card S = 1"
      then obtain a where "S={a}"
        by (auto simp: card_Suc_eq)
      then show ?thesis
        using that by simp
    next
      assume "card S = 2"
      then obtain a b where "S = {a, b}"
        by (metis Suc_1 card_1_singletonE card_Suc_eq)
      then show ?thesis
        using *[of a b] that
        by (auto simp: sum_clauses(2))
    next
      assume "card S > 2"
      then show ?thesis using that n_def
      proof (induct n arbitrary: u S)
        case 0
        then show ?case by auto
      next
        case (Suc n u S)
        have "sum u S = card S" if "\<not> (\<exists>x\<in>S. u x \<noteq> 1)"
          using that unfolding card_eq_sum by auto
        with Suc.prems obtain x where "x \<in> S" and x: "u x \<noteq> 1" by force
        have c: "card (S - {x}) = card S - 1"
          by (simp add: Suc.prems(3) \<open>x \<in> S\<close>)
        have "sum u (S - {x}) = 1 - u x"
          by (simp add: Suc.prems sum_diff1 \<open>x \<in> S\<close>)
        with x have eq1: "inverse (1 - u x) * sum u (S - {x}) = 1"
          by auto
        have inV: "(\<Sum>y\<in>S - {x}. (inverse (1 - u x) * u y) *\<^sub>R y) \<in> V"
        proof (cases "card (S - {x}) > 2")
          case True
          then have S: "S - {x} \<noteq> {}" "card (S - {x}) = n"
            using Suc.prems c by force+
          show ?thesis
          proof (rule Suc.hyps)
            show "(\<Sum>a\<in>S - {x}. inverse (1 - u x) * u a) = 1"
              by (auto simp: eq1 sum_distrib_left[symmetric])
          qed (use S Suc.prems True in auto)
        next
          case False
          then have "card (S - {x}) = Suc (Suc 0)"
            using Suc.prems c by auto
          then obtain a b where ab: "(S - {x}) = {a, b}" "a\<noteq>b"
            unfolding card_Suc_eq by auto
          then show ?thesis
            using eq1 \<open>S \<subseteq> V\<close>
            by (auto simp: sum_distrib_left distrib_left intro!: Suc.prems(2)[of a b])
        qed
        have "u x + (1 - u x) = 1 \<Longrightarrow>
          u x *\<^sub>R x + (1 - u x) *\<^sub>R ((\<Sum>y\<in>S - {x}. u y *\<^sub>R y) /\<^sub>R (1 - u x)) \<in> V"
          by (rule Suc.prems) (use \<open>x \<in> S\<close> Suc.prems inV in \<open>auto simp: scaleR_right.sum\<close>)
        moreover have "(\<Sum>a\<in>S. u a *\<^sub>R a) = u x *\<^sub>R x + (\<Sum>a\<in>S - {x}. u a *\<^sub>R a)"
          by (meson Suc.prems(3) sum.remove \<open>x \<in> S\<close>)
        ultimately show "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
          by (simp add: x)
      qed
    qed (use \<open>S\<noteq>{}\<close> \<open>finite S\<close> in auto)
  qed
  ultimately show ?thesis
    unfolding affine_def by meson
qed


lemma affine_hull_explicit:
  "affine hull p = {y. \<exists>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
proof (rule hull_unique)
  have "\<And>x. sum (\<lambda>z. 1) {x} = 1"
      by auto
  show "p \<subseteq> ?rhs"
  proof (intro subsetI CollectI exI conjI)
    show "\<And>x. sum (\<lambda>z. 1) {x} = 1"
      by auto
  qed auto
  show "?rhs \<subseteq> T" if "p \<subseteq> T" "affine T" for T
    using that unfolding affine by blast
  show "affine ?rhs"
    unfolding affine_def
  proof clarify
    fix u v :: real and sx ux sy uy
    assume uv: "u + v = 1"
      and x: "finite sx" "sx \<noteq> {}" "sx \<subseteq> p" "sum ux sx = (1::real)"
      and y: "finite sy" "sy \<noteq> {}" "sy \<subseteq> p" "sum uy sy = (1::real)" 
    have **: "(sx \<union> sy) \<inter> sx = sx" "(sx \<union> sy) \<inter> sy = sy"
      by auto
    show "\<exists>S w. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p \<and>
        sum w S = 1 \<and> (\<Sum>v\<in>S. w v *\<^sub>R v) = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)"
    proof (intro exI conjI)
      show "finite (sx \<union> sy)"
        using x y by auto
      show "sum (\<lambda>i. (if i\<in>sx then u * ux i else 0) + (if i\<in>sy then v * uy i else 0)) (sx \<union> sy) = 1"
        using x y uv
        by (simp add: sum_Un sum.distrib sum.inter_restrict[symmetric] sum_distrib_left [symmetric] **)
      have "(\<Sum>i\<in>sx \<union> sy. ((if i \<in> sx then u * ux i else 0) + (if i \<in> sy then v * uy i else 0)) *\<^sub>R i)
          = (\<Sum>i\<in>sx. (u * ux i) *\<^sub>R i) + (\<Sum>i\<in>sy. (v * uy i) *\<^sub>R i)"
        using x y
        unfolding scaleR_left_distrib scaleR_zero_left if_smult
        by (simp add: sum_Un sum.distrib sum.inter_restrict[symmetric]  **)
      also have "\<dots> = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)"
        unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] by blast
      finally show "(\<Sum>i\<in>sx \<union> sy. ((if i \<in> sx then u * ux i else 0) + (if i \<in> sy then v * uy i else 0)) *\<^sub>R i) 
                  = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)" .
    qed (use x y in auto)
  qed
qed

lemma affine_hull_finite:
  assumes "finite S"
  shows "affine hull S = {y. \<exists>u. sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
proof -
  have *: "\<exists>h. sum h S = 1 \<and> (\<Sum>v\<in>S. h v *\<^sub>R v) = x" 
    if "F \<subseteq> S" "finite F" "F \<noteq> {}" and sum: "sum u F = 1" and x: "(\<Sum>v\<in>F. u v *\<^sub>R v) = x" for x F u
  proof -
    have "S \<inter> F = F"
      using that by auto
    show ?thesis
    proof (intro exI conjI)
      show "(\<Sum>x\<in>S. if x \<in> F then u x else 0) = 1"
        by (metis (mono_tags, lifting) \<open>S \<inter> F = F\<close> assms sum.inter_restrict sum)
      show "(\<Sum>v\<in>S. (if v \<in> F then u v else 0) *\<^sub>R v) = x"
        by (simp add: if_smult cong: if_cong) (metis (no_types) \<open>S \<inter> F = F\<close> assms sum.inter_restrict x)
    qed
  qed
  show ?thesis
    unfolding affine_hull_explicit using assms
    by (fastforce dest: *)
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Stepping theorems and hence small special cases\<close>

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  by simp

lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows "finite S \<Longrightarrow>
      (\<exists>u. sum u (insert a S) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a S) = y) \<longleftrightarrow>
      (\<exists>v u. sum u S = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y - v *\<^sub>R a)" (is "_ \<Longrightarrow> ?lhs = ?rhs")
proof -
  assume fin: "finite S"
  show "?lhs = ?rhs"
  proof
    assume ?lhs
    then obtain u where u: "sum u (insert a S) = w \<and> (\<Sum>x\<in>insert a S. u x *\<^sub>R x) = y"
      by auto
    show ?rhs
    proof (cases "a \<in> S")
      case True
      then show ?thesis
        using u by (simp add: insert_absorb) (metis diff_zero real_vector.scale_zero_left)
    next
      case False
      show ?thesis
        by (rule exI [where x="u a"]) (use u fin False in auto)
    qed
  next
    assume ?rhs
    then obtain v u where vu: "sum u S = w - v"  "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    have *: "\<And>x M. (if x = a then v else M) *\<^sub>R x = (if x = a then v *\<^sub>R x else M *\<^sub>R x)"
      by auto
    show ?lhs
    proof (cases "a \<in> S")
      case True
      show ?thesis
        by (rule exI [where x="\<lambda>x. (if x=a then v else 0) + u x"])
           (simp add: True scaleR_left_distrib sum.distrib sum_clauses fin vu * cong: if_cong)
    next
      case False
      then show ?thesis
        apply (rule_tac x="\<lambda>x. if x=a then v else u x" in exI) 
        apply (simp add: vu sum_clauses(2)[OF fin] *)
        by (simp add: sum_delta_notmem(3) vu)
    qed
  qed
qed

lemma affine_hull_2:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b| u v. (u + v = 1)}"
  (is "?lhs = ?rhs")
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  have "?lhs = {y. \<exists>u. sum u {a, b} = 1 \<and> (\<Sum>v\<in>{a, b}. u v *\<^sub>R v) = y}"
    using affine_hull_finite[of "{a,b}"] by auto
  also have "\<dots> = {y. \<exists>v u. u b = 1 - v \<and> u b *\<^sub>R b = y - v *\<^sub>R a}"
    by (simp add: affine_hull_finite_step[of "{b}" a])
  also have "\<dots> = ?rhs" unfolding * by auto
  finally show ?thesis by auto
qed

lemma affine_hull_3:
  fixes a b c :: "'a::real_vector"
  shows "affine hull {a,b,c} = {u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c| u v w. u + v + w = 1}"
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  show ?thesis
    apply (simp add: affine_hull_finite affine_hull_finite_step)
    apply (simp only: *)
    apply safe
     apply (metis add.assoc)
    apply (rule_tac x=u in exI, force)
    done
qed

lemma mem_affine:
  assumes "affine S" "x \<in> S" "y \<in> S" "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> S"
  using assms affine_def[of S] by auto

lemma mem_affine_3:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S" "u + v + w = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z \<in> S"
proof -
  have "u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z \<in> affine hull {x, y, z}"
    using affine_hull_3[of x y z] assms by auto
  moreover
  have "affine hull {x, y, z} \<subseteq> affine hull S"
    using hull_mono[of "{x, y, z}" "S"] assms by auto
  moreover
  have "affine hull S = S"
    using assms affine_hull_eq[of S] by auto
  ultimately show ?thesis by auto
qed

lemma mem_affine_3_minus:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S"
  shows "x + v *\<^sub>R (y-z) \<in> S"
  using mem_affine_3[of S x y z 1 v "-v"] assms
  by (simp add: algebra_simps)

corollary%unimportant mem_affine_3_minus2:
    "\<lbrakk>affine S; x \<in> S; y \<in> S; z \<in> S\<rbrakk> \<Longrightarrow> x - v *\<^sub>R (y-z) \<in> S"
  by (metis add_uminus_conv_diff mem_affine_3_minus real_vector.scale_minus_left)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some relations between affine hull and subspaces\<close>

lemma affine_hull_insert_subset_span:
  "affine hull (insert a S) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> S}}"
proof -
  have "\<exists>v T u. x = a + v \<and> (finite T \<and> T \<subseteq> {x - a |x. x \<in> S} \<and> (\<Sum>v\<in>T. u v *\<^sub>R v) = v)"
    if "finite F" "F \<noteq> {}" "F \<subseteq> insert a S" "sum u F = 1" "(\<Sum>v\<in>F. u v *\<^sub>R v) = x"
    for x F u
  proof -
    have *: "(\<lambda>x. x - a) ` (F - {a}) \<subseteq> {x - a |x. x \<in> S}"
      using that by auto
    show ?thesis
    proof (intro exI conjI)
      show "finite ((\<lambda>x. x - a) ` (F - {a}))"
        by (simp add: that(1))
      show "(\<Sum>v\<in>(\<lambda>x. x - a) ` (F - {a}). u(v+a) *\<^sub>R v) = x-a"
        by (simp add: sum.reindex[unfolded inj_on_def] algebra_simps
            sum_subtractf scaleR_left.sum[symmetric] sum_diff1 that)
    qed (use \<open>F \<subseteq> insert a S\<close> in auto)
  qed
  then show ?thesis
    unfolding affine_hull_explicit span_explicit by fast
qed

lemma affine_hull_insert_span:
  assumes "a \<notin> S"
  shows "affine hull (insert a S) = {a + v | v . v \<in> span {x - a | x.  x \<in> S}}"
proof -
  have *: "\<exists>G u. finite G \<and> G \<noteq> {} \<and> G \<subseteq> insert a S \<and> sum u G = 1 \<and> (\<Sum>v\<in>G. u v *\<^sub>R v) = y"
    if "v \<in> span {x - a |x. x \<in> S}" "y = a + v" for y v
  proof -
    from that
    obtain T u where u: "finite T" "T \<subseteq> {x - a |x. x \<in> S}" "a + (\<Sum>v\<in>T. u v *\<^sub>R v) = y"
      unfolding span_explicit by auto
    define F where "F = (\<lambda>x. x + a) ` T"
    have F: "finite F" "F \<subseteq> S" "(\<Sum>v\<in>F. u (v - a) *\<^sub>R (v - a)) = y - a"
      unfolding F_def using u by (auto simp: sum.reindex[unfolded inj_on_def])
    have *: "F \<inter> {a} = {}" "F \<inter> - {a} = F"
      using F assms by auto
    show "\<exists>G u. finite G \<and> G \<noteq> {} \<and> G \<subseteq> insert a S \<and> sum u G = 1 \<and> (\<Sum>v\<in>G. u v *\<^sub>R v) = y"
      apply (rule_tac x = "insert a F" in exI)
      apply (rule_tac x = "\<lambda>x. if x=a then 1 - sum (\<lambda>x. u (x - a)) F else u (x - a)" in exI)
      using assms F
      apply (auto simp:  sum_clauses sum.If_cases if_smult sum_subtractf scaleR_left.sum algebra_simps *)
      done
  qed
  show ?thesis
    by (intro subset_antisym affine_hull_insert_subset_span) (auto simp: affine_hull_explicit dest!: *)
qed

lemma affine_hull_span:
  assumes "a \<in> S"
  shows "affine hull S = {a + v | v. v \<in> span {x - a | x. x \<in> S - {a}}}"
  using affine_hull_insert_span[of a "S - {a}", unfolded insert_Diff[OF assms]] by auto


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Parallel affine sets\<close>

definition affine_parallel :: "'a::real_vector set \<Rightarrow> 'a::real_vector set \<Rightarrow> bool"
  where "affine_parallel S T \<longleftrightarrow> (\<exists>a. T = (\<lambda>x. a + x) ` S)"

lemma affine_parallel_expl_aux:
  fixes S T :: "'a::real_vector set"
  assumes "\<And>x. x \<in> S \<longleftrightarrow> a + x \<in> T"
  shows "T = (\<lambda>x. a + x) ` S"
proof -
  have "x \<in> ((\<lambda>x. a + x) ` S)" if "x \<in> T" for x
    using that
    by (simp add: image_iff) (metis add.commute diff_add_cancel assms)
  moreover have "T \<ge> (\<lambda>x. a + x) ` S"
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma affine_parallel_expl: "affine_parallel S T \<longleftrightarrow> (\<exists>a. \<forall>x. x \<in> S \<longleftrightarrow> a + x \<in> T)"
  by (auto simp add: affine_parallel_def)
    (use affine_parallel_expl_aux [of S _ T] in blast)

lemma affine_parallel_reflex: "affine_parallel S S"
  unfolding affine_parallel_def
  using image_add_0 by blast

lemma affine_parallel_commute:
  assumes "affine_parallel A B"
  shows "affine_parallel B A"
  by (metis affine_parallel_def assms translation_galois)

lemma affine_parallel_assoc:
  assumes "affine_parallel A B"
    and "affine_parallel B C"
  shows "affine_parallel A C"
  by (metis affine_parallel_def assms translation_assoc)

lemma affine_translation_aux:
  fixes a :: "'a::real_vector"
  assumes "affine ((\<lambda>x. a + x) ` S)"
  shows "affine S"
proof -
  have "u *\<^sub>R x + v *\<^sub>R y \<in> S" if xy: "x \<in> S" "y \<in> S" "(u :: real) + v = 1" for x y u v
  proof -
    from that have "(a + x) \<in> ((\<lambda>x. a + x) ` S)" "(a + y) \<in> ((\<lambda>x. a + x) ` S)"
      by auto
    then have h1: "u *\<^sub>R  (a + x) + v *\<^sub>R (a + y) \<in> (\<lambda>x. a + x) ` S"
      using xy assms unfolding affine_def by auto
    have "u *\<^sub>R (a + x) + v *\<^sub>R (a + y) = (u + v) *\<^sub>R a + (u *\<^sub>R x + v *\<^sub>R y)"
      by (simp add: algebra_simps)
    also have "\<dots> = a + (u *\<^sub>R x + v *\<^sub>R y)"
      using \<open>u + v = 1\<close> by auto
    ultimately have "a + (u *\<^sub>R x + v *\<^sub>R y) \<in> (\<lambda>x. a + x) ` S"
      using h1 by auto
    then show ?thesis by auto
  qed
  then show ?thesis unfolding affine_def by auto
qed

lemma affine_translation:
  "affine S \<longleftrightarrow> affine ((+) a ` S)" for a :: "'a::real_vector"
  by (metis affine_translation_aux translation_galois)

lemma parallel_is_affine:
  fixes S T :: "'a::real_vector set"
  assumes "affine S" "affine_parallel S T"
  shows "affine T"
  by (metis affine_parallel_def affine_translation assms)

lemma subspace_imp_affine: "subspace s \<Longrightarrow> affine s"
  unfolding subspace_def affine_def by auto

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_superset subspace_imp_affine subspace_span)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Subspace parallel to an affine set\<close>

lemma subspace_affine: "subspace S \<longleftrightarrow> affine S \<and> 0 \<in> S"
  by (metis add_cancel_right_left affine_alt diff_add_cancel mem_affine_3 scaleR_eq_0_iff subspace_def vector_space_assms(4))

lemma affine_diffs_subspace:
  assumes "affine S" "a \<in> S"
  shows "subspace ((\<lambda>x. (-a)+x) ` S)"
  by (metis ab_left_minus affine_translation assms image_eqI subspace_affine)

lemma affine_diffs_subspace_subtract:
  "subspace ((\<lambda>x. x - a) ` S)" if "affine S" "a \<in> S"
  using that affine_diffs_subspace [of _ a] by simp

lemma parallel_subspace_explicit:
  assumes "affine S"
    and "a \<in> S"
  assumes "L \<equiv> {y. \<exists>x \<in> S. (-a) + x = y}"
  shows "subspace L \<and> affine_parallel S L"
  by (smt (verit) Collect_cong ab_left_minus affine_parallel_def assms image_def mem_Collect_eq parallel_is_affine subspace_affine)

lemma parallel_subspace_aux:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A \<supseteq> B"
  by (metis add.right_neutral affine_parallel_expl assms subsetI subspace_def)

lemma parallel_subspace:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A = B"
  by (simp add: affine_parallel_commute assms parallel_subspace_aux subset_antisym)

lemma affine_parallel_subspace:
  assumes "affine S" "S \<noteq> {}"
  shows "\<exists>!L. subspace L \<and> affine_parallel S L"
  by (meson affine_parallel_assoc affine_parallel_commute assms equals0I parallel_subspace parallel_subspace_explicit)


subsection \<open>Affine Dependence\<close>

text "Formalized by Lars Schewe."

definition\<^marker>\<open>tag important\<close> affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent S \<longleftrightarrow> (\<exists>x\<in>S. x \<in> affine hull (S - {x}))"

lemma affine_dependent_imp_dependent: "affine_dependent S \<Longrightarrow> dependent S"
  unfolding affine_dependent_def dependent_def
  using affine_hull_subset_span by auto

lemma affine_dependent_subset:
   "\<lbrakk>affine_dependent S; S \<subseteq> T\<rbrakk> \<Longrightarrow> affine_dependent T"
  using hull_mono [OF Diff_mono [OF _ subset_refl]]
  by (smt (verit) affine_dependent_def subsetD)

lemma affine_independent_subset:
  shows "\<lbrakk>\<not> affine_dependent T; S \<subseteq> T\<rbrakk> \<Longrightarrow> \<not> affine_dependent S"
  by (metis affine_dependent_subset)

lemma affine_independent_Diff:
   "\<not> affine_dependent S \<Longrightarrow> \<not> affine_dependent(S - T)"
by (meson Diff_subset affine_dependent_subset)

proposition affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>S U. finite S \<and> S \<subseteq> p \<and> sum U S = 0 \<and> (\<exists>v\<in>S. U v \<noteq> 0) \<and> sum (\<lambda>v. U v *\<^sub>R v) S = 0)"
proof -
  have "\<exists>S U. finite S \<and> S \<subseteq> p \<and> sum U S = 0 \<and> (\<exists>v\<in>S. U v \<noteq> 0) \<and> (\<Sum>w\<in>S. U w *\<^sub>R w) = 0"
    if "(\<Sum>w\<in>S. U w *\<^sub>R w) = x" "x \<in> p" "finite S" "S \<noteq> {}" "S \<subseteq> p - {x}" "sum U S = 1" for x S U
  proof (intro exI conjI)
    have "x \<notin> S" 
      using that by auto
    then show "(\<Sum>v \<in> insert x S. if v = x then - 1 else U v) = 0"
      using that by (simp add: sum_delta_notmem)
    show "(\<Sum>w \<in> insert x S. (if w = x then - 1 else U w) *\<^sub>R w) = 0"
      using that \<open>x \<notin> S\<close> by (simp add: if_smult sum_delta_notmem cong: if_cong)
  qed (use that in auto)
  moreover have "\<exists>x\<in>p. \<exists>S U. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p - {x} \<and> sum U S = 1 \<and> (\<Sum>v\<in>S. U v *\<^sub>R v) = x"
    if "(\<Sum>v\<in>S. U v *\<^sub>R v) = 0" "finite S" "S \<subseteq> p" "sum U S = 0" "v \<in> S" "U v \<noteq> 0" for S U v
  proof (intro bexI exI conjI)
    have "S \<noteq> {v}"
      using that by auto
    then show "S - {v} \<noteq> {}"
      using that by auto
    show "(\<Sum>x \<in> S - {v}. - (1 / U v) * U x) = 1"
      unfolding sum_distrib_left[symmetric] sum_diff1[OF \<open>finite S\<close>] by (simp add: that)
    show "(\<Sum>x\<in>S - {v}. (- (1 / U v) * U x) *\<^sub>R x) = v"
      unfolding sum_distrib_left [symmetric] scaleR_scaleR[symmetric]
                scaleR_right.sum [symmetric] sum_diff1[OF \<open>finite S\<close>] 
      using that by auto
    show "S - {v} \<subseteq> p - {v}"
      using that by auto
  qed (use that in auto)
  ultimately show ?thesis
    unfolding affine_dependent_def affine_hull_explicit by auto
qed

lemma affine_dependent_explicit_finite:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows "affine_dependent S \<longleftrightarrow>
    (\<exists>U. sum U S = 0 \<and> (\<exists>v\<in>S. U v \<noteq> 0) \<and> sum (\<lambda>v. U v *\<^sub>R v) S = 0)"
  (is "?lhs = ?rhs")
proof
  have *: "\<And>vt U v. (if vt then U v else 0) *\<^sub>R v = (if vt then (U v) *\<^sub>R v else 0::'a)"
    by auto
  assume ?lhs
  then obtain T U v where
    "finite T" "T \<subseteq> S" "sum U T = 0" "v\<in>T" "U v \<noteq> 0"  "(\<Sum>v\<in>T. U v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  then show ?rhs
    apply (rule_tac x="\<lambda>x. if x\<in>T then U x else 0" in exI)
    apply (auto simp: * sum.inter_restrict[OF assms, symmetric] Int_absorb1[OF \<open>T\<subseteq>S\<close>])
    done
next
  assume ?rhs
  then obtain U v where "sum U S = 0"  "v\<in>S" "U v \<noteq> 0" "(\<Sum>v\<in>S. U v *\<^sub>R v) = 0"
    by auto
  then show ?lhs unfolding affine_dependent_explicit
    using assms by auto
qed

lemma dependent_imp_affine_dependent:
  assumes "dependent {x - a| x . x \<in> S}"
    and "a \<notin> S"
  shows "affine_dependent (insert a S)"
proof -
  from assms(1)[unfolded dependent_explicit] obtain S' U v
    where S: "finite S'" "S' \<subseteq> {x - a |x. x \<in> S}" "v\<in>S'" "U v  \<noteq> 0" "(\<Sum>v\<in>S'. U v *\<^sub>R v) = 0"
    by auto
  define T where "T = (\<lambda>x. x + a) ` S'"
  have inj: "inj_on (\<lambda>x. x + a) S'"
    unfolding inj_on_def by auto
  have "0 \<notin> S'"
    using S(2) assms(2) unfolding subset_eq by auto
  have fin: "finite T" and "T \<subseteq> S"
    unfolding T_def using S(1,2) by auto
  then have "finite (insert a T)" and "insert a T \<subseteq> insert a S"
    by auto
  moreover have *: "\<And>P Q. (\<Sum>x\<in>T. (if x = a then P x else Q x)) = (\<Sum>x\<in>T. Q x)"
    by (smt (verit, best) \<open>T \<subseteq> S\<close> assms(2) subsetD sum.cong)
  have "(\<Sum>x\<in>insert a T. if x = a then - (\<Sum>x\<in>T. U (x - a)) else U (x - a)) = 0"
    by (smt (verit) \<open>T \<subseteq> S\<close> assms(2) fin insert_absorb insert_subset sum.insert sum_mono)
  moreover have "\<exists>v\<in>insert a T. (if v = a then - (\<Sum>x\<in>T. U (x - a)) else U (v - a)) \<noteq> 0"
    using S(3,4) \<open>0\<notin>S'\<close>
    by (rule_tac x="v + a" in bexI) (auto simp: T_def)
  moreover have *: "\<And>P Q. (\<Sum>x\<in>T. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>T. Q x *\<^sub>R x)"
    using \<open>a\<notin>S\<close> \<open>T\<subseteq>S\<close> by (auto intro!: sum.cong)
  have "(\<Sum>x\<in>T. U (x - a)) *\<^sub>R a = (\<Sum>v\<in>T. U (v - a) *\<^sub>R v)"
    unfolding scaleR_left.sum
    unfolding T_def and sum.reindex[OF inj] and o_def
    using S(5)
    by (auto simp: sum.distrib scaleR_right_distrib)
  then have "(\<Sum>v\<in>insert a T. (if v = a then - (\<Sum>x\<in>T. U (x - a)) else U (v - a)) *\<^sub>R v) = 0"
    unfolding sum_clauses(2)[OF fin] using \<open>a\<notin>S\<close> \<open>T\<subseteq>S\<close> by (auto simp: *)
  ultimately show ?thesis
    unfolding affine_dependent_explicit
    by (force intro!: exI[where x="insert a T"])
qed

lemma affine_dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" "card S \<ge> DIM('a) + 2"
  shows "affine_dependent S"
proof -
  have "S \<noteq> {}" using assms by auto
  then obtain a where "a\<in>S" by auto
  have *: "{x - a |x. x \<in> S - {a}} = (\<lambda>x. x - a) ` (S - {a})"
    by auto
  have "card {x - a |x. x \<in> S - {a}} = card (S - {a})"
    unfolding * by (simp add: card_image inj_on_def)
  also have "\<dots> > DIM('a)" using assms(2)
    unfolding card_Diff_singleton[OF \<open>a\<in>S\<close>] by auto
  finally  have "affine_dependent (insert a (S - {a}))"
    using dependent_biggerset dependent_imp_affine_dependent by blast
  then show ?thesis
    by (simp add: \<open>a \<in> S\<close> insert_absorb)
qed

lemma affine_dependent_biggerset_general:
  assumes "finite (S :: 'a::euclidean_space set)"
    and "card S \<ge> dim S + 2"
  shows "affine_dependent S"
proof -
  from assms(2) have "S \<noteq> {}" by auto
  then obtain a where "a\<in>S" by auto
  have *: "{x - a |x. x \<in> S - {a}} = (\<lambda>x. x - a) ` (S - {a})"
    by auto
  have **: "card {x - a |x. x \<in> S - {a}} = card (S - {a})"
    by (metis (no_types, lifting) "*" card_image diff_add_cancel inj_on_def)
  have "dim {x - a |x. x \<in> S - {a}} \<le> dim S"
    using \<open>a\<in>S\<close> by (auto simp: span_base span_diff intro: subset_le_dim)
  also have "\<dots> < dim S + 1" by auto
  also have "\<dots> \<le> card (S - {a})"
    using assms card_Diff_singleton[OF \<open>a\<in>S\<close>] by auto
  finally have "affine_dependent (insert a (S - {a}))"
    by (smt (verit) Collect_cong dependent_imp_affine_dependent dependent_biggerset_general ** Diff_iff insertCI)
  then show ?thesis
    by (simp add: \<open>a \<in> S\<close> insert_absorb)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some Properties of Affine Dependent Sets\<close>

lemma affine_independent_0 [simp]: "\<not> affine_dependent {}"
  by (simp add: affine_dependent_def)

lemma affine_independent_1 [simp]: "\<not> affine_dependent {a}"
  by (simp add: affine_dependent_def)

lemma affine_independent_2 [simp]: "\<not> affine_dependent {a,b}"
  by (simp add: affine_dependent_def insert_Diff_if hull_same)

lemma affine_hull_translation: "affine hull ((\<lambda>x. a + x) `  S) = (\<lambda>x. a + x) ` (affine hull S)"
proof -
  have "affine ((\<lambda>x. a + x) ` (affine hull S))"
    using affine_translation affine_affine_hull by blast
  moreover have "(\<lambda>x. a + x) `  S \<subseteq> (\<lambda>x. a + x) ` (affine hull S)"
    using hull_subset[of S] by auto
  ultimately have h1: "affine hull ((\<lambda>x. a + x) `  S) \<subseteq> (\<lambda>x. a + x) ` (affine hull S)"
    by (metis hull_minimal)
  have "affine((\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)))"
    using affine_translation affine_affine_hull by blast
  moreover have "(\<lambda>x. -a + x) ` (\<lambda>x. a + x) `  S \<subseteq> (\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S))"
    using hull_subset[of "(\<lambda>x. a + x) `  S"] by auto
  moreover have "S = (\<lambda>x. -a + x) ` (\<lambda>x. a + x) `  S"
    using translation_assoc[of "-a" a] by auto
  ultimately have "(\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)) >= (affine hull S)"
    by (metis hull_minimal)
  then have "affine hull ((\<lambda>x. a + x) ` S) >= (\<lambda>x. a + x) ` (affine hull S)"
    by auto
  then show ?thesis using h1 by auto
qed

lemma affine_dependent_translation:
  assumes "affine_dependent S"
  shows "affine_dependent ((\<lambda>x. a + x) ` S)"
proof -
  obtain x where x: "x \<in> S \<and> x \<in> affine hull (S - {x})"
    using assms affine_dependent_def by auto
  have "(+) a ` (S - {x}) = (+) a ` S - {a + x}"
    by auto
  then have "a + x \<in> affine hull ((\<lambda>x. a + x) ` S - {a + x})"
    using affine_hull_translation[of a "S - {x}"] x by auto
  moreover have "a + x \<in> (\<lambda>x. a + x) ` S"
    using x by auto
  ultimately show ?thesis
    unfolding affine_dependent_def by auto
qed

lemma affine_dependent_translation_eq:
  "affine_dependent S \<longleftrightarrow> affine_dependent ((\<lambda>x. a + x) ` S)"
  by (metis affine_dependent_translation translation_galois)

lemma affine_hull_0_dependent:
  assumes "0 \<in> affine hull S"
  shows "dependent S"
proof -
  obtain s u where s_u: "finite s \<and> s \<noteq> {} \<and> s \<subseteq> S \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    using assms affine_hull_explicit[of S] by auto
  then have "\<exists>v\<in>s. u v \<noteq> 0" by auto
  then have "finite s \<and> s \<subseteq> S \<and> (\<exists>v\<in>s. u v \<noteq> 0 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0)"
    using s_u by auto
  then show ?thesis
    unfolding dependent_explicit[of S] by auto
qed

lemma affine_dependent_imp_dependent2:
  assumes "affine_dependent (insert 0 S)"
  shows "dependent S"
proof -
  obtain x where x: "x \<in> insert 0 S \<and> x \<in> affine hull (insert 0 S - {x})"
    using affine_dependent_def[of "(insert 0 S)"] assms by blast
  then have "x \<in> span (insert 0 S - {x})"
    using affine_hull_subset_span by auto
  moreover have "span (insert 0 S - {x}) = span (S - {x})"
    using insert_Diff_if[of "0" S "{x}"] span_insert_0[of "S-{x}"] by auto
  ultimately have "x \<in> span (S - {x})" by auto
  then have "x \<noteq> 0 \<Longrightarrow> dependent S"
    using x dependent_def by auto
  moreover have "dependent S" if "x = 0"
    by (metis that affine_hull_0_dependent Diff_insert_absorb dependent_zero x)
  ultimately show ?thesis by auto
qed

lemma affine_dependent_iff_dependent:
  assumes "a \<notin> S"
  shows "affine_dependent (insert a S) \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` S)"
proof -
  have "((+) (- a) ` S) = {x - a| x . x \<in> S}" by auto
  then show ?thesis
    using affine_dependent_translation_eq[of "(insert a S)" "-a"]
      affine_dependent_imp_dependent2 assms
      dependent_imp_affine_dependent[of a S]
    by (auto simp del: uminus_add_conv_diff)
qed

lemma affine_dependent_iff_dependent2:
  assumes "a \<in> S"
  shows "affine_dependent S \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` (S-{a}))"
  by (metis Diff_iff affine_dependent_iff_dependent assms insert_Diff singletonI)

lemma affine_hull_insert_span_gen:
  "affine hull (insert a S) = (\<lambda>x. a + x) ` span ((\<lambda>x. - a + x) ` S)"
proof (cases "a \<in> S")
  case True
  then have "insert 0 ((\<lambda>x. -a+x) ` (S - {a})) = (\<lambda>x. -a+x) ` S"
    by auto
  then have "span ((\<lambda>x. -a+x) ` (S - {a})) = span ((\<lambda>x. -a+x) ` S)"
    using span_insert_0[of "(+) (- a) ` (S - {a})"]
    by presburger
  moreover have "{x - a |x. x \<in> (S - {a})} = ((\<lambda>x. -a+x) ` (S - {a}))"
    by auto
  moreover have "insert a (S - {a}) = insert a S"
    by auto
  ultimately show ?thesis
    using affine_hull_insert_span[of "a" "S-{a}"] by auto
next
  case False
  have "{x - a |x. x \<in> S} = ((\<lambda>x. -a+x) ` S)" by auto
  with False show ?thesis using affine_hull_insert_span[of a S] by auto
qed

lemma affine_hull_span2:
  assumes "a \<in> S"
  shows "affine hull S = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` (S-{a}))"
  by (metis affine_hull_insert_span_gen assms insert_Diff)

lemma affine_hull_span_gen:
  assumes "a \<in> affine hull S"
  shows "affine hull S = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` S)"
  by (metis affine_hull_insert_span_gen assms hull_redundant)

lemma affine_hull_span_0:
  assumes "0 \<in> affine hull S"
  shows "affine hull S = span S"
  using affine_hull_span_gen[of "0" S] assms by auto

lemma extend_to_affine_basis_nonempty:
  fixes S V :: "'n::real_vector set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V" "S \<noteq> {}"
  shows "\<exists>T. \<not> affine_dependent T \<and> S \<subseteq> T \<and> T \<subseteq> V \<and> affine hull T = affine hull V"
proof -
  obtain a where a: "a \<in> S"
    using assms by auto
  then have h0: "independent  ((\<lambda>x. -a + x) ` (S-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  obtain B where B:
    "(\<lambda>x. -a+x) ` (S - {a}) \<subseteq> B \<and> B \<subseteq> (\<lambda>x. -a+x) ` V \<and> independent B \<and> (\<lambda>x. -a+x) ` V \<subseteq> span B"
    using assms
    by (blast intro: maximal_independent_subset_extend[OF _ h0, of "(\<lambda>x. -a + x) ` V"])
  define T where "T = (\<lambda>x. a+x) ` insert 0 B"
  then have "T = insert a ((\<lambda>x. a+x) ` B)"
    by auto
  then have "affine hull T = (\<lambda>x. a+x) ` span B"
    using affine_hull_insert_span_gen[of a "((\<lambda>x. a+x) ` B)"] translation_assoc[of "-a" a B]
    by auto
  then have "V \<subseteq> affine hull T"
    using B assms translation_inverse_subset[of a V "span B"]
    by auto
  moreover have "T \<subseteq> V"
    using T_def B a assms by auto
  ultimately have "affine hull T = affine hull V"
    by (metis Int_absorb1 Int_absorb2 hull_hull hull_mono)
  moreover have "S \<subseteq> T"
    using T_def B translation_inverse_subset[of a "S-{a}" B]
    by auto
  moreover have "\<not> affine_dependent T"
    using T_def affine_dependent_translation_eq[of "insert 0 B"]
      affine_dependent_imp_dependent2 B
    by auto
  ultimately show ?thesis using \<open>T \<subseteq> V\<close> by auto
qed

lemma affine_basis_exists:
  fixes V :: "'n::real_vector set"
  shows "\<exists>B. B \<subseteq> V \<and> \<not> affine_dependent B \<and> affine hull V = affine hull B"
  by (metis affine_dependent_def affine_independent_1 empty_subsetI extend_to_affine_basis_nonempty insert_subset order_refl)

proposition extend_to_affine_basis:
  fixes S V :: "'n::real_vector set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V"
  obtains T where "\<not> affine_dependent T" "S \<subseteq> T" "T \<subseteq> V" "affine hull T = affine hull V"
  by (metis affine_basis_exists assms(1) assms(2) bot.extremum extend_to_affine_basis_nonempty)


subsection \<open>Affine Dimension of a Set\<close>

definition\<^marker>\<open>tag important\<close> aff_dim :: "('a::euclidean_space) set \<Rightarrow> int"
  where "aff_dim V =
  (SOME d :: int.
    \<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = d + 1)"

lemma aff_dim_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
proof -
  obtain B where "\<not> affine_dependent B \<and> affine hull B = affine hull V"
    using affine_basis_exists[of V] by auto
  then show ?thesis
    unfolding aff_dim_def
      some_eq_ex[of "\<lambda>d. \<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = d + 1"]
    apply auto
    apply (rule exI[of _ "int (card B) - (1 :: int)"])
    apply (rule exI[of _ "B"], auto)
    done
qed

lemma affine_hull_eq_empty [simp]: "affine hull S = {} \<longleftrightarrow> S = {}"
by (metis affine_empty subset_empty subset_hull)

lemma empty_eq_affine_hull[simp]: "{} = affine hull S \<longleftrightarrow> S = {}"
  by (metis affine_hull_eq_empty)

lemma aff_dim_parallel_subspace_aux:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B" "a \<in> B"
  shows "finite B \<and> ((card B) - 1 = dim (span ((\<lambda>x. -a+x) ` (B-{a}))))"
proof -
  have "independent ((\<lambda>x. -a + x) ` (B-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  then have fin: "dim (span ((\<lambda>x. -a+x) ` (B-{a}))) = card ((\<lambda>x. -a + x) ` (B-{a}))"
    "finite ((\<lambda>x. -a + x) ` (B - {a}))"
    using indep_card_eq_dim_span[of "(\<lambda>x. -a+x) ` (B-{a})"] by auto
  show ?thesis
  proof (cases "(\<lambda>x. -a + x) ` (B - {a}) = {}")
    case True
    have "B = insert a ((\<lambda>x. a + x) ` (\<lambda>x. -a + x) ` (B - {a}))"
      using translation_assoc[of "a" "-a" "(B - {a})"] assms by auto
    then have "B = {a}" using True by auto
    then show ?thesis using assms fin by auto
  next
    case False
    then have "card ((\<lambda>x. -a + x) ` (B - {a})) > 0"
      using fin by auto
    moreover have h1: "card ((\<lambda>x. -a + x) ` (B-{a})) = card (B-{a})"
      by (rule card_image) (use translate_inj_on in blast)
    ultimately have "card (B-{a}) > 0" by auto
    then have *: "finite (B - {a})"
      using card_gt_0_iff[of "(B - {a})"] by auto
    then have "card (B - {a}) = card B - 1"
      using card_Diff_singleton assms by auto
    with * show ?thesis using fin h1 by auto
  qed
qed

lemma aff_dim_parallel_subspace:
  fixes V L :: "'n::euclidean_space set"
  assumes "V \<noteq> {}"
    and "subspace L"
    and "affine_parallel (affine hull V) L"
  shows "aff_dim V = int (dim L)"
proof -
  obtain B where
    B: "affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> int (card B) = aff_dim V + 1"
    using aff_dim_basis_exists by auto
  then have "B \<noteq> {}"
    using assms B
    by auto
  then obtain a where a: "a \<in> B" by auto
  define Lb where "Lb = span ((\<lambda>x. -a+x) ` (B-{a}))"
  moreover have "affine_parallel (affine hull B) Lb"
    using Lb_def B assms affine_hull_span2[of a B] a
      affine_parallel_commute[of "Lb" "(affine hull B)"]
    unfolding affine_parallel_def
    by auto
  moreover have "subspace Lb"
    using Lb_def subspace_span by auto
  moreover have "affine hull B \<noteq> {}"
    using assms B by auto
  ultimately have "L = Lb"
    using assms affine_parallel_subspace[of "affine hull B"] affine_affine_hull[of B] B
    by auto
  then have "dim L = dim Lb"
    by auto
  moreover have "card B - 1 = dim Lb" and "finite B"
    using Lb_def aff_dim_parallel_subspace_aux a B by auto
  ultimately show ?thesis
    using B \<open>B \<noteq> {}\<close> card_gt_0_iff[of B] by auto
qed

lemma aff_independent_finite:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "finite B"
  using aff_dim_parallel_subspace_aux assms finite.simps by fastforce


lemma aff_dim_empty:
  fixes S :: "'n::euclidean_space set"
  shows "S = {} \<longleftrightarrow> aff_dim S = -1"
proof -
  obtain B where *: "affine hull B = affine hull S"
    and "\<not> affine_dependent B"
    and "int (card B) = aff_dim S + 1"
    using aff_dim_basis_exists by auto
  moreover
  from * have "S = {} \<longleftrightarrow> B = {}"
    by auto
  ultimately show ?thesis
    using aff_independent_finite[of B] card_gt_0_iff[of B] by auto
qed

lemma aff_dim_empty_eq [simp]: "aff_dim ({}::'a::euclidean_space set) = -1"
  using aff_dim_empty by blast

lemma aff_dim_affine_hull [simp]: "aff_dim (affine hull S) = aff_dim S"
  unfolding aff_dim_def using hull_hull[of _ S] by auto

lemma aff_dim_affine_hull2:
  assumes "affine hull S = affine hull T"
  shows "aff_dim S = aff_dim T"
  unfolding aff_dim_def using assms by auto

lemma aff_dim_unique:
  fixes B V :: "'n::euclidean_space set"
  assumes "affine hull B = affine hull V \<and> \<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim V + 1"
proof (cases "B = {}")
  case True
  then have "V = {}"
    using assms
    by auto
  then have "aff_dim V = (-1::int)"
    using aff_dim_empty by auto
  then show ?thesis
    using \<open>B = {}\<close> by auto
next
  case False
  then obtain a where a: "a \<in> B" by auto
  define Lb where "Lb = span ((\<lambda>x. -a+x) ` (B-{a}))"
  have "affine_parallel (affine hull B) Lb"
    using Lb_def affine_hull_span2[of a B] a
      affine_parallel_commute[of "Lb" "(affine hull B)"]
    unfolding affine_parallel_def by auto
  moreover have "subspace Lb"
    using Lb_def subspace_span by auto
  ultimately have "aff_dim B = int(dim Lb)"
    using aff_dim_parallel_subspace[of B Lb] \<open>B \<noteq> {}\<close> by auto
  moreover have "(card B) - 1 = dim Lb" "finite B"
    using Lb_def aff_dim_parallel_subspace_aux a assms by auto
  ultimately have "of_nat (card B) = aff_dim B + 1"
    using \<open>B \<noteq> {}\<close> card_gt_0_iff[of B] by auto
  then show ?thesis
    using aff_dim_affine_hull2 assms by auto
qed

lemma aff_dim_affine_independent:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim B + 1"
  using aff_dim_unique[of B B] assms by auto

lemma affine_independent_iff_card:
    fixes S :: "'a::euclidean_space set"
    shows "\<not> affine_dependent S \<longleftrightarrow> finite S \<and> aff_dim S = int(card S) - 1" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" 
    by (simp add: aff_dim_affine_independent aff_independent_finite)
  show "?rhs \<Longrightarrow> ?lhs" 
    by (metis of_nat_eq_iff affine_basis_exists aff_dim_unique card_subset_eq diff_add_cancel)
qed

lemma aff_dim_sing [simp]:
  fixes a :: "'n::euclidean_space"
  shows "aff_dim {a} = 0"
  using aff_dim_affine_independent[of "{a}"] affine_independent_1 by auto

lemma aff_dim_2 [simp]:
  fixes a :: "'n::euclidean_space"
  shows "aff_dim {a,b} = (if a = b then 0 else 1)"
proof (clarsimp)
  assume "a \<noteq> b"
  then have "aff_dim{a,b} = card{a,b} - 1"
    using affine_independent_2 [of a b] aff_dim_affine_independent by fastforce
  also have "\<dots> = 1"
    using \<open>a \<noteq> b\<close> by simp
  finally show "aff_dim {a, b} = 1" .
qed

lemma aff_dim_inner_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. B \<subseteq> V \<and> affine hull B = affine hull V \<and>
    \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
  by (metis aff_dim_unique affine_basis_exists)

lemma aff_dim_le_card:
  fixes V :: "'n::euclidean_space set"
  assumes "finite V"
  shows "aff_dim V \<le> of_nat (card V) - 1"
  by (metis aff_dim_inner_basis_exists assms card_mono le_diff_eq of_nat_le_iff)

lemma aff_dim_parallel_le:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S \<le> aff_dim T"
proof (cases "S={} \<or> T={}")
  case True
  then show ?thesis
    by (smt (verit, best) aff_dim_affine_hull2 affine_hull_empty affine_parallel_def assms empty_is_image)
next
  case False
    then obtain L where L: "subspace L" "affine_parallel (affine hull T) L"
      by (metis affine_affine_hull affine_hull_eq_empty affine_parallel_subspace)
    with False show ?thesis
      by (metis aff_dim_parallel_subspace affine_parallel_assoc assms dual_order.refl)
qed

lemma aff_dim_parallel_eq:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S = aff_dim T"
  by (smt (verit, del_insts) aff_dim_parallel_le affine_parallel_commute assms)

lemma aff_dim_translation_eq:
  "aff_dim ((+) a ` S) = aff_dim S" for a :: "'n::euclidean_space"
  by (metis aff_dim_parallel_eq affine_hull_translation affine_parallel_def)

lemma aff_dim_translation_eq_subtract:
  "aff_dim ((\<lambda>x. x - a) ` S) = aff_dim S" for a :: "'n::euclidean_space"
  using aff_dim_translation_eq [of "- a"] by (simp cong: image_cong_simp)

lemma aff_dim_affine:
  fixes S L :: "'n::euclidean_space set"
  assumes "affine S" "subspace L" "affine_parallel S L" "S \<noteq> {}"
  shows "aff_dim S = int (dim L)"
  by (simp add: aff_dim_parallel_subspace assms hull_same)

lemma dim_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "dim (affine hull S) = dim S"
  by (metis affine_hull_subset_span dim_eq_span dim_mono hull_subset span_eq_dim)

lemma aff_dim_subspace:
  fixes S :: "'n::euclidean_space set"
  assumes "subspace S"
  shows "aff_dim S = int (dim S)"
  by (metis aff_dim_affine affine_parallel_subspace assms empty_iff parallel_subspace subspace_affine)

lemma aff_dim_zero:
  fixes S :: "'n::euclidean_space set"
  assumes "0 \<in> affine hull S"
  shows "aff_dim S = int (dim S)"
  by (metis aff_dim_affine_hull aff_dim_subspace affine_hull_span_0 assms dim_span subspace_span)

lemma aff_dim_eq_dim:
  fixes S :: "'n::euclidean_space set"
  assumes "a \<in> affine hull S"
  shows "aff_dim S = int (dim ((+) (- a) ` S))" 
  by (metis ab_left_minus aff_dim_translation_eq aff_dim_zero affine_hull_translation image_eqI assms)

lemma aff_dim_eq_dim_subtract:
  fixes S :: "'n::euclidean_space set"
  assumes "a \<in> affine hull S"
  shows "aff_dim S = int (dim ((\<lambda>x. x - a) ` S))"
  using aff_dim_eq_dim assms by auto

lemma aff_dim_UNIV [simp]: "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
  by (simp add: aff_dim_subspace)

lemma aff_dim_geq:
  fixes V :: "'n::euclidean_space set"
  shows "aff_dim V \<ge> -1"
  by (metis add_le_cancel_right aff_dim_basis_exists diff_self of_nat_0_le_iff uminus_add_conv_diff)

lemma aff_dim_negative_iff [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S < 0 \<longleftrightarrow> S = {}"
  by (metis aff_dim_empty aff_dim_geq diff_0 eq_iff zle_diff1_eq)

lemma aff_lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "aff_dim S < DIM('a)"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
proof (cases "S={}")
  case True
  moreover
  have "(SOME b. b \<in> Basis) \<noteq> 0"
    by (metis norm_some_Basis norm_zero zero_neq_one)
  ultimately show ?thesis
    using that by blast
next
  case False
  then obtain c S' where "c \<notin> S'" "S = insert c S'"
    by (meson equals0I mk_disjoint_insert)
  have "dim ((+) (-c) ` S) < DIM('a)"
    by (metis \<open>S = insert c S'\<close> aff_dim_eq_dim assms hull_inc insertI1 of_nat_less_imp_less)
  then obtain a where "a \<noteq> 0" "span ((+) (-c) ` S) \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane by blast
  moreover
  have "a \<bullet> w = a \<bullet> c" if "span ((+) (- c) ` S) \<subseteq> {x. a \<bullet> x = 0}" "w \<in> S" for w
  proof -
    have "w-c \<in> span ((+) (- c) ` S)"
      by (simp add: span_base \<open>w \<in> S\<close>)
    with that have "w-c \<in> {x. a \<bullet> x = 0}"
      by blast
    then show ?thesis
      by (auto simp: algebra_simps)
  qed
  ultimately have "S \<subseteq> {x. a \<bullet> x = a \<bullet> c}"
    by blast
  then show ?thesis
    by (rule that[OF \<open>a \<noteq> 0\<close>])
qed

lemma affine_independent_card_dim_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "\<not> affine_dependent S" "a \<in> S"
    shows "card S = dim ((\<lambda>x. x - a) ` S) + 1"
  using aff_dim_affine_independent aff_dim_eq_dim_subtract assms hull_subset by fastforce

lemma independent_card_le_aff_dim:
  fixes B :: "'n::euclidean_space set"
  assumes "B \<subseteq> V"
  assumes "\<not> affine_dependent B"
  shows "int (card B) \<le> aff_dim V + 1"
  by (metis aff_dim_unique aff_independent_finite assms card_mono extend_to_affine_basis of_nat_mono)

lemma aff_dim_subset:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
  shows "aff_dim S \<le> aff_dim T"
  by (metis add_le_cancel_right aff_dim_inner_basis_exists assms dual_order.trans independent_card_le_aff_dim)

lemma aff_dim_le_DIM:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S \<le> int (DIM('n))"
  by (metis aff_dim_UNIV aff_dim_subset top_greatest)

lemma affine_dim_equal:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S" "affine T" "S \<noteq> {}" "S \<subseteq> T" "aff_dim S = aff_dim T"
  shows "S = T"
proof -
  obtain a where "a \<in> S" "a \<in> T" "T \<noteq> {}" using assms by auto
  define LS where "LS = {y. \<exists>x \<in> S. (-a) + x = y}"
  then have ls: "subspace LS" "affine_parallel S LS"
    using assms parallel_subspace_explicit[of S a LS] \<open>a \<in> S\<close> by auto
  then have h1: "int(dim LS) = aff_dim S"
    using assms aff_dim_affine[of S LS] by auto
  define LT where "LT = {y. \<exists>x \<in> T. (-a) + x = y}"
  then have lt: "subspace LT \<and> affine_parallel T LT"
    using assms parallel_subspace_explicit[of T a LT] \<open>a \<in> T\<close> by auto
  then have "dim LS = dim LT"
    using assms aff_dim_affine[of T LT] \<open>T \<noteq> {}\<close>  h1 by auto
  moreover have "LS \<le> LT"
    using LS_def LT_def assms by auto
  ultimately have "LS = LT"
    using subspace_dim_equal[of LS LT] ls lt by auto
  moreover have "S = {x. \<exists>y \<in> LS. a+y=x}" "T = {x. \<exists>y \<in> LT. a+y=x}"
    using LS_def LT_def by auto
  ultimately show ?thesis by auto
qed

lemma aff_dim_eq_0:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = 0 \<longleftrightarrow> (\<exists>a. S = {a})"
proof (cases "S = {}")
  case False
  then obtain a where "a \<in> S" by auto
  show ?thesis
  proof safe
    assume 0: "aff_dim S = 0"
    have "\<not> {a,b} \<subseteq> S" if "b \<noteq> a" for b
      by (metis "0" aff_dim_2 aff_dim_subset not_one_le_zero that)
    then show "\<exists>a. S = {a}"
      using \<open>a \<in> S\<close> by blast
  qed auto
qed auto

lemma affine_hull_UNIV:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "affine hull S = (UNIV :: ('n::euclidean_space) set)"
  by (simp add: aff_dim_empty affine_dim_equal assms)

lemma disjoint_affine_hull:
  fixes S :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent S" "T \<subseteq> S" "U \<subseteq> S" "T \<inter> U = {}"
    shows "(affine hull T) \<inter> (affine hull U) = {}"
proof -
  obtain "finite S" "finite T" "finite U"
    using assms by (simp add: aff_independent_finite finite_subset)
  have False if "y \<in> affine hull T" and "y \<in> affine hull U" for y
  proof -
    from that obtain a b
      where a1 [simp]: "sum a T = 1"
        and [simp]: "sum (\<lambda>v. a v *\<^sub>R v) T = y"
        and [simp]: "sum b U = 1" "sum (\<lambda>v. b v *\<^sub>R v) U = y"
      by (auto simp: affine_hull_finite \<open>finite T\<close> \<open>finite U\<close>)
    define c where "c x = (if x \<in> T then a x else if x \<in> U then -(b x) else 0)" for x
    have [simp]: "S \<inter> T = T" "S \<inter> - T \<inter> U = U"
      using assms by auto
    have "sum c S = 0"
      by (simp add: c_def comm_monoid_add_class.sum.If_cases \<open>finite S\<close> sum_negf)
    moreover have "\<not> (\<forall>v\<in>S. c v = 0)"
      by (metis (no_types) IntD1 \<open>S \<inter> T = T\<close> a1 c_def sum.neutral zero_neq_one)
    moreover have "(\<Sum>v\<in>S. c v *\<^sub>R v) = 0"
      by (simp add: c_def if_smult sum_negf comm_monoid_add_class.sum.If_cases \<open>finite S\<close>)
    ultimately show ?thesis
      using assms(1) \<open>finite S\<close> by (auto simp: affine_dependent_explicit)
  qed
  then show ?thesis by blast
qed

end