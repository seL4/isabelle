section "Affine Sets"

theory Affine
imports Linear_Algebra
begin

lemma if_smult: "(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)"
  by (fact if_distrib)

lemma sum_delta_notmem:
  assumes "x \<notin> s"
  shows "sum (\<lambda>y. if (y = x) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (y = x) then P y else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P y else Q y) s = sum Q s"
  apply (rule_tac [!] sum.cong)
  using assms
  apply auto
  done

lemmas independent_finite = independent_imp_finite

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
    using independent_card_le_dim[of d "span d"] independent_substdbasis[OF assms]
      span_superset[of d]
    by auto
  moreover from * have "dim ?B \<le> dim (span d)"
    using dim_substandard[OF assms] by auto
  ultimately show ?thesis
    using s subspace_dim_equal[of "span d" "?B"] subspace_span[of d] by auto
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
  from ex_card[OF this] obtain d :: "'a set" where d: "d \<subseteq> Basis" and t: "card d = dim B"
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
  where "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma affine_alt: "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)"
  unfolding affine_def by (metis eq_diff_eq')

lemma affine_empty [iff]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing [iff]: "affine {x}"
  unfolding affine_alt by (auto simp: scaleR_left_distrib [symmetric])

lemma affine_UNIV [iff]: "affine UNIV"
  unfolding affine_def by auto

lemma affine_Inter [intro]: "(\<And>s. s\<in>f \<Longrightarrow> affine s) \<Longrightarrow> affine (\<Inter>f)"
  unfolding affine_def by auto

lemma affine_Int[intro]: "affine s \<Longrightarrow> affine t \<Longrightarrow> affine (s \<inter> t)"
  unfolding affine_def by auto

lemma affine_scaling: "affine s \<Longrightarrow> affine (image (\<lambda>x. c *\<^sub>R x) s)"
  apply (clarsimp simp add: affine_def)
  apply (rule_tac x="u *\<^sub>R x + v *\<^sub>R y" in image_eqI)
  apply (auto simp: algebra_simps)
  done

lemma affine_affine_hull [simp]: "affine(affine hull s)"
  unfolding hull_def
  using affine_Inter[of "{t. affine t \<and> s \<subseteq> t}"] by auto

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
  shows "affine hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c| u v w. u + v + w = 1}"
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  show ?thesis
    apply (simp add: affine_hull_finite affine_hull_finite_step)
    unfolding *
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

lemma affine_parallel_commut:
  assumes "affine_parallel A B"
  shows "affine_parallel B A"
proof -
  from assms obtain a where B: "B = (\<lambda>x. a + x) ` A"
    unfolding affine_parallel_def by auto
  have [simp]: "(\<lambda>x. x - a) = plus (- a)" by (simp add: fun_eq_iff)
  from B show ?thesis
    using translation_galois [of B a A]
    unfolding affine_parallel_def by blast
qed

lemma affine_parallel_assoc:
  assumes "affine_parallel A B"
    and "affine_parallel B C"
  shows "affine_parallel A C"
proof -
  from assms obtain ab where "B = (\<lambda>x. ab + x) ` A"
    unfolding affine_parallel_def by auto
  moreover
  from assms obtain bc where "C = (\<lambda>x. bc + x) ` B"
    unfolding affine_parallel_def by auto
  ultimately show ?thesis
    using translation_assoc[of bc ab A] unfolding affine_parallel_def by auto
qed

lemma affine_translation_aux:
  fixes a :: "'a::real_vector"
  assumes "affine ((\<lambda>x. a + x) ` S)"
  shows "affine S"
proof -
  {
    fix x y u v
    assume xy: "x \<in> S" "y \<in> S" "(u :: real) + v = 1"
    then have "(a + x) \<in> ((\<lambda>x. a + x) ` S)" "(a + y) \<in> ((\<lambda>x. a + x) ` S)"
      by auto
    then have h1: "u *\<^sub>R  (a + x) + v *\<^sub>R (a + y) \<in> (\<lambda>x. a + x) ` S"
      using xy assms unfolding affine_def by auto
    have "u *\<^sub>R (a + x) + v *\<^sub>R (a + y) = (u + v) *\<^sub>R a + (u *\<^sub>R x + v *\<^sub>R y)"
      by (simp add: algebra_simps)
    also have "\<dots> = a + (u *\<^sub>R x + v *\<^sub>R y)"
      using \<open>u + v = 1\<close> by auto
    ultimately have "a + (u *\<^sub>R x + v *\<^sub>R y) \<in> (\<lambda>x. a + x) ` S"
      using h1 by auto
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> S" by auto
  }
  then show ?thesis unfolding affine_def by auto
qed

lemma affine_translation:
  "affine S \<longleftrightarrow> affine ((+) a ` S)" for a :: "'a::real_vector"
proof
  show "affine ((+) a ` S)" if "affine S"
    using that translation_assoc [of "- a" a S]
    by (auto intro: affine_translation_aux [of "- a" "((+) a ` S)"])
  show "affine S" if "affine ((+) a ` S)"
    using that by (rule affine_translation_aux)
qed

lemma parallel_is_affine:
  fixes S T :: "'a::real_vector set"
  assumes "affine S" "affine_parallel S T"
  shows "affine T"
proof -
  from assms obtain a where "T = (\<lambda>x. a + x) ` S"
    unfolding affine_parallel_def by auto
  then show ?thesis
    using affine_translation assms by auto
qed

lemma subspace_imp_affine: "subspace s \<Longrightarrow> affine s"
  unfolding subspace_def affine_def by auto

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_superset subspace_imp_affine subspace_span)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Subspace parallel to an affine set\<close>

lemma subspace_affine: "subspace S \<longleftrightarrow> affine S \<and> 0 \<in> S"
proof -
  have h0: "subspace S \<Longrightarrow> affine S \<and> 0 \<in> S"
    using subspace_imp_affine[of S] subspace_0 by auto
  {
    assume assm: "affine S \<and> 0 \<in> S"
    {
      fix c :: real
      fix x
      assume x: "x \<in> S"
      have "c *\<^sub>R x = (1-c) *\<^sub>R 0 + c *\<^sub>R x" by auto
      moreover
      have "(1 - c) *\<^sub>R 0 + c *\<^sub>R x \<in> S"
        using affine_alt[of S] assm x by auto
      ultimately have "c *\<^sub>R x \<in> S" by auto
    }
    then have h1: "\<forall>c. \<forall>x \<in> S. c *\<^sub>R x \<in> S" by auto

    {
      fix x y
      assume xy: "x \<in> S" "y \<in> S"
      define u where "u = (1 :: real)/2"
      have "(1/2) *\<^sub>R (x+y) = (1/2) *\<^sub>R (x+y)"
        by auto
      moreover
      have "(1/2) *\<^sub>R (x+y)=(1/2) *\<^sub>R x + (1-(1/2)) *\<^sub>R y"
        by (simp add: algebra_simps)
      moreover
      have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> S"
        using affine_alt[of S] assm xy by auto
      ultimately
      have "(1/2) *\<^sub>R (x+y) \<in> S"
        using u_def by auto
      moreover
      have "x + y = 2 *\<^sub>R ((1/2) *\<^sub>R (x+y))"
        by auto
      ultimately
      have "x + y \<in> S"
        using h1[rule_format, of "(1/2) *\<^sub>R (x+y)" "2"] by auto
    }
    then have "\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S"
      by auto
    then have "subspace S"
      using h1 assm unfolding subspace_def by auto
  }
  then show ?thesis using h0 by metis
qed

lemma affine_diffs_subspace:
  assumes "affine S" "a \<in> S"
  shows "subspace ((\<lambda>x. (-a)+x) ` S)"
proof -
  have [simp]: "(\<lambda>x. x - a) = plus (- a)" by (simp add: fun_eq_iff)
  have "affine ((\<lambda>x. (-a)+x) ` S)"
    using affine_translation assms by blast
  moreover have "0 \<in> ((\<lambda>x. (-a)+x) ` S)"
    using assms exI[of "(\<lambda>x. x\<in>S \<and> -a+x = 0)" a] by auto
  ultimately show ?thesis using subspace_affine by auto
qed

lemma affine_diffs_subspace_subtract:
  "subspace ((\<lambda>x. x - a) ` S)" if "affine S" "a \<in> S"
  using that affine_diffs_subspace [of _ a] by simp

lemma parallel_subspace_explicit:
  assumes "affine S"
    and "a \<in> S"
  assumes "L \<equiv> {y. \<exists>x \<in> S. (-a) + x = y}"
  shows "subspace L \<and> affine_parallel S L"
proof -
  from assms have "L = plus (- a) ` S" by auto
  then have par: "affine_parallel S L"
    unfolding affine_parallel_def ..
  then have "affine L" using assms parallel_is_affine by auto
  moreover have "0 \<in> L"
    using assms by auto
  ultimately show ?thesis
    using subspace_affine par by auto
qed

lemma parallel_subspace_aux:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A \<supseteq> B"
proof -
  from assms obtain a where a: "\<forall>x. x \<in> A \<longleftrightarrow> a + x \<in> B"
    using affine_parallel_expl[of A B] by auto
  then have "-a \<in> A"
    using assms subspace_0[of B] by auto
  then have "a \<in> A"
    using assms subspace_neg[of A "-a"] by auto
  then show ?thesis
    using assms a unfolding subspace_def by auto
qed

lemma parallel_subspace:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A = B"
proof
  show "A \<supseteq> B"
    using assms parallel_subspace_aux by auto
  show "A \<subseteq> B"
    using assms parallel_subspace_aux[of B A] affine_parallel_commut by auto
qed

lemma affine_parallel_subspace:
  assumes "affine S" "S \<noteq> {}"
  shows "\<exists>!L. subspace L \<and> affine_parallel S L"
proof -
  have ex: "\<exists>L. subspace L \<and> affine_parallel S L"
    using assms parallel_subspace_explicit by auto
  {
    fix L1 L2
    assume ass: "subspace L1 \<and> affine_parallel S L1" "subspace L2 \<and> affine_parallel S L2"
    then have "affine_parallel L1 L2"
      using affine_parallel_commut[of S L1] affine_parallel_assoc[of L1 S L2] by auto
    then have "L1 = L2"
      using ass parallel_subspace by auto
  }
  then show ?thesis using ex by auto
qed


subsection \<open>Affine Dependence\<close>

text "Formalized by Lars Schewe."

definition\<^marker>\<open>tag important\<close> affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent s \<longleftrightarrow> (\<exists>x\<in>s. x \<in> affine hull (s - {x}))"

lemma affine_dependent_imp_dependent: "affine_dependent s \<Longrightarrow> dependent s"
  unfolding affine_dependent_def dependent_def
  using affine_hull_subset_span by auto

lemma affine_dependent_subset:
   "\<lbrakk>affine_dependent s; s \<subseteq> t\<rbrakk> \<Longrightarrow> affine_dependent t"
apply (simp add: affine_dependent_def Bex_def)
apply (blast dest: hull_mono [OF Diff_mono [OF _ subset_refl]])
done

lemma affine_independent_subset:
  shows "\<lbrakk>\<not> affine_dependent t; s \<subseteq> t\<rbrakk> \<Longrightarrow> \<not> affine_dependent s"
by (metis affine_dependent_subset)

lemma affine_independent_Diff:
   "\<not> affine_dependent s \<Longrightarrow> \<not> affine_dependent(s - t)"
by (meson Diff_subset affine_dependent_subset)

proposition affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>S u. finite S \<and> S \<subseteq> p \<and> sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) S = 0)"
proof -
  have "\<exists>S u. finite S \<and> S \<subseteq> p \<and> sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> (\<Sum>w\<in>S. u w *\<^sub>R w) = 0"
    if "(\<Sum>w\<in>S. u w *\<^sub>R w) = x" "x \<in> p" "finite S" "S \<noteq> {}" "S \<subseteq> p - {x}" "sum u S = 1" for x S u
  proof (intro exI conjI)
    have "x \<notin> S" 
      using that by auto
    then show "(\<Sum>v \<in> insert x S. if v = x then - 1 else u v) = 0"
      using that by (simp add: sum_delta_notmem)
    show "(\<Sum>w \<in> insert x S. (if w = x then - 1 else u w) *\<^sub>R w) = 0"
      using that \<open>x \<notin> S\<close> by (simp add: if_smult sum_delta_notmem cong: if_cong)
  qed (use that in auto)
  moreover have "\<exists>x\<in>p. \<exists>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p - {x} \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = x"
    if "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0" "finite S" "S \<subseteq> p" "sum u S = 0" "v \<in> S" "u v \<noteq> 0" for S u v
  proof (intro bexI exI conjI)
    have "S \<noteq> {v}"
      using that by auto
    then show "S - {v} \<noteq> {}"
      using that by auto
    show "(\<Sum>x \<in> S - {v}. - (1 / u v) * u x) = 1"
      unfolding sum_distrib_left[symmetric] sum_diff1[OF \<open>finite S\<close>] by (simp add: that)
    show "(\<Sum>x\<in>S - {v}. (- (1 / u v) * u x) *\<^sub>R x) = v"
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
    (\<exists>u. sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) S = 0)"
  (is "?lhs = ?rhs")
proof
  have *: "\<And>vt u v. (if vt then u v else 0) *\<^sub>R v = (if vt then (u v) *\<^sub>R v else 0::'a)"
    by auto
  assume ?lhs
  then obtain t u v where
    "finite t" "t \<subseteq> S" "sum u t = 0" "v\<in>t" "u v \<noteq> 0"  "(\<Sum>v\<in>t. u v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  then show ?rhs
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    apply (auto simp: * sum.inter_restrict[OF assms, symmetric] Int_absorb1[OF \<open>t\<subseteq>S\<close>])
    done
next
  assume ?rhs
  then obtain u v where "sum u S = 0"  "v\<in>S" "u v \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    by auto
  then show ?lhs unfolding affine_dependent_explicit
    using assms by auto
qed

lemma dependent_imp_affine_dependent:
  assumes "dependent {x - a| x . x \<in> s}"
    and "a \<notin> s"
  shows "affine_dependent (insert a s)"
proof -
  from assms(1)[unfolded dependent_explicit] obtain S u v
    where obt: "finite S" "S \<subseteq> {x - a |x. x \<in> s}" "v\<in>S" "u v  \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    by auto
  define t where "t = (\<lambda>x. x + a) ` S"

  have inj: "inj_on (\<lambda>x. x + a) S"
    unfolding inj_on_def by auto
  have "0 \<notin> S"
    using obt(2) assms(2) unfolding subset_eq by auto
  have fin: "finite t" and "t \<subseteq> s"
    unfolding t_def using obt(1,2) by auto
  then have "finite (insert a t)" and "insert a t \<subseteq> insert a s"
    by auto
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x)) = (\<Sum>x\<in>t. Q x)"
    apply (rule sum.cong)
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    apply auto
    done
  have "(\<Sum>x\<in>insert a t. if x = a then - (\<Sum>x\<in>t. u (x - a)) else u (x - a)) = 0"
    unfolding sum_clauses(2)[OF fin] * using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close> by auto
  moreover have "\<exists>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) \<noteq> 0"
    using obt(3,4) \<open>0\<notin>S\<close>
    by (rule_tac x="v + a" in bexI) (auto simp: t_def)
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>t. Q x *\<^sub>R x)"
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close> by (auto intro!: sum.cong)
  have "(\<Sum>x\<in>t. u (x - a)) *\<^sub>R a = (\<Sum>v\<in>t. u (v - a) *\<^sub>R v)"
    unfolding scaleR_left.sum
    unfolding t_def and sum.reindex[OF inj] and o_def
    using obt(5)
    by (auto simp: sum.distrib scaleR_right_distrib)
  then have "(\<Sum>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) *\<^sub>R v) = 0"
    unfolding sum_clauses(2)[OF fin]
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    by (auto simp: *)
  ultimately show ?thesis
    unfolding affine_dependent_explicit
    apply (rule_tac x="insert a t" in exI, auto)
    done
qed

lemma affine_dependent_biggerset:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<ge> DIM('a) + 2"
  shows "affine_dependent s"
proof -
  have "s \<noteq> {}" using assms by auto
  then obtain a where "a\<in>s" by auto
  have *: "{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})"
    by auto
  have "card {x - a |x. x \<in> s - {a}} = card (s - {a})"
    unfolding * by (simp add: card_image inj_on_def)
  also have "\<dots> > DIM('a)" using assms(2)
    unfolding card_Diff_singleton[OF \<open>a\<in>s\<close>] by auto
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>s\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset, auto)
    done
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
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>S\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset_general)
    unfolding **
    apply auto
    done
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
proof -
  {
    assume "affine_dependent ((\<lambda>x. a + x) ` S)"
    then have "affine_dependent S"
      using affine_dependent_translation[of "((\<lambda>x. a + x) ` S)" "-a"] translation_assoc[of "-a" a]
      by auto
  }
  then show ?thesis
    using affine_dependent_translation by auto
qed

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
  moreover
  {
    assume "x = 0"
    then have "0 \<in> affine hull S"
      using x hull_mono[of "S - {0}" S] by auto
    then have "dependent S"
      using affine_hull_0_dependent by auto
  }
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
proof -
  have "insert a (S - {a}) = S"
    using assms by auto
  then show ?thesis
    using assms affine_dependent_iff_dependent[of a "S-{a}"] by auto
qed

lemma affine_hull_insert_span_gen:
  "affine hull (insert a s) = (\<lambda>x. a + x) ` span ((\<lambda>x. - a + x) ` s)"
proof -
  have h1: "{x - a |x. x \<in> s} = ((\<lambda>x. -a+x) ` s)"
    by auto
  {
    assume "a \<notin> s"
    then have ?thesis
      using affine_hull_insert_span[of a s] h1 by auto
  }
  moreover
  {
    assume a1: "a \<in> s"
    have "\<exists>x. x \<in> s \<and> -a+x=0"
      apply (rule exI[of _ a])
      using a1
      apply auto
      done
    then have "insert 0 ((\<lambda>x. -a+x) ` (s - {a})) = (\<lambda>x. -a+x) ` s"
      by auto
    then have "span ((\<lambda>x. -a+x) ` (s - {a}))=span ((\<lambda>x. -a+x) ` s)"
      using span_insert_0[of "(+) (- a) ` (s - {a})"] by (auto simp del: uminus_add_conv_diff)
    moreover have "{x - a |x. x \<in> (s - {a})} = ((\<lambda>x. -a+x) ` (s - {a}))"
      by auto
    moreover have "insert a (s - {a}) = insert a s"
      by auto
    ultimately have ?thesis
      using affine_hull_insert_span[of "a" "s-{a}"] by auto
  }
  ultimately show ?thesis by auto
qed

lemma affine_hull_span2:
  assumes "a \<in> s"
  shows "affine hull s = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` (s-{a}))"
  using affine_hull_insert_span_gen[of a "s - {a}", unfolded insert_Diff[OF assms]]
  by auto

lemma affine_hull_span_gen:
  assumes "a \<in> affine hull s"
  shows "affine hull s = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` s)"
proof -
  have "affine hull (insert a s) = affine hull s"
    using hull_redundant[of a affine s] assms by auto
  then show ?thesis
    using affine_hull_insert_span_gen[of a "s"] by auto
qed

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
proof (cases "V = {}")
  case True
  then show ?thesis
    using affine_independent_0 by auto
next
  case False
  then obtain x where "x \<in> V" by auto
  then show ?thesis
    using affine_dependent_def[of "{x}"] extend_to_affine_basis_nonempty[of "{x}" V]
    by auto
qed

proposition extend_to_affine_basis:
  fixes S V :: "'n::real_vector set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V"
  obtains T where "\<not> affine_dependent T" "S \<subseteq> T" "T \<subseteq> V" "affine hull T = affine hull V"
proof (cases "S = {}")
  case True then show ?thesis
    using affine_basis_exists by (metis empty_subsetI that)
next
  case False
  then show ?thesis by (metis assms extend_to_affine_basis_nonempty that)
qed


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
      affine_parallel_commut[of "Lb" "(affine hull B)"]
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
proof -
  {
    assume "B \<noteq> {}"
    then obtain a where "a \<in> B" by auto
    then have ?thesis
      using aff_dim_parallel_subspace_aux assms by auto
  }
  then show ?thesis by auto
qed


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
  by (simp add: aff_dim_empty [symmetric])

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
      affine_parallel_commut[of "Lb" "(affine hull B)"]
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
    fixes s :: "'a::euclidean_space set"
    shows "\<not> affine_dependent s \<longleftrightarrow> finite s \<and> aff_dim s = int(card s) - 1"
  apply (rule iffI)
  apply (simp add: aff_dim_affine_independent aff_independent_finite)
  by (metis affine_basis_exists [of s] aff_dim_unique card_subset_eq diff_add_cancel of_nat_eq_iff)

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
proof -
  obtain B where B: "\<not> affine_dependent B" "B \<subseteq> V" "affine hull B = affine hull V"
    using affine_basis_exists[of V] by auto
  then have "of_nat(card B) = aff_dim V+1" using aff_dim_unique by auto
  with B show ?thesis by auto
qed

lemma aff_dim_le_card:
  fixes V :: "'n::euclidean_space set"
  assumes "finite V"
  shows "aff_dim V \<le> of_nat (card V) - 1"
proof -
  obtain B where B: "B \<subseteq> V" "of_nat (card B) = aff_dim V + 1"
    using aff_dim_inner_basis_exists[of V] by auto
  then have "card B \<le> card V"
    using assms card_mono by auto
  with B show ?thesis by auto
qed

lemma aff_dim_parallel_eq:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S = aff_dim T"
proof -
  {
    assume "T \<noteq> {}" "S \<noteq> {}"
    then obtain L where L: "subspace L \<and> affine_parallel (affine hull T) L"
      using affine_parallel_subspace[of "affine hull T"]
        affine_affine_hull[of T]
      by auto
    then have "aff_dim T = int (dim L)"
      using aff_dim_parallel_subspace \<open>T \<noteq> {}\<close> by auto
    moreover have *: "subspace L \<and> affine_parallel (affine hull S) L"
       using L affine_parallel_assoc[of "affine hull S" "affine hull T" L] assms by auto
    moreover from * have "aff_dim S = int (dim L)"
      using aff_dim_parallel_subspace \<open>S \<noteq> {}\<close> by auto
    ultimately have ?thesis by auto
  }
  moreover
  {
    assume "S = {}"
    then have "S = {}" and "T = {}"
      using assms
      unfolding affine_parallel_def
      by auto
    then have ?thesis using aff_dim_empty by auto
  }
  moreover
  {
    assume "T = {}"
    then have "S = {}" and "T = {}"
      using assms
      unfolding affine_parallel_def
      by auto
    then have ?thesis
      using aff_dim_empty by auto
  }
  ultimately show ?thesis by blast
qed

lemma aff_dim_translation_eq:
  "aff_dim ((+) a ` S) = aff_dim S" for a :: "'n::euclidean_space"
proof -
  have "affine_parallel (affine hull S) (affine hull ((\<lambda>x. a + x) ` S))"
    unfolding affine_parallel_def
    apply (rule exI[of _ "a"])
    using affine_hull_translation[of a S]
    apply auto
    done
  then show ?thesis
    using aff_dim_parallel_eq[of S "(\<lambda>x. a + x) ` S"] by auto
qed

lemma aff_dim_translation_eq_subtract:
  "aff_dim ((\<lambda>x. x - a) ` S) = aff_dim S" for a :: "'n::euclidean_space"
  using aff_dim_translation_eq [of "- a"] by (simp cong: image_cong_simp)

lemma aff_dim_affine:
  fixes S L :: "'n::euclidean_space set"
  assumes "S \<noteq> {}"
    and "affine S"
    and "subspace L"
    and "affine_parallel S L"
  shows "aff_dim S = int (dim L)"
proof -
  have *: "affine hull S = S"
    using assms affine_hull_eq[of S] by auto
  then have "affine_parallel (affine hull S) L"
    using assms by (simp add: *)
  then show ?thesis
    using assms aff_dim_parallel_subspace[of S L] by blast
qed

lemma dim_affine_hull:
  fixes S :: "'n::euclidean_space set"
  shows "dim (affine hull S) = dim S"
proof -
  have "dim (affine hull S) \<ge> dim S"
    using dim_subset by auto
  moreover have "dim (span S) \<ge> dim (affine hull S)"
    using dim_subset affine_hull_subset_span by blast
  moreover have "dim (span S) = dim S"
    using dim_span by auto
  ultimately show ?thesis by auto
qed

lemma aff_dim_subspace:
  fixes S :: "'n::euclidean_space set"
  assumes "subspace S"
  shows "aff_dim S = int (dim S)"
proof (cases "S={}")
  case True with assms show ?thesis
    by (simp add: subspace_affine)
next
  case False
  with aff_dim_affine[of S S] assms subspace_imp_affine[of S] affine_parallel_reflex[of S] subspace_affine
  show ?thesis by auto
qed

lemma aff_dim_zero:
  fixes S :: "'n::euclidean_space set"
  assumes "0 \<in> affine hull S"
  shows "aff_dim S = int (dim S)"
proof -
  have "subspace (affine hull S)"
    using subspace_affine[of "affine hull S"] affine_affine_hull assms
    by auto
  then have "aff_dim (affine hull S) = int (dim (affine hull S))"
    using assms aff_dim_subspace[of "affine hull S"] by auto
  then show ?thesis
    using aff_dim_affine_hull[of S] dim_affine_hull[of S]
    by auto
qed

lemma aff_dim_eq_dim:
  "aff_dim S = int (dim ((+) (- a) ` S))" if "a \<in> affine hull S"
    for S :: "'n::euclidean_space set"
proof -
  have "0 \<in> affine hull (+) (- a) ` S"
    unfolding affine_hull_translation
    using that by (simp add: ac_simps)
  with aff_dim_zero show ?thesis
    by (metis aff_dim_translation_eq)
qed

lemma aff_dim_eq_dim_subtract:
  "aff_dim S = int (dim ((\<lambda>x. x - a) ` S))" if "a \<in> affine hull S"
    for S :: "'n::euclidean_space set"
  using aff_dim_eq_dim [of a] that by (simp cong: image_cong_simp)

lemma aff_dim_UNIV [simp]: "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
  using aff_dim_subspace[of "(UNIV :: 'n::euclidean_space set)"]
    dim_UNIV[where 'a="'n::euclidean_space"]
  by auto

lemma aff_dim_geq:
  fixes V :: "'n::euclidean_space set"
  shows "aff_dim V \<ge> -1"
proof -
  obtain B where "affine hull B = affine hull V"
    and "\<not> affine_dependent B"
    and "int (card B) = aff_dim V + 1"
    using aff_dim_basis_exists by auto
  then show ?thesis by auto
qed

lemma aff_dim_negative_iff [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S < 0 \<longleftrightarrow>S = {}"
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
proof -
  have non: "\<not> affine_dependent (insert a S)"
    by (simp add: assms insert_absorb)
  have "finite S"
    by (meson assms aff_independent_finite)
  with \<open>a \<in> S\<close> have "card S \<noteq> 0" by auto
  moreover have "dim ((\<lambda>x. x - a) ` S) = card S - 1"
    using aff_dim_eq_dim_subtract aff_dim_unique \<open>a \<in> S\<close> hull_inc insert_absorb non by fastforce
  ultimately show ?thesis
    by auto
qed

lemma independent_card_le_aff_dim:
  fixes B :: "'n::euclidean_space set"
  assumes "B \<subseteq> V"
  assumes "\<not> affine_dependent B"
  shows "int (card B) \<le> aff_dim V + 1"
proof -
  obtain T where T: "\<not> affine_dependent T \<and> B \<subseteq> T \<and> T \<subseteq> V \<and> affine hull T = affine hull V"
    by (metis assms extend_to_affine_basis[of B V])
  then have "of_nat (card T) = aff_dim V + 1"
    using aff_dim_unique by auto
  then show ?thesis
    using T card_mono[of T B] aff_independent_finite[of T] by auto
qed

lemma aff_dim_subset:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
  shows "aff_dim S \<le> aff_dim T"
proof -
  obtain B where B: "\<not> affine_dependent B" "B \<subseteq> S" "affine hull B = affine hull S"
    "of_nat (card B) = aff_dim S + 1"
    using aff_dim_inner_basis_exists[of S] by auto
  then have "int (card B) \<le> aff_dim T + 1"
    using assms independent_card_le_aff_dim[of B T] by auto
  with B show ?thesis by auto
qed

lemma aff_dim_le_DIM:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S \<le> int (DIM('n))"
proof -
  have "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
    using aff_dim_UNIV by auto
  then show "aff_dim (S:: 'n::euclidean_space set) \<le> int(DIM('n))"
    using aff_dim_subset[of S "(UNIV :: ('n::euclidean_space) set)"] subset_UNIV by auto
qed

lemma affine_dim_equal:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S" "affine T" "S \<noteq> {}" "S \<subseteq> T" "aff_dim S = aff_dim T"
  shows "S = T"
proof -
  obtain a where "a \<in> S" using assms by auto
  then have "a \<in> T" using assms by auto
  define LS where "LS = {y. \<exists>x \<in> S. (-a) + x = y}"
  then have ls: "subspace LS" "affine_parallel S LS"
    using assms parallel_subspace_explicit[of S a LS] \<open>a \<in> S\<close> by auto
  then have h1: "int(dim LS) = aff_dim S"
    using assms aff_dim_affine[of S LS] by auto
  have "T \<noteq> {}" using assms by auto
  define LT where "LT = {y. \<exists>x \<in> T. (-a) + x = y}"
  then have lt: "subspace LT \<and> affine_parallel T LT"
    using assms parallel_subspace_explicit[of T a LT] \<open>a \<in> T\<close> by auto
  then have "int(dim LT) = aff_dim T"
    using assms aff_dim_affine[of T LT] \<open>T \<noteq> {}\<close> by auto
  then have "dim LS = dim LT"
    using h1 assms by auto
  moreover have "LS \<le> LT"
    using LS_def LT_def assms by auto
  ultimately have "LS = LT"
    using subspace_dim_equal[of LS LT] ls lt by auto
  moreover have "S = {x. \<exists>y \<in> LS. a+y=x}"
    using LS_def by auto
  moreover have "T = {x. \<exists>y \<in> LT. a+y=x}"
    using LT_def by auto
  ultimately show ?thesis by auto
qed

lemma aff_dim_eq_0:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = 0 \<longleftrightarrow> (\<exists>a. S = {a})"
proof (cases "S = {}")
  case True
  then show ?thesis
    by auto
next
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
qed

lemma affine_hull_UNIV:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "affine hull S = (UNIV :: ('n::euclidean_space) set)"
proof -
  have "S \<noteq> {}"
    using assms aff_dim_empty[of S] by auto
  have h0: "S \<subseteq> affine hull S"
    using hull_subset[of S _] by auto
  have h1: "aff_dim (UNIV :: ('n::euclidean_space) set) = aff_dim S"
    using aff_dim_UNIV assms by auto
  then have h2: "aff_dim (affine hull S) \<le> aff_dim (UNIV :: ('n::euclidean_space) set)"
    using aff_dim_le_DIM[of "affine hull S"] assms h0 by auto
  have h3: "aff_dim S \<le> aff_dim (affine hull S)"
    using h0 aff_dim_subset[of S "affine hull S"] assms by auto
  then have h4: "aff_dim (affine hull S) = aff_dim (UNIV :: ('n::euclidean_space) set)"
    using h0 h1 h2 by auto
  then show ?thesis
    using affine_dim_equal[of "affine hull S" "(UNIV :: ('n::euclidean_space) set)"]
      affine_affine_hull[of S] affine_UNIV assms h4 h0 \<open>S \<noteq> {}\<close>
    by auto
qed

lemma disjoint_affine_hull:
  fixes s :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent s" "t \<subseteq> s" "u \<subseteq> s" "t \<inter> u = {}"
    shows "(affine hull t) \<inter> (affine hull u) = {}"
proof -
  from assms(1) have "finite s"
    by (simp add: aff_independent_finite)
  with assms(2,3) have "finite t" "finite u"
    by (blast intro: finite_subset)+
  have False if "y \<in> affine hull t" and "y \<in> affine hull u" for y
  proof -
    from that obtain a b
      where a1 [simp]: "sum a t = 1"
        and [simp]: "sum (\<lambda>v. a v *\<^sub>R v) t = y"
        and [simp]: "sum b u = 1" "sum (\<lambda>v. b v *\<^sub>R v) u = y"
      by (auto simp: affine_hull_finite \<open>finite t\<close> \<open>finite u\<close>)
    define c where "c x = (if x \<in> t then a x else if x \<in> u then -(b x) else 0)" for x
    from assms(2,3,4) have [simp]: "s \<inter> t = t" "s \<inter> - t \<inter> u = u"
      by auto
    have "sum c s = 0"
      by (simp add: c_def comm_monoid_add_class.sum.If_cases \<open>finite s\<close> sum_negf)
    moreover have "\<not> (\<forall>v\<in>s. c v = 0)"
      by (metis (no_types) IntD1 \<open>s \<inter> t = t\<close> a1 c_def sum.neutral zero_neq_one)
    moreover have "(\<Sum>v\<in>s. c v *\<^sub>R v) = 0"
      by (simp add: c_def if_smult sum_negf comm_monoid_add_class.sum.If_cases \<open>finite s\<close>)
    ultimately show ?thesis
      using assms(1) \<open>finite s\<close> by (auto simp: affine_dependent_explicit)
  qed
  then show ?thesis by blast
qed

end