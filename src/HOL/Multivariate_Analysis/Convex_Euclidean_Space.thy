(*  Title:      HOL/Multivariate_Analysis/Convex_Euclidean_Space.thy
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Bogdan Grechuk, University of Edinburgh
*)

header {* Convex sets, functions and related things. *}

theory Convex_Euclidean_Space
imports
  Topology_Euclidean_Space
  "~~/src/HOL/Library/Convex"
  "~~/src/HOL/Library/Set_Algebras"
begin


(* ------------------------------------------------------------------------- *)
(* To be moved elsewhere                                                     *)
(* ------------------------------------------------------------------------- *)

lemma linear_scaleR: "linear (\<lambda>x. scaleR c x)"
  by (simp add: linear_def scaleR_add_right)

lemma injective_scaleR: "c \<noteq> 0 \<Longrightarrow> inj (\<lambda>(x::'a::real_vector). scaleR c x)"
  by (simp add: inj_on_def)

lemma linear_add_cmul:
  assumes "linear f"
  shows "f(a *\<^sub>R x + b *\<^sub>R y) = a *\<^sub>R f x +  b *\<^sub>R f y"
  using linear_add[of f] linear_cmul[of f] assms by simp

lemma mem_convex_2:
  assumes "convex S" "x : S" "y : S" "u>=0" "v>=0" "u+v=1"
  shows "(u *\<^sub>R x + v *\<^sub>R y) : S"
  using assms convex_def[of S] by auto

lemma mem_convex_alt:
  assumes "convex S" "x : S" "y : S" "u>=0" "v>=0" "u+v>0"
  shows "((u/(u+v)) *\<^sub>R x + (v/(u+v)) *\<^sub>R y) : S"
  apply (subst mem_convex_2)
  using assms
  apply (auto simp add: algebra_simps zero_le_divide_iff)
  using add_divide_distrib[of u v "u+v"]
  apply auto
  done

lemma inj_on_image_mem_iff: "inj_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f a \<in> f`A \<Longrightarrow> a \<in> B \<Longrightarrow> a \<in> A"
  by (blast dest: inj_onD)

lemma independent_injective_on_span_image:
  assumes iS: "independent S"
    and lf: "linear f"
    and fi: "inj_on f (span S)"
  shows "independent (f ` S)"
proof -
  {
    fix a
    assume a: "a : S" "f a : span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})"
      using fi a span_inc by (auto simp add: inj_on_def)
    from a have "f a : f ` span (S -{a})"
      unfolding eq span_linear_image[OF lf, of "S - {a}"] by blast
    moreover have "span (S -{a}) <= span S" using span_mono[of "S-{a}" S] by auto
    ultimately have "a : span (S -{a})" using fi a span_inc by (auto simp add: inj_on_def)
    with a(1) iS have False by (simp add: dependent_def)
  }
  then show ?thesis unfolding dependent_def by blast
qed

lemma dim_image_eq:
  fixes f :: "'n::euclidean_space => 'm::euclidean_space"
  assumes lf: "linear f" and fi: "inj_on f (span S)"
  shows "dim (f ` S) = dim (S:: ('n::euclidean_space) set)"
proof -
  obtain B where B_def: "B \<subseteq> S & independent B & S \<subseteq> span B & card B = dim S"
    using basis_exists[of S] by auto
  then have "span S = span B"
    using span_mono[of B S] span_mono[of S "span B"] span_span[of B] by auto
  then have "independent (f ` B)"
    using independent_injective_on_span_image[of B f] B_def assms by auto
  moreover have "card (f ` B) = card B"
    using assms card_image[of f B] subset_inj_on[of f "span S" B] B_def span_inc by auto
  moreover have "(f ` B) \<subseteq> (f ` S)" using B_def by auto
  ultimately have "dim (f ` S) \<ge> dim S"
    using independent_card_le_dim[of "f ` B" "f ` S"] B_def by auto
  then show ?thesis using dim_image_le[of f S] assms by auto
qed

lemma linear_injective_on_subspace_0:
  assumes lf: "linear f"
    and "subspace S"
  shows "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x = f y \<longrightarrow> x = y)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_sub[OF lf])
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
    using `subspace S` subspace_def[of S] subspace_sub[of S] by auto
  finally show ?thesis .
qed

lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (Inter f)"
  unfolding subspace_def by auto

lemma span_eq[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)

lemma substdbasis_expansion_unique:
  assumes d: "d \<subseteq> Basis"
  shows "(\<Sum>i\<in>d. f i *\<^sub>R i) = (x::'a::euclidean_space) \<longleftrightarrow>
    (\<forall>i\<in>Basis. (i \<in> d \<longrightarrow> f i = x \<bullet> i) \<and> (i \<notin> d \<longrightarrow> x \<bullet> i = 0))"
proof -
  have *: "\<And>x a b P. x * (if P then a else b) = (if P then x*a else x*b)"
    by auto
  have **: "finite d"
    by (auto intro: finite_subset[OF assms])
  have ***: "\<And>i. i \<in> Basis \<Longrightarrow> (\<Sum>i\<in>d. f i *\<^sub>R i) \<bullet> i = (\<Sum>x\<in>d. if x = i then f x else 0)"
    using d
    by (auto intro!: setsum_cong simp: inner_Basis inner_setsum_left)
  show ?thesis
    unfolding euclidean_eq_iff[where 'a='a] by (auto simp: setsum_delta[OF **] ***)
qed

lemma independent_substdbasis: "d \<subseteq> Basis \<Longrightarrow> independent d"
  by (rule independent_mono[OF independent_Basis])

lemma dim_cball:
  assumes "e > 0"
  shows "dim (cball (0 :: 'n::euclidean_space) e) = DIM('n)"
proof -
  {
    fix x :: "'n::euclidean_space"
    def y \<equiv> "(e / norm x) *\<^sub>R x"
    then have "y : cball 0 e"
      using cball_def dist_norm[of 0 y] assms by auto
    moreover have *: "x = (norm x/e) *\<^sub>R y"
      using y_def assms by simp
    moreover from * have "x = (norm x/e) *\<^sub>R y"
      by auto
    ultimately have "x : span (cball 0 e)"
      using span_mul[of y "cball 0 e" "norm x/e"] span_inc[of "cball 0 e"] by auto
  }
  then have "span (cball 0 e) = (UNIV :: ('n::euclidean_space) set)"
    by auto
  then show ?thesis
    using dim_span[of "cball (0 :: 'n::euclidean_space) e"] by (auto simp add: dim_UNIV)
qed

lemma indep_card_eq_dim_span:
  fixes B :: "('n::euclidean_space) set"
  assumes "independent B"
  shows "finite B & card B = dim (span B)"
  using assms basis_card_eq_dim[of B "span B"] span_inc by auto

lemma setsum_not_0: "setsum f A ~= 0 ==> EX a:A. f a ~= 0"
  by (rule ccontr) auto

lemma translate_inj_on:
  fixes A :: "('a::ab_group_add) set"
  shows "inj_on (%x. a+x) A"
  unfolding inj_on_def by auto

lemma translation_assoc:
  fixes a b :: "'a::ab_group_add"
  shows "(\<lambda>x. b+x) ` ((\<lambda>x. a+x) ` S) = (\<lambda>x. (a+b)+x) ` S"
  by auto

lemma translation_invert:
  fixes a :: "'a::ab_group_add"
  assumes "(\<lambda>x. a+x) ` A = (\<lambda>x. a+x) ` B"
  shows "A = B"
proof -
  have "(%x. -a+x) ` ((%x. a+x) ` A) = (%x. -a+x) ` ((%x. a+x) ` B)"
    using assms by auto
  then show ?thesis
    using translation_assoc[of "-a" a A] translation_assoc[of "-a" a B] by auto
qed

lemma translation_galois:
  fixes a :: "'a::ab_group_add"
  shows "T=((\<lambda>x. a+x) ` S) <-> S=((\<lambda>x. (-a)+x) ` T)"
  using translation_assoc[of "-a" a S] apply auto
  using translation_assoc[of a "-a" T] apply auto
  done

lemma translation_inverse_subset:
  assumes "((%x. -a+x) ` V) <= (S :: 'n::ab_group_add set)"
  shows "V <= ((%x. a+x) ` S)"
proof -
  { fix x
    assume "x:V"
    then have "x-a : S" using assms by auto
    then have "x : {a + v |v. v : S}"
      apply auto
      apply (rule exI[of _ "x-a"])
      apply simp
      done
    then have "x : ((%x. a+x) ` S)" by auto
  } then show ?thesis by auto
qed

lemma basis_to_basis_subspace_isomorphism:
  assumes s: "subspace (S:: ('n::euclidean_space) set)"
    and t: "subspace (T :: ('m::euclidean_space) set)"
    and d: "dim S = dim T"
    and B: "B <= S" "independent B" "S <= span B" "card B = dim S"
    and C: "C <= T" "independent C" "T <= span C" "card C = dim T"
  shows "EX f. linear f & f ` B = C & f ` S = T & inj_on f S"
proof -
(* Proof is a modified copy of the proof of similar lemma subspace_isomorphism
*)
  from B independent_bound have fB: "finite B" by blast
  from C independent_bound have fC: "finite C" by blast
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" using `finite B` `finite C` by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear g" "\<forall>x\<in> B. g x = f x" by blast
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by simp
  have "g ` B = f ` B" using g(2)
    by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B" using f(2) g(2)
    by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  { fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B" by blast+
    from gxy have th0: "g (x - y) = 0" by (simp add: linear_sub[OF g(1)])
    have th1: "x - y \<in> span B" using x' y' by (metis span_sub)
    have "x=y" using g0[OF th1 th0] by simp
  } then have giS: "inj_on g S" unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s]
  have "g ` S = span (g ` B)" by (simp add: span_linear_image[OF g(1)])
  also have "\<dots> = span C" unfolding gBC ..
  also have "\<dots> = T" using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS gBC show ?thesis by blast
qed

lemma closure_bounded_linear_image:
  assumes f: "bounded_linear f"
  shows "f ` (closure S) \<subseteq> closure (f ` S)"
  using linear_continuous_on [OF f] closed_closure closure_subset
  by (rule image_closure_subset)

lemma closure_linear_image:
  fixes f :: "('m::euclidean_space) => ('n::real_normed_vector)"
  assumes "linear f"
  shows "f ` (closure S) <= closure (f ` S)"
  using assms unfolding linear_conv_bounded_linear
  by (rule closure_bounded_linear_image)

lemma closure_injective_linear_image:
  fixes f :: "('n::euclidean_space) => ('n::euclidean_space)"
  assumes "linear f" "inj f"
  shows "f ` (closure S) = closure (f ` S)"
proof -
  obtain f' where f'_def: "linear f' & f o f' = id & f' o f = id"
    using assms linear_injective_isomorphism[of f] isomorphism_expand by auto
  then have "f' ` closure (f ` S) <= closure (S)"
    using closure_linear_image[of f' "f ` S"] image_compose[of f' f] by auto
  then have "f ` f' ` closure (f ` S) <= f ` closure (S)" by auto
  then have "closure (f ` S) <= f ` closure (S)"
    using image_compose[of f f' "closure (f ` S)"] f'_def by auto
  then show ?thesis using closure_linear_image[of f S] assms by auto
qed

lemma closure_direct_sum:
  shows "closure (S <*> T) = closure S <*> closure T"
  by (rule closure_Times)

lemma closure_scaleR:
  fixes S :: "('a::real_normed_vector) set"
  shows "(op *\<^sub>R c) ` (closure S) = closure ((op *\<^sub>R c) ` S)"
proof
  show "(op *\<^sub>R c) ` (closure S) \<subseteq> closure ((op *\<^sub>R c) ` S)"
    using bounded_linear_scaleR_right by (rule closure_bounded_linear_image)
  show "closure ((op *\<^sub>R c) ` S) \<subseteq> (op *\<^sub>R c) ` (closure S)"
    by (intro closure_minimal image_mono closure_subset closed_scaling closed_closure)
qed

lemma fst_linear: "linear fst"
  unfolding linear_def by (simp add: algebra_simps)

lemma snd_linear: "linear snd"
  unfolding linear_def by (simp add: algebra_simps)

lemma fst_snd_linear: "linear (%(x,y). x + y)"
  unfolding linear_def by (simp add: algebra_simps)

lemma scaleR_2:
  fixes x :: "'a::real_vector"
  shows "scaleR 2 x = x + x"
  unfolding one_add_one [symmetric] scaleR_left_distrib by simp

lemma vector_choose_size:
  "0 <= c ==> \<exists>(x::'a::euclidean_space). norm x = c"
  apply (rule exI[where x="c *\<^sub>R (SOME i. i \<in> Basis)"])
  apply (auto simp: SOME_Basis)
  done

lemma setsum_delta_notmem:
  assumes "x \<notin> s"
  shows "setsum (\<lambda>y. if (y = x) then P x else Q y) s = setsum Q s"
    and "setsum (\<lambda>y. if (x = y) then P x else Q y) s = setsum Q s"
    and "setsum (\<lambda>y. if (y = x) then P y else Q y) s = setsum Q s"
    and "setsum (\<lambda>y. if (x = y) then P y else Q y) s = setsum Q s"
  apply (rule_tac [!] setsum_cong2)
  using assms apply auto
  done

lemma setsum_delta'':
  fixes s::"'a::real_vector set"
  assumes "finite s"
  shows "(\<Sum>x\<in>s. (if y = x then f x else 0) *\<^sub>R x) = (if y\<in>s then (f y) *\<^sub>R y else 0)"
proof -
  have *: "\<And>x y. (if y = x then f x else (0::real)) *\<^sub>R x = (if x=y then (f x) *\<^sub>R x else 0)"
    by auto
  show ?thesis
    unfolding * using setsum_delta[OF assms, of y "\<lambda>x. f x *\<^sub>R x"] by auto
qed

lemma if_smult:"(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)" by auto

lemma image_smult_interval:
  "(\<lambda>x. m *\<^sub>R (x::'a::ordered_euclidean_space)) ` {a..b} =
    (if {a..b} = {} then {} else if 0 \<le> m then {m *\<^sub>R a..m *\<^sub>R b} else {m *\<^sub>R b..m *\<^sub>R a})"
  using image_affinity_interval[of m 0 a b] by auto

lemma dist_triangle_eq:
  fixes x y z :: "'a::real_inner"
  shows "dist x z = dist x y + dist y z \<longleftrightarrow> norm (x - y) *\<^sub>R (y - z) = norm (y - z) *\<^sub>R (x - y)"
proof -
  have *: "x - y + (y - z) = x - z" by auto
  show ?thesis unfolding dist_norm norm_triangle_eq[of "x - y" "y - z", unfolded *]
    by (auto simp add:norm_minus_commute)
qed

lemma norm_minus_eqI:"x = - y \<Longrightarrow> norm x = norm y" by auto

lemma Min_grI:
  assumes "finite A" "A \<noteq> {}" "\<forall>a\<in>A. x < a"
  shows "x < Min A"
  unfolding Min_gr_iff[OF assms(1,2)] using assms(3) by auto

lemma norm_lt: "norm x < norm y \<longleftrightarrow> inner x x < inner y y"
  unfolding norm_eq_sqrt_inner by simp

lemma norm_le: "norm x \<le> norm y \<longleftrightarrow> inner x x \<le> inner y y"
  unfolding norm_eq_sqrt_inner by simp


subsection {* Affine set and affine hull *}

definition affine :: "'a::real_vector set \<Rightarrow> bool"
  where "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma affine_alt: "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)"
  unfolding affine_def by (metis eq_diff_eq')

lemma affine_empty[intro]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing[intro]: "affine {x}"
  unfolding affine_alt by (auto simp add: scaleR_left_distrib [symmetric])

lemma affine_UNIV[intro]: "affine UNIV"
  unfolding affine_def by auto

lemma affine_Inter: "(\<forall>s\<in>f. affine s) \<Longrightarrow> affine (\<Inter> f)"
  unfolding affine_def by auto

lemma affine_Int: "affine s \<Longrightarrow> affine t \<Longrightarrow> affine (s \<inter> t)"
  unfolding affine_def by auto

lemma affine_affine_hull: "affine(affine hull s)"
  unfolding hull_def
  using affine_Inter[of "{t. affine t \<and> s \<subseteq> t}"] by auto

lemma affine_hull_eq[simp]: "(affine hull s = s) \<longleftrightarrow> affine s"
  by (metis affine_affine_hull hull_same)


subsubsection {* Some explicit formulations (from Lars Schewe) *}

lemma affine:
  fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow>
    (\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> setsum u s = 1 \<longrightarrow> (setsum (\<lambda>x. (u x) *\<^sub>R x)) s \<in> V)"
  unfolding affine_def
  apply rule
  apply(rule, rule, rule)
  apply(erule conjE)+
  defer
  apply (rule, rule, rule, rule, rule)
proof -
  fix x y u v
  assume as: "x \<in> V" "y \<in> V" "u + v = (1::real)"
    "\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> setsum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
  then show "u *\<^sub>R x + v *\<^sub>R y \<in> V"
    apply (cases "x = y")
    using as(4)[THEN spec[where x="{x,y}"], THEN spec[where x="\<lambda>w. if w = x then u else v"]]
      and as(1-3)
    by (auto simp add: scaleR_left_distrib[symmetric])
next
  fix s u
  assume as: "\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
    "finite s" "s \<noteq> {}" "s \<subseteq> V" "setsum u s = (1::real)"
  def n \<equiv> "card s"
  have "card s = 0 \<or> card s = 1 \<or> card s = 2 \<or> card s > 2" by auto
  then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
  proof (auto simp only: disjE)
    assume "card s = 2"
    then have "card s = Suc (Suc 0)" by auto
    then obtain a b where "s = {a, b}" unfolding card_Suc_eq by auto
    then show ?thesis
      using as(1)[THEN bspec[where x=a], THEN bspec[where x=b]] using as(4,5)
      by (auto simp add: setsum_clauses(2))
  next
    assume "card s > 2"
    then show ?thesis using as and n_def
    proof (induct n arbitrary: u s)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      fix s :: "'a set" and u :: "'a \<Rightarrow> real"
      assume IA:
        "\<And>u s.  \<lbrakk>2 < card s; \<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V; finite s;
          s \<noteq> {}; s \<subseteq> V; setsum u s = 1; n = card s \<rbrakk> \<Longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
        and as:
          "Suc n = card s" "2 < card s" "\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
           "finite s" "s \<noteq> {}" "s \<subseteq> V" "setsum u s = 1"
      have "\<exists>x\<in>s. u x \<noteq> 1"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "setsum u s = real_of_nat (card s)" unfolding card_eq_setsum by auto
        then show False
          using as(7) and `card s > 2`
          by (metis One_nat_def less_Suc0 Zero_not_Suc of_nat_1 of_nat_eq_iff numeral_2_eq_2)
      qed
      then obtain x where x:"x\<in>s" "u x \<noteq> 1" by auto

      have c: "card (s - {x}) = card s - 1"
        apply (rule card_Diff_singleton) using `x\<in>s` as(4) by auto
      have *: "s = insert x (s - {x})" "finite (s - {x})"
        using `x\<in>s` and as(4) by auto
      have **: "setsum u (s - {x}) = 1 - u x"
        using setsum_clauses(2)[OF *(2), of u x, unfolded *(1)[symmetric] as(7)] by auto
      have ***: "inverse (1 - u x) * setsum u (s - {x}) = 1"
        unfolding ** using `u x \<noteq> 1` by auto
      have "(\<Sum>xa\<in>s - {x}. (inverse (1 - u x) * u xa) *\<^sub>R xa) \<in> V"
      proof (cases "card (s - {x}) > 2")
        case True
        then have "s - {x} \<noteq> {}" "card (s - {x}) = n"
          unfolding c and as(1)[symmetric]
        proof (rule_tac ccontr)
          assume "\<not> s - {x} \<noteq> {}"
          then have "card (s - {x}) = 0" unfolding card_0_eq[OF *(2)] by simp
          then show False using True by auto
        qed auto
        then show ?thesis
          apply (rule_tac IA[of "s - {x}" "\<lambda>y. (inverse (1 - u x) * u y)"])
          unfolding setsum_right_distrib[symmetric] using as and *** and True
          apply auto
          done
      next
        case False
        then have "card (s - {x}) = Suc (Suc 0)" using as(2) and c by auto
        then obtain a b where "(s - {x}) = {a, b}" "a\<noteq>b" unfolding card_Suc_eq by auto
        then show ?thesis using as(3)[THEN bspec[where x=a], THEN bspec[where x=b]]
          using *** *(2) and `s \<subseteq> V`
          unfolding setsum_right_distrib by (auto simp add: setsum_clauses(2))
      qed
      then have "u x + (1 - u x) = 1 \<Longrightarrow>
          u x *\<^sub>R x + (1 - u x) *\<^sub>R ((\<Sum>xa\<in>s - {x}. u xa *\<^sub>R xa) /\<^sub>R (1 - u x)) \<in> V"
        apply -
        apply (rule as(3)[rule_format])
        unfolding  Real_Vector_Spaces.scaleR_right.setsum
        using x(1) as(6) apply auto
        done
      then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
        unfolding scaleR_scaleR[symmetric] and scaleR_right.setsum [symmetric]
        apply (subst *)
        unfolding setsum_clauses(2)[OF *(2)]
        using `u x \<noteq> 1` apply auto
        done
    qed
  next
    assume "card s = 1"
    then obtain a where "s={a}" by (auto simp add: card_Suc_eq)
    then show ?thesis using as(4,5) by simp
  qed (insert `s\<noteq>{}` `finite s`, auto)
qed

lemma affine_hull_explicit:
  "affine hull p = {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> setsum (\<lambda>v. (u v) *\<^sub>R v) s = y}"
  apply (rule hull_unique)
  apply (subst subset_eq)
  prefer 3
  apply rule
  unfolding mem_Collect_eq
  apply (erule exE)+
  apply (erule conjE)+
  prefer 2
  apply rule
proof -
  fix x
  assume "x\<in>p"
  then show "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x="{x}" in exI, rule_tac x="\<lambda>x. 1" in exI)
    apply auto
    done
next
  fix t x s u
  assume as: "p \<subseteq> t" "affine t" "finite s" "s \<noteq> {}" "s \<subseteq> p" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  then show "x \<in> t"
    using as(2)[unfolded affine, THEN spec[where x=s], THEN spec[where x=u]] by auto
next
  show "affine {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y}"
    unfolding affine_def
    apply (rule, rule, rule, rule, rule)
    unfolding mem_Collect_eq
  proof -
    fix u v :: real
    assume uv: "u + v = 1"
    fix x
    assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    then obtain sx ux where
      x: "finite sx" "sx \<noteq> {}" "sx \<subseteq> p" "setsum ux sx = 1" "(\<Sum>v\<in>sx. ux v *\<^sub>R v) = x" by auto
    fix y assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
    then obtain sy uy where
      y: "finite sy" "sy \<noteq> {}" "sy \<subseteq> p" "setsum uy sy = 1" "(\<Sum>v\<in>sy. uy v *\<^sub>R v) = y" by auto
    have xy: "finite (sx \<union> sy)" using x(1) y(1) by auto
    have **: "(sx \<union> sy) \<inter> sx = sx" "(sx \<union> sy) \<inter> sy = sy" by auto
    show "\<exists>s ua. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and>
        setsum ua s = 1 \<and> (\<Sum>v\<in>s. ua v *\<^sub>R v) = u *\<^sub>R x + v *\<^sub>R y"
      apply (rule_tac x="sx \<union> sy" in exI)
      apply (rule_tac x="\<lambda>a. (if a\<in>sx then u * ux a else 0) + (if a\<in>sy then v * uy a else 0)" in exI)
      unfolding scaleR_left_distrib setsum_addf if_smult scaleR_zero_left ** setsum_restrict_set[OF xy, symmetric]
      unfolding scaleR_scaleR[symmetric] Real_Vector_Spaces.scaleR_right.setsum [symmetric] and setsum_right_distrib[symmetric]
      unfolding x y
      using x(1-3) y(1-3) uv apply simp
      done
  qed
qed

lemma affine_hull_finite:
  assumes "finite s"
  shows "affine hull s = {y. \<exists>u. setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding affine_hull_explicit and set_eq_iff and mem_Collect_eq apply (rule,rule)
  apply(erule exE)+
  apply(erule conjE)+
  defer
  apply (erule exE)
  apply (erule conjE)
proof -
  fix x u
  assume "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  then show "\<exists>sa u. finite sa \<and>
      \<not> (\<forall>x. (x \<in> sa) = (x \<in> {})) \<and> sa \<subseteq> s \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = x"
    apply (rule_tac x=s in exI, rule_tac x=u in exI)
    using assms apply auto
    done
next
  fix x t u
  assume "t \<subseteq> s"
  then have *: "s \<inter> t = t" by auto
  assume "finite t" "\<not> (\<forall>x. (x \<in> t) = (x \<in> {}))" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  then show "\<exists>u. setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    unfolding if_smult scaleR_zero_left and setsum_restrict_set[OF assms, symmetric] and *
    apply auto
    done
qed


subsubsection {* Stepping theorems and hence small special cases *}

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  by (rule hull_unique) auto

lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows
    "(\<exists>u. setsum u {} = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) {} = y) \<longleftrightarrow> w = 0 \<and> y = 0" (is ?th1)
    "finite s \<Longrightarrow>
      (\<exists>u. setsum u (insert a s) = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y) \<longleftrightarrow>
      (\<exists>v u. setsum u s = w - v \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)" (is "?as \<Longrightarrow> (?lhs = ?rhs)")
proof -
  show ?th1 by simp
  assume ?as
  {
    assume ?lhs
    then obtain u where u: "setsum u (insert a s) = w \<and> (\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y"
      by auto
    have ?rhs
    proof (cases "a \<in> s")
      case True
      then have *: "insert a s = s" by auto
      show ?thesis
        using u[unfolded *]
        apply(rule_tac x=0 in exI)
        apply auto
        done
    next
      case False
      then show ?thesis
        apply (rule_tac x="u a" in exI)
        using u and `?as`
        apply auto
        done
    qed
  }
  moreover
  {
    assume ?rhs
    then obtain v u where vu: "setsum u s = w - v"  "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    have *: "\<And>x M. (if x = a then v else M) *\<^sub>R x = (if x = a then v *\<^sub>R x else M *\<^sub>R x)"
      by auto
    have ?lhs
    proof (cases "a \<in> s")
      case True
      then show ?thesis
        apply (rule_tac x="\<lambda>x. (if x=a then v else 0) + u x" in exI)
        unfolding setsum_clauses(2)[OF `?as`] apply simp
        unfolding scaleR_left_distrib and setsum_addf
        unfolding vu and * and scaleR_zero_left
        apply (auto simp add: setsum_delta[OF `?as`])
        done
    next
      case False
      then have **:
        "\<And>x. x \<in> s \<Longrightarrow> u x = (if x = a then v else u x)"
        "\<And>x. x \<in> s \<Longrightarrow> u x *\<^sub>R x = (if x = a then v *\<^sub>R x else u x *\<^sub>R x)" by auto
      from False show ?thesis
        apply (rule_tac x="\<lambda>x. if x=a then v else u x" in exI)
        unfolding setsum_clauses(2)[OF `?as`] and * using vu
        using setsum_cong2[of s "\<lambda>x. u x *\<^sub>R x" "\<lambda>x. if x = a then v *\<^sub>R x else u x *\<^sub>R x", OF **(2)]
        using setsum_cong2[of s u "\<lambda>x. if x = a then v else u x", OF **(1)]
        apply auto
        done
    qed
  }
  ultimately show "?lhs = ?rhs" by blast
qed

lemma affine_hull_2:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b| u v. (u + v = 1)}"
  (is "?lhs = ?rhs")
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  have "?lhs = {y. \<exists>u. setsum u {a, b} = 1 \<and> (\<Sum>v\<in>{a, b}. u v *\<^sub>R v) = y}"
    using affine_hull_finite[of "{a,b}"] by auto
  also have "\<dots> = {y. \<exists>v u. u b = 1 - v \<and> u b *\<^sub>R b = y - v *\<^sub>R a}"
    by (simp add: affine_hull_finite_step(2)[of "{b}" a])
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
    apply auto
    apply (rule_tac x=v in exI)
    apply (rule_tac x=va in exI)
    apply auto
    apply (rule_tac x=u in exI)
    apply force
    done
qed

lemma mem_affine:
  assumes "affine S" "x : S" "y : S" "u + v = 1"
  shows "(u *\<^sub>R x + v *\<^sub>R y) : S"
  using assms affine_def[of S] by auto

lemma mem_affine_3:
  assumes "affine S" "x : S" "y : S" "z : S" "u + v + w = 1"
  shows "(u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z) : S"
proof -
  have "(u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z) : affine hull {x, y, z}"
    using affine_hull_3[of x y z] assms by auto
  moreover
  have "affine hull {x, y, z} <= affine hull S"
    using hull_mono[of "{x, y, z}" "S"] assms by auto
  moreover
  have "affine hull S = S" using assms affine_hull_eq[of S] by auto
  ultimately show ?thesis by auto
qed

lemma mem_affine_3_minus:
  assumes "affine S" "x : S" "y : S" "z : S"
  shows "x + v *\<^sub>R (y-z) : S"
  using mem_affine_3[of S x y z 1 v "-v"] assms by (simp add: algebra_simps)


subsubsection {* Some relations between affine hull and subspaces *}

lemma affine_hull_insert_subset_span:
  "affine hull (insert a s) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> s}}"
  unfolding subset_eq Ball_def
  unfolding affine_hull_explicit span_explicit mem_Collect_eq
  apply (rule, rule)
  apply (erule exE)+
  apply (erule conjE)+
proof -
  fix x t u
  assume as: "finite t" "t \<noteq> {}" "t \<subseteq> insert a s" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  have "(\<lambda>x. x - a) ` (t - {a}) \<subseteq> {x - a |x. x \<in> s}" using as(3) by auto
  then show "\<exists>v. x = a + v \<and> (\<exists>S u. finite S \<and> S \<subseteq> {x - a |x. x \<in> s} \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = v)"
    apply (rule_tac x="x - a" in exI)
    apply (rule conjI, simp)
    apply (rule_tac x="(\<lambda>x. x - a) ` (t - {a})" in exI)
    apply (rule_tac x="\<lambda>x. u (x + a)" in exI)
    apply (rule conjI) using as(1) apply simp
    apply (erule conjI)
    using as(1)
    apply (simp add: setsum_reindex[unfolded inj_on_def] scaleR_right_diff_distrib
      setsum_subtractf scaleR_left.setsum[symmetric] setsum_diff1 scaleR_left_diff_distrib)
    unfolding as
    apply simp
    done
qed

lemma affine_hull_insert_span:
  assumes "a \<notin> s"
  shows "affine hull (insert a s) = {a + v | v . v \<in> span {x - a | x.  x \<in> s}}"
  apply (rule, rule affine_hull_insert_subset_span)
  unfolding subset_eq Ball_def
  unfolding affine_hull_explicit and mem_Collect_eq
proof (rule, rule, erule exE, erule conjE)
  fix y v
  assume "y = a + v" "v \<in> span {x - a |x. x \<in> s}"
  then obtain t u where obt:"finite t" "t \<subseteq> {x - a |x. x \<in> s}" "a + (\<Sum>v\<in>t. u v *\<^sub>R v) = y"
    unfolding span_explicit by auto
  def f \<equiv> "(\<lambda>x. x + a) ` t"
  have f:"finite f" "f \<subseteq> s" "(\<Sum>v\<in>f. u (v - a) *\<^sub>R (v - a)) = y - a"
    unfolding f_def using obt by (auto simp add: setsum_reindex[unfolded inj_on_def])
  have *: "f \<inter> {a} = {}" "f \<inter> - {a} = f" using f(2) assms by auto
  show "\<exists>sa u. finite sa \<and> sa \<noteq> {} \<and> sa \<subseteq> insert a s \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
    apply (rule_tac x = "insert a f" in exI)
    apply (rule_tac x = "\<lambda>x. if x=a then 1 - setsum (\<lambda>x. u (x - a)) f else u (x - a)" in exI)
    using assms and f unfolding setsum_clauses(2)[OF f(1)] and if_smult
    unfolding setsum_cases[OF f(1), of "\<lambda>x. x = a"]
    apply (auto simp add: setsum_subtractf scaleR_left.setsum algebra_simps *)
    done
qed

lemma affine_hull_span:
  assumes "a \<in> s"
  shows "affine hull s = {a + v | v. v \<in> span {x - a | x. x \<in> s - {a}}}"
  using affine_hull_insert_span[of a "s - {a}", unfolded insert_Diff[OF assms]] by auto


subsubsection {* Parallel affine sets *}

definition affine_parallel :: "'a::real_vector set => 'a::real_vector set => bool"
  where "affine_parallel S T = (? a. T = ((%x. a + x) ` S))"

lemma affine_parallel_expl_aux:
  fixes S T :: "'a::real_vector set"
  assumes "!x. (x : S <-> (a+x) : T)"
  shows "T = ((%x. a + x) ` S)"
proof -
  {
    fix x
    assume "x : T"
    then have "(-a)+x : S" using assms by auto
    then have "x : ((%x. a + x) ` S)"
      using imageI[of "-a+x" S "(%x. a+x)"] by auto
  }
  moreover have "T >= ((%x. a + x) ` S)" using assms by auto
  ultimately show ?thesis by auto
qed

lemma affine_parallel_expl: "affine_parallel S T = (? a. !x. (x : S <-> (a+x) : T))"
  unfolding affine_parallel_def
  using affine_parallel_expl_aux[of S _ T] by auto

lemma affine_parallel_reflex: "affine_parallel S S"
  unfolding affine_parallel_def
  apply (rule exI[of _ "0"])
  apply auto
  done

lemma affine_parallel_commut:
  assumes "affine_parallel A B"
  shows "affine_parallel B A"
proof -
  from assms obtain a where "B=((%x. a + x) ` A)"
    unfolding affine_parallel_def by auto
  then show ?thesis
    using translation_galois[of B a A] unfolding affine_parallel_def by auto
qed

lemma affine_parallel_assoc:
  assumes "affine_parallel A B" "affine_parallel B C"
  shows "affine_parallel A C"
proof -
  from assms obtain ab where "B=((%x. ab + x) ` A)"
    unfolding affine_parallel_def by auto
  moreover
  from assms obtain bc where "C=((%x. bc + x) ` B)"
    unfolding affine_parallel_def by auto
  ultimately show ?thesis
    using translation_assoc[of bc ab A] unfolding affine_parallel_def by auto
qed

lemma affine_translation_aux:
  fixes a :: "'a::real_vector"
  assumes "affine ((%x. a + x) ` S)" shows "affine S"
proof -
  {
    fix x y u v
    assume xy: "x : S" "y : S" "(u :: real)+v=1"
    then have "(a+x):((%x. a + x) ` S)" "(a+y):((%x. a + x) ` S)" by auto
    then have h1: "u *\<^sub>R  (a+x) + v *\<^sub>R (a+y) : ((%x. a + x) ` S)"
      using xy assms unfolding affine_def by auto
    have "u *\<^sub>R (a+x) + v *\<^sub>R (a+y) = (u+v) *\<^sub>R a + (u *\<^sub>R x + v *\<^sub>R y)"
      by (simp add: algebra_simps)
    also have "...= a + (u *\<^sub>R x + v *\<^sub>R y)" using `u+v=1` by auto
    ultimately have "a + (u *\<^sub>R x + v *\<^sub>R y) : ((%x. a + x) ` S)" using h1 by auto
    then have "u *\<^sub>R x + v *\<^sub>R y : S" by auto
  }
  then show ?thesis unfolding affine_def by auto
qed

lemma affine_translation:
  fixes a :: "'a::real_vector"
  shows "affine S <-> affine ((%x. a + x) ` S)"
proof -
  have "affine S ==> affine ((%x. a + x) ` S)"
    using affine_translation_aux[of "-a" "((%x. a + x) ` S)"]
    using translation_assoc[of "-a" a S] by auto
  then show ?thesis using affine_translation_aux by auto
qed

lemma parallel_is_affine:
  fixes S T :: "'a::real_vector set"
  assumes "affine S" "affine_parallel S T"
  shows "affine T"
proof -
  from assms obtain a where "T=((%x. a + x) ` S)"
    unfolding affine_parallel_def by auto
  then show ?thesis using affine_translation assms by auto
qed

lemma subspace_imp_affine: "subspace s \<Longrightarrow> affine s"
  unfolding subspace_def affine_def by auto


subsubsection {* Subspace parallel to an affine set *}

lemma subspace_affine: "subspace S <-> (affine S & 0 : S)"
proof -
  have h0: "subspace S \<Longrightarrow> affine S & 0 \<in> S"
    using subspace_imp_affine[of S] subspace_0 by auto
  {
    assume assm: "affine S & 0 : S"
    {
      fix c :: real
      fix x assume x_def: "x : S"
      have "c *\<^sub>R x = (1-c) *\<^sub>R 0 + c *\<^sub>R x" by auto
      moreover
      have "(1-c) *\<^sub>R 0 + c *\<^sub>R x : S"
        using affine_alt[of S] assm x_def by auto
      ultimately have "c *\<^sub>R x : S" by auto
    }
    then have h1: "!c. !x : S. c *\<^sub>R x : S" by auto

    {
      fix x y
      assume xy_def: "x \<in> S" "y \<in> S"
      def u == "(1 :: real)/2"
      have "(1/2) *\<^sub>R (x+y) = (1/2) *\<^sub>R (x+y)"
        by auto
      moreover
      have "(1/2) *\<^sub>R (x+y)=(1/2) *\<^sub>R x + (1-(1/2)) *\<^sub>R y"
        by (simp add: algebra_simps)
      moreover
      have "(1-u) *\<^sub>R x + u *\<^sub>R y : S"
        using affine_alt[of S] assm xy_def by auto
      ultimately
      have "(1/2) *\<^sub>R (x+y) : S"
        using u_def by auto
      moreover
      have "(x+y) = 2 *\<^sub>R ((1/2) *\<^sub>R (x+y))"
        by auto
      ultimately
      have "(x+y) : S"
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
  assumes "affine S" "a : S"
  shows "subspace ((\<lambda>x. (-a)+x) ` S)"
proof -
  have "affine ((\<lambda>x. (-a)+x) ` S)"
    using  affine_translation assms by auto
  moreover have "0 : ((\<lambda>x. (-a)+x) ` S)"
    using assms exI[of "(\<lambda>x. x:S & -a+x = 0)" a] by auto
  ultimately show ?thesis using subspace_affine by auto
qed

lemma parallel_subspace_explicit:
  assumes "affine S" "a : S"
  assumes "L \<equiv> {y. \<exists>x \<in> S. (-a)+x=y}"
  shows "subspace L & affine_parallel S L"
proof -
  have par: "affine_parallel S L"
    unfolding affine_parallel_def using assms by auto
  then have "affine L" using assms parallel_is_affine by auto
  moreover have "0 \<in> L"
    using assms
    apply auto
    using exI[of "(%x. x:S & -a+x=0)" a]
    apply auto
    done
  ultimately show ?thesis
    using subspace_affine par by auto
qed

lemma parallel_subspace_aux:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A \<supseteq> B"
proof -
  from assms obtain a where a_def: "\<forall>x. (x \<in> A \<longleftrightarrow> (a+x) \<in> B)"
    using affine_parallel_expl[of A B] by auto
  then have "-a \<in> A"
    using assms subspace_0[of B] by auto
  then have "a \<in> A"
    using assms subspace_neg[of A "-a"] by auto
  then show ?thesis
    using assms a_def unfolding subspace_def by auto
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
  shows "\<exists>!L. subspace L & affine_parallel S L"
proof -
  have ex: "\<exists>L. subspace L & affine_parallel S L"
    using assms parallel_subspace_explicit by auto
  {
    fix L1 L2
    assume ass: "subspace L1 & affine_parallel S L1" "subspace L2 & affine_parallel S L2"
    then have "affine_parallel L1 L2"
      using affine_parallel_commut[of S L1] affine_parallel_assoc[of L1 S L2] by auto
    then have "L1 = L2"
      using ass parallel_subspace by auto
  }
  then show ?thesis using ex by auto
qed


subsection {* Cones *}

definition cone :: "'a::real_vector set \<Rightarrow> bool"
  where "cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> s)"

lemma cone_empty[intro, simp]: "cone {}"
  unfolding cone_def by auto

lemma cone_univ[intro, simp]: "cone UNIV"
  unfolding cone_def by auto

lemma cone_Inter[intro]: "\<forall>s\<in>f. cone s \<Longrightarrow> cone(\<Inter> f)"
  unfolding cone_def by auto


subsubsection {* Conic hull *}

lemma cone_cone_hull: "cone (cone hull s)"
  unfolding hull_def by auto

lemma cone_hull_eq: "cone hull s = s \<longleftrightarrow> cone s"
  apply (rule hull_eq)
  using cone_Inter
  unfolding subset_eq
  apply auto
  done

lemma mem_cone:
  assumes "cone S" "x \<in> S" "c \<ge> 0"
  shows "c *\<^sub>R x : S"
  using assms cone_def[of S] by auto

lemma cone_contains_0:
  assumes "cone S"
  shows "S \<noteq> {} \<longleftrightarrow> 0 \<in> S"
proof -
  {
    assume "S \<noteq> {}"
    then obtain a where "a \<in> S" by auto
    then have "0 \<in> S"
      using assms mem_cone[of S a 0] by auto
  }
  then show ?thesis by auto
qed

lemma cone_0: "cone {0}"
  unfolding cone_def by auto

lemma cone_Union[intro]: "(\<forall>s\<in>f. cone s) \<longrightarrow> cone (Union f)"
  unfolding cone_def by blast

lemma cone_iff:
  assumes "S ~= {}"
  shows "cone S \<longleftrightarrow> 0 \<in> S & (\<forall>c. c>0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
proof -
  {
    assume "cone S"
    {
      fix c
      assume "(c :: real) > 0"
      {
        fix x
        assume "x : S"
        then have "x : (op *\<^sub>R c) ` S"
          unfolding image_def
          using `cone S` `c>0` mem_cone[of S x "1/c"]
            exI[of "(%t. t:S & x = c *\<^sub>R t)" "(1 / c) *\<^sub>R x"]
          apply auto
          done
      }
      moreover
      {
        fix x
        assume "x : (op *\<^sub>R c) ` S"
        (*from this obtain t where "t:S & x = c *\<^sub>R t" by auto*)
        then have "x:S"
          using `cone S` `c>0` unfolding cone_def image_def `c>0` by auto
      }
      ultimately have "(op *\<^sub>R c) ` S = S" by auto
    }
    then have "0 \<in> S & (\<forall>c. c > 0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
      using `cone S` cone_contains_0[of S] assms by auto
  }
  moreover
  {
    assume a: "0 \<in> S & (\<forall>c. c > 0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
    {
      fix x
      assume "x \<in> S"
      fix c1
      assume "(c1 :: real) \<ge> 0"
      then have "c1 = 0 | c1 > 0" by auto
      then have "c1 *\<^sub>R x : S" using a `x \<in> S` by auto
    }
    then have "cone S" unfolding cone_def by auto
  }
  ultimately show ?thesis by blast
qed

lemma cone_hull_empty: "cone hull {} = {}"
  by (metis cone_empty cone_hull_eq)

lemma cone_hull_empty_iff: "S = {} \<longleftrightarrow> cone hull S = {}"
  by (metis bot_least cone_hull_empty hull_subset xtrans(5))

lemma cone_hull_contains_0: "S \<noteq> {} \<longleftrightarrow> 0 \<in> cone hull S"
  using cone_cone_hull[of S] cone_contains_0[of "cone hull S"] cone_hull_empty_iff[of S]
  by auto

lemma mem_cone_hull:
  assumes "x : S" "c \<ge> 0"
  shows "c *\<^sub>R x \<in> cone hull S"
  by (metis assms cone_cone_hull hull_inc mem_cone)

lemma cone_hull_expl: "cone hull S = {c *\<^sub>R x | c x. c \<ge> 0 & x \<in> S}" (is "?lhs = ?rhs")
proof -
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain cx xx where x_def: "x = cx *\<^sub>R xx & (cx :: real) \<ge> 0 & xx \<in> S"
      by auto
    fix c
    assume c_def: "(c :: real) \<ge> 0"
    then have "c *\<^sub>R x = (c*cx) *\<^sub>R xx"
      using x_def by (simp add: algebra_simps)
    moreover
    have "c * cx \<ge> 0"
      using c_def x_def using mult_nonneg_nonneg by auto
    ultimately
    have "c *\<^sub>R x \<in> ?rhs" using x_def by auto
  }
  then have "cone ?rhs" unfolding cone_def by auto
  then have "?rhs : Collect cone" unfolding mem_Collect_eq by auto
  {
    fix x
    assume "x \<in> S"
    then have "1 *\<^sub>R x \<in> ?rhs"
      apply auto
      apply (rule_tac x="1" in exI)
      apply auto
      done
    then have "x \<in> ?rhs" by auto
  } then have "S \<subseteq> ?rhs" by auto
  then have "?lhs \<subseteq> ?rhs"
    using `?rhs \<in> Collect cone` hull_minimal[of S "?rhs" "cone"] by auto
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain cx xx where x_def: "x = cx *\<^sub>R xx & (cx :: real) \<ge> 0 & xx \<in> S" by auto
    then have "xx \<in> cone hull S" using hull_subset[of S] by auto
    then have "x \<in> ?lhs"
      using x_def cone_cone_hull[of S] cone_def[of "cone hull S"] by auto
  }
  ultimately show ?thesis by auto
qed

lemma cone_closure:
  fixes S :: "('a::real_normed_vector) set"
  assumes "cone S"
  shows "cone (closure S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  then have "0 \<in> S & (!c. c>0 --> op *\<^sub>R c ` S = S)"
    using cone_iff[of S] assms by auto
  then have "0 \<in> closure S & (\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` closure S = closure S)"
    using closure_subset by (auto simp add: closure_scaleR)
  then show ?thesis using cone_iff[of "closure S"] by auto
qed


subsection {* Affine dependence and consequential theorems (from Lars Schewe) *}

definition affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent s \<longleftrightarrow> (\<exists>x\<in>s. x \<in> (affine hull (s - {x})))"

lemma affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>s u. finite s \<and> s \<subseteq> p \<and> setsum u s = 0 \<and>
    (\<exists>v\<in>s. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  unfolding affine_dependent_def affine_hull_explicit mem_Collect_eq
  apply rule
  apply (erule bexE, erule exE, erule exE)
  apply (erule conjE)+
  defer
  apply (erule exE, erule exE)
  apply (erule conjE)+
  apply (erule bexE)
proof -
  fix x s u
  assume as: "x \<in> p" "finite s" "s \<noteq> {}" "s \<subseteq> p - {x}" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  have "x \<notin> s" using as(1,4) by auto
  show "\<exists>s u. finite s \<and> s \<subseteq> p \<and> setsum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    apply (rule_tac x="insert x s" in exI, rule_tac x="\<lambda>v. if v = x then - 1 else u v" in exI)
    unfolding if_smult and setsum_clauses(2)[OF as(2)] and setsum_delta_notmem[OF `x\<notin>s`] and as
    using as apply auto
    done
next
  fix s u v
  assume as: "finite s" "s \<subseteq> p" "setsum u s = 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0" "v \<in> s" "u v \<noteq> 0"
  have "s \<noteq> {v}" using as(3,6) by auto
  then show "\<exists>x\<in>p. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p - {x} \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x=v in bexI)
    apply (rule_tac x="s - {v}" in exI)
    apply (rule_tac x="\<lambda>x. - (1 / u v) * u x" in exI)
    unfolding scaleR_scaleR[symmetric] and scaleR_right.setsum [symmetric]
    unfolding setsum_right_distrib[symmetric] and setsum_diff1[OF as(1)]
    using as
    apply auto
    done
qed

lemma affine_dependent_explicit_finite:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows "affine_dependent s \<longleftrightarrow>
    (\<exists>u. setsum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  (is "?lhs = ?rhs")
proof
  have *: "\<And>vt u v. (if vt then u v else 0) *\<^sub>R v = (if vt then (u v) *\<^sub>R v else (0::'a))"
    by auto
  assume ?lhs
  then obtain t u v where
      "finite t" "t \<subseteq> s" "setsum u t = 0" "v\<in>t" "u v \<noteq> 0"  "(\<Sum>v\<in>t. u v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  then show ?rhs
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    apply auto unfolding * and setsum_restrict_set[OF assms, symmetric]
    unfolding Int_absorb1[OF `t\<subseteq>s`]
    apply auto
    done
next
  assume ?rhs
  then obtain u v where "setsum u s = 0"  "v\<in>s" "u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0" by auto
  then show ?lhs unfolding affine_dependent_explicit
    using assms by auto
qed


subsection {* Connectedness of convex sets *}

lemma connectedD:
  "connected S \<Longrightarrow> open A \<Longrightarrow> open B \<Longrightarrow> S \<subseteq> A \<union> B \<Longrightarrow> A \<inter> B \<inter> S = {} \<Longrightarrow> A \<inter> S = {} \<or> B \<inter> S = {}"
  by (metis connected_def)

lemma convex_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "connected s"
proof (rule connectedI)
  fix A B
  assume "open A" "open B" "A \<inter> B \<inter> s = {}" "s \<subseteq> A \<union> B"
  moreover
  assume "A \<inter> s \<noteq> {}" "B \<inter> s \<noteq> {}"
  then obtain a b where a: "a \<in> A" "a \<in> s" and b: "b \<in> B" "b \<in> s" by auto
  def f \<equiv> "\<lambda>u. u *\<^sub>R a + (1 - u) *\<^sub>R b"
  then have "continuous_on {0 .. 1} f"
    by (auto intro!: continuous_on_intros)
  then have "connected (f ` {0 .. 1})"
    by (auto intro!: connected_continuous_image)
  note connectedD[OF this, of A B]
  moreover have "a \<in> A \<inter> f ` {0 .. 1}"
    using a by (auto intro!: image_eqI[of _ _ 1] simp: f_def)
  moreover have "b \<in> B \<inter> f ` {0 .. 1}"
    using b by (auto intro!: image_eqI[of _ _ 0] simp: f_def)
  moreover have "f ` {0 .. 1} \<subseteq> s"
    using `convex s` a b unfolding convex_def f_def by auto
  ultimately show False by auto
qed

text {* One rather trivial consequence. *}

lemma connected_UNIV[intro]: "connected (UNIV :: 'a::real_normed_vector set)"
  by(simp add: convex_connected convex_UNIV)

text {* Balls, being convex, are connected. *}

lemma convex_box:
  fixes a::"'a::euclidean_space"
  assumes "\<And>i. i\<in>Basis \<Longrightarrow> convex {x. P i x}"
  shows "convex {x. \<forall>i\<in>Basis. P i (x\<bullet>i)}"
  using assms unfolding convex_def
  by (auto simp: inner_add_left)

lemma convex_positive_orthant: "convex {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i)}"
  by (rule convex_box) (simp add: atLeast_def[symmetric] convex_real_interval)

lemma convex_local_global_minimum:
  fixes s :: "'a::real_normed_vector set"
  assumes "0<e" "convex_on s f" "ball x e \<subseteq> s" "\<forall>y\<in>ball x e. f x \<le> f y"
  shows "\<forall>y\<in>s. f x \<le> f y"
proof (rule ccontr)
  have "x \<in> s" using assms(1,3) by auto
  assume "\<not> ?thesis"
  then obtain y where "y\<in>s" and y: "f x > f y" by auto
  hence xy: "0 < dist x y" by (auto simp add: dist_nz[symmetric])

  then obtain u where "0 < u" "u \<le> 1" and u:"u < e / dist x y"
    using real_lbound_gt_zero[of 1 "e / dist x y"]
    using xy `e>0` and divide_pos_pos[of e "dist x y"] by auto
  then have "f ((1-u) *\<^sub>R x + u *\<^sub>R y) \<le> (1-u) * f x + u * f y"
    using `x\<in>s` `y\<in>s`
    using assms(2)[unfolded convex_on_def,
      THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x="1-u"]]
    by auto
  moreover
  have *: "x - ((1 - u) *\<^sub>R x + u *\<^sub>R y) = u *\<^sub>R (x - y)"
    by (simp add: algebra_simps)
  have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> ball x e"
    unfolding mem_ball dist_norm
    unfolding * and norm_scaleR and abs_of_pos[OF `0<u`]
    unfolding dist_norm[symmetric]
    using u
    unfolding pos_less_divide_eq[OF xy]
    by auto
  then have "f x \<le> f ((1 - u) *\<^sub>R x + u *\<^sub>R y)"
    using assms(4) by auto
  ultimately show False
    using mult_strict_left_mono[OF y `u>0`]
    unfolding left_diff_distrib
    by auto
qed

lemma convex_ball:
  fixes x :: "'a::real_normed_vector"
  shows "convex (ball x e)"
proof (auto simp add: convex_def)
  fix y z
  assume yz: "dist x y < e" "dist x z < e"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
    using uv yz
    using convex_distance[of "ball x e" x, unfolded convex_on_def,
      THEN bspec[where x=y], THEN bspec[where x=z]]
    by auto
  then show "dist x (u *\<^sub>R y + v *\<^sub>R z) < e"
    using convex_bound_lt[OF yz uv] by auto
qed

lemma convex_cball:
  fixes x :: "'a::real_normed_vector"
  shows "convex(cball x e)"
proof (auto simp add: convex_def Ball_def)
  fix y z
  assume yz: "dist x y \<le> e" "dist x z \<le> e"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
    using uv yz
    using convex_distance[of "cball x e" x, unfolded convex_on_def,
      THEN bspec[where x=y], THEN bspec[where x=z]]
    by auto
  then show "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> e"
    using convex_bound_le[OF yz uv] by auto
qed

lemma connected_ball:
  fixes x :: "'a::real_normed_vector"
  shows "connected (ball x e)"
  using convex_connected convex_ball by auto

lemma connected_cball:
  fixes x :: "'a::real_normed_vector"
  shows "connected (cball x e)"
  using convex_connected convex_cball by auto


subsection {* Convex hull *}

lemma convex_convex_hull: "convex (convex hull s)"
  unfolding hull_def
  using convex_Inter[of "{t. convex t \<and> s \<subseteq> t}"]
  by auto

lemma convex_hull_eq: "convex hull s = s \<longleftrightarrow> convex s"
  by (metis convex_convex_hull hull_same)

lemma bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "bounded s" shows "bounded(convex hull s)"
proof -
  from assms obtain B where B: "\<forall>x\<in>s. norm x \<le> B"
    unfolding bounded_iff by auto
  show ?thesis
    apply (rule bounded_subset[OF bounded_cball, of _ 0 B])
    unfolding subset_hull[of convex, OF convex_cball]
    unfolding subset_eq mem_cball dist_norm using B
    apply auto
    done
qed

lemma finite_imp_bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  shows "finite s \<Longrightarrow> bounded (convex hull s)"
  using bounded_convex_hull finite_imp_bounded
  by auto


subsubsection {* Convex hull is "preserved" by a linear function *}

lemma convex_hull_linear_image:
  assumes "bounded_linear f"
  shows "f ` (convex hull s) = convex hull (f ` s)"
  apply rule
  unfolding subset_eq ball_simps
  apply (rule_tac[!] hull_induct, rule hull_inc)
  prefer 3
  apply (erule imageE)
  apply (rule_tac x=xa in image_eqI)
  apply assumption
  apply (rule hull_subset[unfolded subset_eq, rule_format])
  apply assumption
proof -
  interpret f: bounded_linear f by fact
  show "convex {x. f x \<in> convex hull f ` s}"
    unfolding convex_def
    by (auto simp add: f.scaleR f.add convex_convex_hull[unfolded convex_def, rule_format])
  show "convex {x. x \<in> f ` (convex hull s)}"
    using  convex_convex_hull[unfolded convex_def, of s]
    unfolding convex_def by (auto simp add: f.scaleR [symmetric] f.add [symmetric])
qed auto

lemma in_convex_hull_linear_image:
  assumes "bounded_linear f" "x \<in> convex hull s"
  shows "(f x) \<in> convex hull (f ` s)"
  using convex_hull_linear_image[OF assms(1)] assms(2) by auto


subsubsection {* Stepping theorems for convex hulls of finite sets *}

lemma convex_hull_empty[simp]: "convex hull {} = {}"
  by (rule hull_unique) auto

lemma convex_hull_singleton[simp]: "convex hull {a} = {a}"
  by (rule hull_unique) auto

lemma convex_hull_insert:
  fixes s :: "'a::real_vector set"
  assumes "s \<noteq> {}"
  shows "convex hull (insert a s) =
    {x. \<exists>u\<ge>0. \<exists>v\<ge>0. \<exists>b. (u + v = 1) \<and> b \<in> (convex hull s) \<and> (x = u *\<^sub>R a + v *\<^sub>R b)}"
  (is "?xyz = ?hull")
  apply (rule, rule hull_minimal, rule)
  unfolding insert_iff
  prefer 3
  apply rule
proof -
  fix x
  assume x: "x = a \<or> x \<in> s"
  then show "x \<in> ?hull"
    apply rule
    unfolding mem_Collect_eq
    apply (rule_tac x=1 in exI)
    defer
    apply (rule_tac x=0 in exI)
    using assms hull_subset[of s convex]
    apply auto
    done
next
  fix x
  assume "x \<in> ?hull"
  then obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "x = u *\<^sub>R a + v *\<^sub>R b"
    by auto
  have "a \<in> convex hull insert a s" "b\<in>convex hull insert a s"
    using hull_mono[of s "insert a s" convex] hull_mono[of "{a}" "insert a s" convex] and obt(4)
    by auto
  then show "x \<in> convex hull insert a s"
    unfolding obt(5)
    using convex_convex_hull[of "insert a s", unfolded convex_def]
    apply (erule_tac x = a in ballE)
    apply (erule_tac x = b in ballE)
    apply (erule_tac x = u in allE)
    using obt
    apply auto
    done
next
  show "convex ?hull"
    unfolding convex_def
    apply (rule, rule, rule, rule, rule, rule, rule)
  proof -
    fix x y u v
    assume as: "(0::real) \<le> u" "0 \<le> v" "u + v = 1" "x\<in>?hull" "y\<in>?hull"
    from as(4) obtain u1 v1 b1
      where obt1: "u1\<ge>0" "v1\<ge>0" "u1 + v1 = 1" "b1 \<in> convex hull s" "x = u1 *\<^sub>R a + v1 *\<^sub>R b1" by auto
    from as(5) obtain u2 v2 b2
      where obt2: "u2\<ge>0" "v2\<ge>0" "u2 + v2 = 1" "b2 \<in> convex hull s" "y = u2 *\<^sub>R a + v2 *\<^sub>R b2" by auto
    have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
      by (auto simp add: algebra_simps)
    have **: "\<exists>b \<in> convex hull s. u *\<^sub>R x + v *\<^sub>R y =
      (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)"
    proof (cases "u * v1 + v * v2 = 0")
      case True
      have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
        by (auto simp add: algebra_simps)
      from True have ***: "u * v1 = 0" "v * v2 = 0"
        using mult_nonneg_nonneg[OF `u\<ge>0` `v1\<ge>0`] mult_nonneg_nonneg[OF `v\<ge>0` `v2\<ge>0`]
        by arith+
      then have "u * u1 + v * u2 = 1"
        using as(3) obt1(3) obt2(3) by auto
      then show ?thesis
        unfolding obt1(5) obt2(5) *
        using assms hull_subset[of s convex]
        by (auto simp add: *** scaleR_right_distrib)
    next
      case False
      have "1 - (u * u1 + v * u2) = (u + v) - (u * u1 + v * u2)"
        using as(3) obt1(3) obt2(3) by (auto simp add: field_simps)
      also have "\<dots> = u * (v1 + u1 - u1) + v * (v2 + u2 - u2)"
        using as(3) obt1(3) obt2(3) by (auto simp add: field_simps)
      also have "\<dots> = u * v1 + v * v2"
        by simp
      finally have **:"1 - (u * u1 + v * u2) = u * v1 + v * v2" by auto
      have "0 \<le> u * v1 + v * v2" "0 \<le> u * v1" "0 \<le> u * v1 + v * v2" "0 \<le> v * v2"
        apply (rule add_nonneg_nonneg)
        prefer 4
        apply (rule add_nonneg_nonneg)
        apply (rule_tac [!] mult_nonneg_nonneg)
        using as(1,2) obt1(1,2) obt2(1,2)
        apply auto
        done
      then show ?thesis
        unfolding obt1(5) obt2(5)
        unfolding * and **
        using False
        apply (rule_tac x = "((u * v1) / (u * v1 + v * v2)) *\<^sub>R b1 + ((v * v2) / (u * v1 + v * v2)) *\<^sub>R b2" in bexI)
        defer
        apply (rule convex_convex_hull[of s, unfolded convex_def, rule_format])
        using obt1(4) obt2(4)
        unfolding add_divide_distrib[symmetric] and zero_le_divide_iff
        apply (auto simp add: scaleR_left_distrib scaleR_right_distrib)
        done
    qed
    have u1: "u1 \<le> 1"
      unfolding obt1(3)[symmetric] and not_le using obt1(2) by auto
    have u2: "u2 \<le> 1"
      unfolding obt2(3)[symmetric] and not_le using obt2(2) by auto
    have "u1 * u + u2 * v \<le> (max u1 u2) * u + (max u1 u2) * v"
      apply (rule add_mono)
      apply (rule_tac [!] mult_right_mono)
      using as(1,2) obt1(1,2) obt2(1,2)
      apply auto
      done
    also have "\<dots> \<le> 1"
      unfolding distrib_left[symmetric] and as(3) using u1 u2 by auto
    finally show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
      unfolding mem_Collect_eq
      apply (rule_tac x="u * u1 + v * u2" in exI)
      apply (rule conjI)
      defer
      apply (rule_tac x="1 - u * u1 - v * u2" in exI)
      unfolding Bex_def
      using as(1,2) obt1(1,2) obt2(1,2) **
      apply (auto intro!: mult_nonneg_nonneg add_nonneg_nonneg simp add: algebra_simps)
      done
  qed
qed


subsubsection {* Explicit expression for convex hull *}

lemma convex_hull_indexed:
  fixes s :: "'a::real_vector set"
  shows "convex hull s =
    {y. \<exists>k u x. (\<forall>i\<in>{1::nat .. k}. 0 \<le> u i \<and> x i \<in> s) \<and>
        (setsum u {1..k} = 1) \<and>
        (setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} = y)}" (is "?xyz = ?hull")
  apply (rule hull_unique)
  apply rule
  defer
  apply (subst convex_def)
  apply (rule, rule, rule, rule, rule, rule, rule)
proof -
  fix x
  assume "x\<in>s"
  then show "x \<in> ?hull"
    unfolding mem_Collect_eq
    apply (rule_tac x=1 in exI, rule_tac x="\<lambda>x. 1" in exI)
    apply auto
    done
next
  fix t
  assume as: "s \<subseteq> t" "convex t"
  show "?hull \<subseteq> t"
    apply rule
    unfolding mem_Collect_eq
    apply (elim exE conjE)
  proof -
    fix x k u y
    assume assm:
      "\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> s"
      "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
    show "x\<in>t"
      unfolding assm(3) [symmetric]
      apply (rule as(2)[unfolded convex, rule_format])
      using assm(1,2) as(1) apply auto
      done
  qed
next
  fix x y u v
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = (1::real)" and xy: "x \<in> ?hull" "y \<in> ?hull"
  from xy obtain k1 u1 x1 where
      x: "\<forall>i\<in>{1::nat..k1}. 0\<le>u1 i \<and> x1 i \<in> s" "setsum u1 {Suc 0..k1} = 1" "(\<Sum>i = Suc 0..k1. u1 i *\<^sub>R x1 i) = x"
    by auto
  from xy obtain k2 u2 x2 where
      y: "\<forall>i\<in>{1::nat..k2}. 0\<le>u2 i \<and> x2 i \<in> s" "setsum u2 {Suc 0..k2} = 1" "(\<Sum>i = Suc 0..k2. u2 i *\<^sub>R x2 i) = y"
    by auto
  have *: "\<And>P (x1::'a) x2 s1 s2 i.
    (if P i then s1 else s2) *\<^sub>R (if P i then x1 else x2) = (if P i then s1 *\<^sub>R x1 else s2 *\<^sub>R x2)"
    "{1..k1 + k2} \<inter> {1..k1} = {1..k1}" "{1..k1 + k2} \<inter> - {1..k1} = (\<lambda>i. i + k1) ` {1..k2}"
    prefer 3
    apply (rule, rule)
    unfolding image_iff
    apply (rule_tac x = "x - k1" in bexI)
    apply (auto simp add: not_le)
    done
  have inj: "inj_on (\<lambda>i. i + k1) {1..k2}"
    unfolding inj_on_def by auto
  show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
    apply rule
    apply (rule_tac x="k1 + k2" in exI)
    apply (rule_tac x="\<lambda>i. if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)" in exI)
    apply (rule_tac x="\<lambda>i. if i \<in> {1..k1} then x1 i else x2 (i - k1)" in exI)
    apply (rule, rule)
    defer
    apply rule
    unfolding * and setsum_cases[OF finite_atLeastAtMost[of 1 "k1 + k2"]] and
      setsum_reindex[OF inj] and o_def Collect_mem_eq
    unfolding scaleR_scaleR[symmetric] scaleR_right.setsum [symmetric] setsum_right_distrib[symmetric]
  proof -
    fix i
    assume i: "i \<in> {1..k1+k2}"
    show "0 \<le> (if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)) \<and>
      (if i \<in> {1..k1} then x1 i else x2 (i - k1)) \<in> s"
    proof (cases "i\<in>{1..k1}")
      case True
      then show ?thesis
        using mult_nonneg_nonneg[of u "u1 i"] and uv(1) x(1)[THEN bspec[where x=i]] by auto
    next
      case False
      def j \<equiv> "i - k1"
      from i False have "j \<in> {1..k2}" unfolding j_def by auto
      then show ?thesis
        unfolding j_def[symmetric]
        using False
        using mult_nonneg_nonneg[of v "u2 j"] and uv(2) y(1)[THEN bspec[where x=j]]
        apply auto
        done
    qed
  qed (auto simp add: not_le x(2,3) y(2,3) uv(3))
qed

lemma convex_hull_finite:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows "convex hull s = {y. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and>
    setsum u s = 1 \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y}" (is "?HULL = ?set")
proof (rule hull_unique, auto simp add: convex_def[of ?set])
  fix x
  assume "x \<in> s"
  then show "\<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = x"
    apply (rule_tac x="\<lambda>y. if x=y then 1 else 0" in exI)
    apply auto
    unfolding setsum_delta'[OF assms] and setsum_delta''[OF assms]
    apply auto
    done
next
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  fix ux assume ux: "\<forall>x\<in>s. 0 \<le> ux x" "setsum ux s = (1::real)"
  fix uy assume uy: "\<forall>x\<in>s. 0 \<le> uy x" "setsum uy s = (1::real)"
  { fix x
    assume "x\<in>s"
    then have "0 \<le> u * ux x + v * uy x"
      using ux(1)[THEN bspec[where x=x]] uy(1)[THEN bspec[where x=x]] and uv(1,2)
      apply auto
      apply (metis add_nonneg_nonneg mult_nonneg_nonneg uv(1) uv(2))
      done
  }
  moreover
  have "(\<Sum>x\<in>s. u * ux x + v * uy x) = 1"
    unfolding setsum_addf and setsum_right_distrib[symmetric] and ux(2) uy(2)
    using uv(3) by auto
  moreover
  have "(\<Sum>x\<in>s. (u * ux x + v * uy x) *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    unfolding scaleR_left_distrib and setsum_addf and scaleR_scaleR[symmetric] and scaleR_right.setsum [symmetric]
    by auto
  ultimately
  show "\<exists>uc. (\<forall>x\<in>s. 0 \<le> uc x) \<and> setsum uc s = 1 \<and>
      (\<Sum>x\<in>s. uc x *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    apply (rule_tac x="\<lambda>x. u * ux x + v * uy x" in exI)
    apply auto
    done
next
  fix t
  assume t: "s \<subseteq> t" "convex t"
  fix u
  assume u: "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = (1::real)"
  then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> t"
    using t(2)[unfolded convex_explicit, THEN spec[where x=s], THEN spec[where x=u]]
    using assms and t(1) by auto
qed


subsubsection {* Another formulation from Lars Schewe *}

lemma setsum_constant_scaleR:
  fixes y :: "'a::real_vector"
  shows "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>R y"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (simp_all add: algebra_simps)
  done

lemma convex_hull_explicit:
  fixes p :: "'a::real_vector set"
  shows "convex hull p = {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and>
    (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}" (is "?lhs = ?rhs")
proof -
  {
    fix x
    assume "x\<in>?lhs"
    then obtain k u y where
        obt: "\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> p" "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
      unfolding convex_hull_indexed by auto

    have fin: "finite {1..k}" by auto
    have fin': "\<And>v. finite {i \<in> {1..k}. y i = v}" by auto
    {
      fix j
      assume "j\<in>{1..k}"
      then have "y j \<in> p" "0 \<le> setsum u {i. Suc 0 \<le> i \<and> i \<le> k \<and> y i = y j}"
        using obt(1)[THEN bspec[where x=j]] and obt(2)
        apply simp
        apply (rule setsum_nonneg)
        using obt(1)
        apply auto
        done
    }
    moreover
    have "(\<Sum>v\<in>y ` {1..k}. setsum u {i \<in> {1..k}. y i = v}) = 1"
      unfolding setsum_image_gen[OF fin, symmetric] using obt(2) by auto
    moreover have "(\<Sum>v\<in>y ` {1..k}. setsum u {i \<in> {1..k}. y i = v} *\<^sub>R v) = x"
      using setsum_image_gen[OF fin, of "\<lambda>i. u i *\<^sub>R y i" y, symmetric]
      unfolding scaleR_left.setsum using obt(3) by auto
    ultimately
    have "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
      apply (rule_tac x="y ` {1..k}" in exI)
      apply (rule_tac x="\<lambda>v. setsum u {i\<in>{1..k}. y i = v}" in exI)
      apply auto
      done
    then have "x\<in>?rhs" by auto
  }
  moreover
  {
    fix y
    assume "y\<in>?rhs"
    then obtain s u where
      obt: "finite s" "s \<subseteq> p" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = y" by auto

    obtain f where f: "inj_on f {1..card s}" "f ` {1..card s} = s"
      using ex_bij_betw_nat_finite_1[OF obt(1)] unfolding bij_betw_def by auto

    {
      fix i :: nat
      assume "i\<in>{1..card s}"
      then have "f i \<in> s"
        apply (subst f(2)[symmetric])
        apply auto
        done
      then have "0 \<le> u (f i)" "f i \<in> p" using obt(2,3) by auto
    }
    moreover have *:"finite {1..card s}" by auto
    {
      fix y
      assume "y\<in>s"
      then obtain i where "i\<in>{1..card s}" "f i = y"
        using f using image_iff[of y f "{1..card s}"]
        by auto
      then have "{x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = {i}"
        apply auto
        using f(1)[unfolded inj_on_def]
        apply(erule_tac x=x in ballE)
        apply auto
        done
      then have "card {x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = 1" by auto
      then have "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x)) = u y"
          "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x) = u y *\<^sub>R y"
        by (auto simp add: setsum_constant_scaleR)
    }
    then have "(\<Sum>x = 1..card s. u (f x)) = 1" "(\<Sum>i = 1..card s. u (f i) *\<^sub>R f i) = y"
      unfolding setsum_image_gen[OF *(1), of "\<lambda>x. u (f x) *\<^sub>R f x" f] and setsum_image_gen[OF *(1), of "\<lambda>x. u (f x)" f]
      unfolding f using setsum_cong2[of s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x)" "\<lambda>v. u v *\<^sub>R v"]
      using setsum_cong2 [of s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x))" u]
      unfolding obt(4,5)
      by auto
    ultimately
    have "\<exists>k u x. (\<forall>i\<in>{1..k}. 0 \<le> u i \<and> x i \<in> p) \<and> setsum u {1..k} = 1 \<and>
        (\<Sum>i::nat = 1..k. u i *\<^sub>R x i) = y"
      apply (rule_tac x="card s" in exI)
      apply (rule_tac x="u \<circ> f" in exI)
      apply (rule_tac x=f in exI)
      apply fastforce
      done
    then have "y \<in> ?lhs"
      unfolding convex_hull_indexed by auto
  }
  ultimately show ?thesis
    unfolding set_eq_iff by blast
qed


subsubsection {* A stepping theorem for that expansion *}

lemma convex_hull_finite_step:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows
    "(\<exists>u. (\<forall>x\<in>insert a s. 0 \<le> u x) \<and> setsum u (insert a s) = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y)
      \<longleftrightarrow> (\<exists>v\<ge>0. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = w - v \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)"
  (is "?lhs = ?rhs")
proof (rule, case_tac[!] "a\<in>s")
  assume "a \<in> s"
  then have *:" insert a s = s" by auto
  assume ?lhs
  then show ?rhs
    unfolding *
    apply (rule_tac x=0 in exI)
    apply auto
    done
next
  assume ?lhs
  then obtain u where
      u: "\<forall>x\<in>insert a s. 0 \<le> u x" "setsum u (insert a s) = w" "(\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y"
    by auto
  assume "a \<notin> s"
  then show ?rhs
    apply (rule_tac x="u a" in exI)
    using u(1)[THEN bspec[where x=a]]
    apply simp
    apply (rule_tac x=u in exI)
    using u[unfolded setsum_clauses(2)[OF assms]] and `a\<notin>s`
    apply auto
    done
next
  assume "a \<in> s"
  then have *: "insert a s = s" by auto
  have fin: "finite (insert a s)" using assms by auto
  assume ?rhs
  then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  show ?lhs
    apply (rule_tac x = "\<lambda>x. (if a = x then v else 0) + u x" in exI)
    unfolding scaleR_left_distrib and setsum_addf and setsum_delta''[OF fin] and setsum_delta'[OF fin]
    unfolding setsum_clauses(2)[OF assms]
    using uv and uv(2)[THEN bspec[where x=a]] and `a\<in>s`
    apply auto
    done
next
  assume ?rhs
  then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  moreover
  assume "a \<notin> s"
  moreover
  have "(\<Sum>x\<in>s. if a = x then v else u x) = setsum u s"
    and "(\<Sum>x\<in>s. (if a = x then v else u x) *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)"
    apply (rule_tac setsum_cong2)
    defer
    apply (rule_tac setsum_cong2)
    using `a \<notin> s`
    apply auto
    done
  ultimately show ?lhs
    apply (rule_tac x="\<lambda>x. if a = x then v else u x" in exI)
    unfolding setsum_clauses(2)[OF assms]
    apply auto
    done
qed


subsubsection {* Hence some special cases *}

lemma convex_hull_2:
  "convex hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b | u v. 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1}"
proof -
  have *: "\<And>u. (\<forall>x\<in>{a, b}. 0 \<le> u x) \<longleftrightarrow> 0 \<le> u a \<and> 0 \<le> u b"
    by auto
  have **: "finite {b}" by auto
  show ?thesis
    apply (simp add: convex_hull_finite)
    unfolding convex_hull_finite_step[OF **, of a 1, unfolded * conj_assoc]
    apply auto
    apply (rule_tac x=v in exI)
    apply (rule_tac x="1 - v" in exI)
    apply simp
    apply (rule_tac x=u in exI)
    apply simp
    apply (rule_tac x="\<lambda>x. v" in exI)
    apply simp
    done
qed

lemma convex_hull_2_alt: "convex hull {a,b} = {a + u *\<^sub>R (b - a) | u.  0 \<le> u \<and> u \<le> 1}"
  unfolding convex_hull_2
proof (rule Collect_cong)
  have *: "\<And>x y ::real. x + y = 1 \<longleftrightarrow> x = 1 - y"
    by auto
  fix x
  show "(\<exists>v u. x = v *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> v \<and> 0 \<le> u \<and> v + u = 1) \<longleftrightarrow>
    (\<exists>u. x = a + u *\<^sub>R (b - a) \<and> 0 \<le> u \<and> u \<le> 1)"
    unfolding *
    apply auto
    apply (rule_tac[!] x=u in exI)
    apply (auto simp add: algebra_simps)
    done
qed

lemma convex_hull_3:
  "convex hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
proof -
  have fin: "finite {a,b,c}" "finite {b,c}" "finite {c}"
    by auto
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by (auto simp add: field_simps)
  show ?thesis
    unfolding convex_hull_finite[OF fin(1)] and convex_hull_finite_step[OF fin(2)] and *
    unfolding convex_hull_finite_step[OF fin(3)]
    apply (rule Collect_cong)
    apply simp
    apply auto
    apply (rule_tac x=va in exI)
    apply (rule_tac x="u c" in exI)
    apply simp
    apply (rule_tac x="1 - v - w" in exI)
    apply simp
    apply (rule_tac x=v in exI)
    apply simp
    apply (rule_tac x="\<lambda>x. w" in exI)
    apply simp
    done
qed

lemma convex_hull_3_alt:
  "convex hull {a,b,c} = {a + u *\<^sub>R (b - a) + v *\<^sub>R (c - a) | u v.  0 \<le> u \<and> 0 \<le> v \<and> u + v \<le> 1}"
proof -
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by auto
  show ?thesis
    unfolding convex_hull_3
    apply (auto simp add: *)
    apply (rule_tac x=v in exI)
    apply (rule_tac x=w in exI)
    apply (simp add: algebra_simps)
    apply (rule_tac x=u in exI)
    apply (rule_tac x=v in exI)
    apply (simp add: algebra_simps)
    done
qed


subsection {* Relations among closure notions and corresponding hulls *}

lemma affine_imp_convex: "affine s \<Longrightarrow> convex s"
  unfolding affine_def convex_def by auto

lemma subspace_imp_convex: "subspace s \<Longrightarrow> convex s"
  using subspace_imp_affine affine_imp_convex by auto

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_inc subspace_imp_affine subspace_span)

lemma convex_hull_subset_span: "(convex hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_inc subspace_imp_convex subspace_span)

lemma convex_hull_subset_affine_hull: "(convex hull s) \<subseteq> (affine hull s)"
  by (metis affine_affine_hull affine_imp_convex hull_minimal hull_subset)


lemma affine_dependent_imp_dependent: "affine_dependent s \<Longrightarrow> dependent s"
  unfolding affine_dependent_def dependent_def
  using affine_hull_subset_span by auto

lemma dependent_imp_affine_dependent:
  assumes "dependent {x - a| x . x \<in> s}"
    and "a \<notin> s"
  shows "affine_dependent (insert a s)"
proof -
  from assms(1)[unfolded dependent_explicit] obtain S u v
    where obt:"finite S" "S \<subseteq> {x - a |x. x \<in> s}" "v\<in>S" "u v  \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0" by auto
  def t \<equiv> "(\<lambda>x. x + a) ` S"

  have inj:"inj_on (\<lambda>x. x + a) S"
    unfolding inj_on_def by auto
  have "0 \<notin> S"
    using obt(2) assms(2) unfolding subset_eq by auto
  have fin: "finite t" and  "t \<subseteq> s"
    unfolding t_def using obt(1,2) by auto
  then have "finite (insert a t)" and "insert a t \<subseteq> insert a s"
    by auto
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x)) = (\<Sum>x\<in>t. Q x)"
    apply (rule setsum_cong2)
    using `a\<notin>s` `t\<subseteq>s`
    apply auto
    done
  have "(\<Sum>x\<in>insert a t. if x = a then - (\<Sum>x\<in>t. u (x - a)) else u (x - a)) = 0"
    unfolding setsum_clauses(2)[OF fin]
    using `a\<notin>s` `t\<subseteq>s`
    apply auto
    unfolding *
    apply auto
    done
  moreover have "\<exists>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) \<noteq> 0"
    apply (rule_tac x="v + a" in bexI)
    using obt(3,4) and `0\<notin>S`
    unfolding t_def
    apply auto
    done
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>t. Q x *\<^sub>R x)"
    apply (rule setsum_cong2)
    using `a\<notin>s` `t\<subseteq>s`
    apply auto
    done
  have "(\<Sum>x\<in>t. u (x - a)) *\<^sub>R a = (\<Sum>v\<in>t. u (v - a) *\<^sub>R v)"
    unfolding scaleR_left.setsum
    unfolding t_def and setsum_reindex[OF inj] and o_def
    using obt(5)
    by (auto simp add: setsum_addf scaleR_right_distrib)
  then have "(\<Sum>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) *\<^sub>R v) = 0"
    unfolding setsum_clauses(2)[OF fin]
    using `a\<notin>s` `t\<subseteq>s`
    by (auto simp add: *)
  ultimately show ?thesis
    unfolding affine_dependent_explicit
    apply (rule_tac x="insert a t" in exI)
    apply auto
    done
qed

lemma convex_cone:
  "convex s \<and> cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. (x + y) \<in> s) \<and> (\<forall>x\<in>s. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> s)"
  (is "?lhs = ?rhs")
proof -
  {
    fix x y
    assume "x\<in>s" "y\<in>s" and ?lhs
    then have "2 *\<^sub>R x \<in>s" "2 *\<^sub>R y \<in> s"
      unfolding cone_def by auto
    then have "x + y \<in> s"
      using `?lhs`[unfolded convex_def, THEN conjunct1]
      apply (erule_tac x="2*\<^sub>R x" in ballE)
      apply (erule_tac x="2*\<^sub>R y" in ballE)
      apply (erule_tac x="1/2" in allE)
      apply simp
      apply (erule_tac x="1/2" in allE)
      apply auto
      done
  }
  then show ?thesis
    unfolding convex_def cone_def by blast
qed

lemma affine_dependent_biggerset:
  fixes s::"('a::euclidean_space) set"
  assumes "finite s" "card s \<ge> DIM('a) + 2"
  shows "affine_dependent s"
proof -
  have "s \<noteq> {}" using assms by auto
  then obtain a where "a\<in>s" by auto
  have *: "{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})"
    by auto
  have "card {x - a |x. x \<in> s - {a}} = card (s - {a})"
    unfolding *
    apply (rule card_image)
    unfolding inj_on_def
    apply auto
    done
  also have "\<dots> > DIM('a)" using assms(2)
    unfolding card_Diff_singleton[OF assms(1) `a\<in>s`] by auto
  finally show ?thesis
    apply (subst insert_Diff[OF `a\<in>s`, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset)
    apply auto
    done
qed

lemma affine_dependent_biggerset_general:
  assumes "finite (s::('a::euclidean_space) set)" "card s \<ge> dim s + 2"
  shows "affine_dependent s"
proof -
  from assms(2) have "s \<noteq> {}" by auto
  then obtain a where "a\<in>s" by auto
  have *: "{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})"
    by auto
  have **: "card {x - a |x. x \<in> s - {a}} = card (s - {a})"
    unfolding *
    apply (rule card_image)
    unfolding inj_on_def
    apply auto
    done
  have "dim {x - a |x. x \<in> s - {a}} \<le> dim s"
    apply (rule subset_le_dim)
    unfolding subset_eq
    using `a\<in>s`
    apply (auto simp add:span_superset span_sub)
    done
  also have "\<dots> < dim s + 1" by auto
  also have "\<dots> \<le> card (s - {a})"
    using assms
    using card_Diff_singleton[OF assms(1) `a\<in>s`]
    by auto
  finally show ?thesis
    apply (subst insert_Diff[OF `a\<in>s`, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset_general)
    unfolding **
    apply auto
    done
qed


subsection {* Caratheodory's theorem. *}

lemma convex_hull_caratheodory:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p =
    {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and>
      (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding convex_hull_explicit set_eq_iff mem_Collect_eq
proof (rule, rule)
  fix y
  let ?P = "\<lambda>n. \<exists>s u. finite s \<and> card s = n \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and>
    setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  assume "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  then obtain N where "?P N" by auto
  then have "\<exists>n\<le>N. (\<forall>k<n. \<not> ?P k) \<and> ?P n"
    apply (rule_tac ex_least_nat_le)
    apply auto
    done
  then obtain n where "?P n" and smallest: "\<forall>k<n. \<not> ?P k"
    by blast
  then obtain s u where obt: "finite s" "card s = n" "s\<subseteq>p" "\<forall>x\<in>s. 0 \<le> u x"
    "setsum u s = 1"  "(\<Sum>v\<in>s. u v *\<^sub>R v) = y" by auto

  have "card s \<le> DIM('a) + 1"
  proof (rule ccontr, simp only: not_le)
    assume "DIM('a) + 1 < card s"
    then have "affine_dependent s"
      using affine_dependent_biggerset[OF obt(1)] by auto
    then obtain w v where wv: "setsum w s = 0" "v\<in>s" "w v \<noteq> 0" "(\<Sum>v\<in>s. w v *\<^sub>R v) = 0"
      using affine_dependent_explicit_finite[OF obt(1)] by auto
    def i \<equiv> "(\<lambda>v. (u v) / (- w v)) ` {v\<in>s. w v < 0}"
    def t \<equiv> "Min i"
    have "\<exists>x\<in>s. w x < 0"
    proof (rule ccontr, simp add: not_less)
      assume as:"\<forall>x\<in>s. 0 \<le> w x"
      then have "setsum w (s - {v}) \<ge> 0"
        apply (rule_tac setsum_nonneg)
        apply auto
        done
      then have "setsum w s > 0"
        unfolding setsum_diff1'[OF obt(1) `v\<in>s`]
        using as[THEN bspec[where x=v]] and `v\<in>s`
        using `w v \<noteq> 0`
        by auto
      then show False using wv(1) by auto
    qed
    then have "i \<noteq> {}" unfolding i_def by auto

    then have "t \<ge> 0"
      using Min_ge_iff[of i 0 ] and obt(1)
      unfolding t_def i_def
      using obt(4)[unfolded le_less]
      apply auto
      unfolding divide_le_0_iff
      apply auto
      done
    have t: "\<forall>v\<in>s. u v + t * w v \<ge> 0"
    proof
      fix v
      assume "v \<in> s"
      then have v: "0 \<le> u v"
        using obt(4)[THEN bspec[where x=v]] by auto
      show "0 \<le> u v + t * w v"
      proof (cases "w v < 0")
        case False
        then show ?thesis
          apply (rule_tac add_nonneg_nonneg)
          using v
          apply simp
          apply (rule mult_nonneg_nonneg)
          using `t\<ge>0`
          apply auto
          done
      next
        case True
        then have "t \<le> u v / (- w v)"
          using `v\<in>s`
          unfolding t_def i_def
          apply (rule_tac Min_le)
          using obt(1)
          apply auto
          done
        then show ?thesis
          unfolding real_0_le_add_iff
          using pos_le_divide_eq[OF True[unfolded neg_0_less_iff_less[symmetric]]]
          by auto
      qed
    qed

    obtain a where "a \<in> s" and "t = (\<lambda>v. (u v) / (- w v)) a" and "w a < 0"
      using Min_in[OF _ `i\<noteq>{}`] and obt(1) unfolding i_def t_def by auto
    then have a: "a \<in> s" "u a + t * w a = 0" by auto
    have *: "\<And>f. setsum f (s - {a}) = setsum f s - ((f a)::'b::ab_group_add)"
      unfolding setsum_diff1'[OF obt(1) `a\<in>s`] by auto
    have "(\<Sum>v\<in>s. u v + t * w v) = 1"
      unfolding setsum_addf wv(1) setsum_right_distrib[symmetric] obt(5) by auto
    moreover have "(\<Sum>v\<in>s. u v *\<^sub>R v + (t * w v) *\<^sub>R v) - (u a *\<^sub>R a + (t * w a) *\<^sub>R a) = y"
      unfolding setsum_addf obt(6) scaleR_scaleR[symmetric] scaleR_right.setsum [symmetric] wv(4)
      using a(2) [THEN eq_neg_iff_add_eq_0 [THEN iffD2]] by simp
    ultimately have "?P (n - 1)"
      apply (rule_tac x="(s - {a})" in exI)
      apply (rule_tac x="\<lambda>v. u v + t * w v" in exI)
      using obt(1-3) and t and a
      apply (auto simp add: * scaleR_left_distrib)
      done
    then show False
      using smallest[THEN spec[where x="n - 1"]] by auto
  qed
  then show "\<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and>
    (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y" using obt by auto
qed auto

lemma caratheodory:
  "convex hull p =
    {x::'a::euclidean_space. \<exists>s. finite s \<and> s \<subseteq> p \<and>
      card s \<le> DIM('a) + 1 \<and> x \<in> convex hull s}"
  unfolding set_eq_iff
  apply rule
  apply rule
  unfolding mem_Collect_eq
proof -
  fix x
  assume "x \<in> convex hull p"
  then obtain s u where "finite s" "s \<subseteq> p" "card s \<le> DIM('a) + 1"
    "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    unfolding convex_hull_caratheodory by auto
  then show "\<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and> x \<in> convex hull s"
    apply (rule_tac x=s in exI)
    using hull_subset[of s convex]
    using convex_convex_hull[unfolded convex_explicit, of s, THEN spec[where x=s], THEN spec[where x=u]]
    apply auto
    done
next
  fix x
  assume "\<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and> x \<in> convex hull s"
  then obtain s where "finite s" "s \<subseteq> p" "card s \<le> DIM('a) + 1" "x \<in> convex hull s"
    by auto
  then show "x \<in> convex hull p"
    using hull_mono[OF `s\<subseteq>p`] by auto
qed


subsection {* Some Properties of Affine Dependent Sets *}

lemma affine_independent_empty: "~(affine_dependent {})"
  by (simp add: affine_dependent_def)

lemma affine_independent_sing: "\<not> affine_dependent {a}"
  by (simp add: affine_dependent_def)

lemma affine_hull_translation: "affine hull ((\<lambda>x. a + x) `  S) = (\<lambda>x. a + x) ` (affine hull S)"
proof -
  have "affine ((\<lambda>x. a + x) ` (affine hull S))"
    using affine_translation affine_affine_hull by auto
  moreover have "(\<lambda>x. a + x) `  S <= (\<lambda>x. a + x) ` (affine hull S)"
    using hull_subset[of S] by auto
  ultimately have h1: "affine hull ((\<lambda>x. a + x) `  S) <= (\<lambda>x. a + x) ` (affine hull S)"
    by (metis hull_minimal)
  have "affine((\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)))"
    using affine_translation affine_affine_hull by auto
  moreover have "(\<lambda>x. -a + x) ` (%x. a + x) `  S <= (\<lambda>x. -a + x) ` (affine hull ((%x. a + x) `  S))"
    using hull_subset[of "(\<lambda>x. a + x) `  S"] by auto
  moreover have "S = (\<lambda>x. -a + x) ` (%x. a + x) `  S"
    using translation_assoc[of "-a" a] by auto
  ultimately have "(\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)) >= (affine hull S)"
    by (metis hull_minimal)
  then have "affine hull ((\<lambda>x. a + x) ` S) >= (\<lambda>x. a + x) ` (affine hull S)"
    by auto
  from this show ?thesis using h1 by auto
qed

lemma affine_dependent_translation:
  assumes "affine_dependent S"
  shows "affine_dependent ((%x. a + x) ` S)"
proof -
  obtain x where x_def: "x : S & x : affine hull (S - {x})"
    using assms affine_dependent_def by auto
  have "op + a ` (S - {x}) = op + a ` S - {a + x}"
    by auto
  then have "a+x \<in> affine hull ((%x. a + x) ` S - {a+x})"
    using affine_hull_translation[of a "S-{x}"] x_def by auto
  moreover have "a+x : (\<lambda>x. a + x) ` S"
    using x_def by auto
  ultimately show ?thesis
    unfolding affine_dependent_def by auto
qed

lemma affine_dependent_translation_eq:
  "affine_dependent S <-> affine_dependent ((%x. a + x) ` S)"
proof -
  {
    assume "affine_dependent ((%x. a + x) ` S)"
    then have "affine_dependent S"
      using affine_dependent_translation[of "((%x. a + x) ` S)" "-a"] translation_assoc[of "-a" a]
      by auto
  }
  then show ?thesis
    using affine_dependent_translation by auto
qed

lemma affine_hull_0_dependent:
  assumes "0 : affine hull S"
  shows "dependent S"
proof -
  obtain s u where s_u_def: "finite s & s ~= {} & s <= S & setsum u s = 1 & (SUM v:s. u v *\<^sub>R v) = 0"
    using assms affine_hull_explicit[of S] by auto
  then have "EX v:s. u v \<noteq> 0"
    using setsum_not_0[of "u" "s"] by auto
  then have "finite s & s <= S & (EX v:s. u v ~= 0 & (SUM v:s. u v *\<^sub>R v) = 0)"
    using s_u_def by auto
  then show ?thesis
    unfolding dependent_explicit[of S] by auto
qed

lemma affine_dependent_imp_dependent2:
  assumes "affine_dependent (insert 0 S)"
  shows "dependent S"
proof -
  obtain x where x_def: "x:insert 0 S & x : affine hull (insert 0 S - {x})"
    using affine_dependent_def[of "(insert 0 S)"] assms by blast
  then have "x \<in> span (insert 0 S - {x})"
    using affine_hull_subset_span by auto
  moreover have "span (insert 0 S - {x}) = span (S - {x})"
    using insert_Diff_if[of "0" S "{x}"] span_insert_0[of "S-{x}"] by auto
  ultimately have "x \<in> span (S - {x})" by auto
  then have "x \<noteq> 0 \<Longrightarrow> dependent S"
    using x_def dependent_def by auto
  moreover
  {
    assume "x = 0"
    then have "0 \<in> affine hull S"
      using x_def hull_mono[of "S - {0}" S] by auto
    then have "dependent S"
      using affine_hull_0_dependent by auto
  }
  ultimately show ?thesis by auto
qed

lemma affine_dependent_iff_dependent:
  assumes "a \<notin> S"
  shows "affine_dependent (insert a S) \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` S)"
proof -
  have "(op + (- a) ` S) = {x - a| x . x : S}" by auto
  then show ?thesis
    using affine_dependent_translation_eq[of "(insert a S)" "-a"]
      affine_dependent_imp_dependent2 assms
      dependent_imp_affine_dependent[of a S]
    by auto
qed

lemma affine_dependent_iff_dependent2:
  assumes "a : S"
  shows "affine_dependent S <-> dependent ((%x. -a + x) ` (S-{a}))"
proof -
  have "insert a (S - {a})=S"
    using assms by auto
  then show ?thesis
    using assms affine_dependent_iff_dependent[of a "S-{a}"] by auto
qed

lemma affine_hull_insert_span_gen:
  "affine hull (insert a s) = (%x. a+x) ` span ((%x. -a+x) ` s)"
proof -
  have h1: "{x - a |x. x : s}=((%x. -a+x) ` s)"
    by auto
  {
    assume "a \<notin> s"
    then have ?thesis
      using affine_hull_insert_span[of a s] h1 by auto
  }
  moreover
  {
    assume a1: "a \<in> s"
    have "\<exists>x. x \<in> s & -a+x=0"
      apply (rule exI[of _ a])
      using a1
      apply auto
      done
    then have "insert 0 ((%x. -a+x) ` (s - {a}))=(%x. -a+x) ` s"
      by auto
    then have "span ((%x. -a+x) ` (s - {a}))=span ((%x. -a+x) ` s)"
      using span_insert_0[of "op + (- a) ` (s - {a})"] by auto
    moreover have "{x - a |x. x : (s - {a})}=((%x. -a+x) ` (s - {a}))"
      by auto
    moreover have "insert a (s - {a})=(insert a s)"
      using assms by auto
    ultimately have ?thesis
      using assms affine_hull_insert_span[of "a" "s-{a}"] by auto
  }
  ultimately show ?thesis by auto
qed

lemma affine_hull_span2:
  assumes "a \<in> s"
  shows "affine hull s = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` (s-{a}))"
  using affine_hull_insert_span_gen[of a "s - {a}", unfolded insert_Diff[OF assms]]
  by auto

lemma affine_hull_span_gen:
  assumes "a : affine hull s"
  shows "affine hull s = (%x. a+x) ` span ((%x. -a+x) ` s)"
proof -
  have "affine hull (insert a s) = affine hull s"
    using hull_redundant[of a affine s] assms by auto
  then show ?thesis
    using affine_hull_insert_span_gen[of a "s"] by auto
qed

lemma affine_hull_span_0:
  assumes "0 : affine hull S"
  shows "affine hull S = span S"
  using affine_hull_span_gen[of "0" S] assms by auto


lemma extend_to_affine_basis:
  fixes S V :: "('n::euclidean_space) set"
  assumes "\<not> affine_dependent S" "S <= V" "S \<noteq> {}"
  shows "\<exists>T. \<not> affine_dependent T & S <=T & T <= V & affine hull T = affine hull V"
proof -
  obtain a where a_def: "a \<in> S"
    using assms by auto
  then have h0: "independent  ((%x. -a + x) ` (S-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  then obtain B where B_def:
    "(%x. -a+x) ` (S - {a}) <= B & B <= (%x. -a+x) ` V & independent B & (%x. -a+x) ` V <= span B"
     using maximal_independent_subset_extend[of "(%x. -a+x) ` (S-{a})" "(%x. -a + x) ` V"] assms
     by blast
  def T \<equiv> "(%x. a+x) ` (insert 0 B)"
  then have "T = insert a ((%x. a+x) ` B)" by auto
  then have "affine hull T = (%x. a+x) ` span B"
    using affine_hull_insert_span_gen[of a "((%x. a+x) ` B)"] translation_assoc[of "-a" a B]
    by auto
  then have "V <= affine hull T"
    using B_def assms translation_inverse_subset[of a V "span B"]
    by auto
  moreover have "T<=V"
    using T_def B_def a_def assms by auto
  ultimately have "affine hull T = affine hull V"
    by (metis Int_absorb1 Int_absorb2 hull_hull hull_mono)
  moreover have "S <= T"
    using T_def B_def translation_inverse_subset[of a "S-{a}" B]
    by auto
  moreover have "\<not> affine_dependent T"
    using T_def affine_dependent_translation_eq[of "insert 0 B"] affine_dependent_imp_dependent2 B_def
    by auto
  ultimately show ?thesis using `T<=V` by auto
qed

lemma affine_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. B <= V & \<not> affine_dependent B & affine hull V = affine hull B"
proof (cases "V = {}")
  case True
  then show ?thesis
    using affine_independent_empty by auto
next
  case False
  then obtain x where "x \<in> V" by auto
  then show ?thesis
    using affine_dependent_def[of "{x}"] extend_to_affine_basis[of "{x}:: ('n::euclidean_space) set" V]
    by auto
qed


subsection {* Affine Dimension of a Set *}

definition "aff_dim V =
  (SOME d :: int. ? B. (affine hull B=affine hull V) & ~(affine_dependent B) & (of_nat(card B) = d+1))"

lemma aff_dim_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "? B. (affine hull B=affine hull V) & ~(affine_dependent B) & (of_nat(card B) = aff_dim V+1)"
proof -
  obtain B where B_def: "\<not> affine_dependent B & affine hull B = affine hull V"
    using affine_basis_exists[of V] by auto
  then show ?thesis
    unfolding aff_dim_def some_eq_ex[of "\<lambda>d. \<exists>(B :: ('n::euclidean_space) set). affine hull B = affine hull V
      & \<not> affine_dependent B & of_nat (card B) = d+1"]
    apply auto
    apply (rule exI[of _ "int (card B)-(1 :: int)"])
    apply (rule exI[of _ "B"])
    apply auto
    done
qed

lemma affine_hull_nonempty: "S \<noteq> {} \<longleftrightarrow> affine hull S \<noteq> {}"
proof -
  have "S = {} \<Longrightarrow> affine hull S = {}"
    using affine_hull_empty by auto
  moreover have "affine hull S = {} \<Longrightarrow> S = {}"
    unfolding hull_def by auto
  ultimately show ?thesis by blast
qed

lemma aff_dim_parallel_subspace_aux:
  fixes B :: "('n::euclidean_space) set"
  assumes "\<not> affine_dependent B" "a \<in> B"
  shows "finite B & ((card B) - 1 = dim (span ((%x. -a+x) ` (B-{a}))))"
proof -
  have "independent ((%x. -a + x) ` (B-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  then have fin: "dim (span ((%x. -a+x) ` (B-{a}))) = card ((%x. -a + x) ` (B-{a}))"
    "finite ((%x. -a + x) ` (B - {a}))"  using indep_card_eq_dim_span[of "(%x. -a+x) ` (B-{a})"]
    by auto
  show ?thesis
  proof (cases "(%x. -a + x) ` (B - {a}) = {}")
    case True
    have "B = insert a ((%x. a + x) ` (%x. -a + x) ` (B - {a}))"
      using translation_assoc[of "a" "-a" "(B - {a})"] assms by auto
    then have "B={a}" using True by auto
    then show ?thesis using assms fin by auto
  next
    case False
    then have "card ((%x. -a + x) ` (B - {a}))>0"
      using fin by auto
    moreover have h1: "card ((%x. -a + x) ` (B-{a})) = card (B-{a})"
       apply (rule card_image)
       using translate_inj_on
       apply auto
       done
    ultimately have "card (B-{a})>0" by auto
    then have *: "finite(B-{a})"
      using card_gt_0_iff[of "(B - {a})"] by auto
    then have "(card (B-{a})= (card B) - 1)"
      using card_Diff_singleton assms by auto
    with * show ?thesis using fin h1 by auto
  qed
qed

lemma aff_dim_parallel_subspace:
  fixes V L :: "('n::euclidean_space) set"
  assumes "V \<noteq> {}"
  assumes "subspace L" "affine_parallel (affine hull V) L"
  shows "aff_dim V = int (dim L)"
proof -
  obtain B where B_def: "affine hull B = affine hull V & ~ affine_dependent B & int (card B) = aff_dim V + 1"
    using aff_dim_basis_exists by auto
  then have "B \<noteq> {}"
    using assms B_def affine_hull_nonempty[of V] affine_hull_nonempty[of B]
    by auto
  then obtain a where a_def: "a \<in> B" by auto
  def Lb \<equiv> "span ((\<lambda>x. -a+x) ` (B-{a}))"
  moreover have "affine_parallel (affine hull B) Lb"
    using Lb_def B_def assms affine_hull_span2[of a B] a_def  affine_parallel_commut[of "Lb" "(affine hull B)"]
    unfolding affine_parallel_def by auto
  moreover have "subspace Lb"
    using Lb_def subspace_span by auto
  moreover have "affine hull B \<noteq> {}"
    using assms B_def affine_hull_nonempty[of V] by auto
  ultimately have "L = Lb"
    using assms affine_parallel_subspace[of "affine hull B"] affine_affine_hull[of B] B_def
    by auto
  then have "dim L = dim Lb" by auto
  moreover have "(card B) - 1 = dim Lb" "finite B"
    using Lb_def aff_dim_parallel_subspace_aux a_def B_def by auto
(*  hence "card B=dim Lb+1" using `B~={}` card_gt_0_iff[of B] by auto *)
  ultimately show ?thesis
    using B_def `B \<noteq> {}` card_gt_0_iff[of B] by auto
qed

lemma aff_independent_finite:
  fixes B :: "('n::euclidean_space) set"
  assumes "~(affine_dependent B)"
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

lemma independent_finite:
  fixes B :: "('n::euclidean_space) set"
  assumes "independent B"
  shows "finite B"
  using affine_dependent_imp_dependent[of B] aff_independent_finite[of B] assms
  by auto

lemma subspace_dim_equal:
  assumes "subspace (S :: ('n::euclidean_space) set)" "subspace T" "S <= T" "dim S >= dim T"
  shows "S = T"
proof -
  obtain B where B_def: "B <= S & independent B & S <= span B & (card B = dim S)" using basis_exists[of S] by auto
  hence "span B <= S" using span_mono[of B S] span_eq[of S] assms by metis
  hence "span B = S" using B_def by auto
  have "dim S = dim T" using assms dim_subset[of S T] by auto
  hence "T <= span B" using card_eq_dim[of B T] B_def independent_finite assms by auto
  from this show ?thesis using assms `span B=S` by auto
qed

lemma span_substd_basis:
  assumes d: "d \<subseteq> Basis"
  shows "span d = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}" (is "_ = ?B")
proof-
have "d <= ?B" using d by (auto simp: inner_Basis)
moreover have s: "subspace ?B" using subspace_substandard[of "%i. i ~: d"] .
ultimately have "span d <= ?B" using span_mono[of d "?B"] span_eq[of "?B"] by blast
moreover have "card d <= dim (span d)" using independent_card_le_dim[of d "span d"]
   independent_substdbasis[OF assms] span_inc[of d] by auto
moreover hence "dim ?B <= dim (span d)" using dim_substandard[OF assms] by auto
ultimately show ?thesis using s subspace_dim_equal[of "span d" "?B"]
  subspace_span[of d] by auto
qed

lemma basis_to_substdbasis_subspace_isomorphism:
fixes B :: "('a::euclidean_space) set"
assumes "independent B"
shows "EX f (d::'a set). card d = card B \<and> linear f \<and> f ` B = d \<and>
       f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} \<and> inj_on f (span B) \<and> d \<subseteq> Basis"
proof-
  have B:"card B=dim B" using dim_unique[of B B "card B"] assms span_inc[of B] by auto
  have "dim B \<le> card (Basis :: 'a set)" using dim_subset_UNIV[of B] by simp
  from ex_card[OF this] obtain d :: "'a set" where d: "d \<subseteq> Basis" and t: "card d = dim B" by auto
  let ?t = "{x::'a::euclidean_space. \<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0}"
  have "EX f. linear f & f ` B = d & f ` span B = ?t & inj_on f (span B)"
    apply (rule basis_to_basis_subspace_isomorphism[of "span B" ?t B "d"])
    apply(rule subspace_span) apply(rule subspace_substandard) defer
    apply(rule span_inc) apply(rule assms) defer unfolding dim_span[of B] apply(rule B)
    unfolding span_substd_basis[OF d, symmetric] 
    apply(rule span_inc)
    apply(rule independent_substdbasis[OF d]) apply(rule,assumption)
    unfolding t[symmetric] span_substd_basis[OF d] dim_substandard[OF d] by auto
  with t `card B = dim B` d show ?thesis by auto
qed

lemma aff_dim_empty:
fixes S :: "('n::euclidean_space) set"
shows "S = {} <-> aff_dim S = -1"
proof-
obtain B where "affine hull B = affine hull S & ~ affine_dependent B & int (card B) = aff_dim S + 1" using aff_dim_basis_exists by auto
moreover hence "S={} <-> B={}" using affine_hull_nonempty[of B] affine_hull_nonempty[of S] by auto
ultimately show ?thesis using aff_independent_finite[of B] card_gt_0_iff[of B] by auto
qed

lemma aff_dim_affine_hull:
shows "aff_dim (affine hull S)=aff_dim S"
unfolding aff_dim_def using hull_hull[of _ S] by auto

lemma aff_dim_affine_hull2:
assumes "affine hull S=affine hull T"
shows "aff_dim S=aff_dim T" unfolding aff_dim_def using assms by auto

lemma aff_dim_unique:
fixes B V :: "('n::euclidean_space) set"
assumes "(affine hull B=affine hull V) & ~(affine_dependent B)"
shows "of_nat(card B) = aff_dim V+1"
proof-
{ assume "B={}" hence "V={}" using affine_hull_nonempty[of V] affine_hull_nonempty[of B] assms by auto
  hence "aff_dim V = (-1::int)"  using aff_dim_empty by auto
  hence ?thesis using `B={}` by auto
}
moreover
{ assume "B~={}" from this obtain a where a_def: "a:B" by auto
  def Lb == "span ((%x. -a+x) ` (B-{a}))"
  have "affine_parallel (affine hull B) Lb"
     using Lb_def affine_hull_span2[of a B] a_def  affine_parallel_commut[of "Lb" "(affine hull B)"]
     unfolding affine_parallel_def by auto
  moreover have "subspace Lb" using Lb_def subspace_span by auto
  ultimately have "aff_dim B=int(dim Lb)" using aff_dim_parallel_subspace[of B Lb] `B~={}` by auto
  moreover have "(card B) - 1 = dim Lb" "finite B" using Lb_def aff_dim_parallel_subspace_aux a_def assms by auto
  ultimately have "(of_nat(card B) = aff_dim B+1)" using  `B~={}` card_gt_0_iff[of B] by auto
  hence ?thesis using aff_dim_affine_hull2 assms by auto
} ultimately show ?thesis by blast
qed

lemma aff_dim_affine_independent:
fixes B :: "('n::euclidean_space) set"
assumes "~(affine_dependent B)"
shows "of_nat(card B) = aff_dim B+1"
  using aff_dim_unique[of B B] assms by auto

lemma aff_dim_sing:
fixes a :: "'n::euclidean_space"
shows "aff_dim {a}=0"
  using aff_dim_affine_independent[of "{a}"] affine_independent_sing by auto

lemma aff_dim_inner_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "? B. B<=V & (affine hull B=affine hull V) & ~(affine_dependent B) & (of_nat(card B) = aff_dim V+1)"
proof-
obtain B where B_def: "~(affine_dependent B) & B<=V & (affine hull B=affine hull V)" using affine_basis_exists[of V] by auto
moreover hence "of_nat(card B) = aff_dim V+1" using aff_dim_unique by auto
ultimately show ?thesis by auto
qed

lemma aff_dim_le_card:
fixes V :: "('n::euclidean_space) set"
assumes "finite V"
shows "aff_dim V <= of_nat(card V) - 1"
 proof-
 obtain B where B_def: "B<=V & (of_nat(card B) = aff_dim V+1)" using aff_dim_inner_basis_exists[of V] by auto
 moreover hence "card B <= card V" using assms card_mono by auto
 ultimately show ?thesis by auto
qed

lemma aff_dim_parallel_eq:
fixes S T :: "('n::euclidean_space) set"
assumes "affine_parallel (affine hull S) (affine hull T)"
shows "aff_dim S=aff_dim T"
proof-
{ assume "T~={}" "S~={}"
  from this obtain L where L_def: "subspace L & affine_parallel (affine hull T) L"
       using affine_parallel_subspace[of "affine hull T"] affine_affine_hull[of T] affine_hull_nonempty by auto
  hence "aff_dim T = int(dim L)" using aff_dim_parallel_subspace `T~={}` by auto
  moreover have "subspace L & affine_parallel (affine hull S) L"
     using L_def affine_parallel_assoc[of "affine hull S" "affine hull T" L] assms by auto
  moreover hence "aff_dim S = int(dim L)" using aff_dim_parallel_subspace `S~={}` by auto
  ultimately have ?thesis by auto
}
moreover
{ assume "S={}" hence "S={} & T={}" using assms affine_hull_nonempty unfolding affine_parallel_def by auto
  hence ?thesis using aff_dim_empty by auto
}
moreover
{ assume "T={}" hence "S={} & T={}" using assms affine_hull_nonempty unfolding affine_parallel_def by auto
  hence ?thesis using aff_dim_empty by auto
}
ultimately show ?thesis by blast
qed

lemma aff_dim_translation_eq:
fixes a :: "'n::euclidean_space"
shows "aff_dim ((%x. a + x) ` S)=aff_dim S"
proof-
have "affine_parallel (affine hull S) (affine hull ((%x. a + x) ` S))" unfolding affine_parallel_def apply (rule exI[of _ "a"]) using affine_hull_translation[of a S] by auto
from this show ?thesis using  aff_dim_parallel_eq[of S "(%x. a + x) ` S"] by auto
qed

lemma aff_dim_affine:
fixes S L :: "('n::euclidean_space) set"
assumes "S ~= {}" "affine S"
assumes "subspace L" "affine_parallel S L"
shows "aff_dim S=int(dim L)"
proof-
have 1: "(affine hull S) = S" using assms affine_hull_eq[of S] by auto
hence "affine_parallel (affine hull S) L" using assms by (simp add:1)
from this show ?thesis using assms aff_dim_parallel_subspace[of S L] by blast
qed

lemma dim_affine_hull:
fixes S :: "('n::euclidean_space) set"
shows "dim (affine hull S)=dim S"
proof-
have "dim (affine hull S)>=dim S" using dim_subset by auto
moreover have "dim(span S) >= dim (affine hull S)" using dim_subset affine_hull_subset_span by auto
moreover have "dim(span S)=dim S" using dim_span by auto
ultimately show ?thesis by auto
qed

lemma aff_dim_subspace:
fixes S :: "('n::euclidean_space) set"
assumes "S ~= {}" "subspace S"
shows "aff_dim S=int(dim S)" using aff_dim_affine[of S S] assms subspace_imp_affine[of S] affine_parallel_reflex[of S] by auto

lemma aff_dim_zero:
fixes S :: "('n::euclidean_space) set"
assumes "0 : affine hull S"
shows "aff_dim S=int(dim S)"
proof-
have "subspace(affine hull S)" using subspace_affine[of "affine hull S"] affine_affine_hull assms by auto
hence "aff_dim (affine hull S) =int(dim (affine hull S))" using assms aff_dim_subspace[of "affine hull S"] by auto
from this show ?thesis using aff_dim_affine_hull[of S] dim_affine_hull[of S] by auto
qed

lemma aff_dim_univ: "aff_dim (UNIV :: ('n::euclidean_space) set) = int(DIM('n))"
  using aff_dim_subspace[of "(UNIV :: ('n::euclidean_space) set)"]
    dim_UNIV[where 'a="'n::euclidean_space"] by auto

lemma aff_dim_geq:
  fixes V :: "('n::euclidean_space) set"
  shows "aff_dim V >= -1"
proof-
obtain B where B_def: "affine hull B = affine hull V & ~ affine_dependent B & int (card B) = aff_dim V + 1" using aff_dim_basis_exists by auto
from this show ?thesis by auto
qed

lemma independent_card_le_aff_dim:
  assumes "(B::('n::euclidean_space) set) <= V"
  assumes "~(affine_dependent B)"
  shows "int(card B) <= aff_dim V+1"
proof-
{ assume "B~={}"
  from this obtain T where T_def: "~(affine_dependent T) & B<=T & T<=V & affine hull T = affine hull V"
  using assms extend_to_affine_basis[of B V] by auto
  hence "of_nat(card T) = aff_dim V+1" using aff_dim_unique by auto
  hence ?thesis using T_def card_mono[of T B] aff_independent_finite[of T] by auto
}
moreover
{ assume "B={}"
  moreover have "-1<= aff_dim V" using aff_dim_geq by auto
  ultimately have ?thesis by auto
}  ultimately show ?thesis by blast
qed

lemma aff_dim_subset:
  fixes S T :: "('n::euclidean_space) set"
  assumes "S <= T"
  shows "aff_dim S <= aff_dim T"
proof-
obtain B where B_def: "~(affine_dependent B) & B<=S & (affine hull B=affine hull S) & of_nat(card B) = aff_dim S+1" using aff_dim_inner_basis_exists[of S] by auto
moreover hence "int (card B) <= aff_dim T + 1" using assms independent_card_le_aff_dim[of B T] by auto
ultimately show ?thesis by auto
qed

lemma aff_dim_subset_univ:
fixes S :: "('n::euclidean_space) set"
shows "aff_dim S <= int(DIM('n))"
proof -
  have "aff_dim (UNIV :: ('n::euclidean_space) set) = int(DIM('n))" using aff_dim_univ by auto
  from this show "aff_dim (S:: ('n::euclidean_space) set) <= int(DIM('n))" using assms aff_dim_subset[of S "(UNIV :: ('n::euclidean_space) set)"] subset_UNIV by auto
qed

lemma affine_dim_equal:
assumes "affine (S :: ('n::euclidean_space) set)" "affine T" "S ~= {}" "S <= T" "aff_dim S = aff_dim T"
shows "S=T"
proof-
obtain a where "a : S" using assms by auto
hence "a : T" using assms by auto
def LS == "{y. ? x : S. (-a)+x=y}"
hence ls: "subspace LS & affine_parallel S LS" using assms parallel_subspace_explicit[of S a LS] `a : S` by auto
hence h1: "int(dim LS) = aff_dim S" using assms aff_dim_affine[of S LS] by auto
have "T ~= {}" using assms by auto
def LT == "{y. ? x : T. (-a)+x=y}"
hence lt: "subspace LT & affine_parallel T LT" using assms parallel_subspace_explicit[of T a LT] `a : T` by auto
hence "int(dim LT) = aff_dim T" using assms aff_dim_affine[of T LT] `T ~= {}` by auto
hence "dim LS = dim LT" using h1 assms by auto
moreover have "LS <= LT" using LS_def LT_def assms by auto
ultimately have "LS=LT" using subspace_dim_equal[of LS LT] ls lt by auto
moreover have "S = {x. ? y : LS. a+y=x}" using LS_def by auto
moreover have "T = {x. ? y : LT. a+y=x}" using LT_def by auto
ultimately show ?thesis by auto
qed

lemma affine_hull_univ:
fixes S :: "('n::euclidean_space) set"
assumes "aff_dim S = int(DIM('n))"
shows "affine hull S = (UNIV :: ('n::euclidean_space) set)"
proof-
have "S ~= {}" using assms aff_dim_empty[of S] by auto
have h0: "S <= affine hull S" using hull_subset[of S _] by auto
have h1: "aff_dim (UNIV :: ('n::euclidean_space) set) = aff_dim S" using aff_dim_univ assms by auto
hence h2: "aff_dim (affine hull S) <= aff_dim (UNIV :: ('n::euclidean_space) set)" using aff_dim_subset_univ[of "affine hull S"] assms h0 by auto
have h3: "aff_dim S <= aff_dim (affine hull S)" using h0 aff_dim_subset[of S "affine hull S"] assms by auto
hence h4: "aff_dim (affine hull S) = aff_dim (UNIV :: ('n::euclidean_space) set)" using h0 h1 h2 by auto
from this show ?thesis using affine_dim_equal[of "affine hull S" "(UNIV :: ('n::euclidean_space) set)"] affine_affine_hull[of S] affine_UNIV assms h4 h0 `S ~= {}` by auto
qed

lemma aff_dim_convex_hull:
fixes S :: "('n::euclidean_space) set"
shows "aff_dim (convex hull S)=aff_dim S"
  using aff_dim_affine_hull[of S] convex_hull_subset_affine_hull[of S]
  hull_subset[of S "convex"] aff_dim_subset[of S "convex hull S"]
  aff_dim_subset[of "convex hull S" "affine hull S"] by auto

lemma aff_dim_cball:
fixes a :: "'n::euclidean_space"
assumes "0<e"
shows "aff_dim (cball a e) = int (DIM('n))"
proof-
have "(%x. a + x) ` (cball 0 e)<=cball a e" unfolding cball_def dist_norm by auto
hence "aff_dim (cball (0 :: 'n::euclidean_space) e) <= aff_dim (cball a e)"
  using aff_dim_translation_eq[of a "cball 0 e"]
        aff_dim_subset[of "op + a ` cball 0 e" "cball a e"] by auto
moreover have "aff_dim (cball (0 :: 'n::euclidean_space) e) = int (DIM('n))"
   using hull_inc[of "(0 :: 'n::euclidean_space)" "cball 0 e"] centre_in_cball[of "(0 :: 'n::euclidean_space)"] assms
   by (simp add: dim_cball[of e] aff_dim_zero[of "cball 0 e"])
ultimately show ?thesis using aff_dim_subset_univ[of "cball a e"] by auto
qed

lemma aff_dim_open:
fixes S :: "('n::euclidean_space) set"
assumes "open S" "S ~= {}"
shows "aff_dim S = int (DIM('n))"
proof-
obtain x where "x:S" using assms by auto
from this obtain e where e_def: "e>0 & cball x e <= S" using open_contains_cball[of S] assms by auto
from this have "aff_dim (cball x e) <= aff_dim S" using aff_dim_subset by auto
from this show ?thesis using aff_dim_cball[of e x] aff_dim_subset_univ[of S] e_def by auto
qed

lemma low_dim_interior:
fixes S :: "('n::euclidean_space) set"
assumes "~(aff_dim S = int (DIM('n)))"
shows "interior S = {}"
proof-
have "aff_dim(interior S) <= aff_dim S"
   using interior_subset aff_dim_subset[of "interior S" S] by auto
from this show ?thesis using aff_dim_open[of "interior S"] aff_dim_subset_univ[of S] assms by auto
qed

subsection {* Relative interior of a set *}

definition "rel_interior S = {x. ? T. openin (subtopology euclidean (affine hull S)) T & x : T & T <= S}"

lemma rel_interior: "rel_interior S = {x : S. ? T. open T & x : T & (T Int (affine hull S)) <= S}"
  unfolding rel_interior_def[of S] openin_open[of "affine hull S"] apply auto
proof-
fix x T assume a: "x:S" "open T" "x : T" "(T Int (affine hull S)) <= S"
hence h1: "x : T Int affine hull S" using hull_inc by auto
show "EX Tb. (EX Ta. open Ta & Tb = affine hull S Int Ta) & x : Tb & Tb <= S"
apply (rule_tac x="T Int (affine hull S)" in exI)
using a h1 by auto
qed

lemma mem_rel_interior:
     "x : rel_interior S <-> (? T. open T & x : (T Int S) & (T Int (affine hull S)) <= S)"
     by (auto simp add: rel_interior)

lemma mem_rel_interior_ball: "x : rel_interior S <-> x : S & (? e. 0 < e & ((ball x e) Int (affine hull S)) <= S)"
  apply (simp add: rel_interior, safe)
  apply (force simp add: open_contains_ball)
  apply (rule_tac x="ball x e" in exI)
  apply simp
  done

lemma rel_interior_ball:
      "rel_interior S = {x : S. ? e. e>0 & ((ball x e) Int (affine hull S)) <= S}"
      using mem_rel_interior_ball [of _ S] by auto

lemma mem_rel_interior_cball: "x : rel_interior S <-> x : S & (? e. 0 < e & ((cball x e) Int (affine hull S)) <= S)"
  apply (simp add: rel_interior, safe)
  apply (force simp add: open_contains_cball)
  apply (rule_tac x="ball x e" in exI)
  apply (simp add: subset_trans [OF ball_subset_cball])
  apply auto
  done

lemma rel_interior_cball: "rel_interior S = {x : S. ? e. e>0 & ((cball x e) Int (affine hull S)) <= S}"       using mem_rel_interior_cball [of _ S] by auto

lemma rel_interior_empty: "rel_interior {} = {}"
   by (auto simp add: rel_interior_def)

lemma affine_hull_sing: "affine hull {a :: 'n::euclidean_space} = {a}"
by (metis affine_hull_eq affine_sing)

lemma rel_interior_sing: "rel_interior {a :: 'n::euclidean_space} = {a}"
   unfolding rel_interior_ball affine_hull_sing apply auto
   apply(rule_tac x="1 :: real" in exI) apply simp
   done

lemma subset_rel_interior:
fixes S T :: "('n::euclidean_space) set"
assumes "S<=T" "affine hull S=affine hull T"
shows "rel_interior S <= rel_interior T"
  using assms by (auto simp add: rel_interior_def)

lemma rel_interior_subset: "rel_interior S <= S"
   by (auto simp add: rel_interior_def)

lemma rel_interior_subset_closure: "rel_interior S <= closure S"
   using rel_interior_subset by (auto simp add: closure_def)

lemma interior_subset_rel_interior: "interior S <= rel_interior S"
   by (auto simp add: rel_interior interior_def)

lemma interior_rel_interior:
fixes S :: "('n::euclidean_space) set"
assumes "aff_dim S = int(DIM('n))"
shows "rel_interior S = interior S"
proof -
have "affine hull S = UNIV" using assms affine_hull_univ[of S] by auto
from this show ?thesis unfolding rel_interior interior_def by auto
qed

lemma rel_interior_open:
fixes S :: "('n::euclidean_space) set"
assumes "open S"
shows "rel_interior S = S"
by (metis assms interior_eq interior_subset_rel_interior rel_interior_subset set_eq_subset)

lemma interior_rel_interior_gen:
fixes S :: "('n::euclidean_space) set"
shows "interior S = (if aff_dim S = int(DIM('n)) then rel_interior S else {})"
by (metis interior_rel_interior low_dim_interior)

lemma rel_interior_univ:
fixes S :: "('n::euclidean_space) set"
shows "rel_interior (affine hull S) = affine hull S"
proof-
have h1: "rel_interior (affine hull S) <= affine hull S" using rel_interior_subset by auto
{ fix x assume x_def: "x : affine hull S"
  obtain e :: real where "e=1" by auto
  hence "e>0 & ball x e Int affine hull (affine hull S) <= affine hull S" using hull_hull[of _ S] by auto
  hence "x : rel_interior (affine hull S)" using x_def rel_interior_ball[of "affine hull S"] by auto
} from this show ?thesis using h1 by auto
qed

lemma rel_interior_univ2: "rel_interior (UNIV :: ('n::euclidean_space) set) = UNIV"
by (metis open_UNIV rel_interior_open)

lemma rel_interior_convex_shrink:
  fixes S :: "('a::euclidean_space) set"
  assumes "convex S" "c : rel_interior S" "x : S" "0 < e" "e <= 1"
  shows "x - e *\<^sub>R (x - c) : rel_interior S"
proof-
(* Proof is a modified copy of the proof of similar lemma mem_interior_convex_shrink
*)
obtain d where "d>0" and d:"ball c d Int affine hull S <= S"
  using assms(2) unfolding  mem_rel_interior_ball by auto
{   fix y assume as:"dist (x - e *\<^sub>R (x - c)) y < e * d & y : affine hull S"
    have *:"y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x" using `e>0` by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "x : affine hull S" using assms hull_subset[of S] by auto
    moreover have "1 / e + - ((1 - e) / e) = 1"
       using `e>0` left_diff_distrib[of "1" "(1-e)" "1/e"] by auto
    ultimately have **: "(1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x : affine hull S"
        using as affine_affine_hull[of S] mem_affine[of "affine hull S" y x "(1 / e)" "-((1 - e) / e)"] by (simp add: algebra_simps)
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = abs(1/e) * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm unfolding norm_scaleR[symmetric] apply(rule arg_cong[where f=norm]) using `e>0`
      by(auto simp add:euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    also have "... = abs(1/e) * norm (x - e *\<^sub>R (x - c) - y)" by(auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "... < d" using as[unfolded dist_norm] and `e>0`
      by(auto simp add:pos_divide_less_eq[OF `e>0`] mult_commute)
    finally have "y : S" apply(subst *)
apply(rule assms(1)[unfolded convex_alt,rule_format])
      apply(rule d[unfolded subset_eq,rule_format]) unfolding mem_ball using assms(3-5) ** by auto
} hence "ball (x - e *\<^sub>R (x - c)) (e*d) Int affine hull S <= S" by auto
moreover have "0 < e*d" using `0<e` `0<d` by (rule mult_pos_pos)
moreover have "c : S" using assms rel_interior_subset by auto
moreover hence "x - e *\<^sub>R (x - c) : S"
   using mem_convex[of S x c e] apply (simp add: algebra_simps) using assms by auto
ultimately show ?thesis
  using mem_rel_interior_ball[of "x - e *\<^sub>R (x - c)" S] `e>0` by auto
qed

lemma interior_real_semiline:
fixes a :: real
shows "interior {a..} = {a<..}"
proof-
{ fix y assume "a<y" hence "y : interior {a..}"
  apply (simp add: mem_interior) apply (rule_tac x="(y-a)" in exI) apply (auto simp add: dist_norm)
  done }
moreover
{ fix y assume "y : interior {a..}" (*hence "a<=y" using interior_subset by auto*)
  from this obtain e where e_def: "e>0 & cball y e \<subseteq> {a..}"
     using mem_interior_cball[of y "{a..}"] by auto
  moreover hence "y-e : cball y e" by (auto simp add: cball_def dist_norm)
  ultimately have "a<=y-e" by auto
  hence "a<y" using e_def by auto
} ultimately show ?thesis by auto
qed

lemma rel_interior_real_interval:
  fixes a b :: real assumes "a < b" shows "rel_interior {a..b} = {a<..<b}"
proof-
  have "{a<..<b} \<noteq> {}" using assms unfolding set_eq_iff by (auto intro!: exI[of _ "(a + b) / 2"])
  then show ?thesis
    using interior_rel_interior_gen[of "{a..b}", symmetric]
    by (simp split: split_if_asm add: interior_closed_interval)
qed

lemma rel_interior_real_semiline:
  fixes a :: real shows "rel_interior {a..} = {a<..}"
proof-
  have *: "{a<..} \<noteq> {}" unfolding set_eq_iff by (auto intro!: exI[of _ "a + 1"])
  then show ?thesis using interior_real_semiline
     interior_rel_interior_gen[of "{a..}"]
     by (auto split: split_if_asm)
qed

subsubsection {* Relative open sets *}

definition "rel_open S <-> (rel_interior S) = S"

lemma rel_open: "rel_open S <-> openin (subtopology euclidean (affine hull S)) S"
 unfolding rel_open_def rel_interior_def apply auto
 using openin_subopen[of "subtopology euclidean (affine hull S)" S] by auto

lemma opein_rel_interior:
  "openin (subtopology euclidean (affine hull S)) (rel_interior S)"
  apply (simp add: rel_interior_def)
  apply (subst openin_subopen) by blast

lemma affine_rel_open:
  fixes S :: "('n::euclidean_space) set"
  assumes "affine S" shows "rel_open S"
  unfolding rel_open_def using assms rel_interior_univ[of S] affine_hull_eq[of S] by metis

lemma affine_closed:
  fixes S :: "('n::euclidean_space) set"
  assumes "affine S" shows "closed S"
proof-
{ assume "S ~= {}"
  from this obtain L where L_def: "subspace L & affine_parallel S L"
     using assms affine_parallel_subspace[of S] by auto
  from this obtain "a" where a_def: "S=(op + a ` L)"
     using affine_parallel_def[of L S] affine_parallel_commut by auto
  have "closed L" using L_def closed_subspace by auto
  hence "closed S" using closed_translation a_def by auto
} from this show ?thesis by auto
qed

lemma closure_affine_hull:
  fixes S :: "('n::euclidean_space) set"
  shows "closure S <= affine hull S"
  by (intro closure_minimal hull_subset affine_closed affine_affine_hull)

lemma closure_same_affine_hull:
  fixes S :: "('n::euclidean_space) set"
  shows "affine hull (closure S) = affine hull S"
proof-
have "affine hull (closure S) <= affine hull S"
   using hull_mono[of "closure S" "affine hull S" "affine"] closure_affine_hull[of S] hull_hull[of "affine" S] by auto
moreover have "affine hull (closure S) >= affine hull S"
   using hull_mono[of "S" "closure S" "affine"] closure_subset by auto
ultimately show ?thesis by auto
qed

lemma closure_aff_dim:
  fixes S :: "('n::euclidean_space) set"
  shows "aff_dim (closure S) = aff_dim S"
proof-
have "aff_dim S <= aff_dim (closure S)" using aff_dim_subset closure_subset by auto
moreover have "aff_dim (closure S) <= aff_dim (affine hull S)"
  using aff_dim_subset closure_affine_hull by auto
moreover have "aff_dim (affine hull S) = aff_dim S" using aff_dim_affine_hull by auto
ultimately show ?thesis by auto
qed

lemma rel_interior_closure_convex_shrink:
  fixes S :: "(_::euclidean_space) set"
  assumes "convex S" "c : rel_interior S" "x : closure S" "0 < e" "e <= 1"
  shows "x - e *\<^sub>R (x - c) : rel_interior S"
proof-
(* Proof is a modified copy of the proof of similar lemma mem_interior_closure_convex_shrink
*)
obtain d where "d>0" and d:"ball c d Int affine hull S <= S"
  using assms(2) unfolding mem_rel_interior_ball by auto
have "EX y : S. norm (y - x) * (1 - e) < e * d" proof(cases "x : S")
    case True thus ?thesis using `e>0` `d>0` by(rule_tac bexI[where x=x], auto intro!: mult_pos_pos) next
    case False hence x:"x islimpt S" using assms(3)[unfolded closure_def] by auto
    show ?thesis proof(cases "e=1")
      case True obtain y where "y : S" "y ~= x" "dist y x < 1"
        using x[unfolded islimpt_approachable,THEN spec[where x=1]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding True using `d>0` by auto next
      case False hence "0 < e * d / (1 - e)" and *:"1 - e > 0"
        using `e<=1` `e>0` `d>0` by(auto intro!:mult_pos_pos divide_pos_pos)
      then obtain y where "y : S" "y ~= x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding dist_norm using pos_less_divide_eq[OF *] by auto qed qed
  then obtain y where "y : S" and y:"norm (y - x) * (1 - e) < e * d" by auto
  def z == "c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *:"x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)" unfolding z_def using `e>0` by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have zball: "z\<in>ball c d"
    using mem_ball z_def dist_norm[of c] using y and assms(4,5) by (auto simp add:field_simps norm_minus_commute)
  have "x : affine hull S" using closure_affine_hull assms by auto
  moreover have "y : affine hull S" using `y : S` hull_subset[of S] by auto
  moreover have "c : affine hull S" using assms rel_interior_subset hull_subset[of S] by auto
  ultimately have "z : affine hull S"
    using z_def affine_affine_hull[of S]
          mem_affine_3_minus [of "affine hull S" c x y "(1 - e) / e"]
          assms by (auto simp add: field_simps)
  hence "z : S" using d zball by auto
  obtain d1 where "d1>0" and d1:"ball z d1 <= ball c d"
    using zball open_ball[of c d] openE[of "ball c d" z] by auto
  hence "(ball z d1) Int (affine hull S) <= (ball c d) Int (affine hull S)" by auto
  hence "(ball z d1) Int (affine hull S) <= S" using d by auto
  hence "z : rel_interior S" using mem_rel_interior_ball using `d1>0` `z : S` by auto
  hence "y - e *\<^sub>R (y - z) : rel_interior S" using rel_interior_convex_shrink[of S z y e] assms`y : S` by auto
  thus ?thesis using * by auto
qed

subsubsection{* Relative interior preserves under linear transformations *}

lemma rel_interior_translation_aux:
fixes a :: "'n::euclidean_space"
shows "((%x. a + x) ` rel_interior S) <= rel_interior ((%x. a + x) ` S)"
proof-
{ fix x assume x_def: "x : rel_interior S"
  from this obtain T where T_def: "open T & x : (T Int S) & (T Int (affine hull S)) <= S" using mem_rel_interior[of x S] by auto
  from this have "open ((%x. a + x) ` T)" and
    "(a + x) : (((%x. a + x) ` T) Int ((%x. a + x) ` S))" and
    "(((%x. a + x) ` T) Int (affine hull ((%x. a + x) ` S))) <= ((%x. a + x) ` S)"
    using affine_hull_translation[of a S] open_translation[of T a] x_def by auto
  from this have "(a+x) : rel_interior ((%x. a + x) ` S)"
    using mem_rel_interior[of "a+x" "((%x. a + x) ` S)"] by auto
} from this show ?thesis by auto
qed

lemma rel_interior_translation:
fixes a :: "'n::euclidean_space"
shows "rel_interior ((%x. a + x) ` S) = ((%x. a + x) ` rel_interior S)"
proof-
have "(%x. (-a) + x) ` rel_interior ((%x. a + x) ` S) <= rel_interior S"
   using rel_interior_translation_aux[of "-a" "(%x. a + x) ` S"]
         translation_assoc[of "-a" "a"] by auto
hence "((%x. a + x) ` rel_interior S) >= rel_interior ((%x. a + x) ` S)"
   using translation_inverse_subset[of a "rel_interior (op + a ` S)" "rel_interior S"]
   by auto
from this show ?thesis using  rel_interior_translation_aux[of a S] by auto
qed


lemma affine_hull_linear_image:
assumes "bounded_linear f"
shows "f ` (affine hull s) = affine hull f ` s"
(* Proof is a modified copy of the proof of similar lemma convex_hull_linear_image
*)
  apply rule unfolding subset_eq ball_simps apply(rule_tac[!] hull_induct, rule hull_inc) prefer 3
  apply(erule imageE)apply(rule_tac x=xa in image_eqI) apply assumption
  apply(rule hull_subset[unfolded subset_eq, rule_format]) apply assumption
proof-
  interpret f: bounded_linear f by fact
  show "affine {x. f x : affine hull f ` s}"
  unfolding affine_def by(auto simp add: f.scaleR f.add affine_affine_hull[unfolded affine_def, rule_format]) next
  interpret f: bounded_linear f by fact
  show "affine {x. x : f ` (affine hull s)}" using affine_affine_hull[unfolded affine_def, of s]
    unfolding affine_def by (auto simp add: f.scaleR [symmetric] f.add [symmetric])
qed auto


lemma rel_interior_injective_on_span_linear_image:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
fixes S :: "('m::euclidean_space) set"
assumes "bounded_linear f" and "inj_on f (span S)"
shows "rel_interior (f ` S) = f ` (rel_interior S)"
proof-
{ fix z assume z_def: "z : rel_interior (f ` S)"
  have "z : f ` S" using z_def rel_interior_subset[of "f ` S"] by auto
  from this obtain x where x_def: "x : S & (f x = z)" by auto
  obtain e2 where e2_def: "e2>0 & cball z e2 Int affine hull (f ` S) <= (f ` S)"
    using z_def rel_interior_cball[of "f ` S"] by auto
  obtain K where K_def: "K>0 & (! x. norm (f x) <= norm x * K)"
   using assms Real_Vector_Spaces.bounded_linear.pos_bounded[of f] by auto
  def e1 == "1/K" hence e1_def: "e1>0 & (! x. e1 * norm (f x) <= norm x)"
   using K_def pos_le_divide_eq[of e1] by auto
  def e == "e1 * e2" hence "e>0" using e1_def e2_def mult_pos_pos by auto
  { fix y assume y_def: "y : cball x e Int affine hull S"
    from this have h1: "f y : affine hull (f ` S)"
      using affine_hull_linear_image[of f S] assms by auto
    from y_def have "norm (x-y)<=e1 * e2"
      using cball_def[of x e] dist_norm[of x y] e_def by auto
    moreover have "(f x)-(f y)=f (x-y)"
       using assms linear_sub[of f x y] linear_conv_bounded_linear[of f] by auto
    moreover have "e1 * norm (f (x-y)) <= norm (x-y)" using e1_def by auto
    ultimately have "e1 * norm ((f x)-(f y)) <= e1 * e2" by auto
    hence "(f y) : (cball z e2)"
      using cball_def[of "f x" e2] dist_norm[of "f x" "f y"] e1_def x_def by auto
    hence "f y : (f ` S)" using y_def e2_def h1 by auto
    hence "y : S" using assms y_def hull_subset[of S] affine_hull_subset_span
         inj_on_image_mem_iff[of f "span S" S y] by auto
  }
  hence "z : f ` (rel_interior S)" using mem_rel_interior_cball[of x S] `e>0` x_def by auto
}
moreover
{ fix x assume x_def: "x : rel_interior S"
  from this obtain e2 where e2_def: "e2>0 & cball x e2 Int affine hull S <= S"
    using rel_interior_cball[of S] by auto
  have "x : S" using x_def rel_interior_subset by auto
  hence *: "f x : f ` S" by auto
  have "! x:span S. f x = 0 --> x = 0"
    using assms subspace_span linear_conv_bounded_linear[of f]
          linear_injective_on_subspace_0[of f "span S"] by auto
  from this obtain e1 where e1_def: "e1>0 & (! x : span S. e1 * norm x <= norm (f x))"
   using assms injective_imp_isometric[of "span S" f]
         subspace_span[of S] closed_subspace[of "span S"] by auto
  def e == "e1 * e2" hence "e>0" using e1_def e2_def mult_pos_pos by auto
  { fix y assume y_def: "y : cball (f x) e Int affine hull (f ` S)"
    from this have "y : f ` (affine hull S)" using affine_hull_linear_image[of f S] assms by auto
    from this obtain xy where xy_def: "xy : affine hull S & (f xy = y)" by auto
    from this y_def have "norm ((f x)-(f xy))<=e1 * e2"
      using cball_def[of "f x" e] dist_norm[of "f x" y] e_def by auto
    moreover have "(f x)-(f xy)=f (x-xy)"
       using assms linear_sub[of f x xy] linear_conv_bounded_linear[of f] by auto
    moreover have "x-xy : span S"
       using subspace_sub[of "span S" x xy] subspace_span `x : S` xy_def
             affine_hull_subset_span[of S] span_inc by auto
    moreover hence "e1 * norm (x-xy) <= norm (f (x-xy))" using e1_def by auto
    ultimately have "e1 * norm (x-xy) <= e1 * e2" by auto
    hence "xy : (cball x e2)"  using cball_def[of x e2] dist_norm[of x xy] e1_def by auto
    hence "y : (f ` S)" using xy_def e2_def by auto
  }
  hence "(f x) : rel_interior (f ` S)"
     using mem_rel_interior_cball[of "(f x)" "(f ` S)"] * `e>0` by auto
}
ultimately show ?thesis by auto
qed

lemma rel_interior_injective_linear_image:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
assumes "bounded_linear f" and "inj f"
shows "rel_interior (f ` S) = f ` (rel_interior S)"
using assms rel_interior_injective_on_span_linear_image[of f S]
      subset_inj_on[of f "UNIV" "span S"] by auto

subsection{* Some Properties of subset of standard basis *}

lemma affine_hull_substd_basis: assumes "d\<subseteq>Basis"
  shows "affine hull (insert 0 d) =
  {x::'a::euclidean_space. (\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)}"
 (is "affine hull (insert 0 ?A) = ?B")
proof- have *:"\<And>A. op + (0\<Colon>'a) ` A = A" "\<And>A. op + (- (0\<Colon>'a)) ` A = A" by auto
  show ?thesis unfolding affine_hull_insert_span_gen span_substd_basis[OF assms,symmetric] * ..
qed

lemma affine_hull_convex_hull: "affine hull (convex hull S) = affine hull S"
by (metis Int_absorb1 Int_absorb2 convex_hull_subset_affine_hull hull_hull hull_mono hull_subset)

subsection {* Openness and compactness are preserved by convex hull operation. *}

lemma open_convex_hull[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open(convex hull s)"
  unfolding open_contains_cball convex_hull_explicit unfolding mem_Collect_eq ball_simps(8)
proof(rule, rule) fix a
  assume "\<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = a"
  then obtain t u where obt:"finite t" "t\<subseteq>s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = a" by auto

  from assms[unfolded open_contains_cball] obtain b where b:"\<forall>x\<in>s. 0 < b x \<and> cball x (b x) \<subseteq> s"
    using bchoice[of s "\<lambda>x e. e>0 \<and> cball x e \<subseteq> s"] by auto
  have "b ` t\<noteq>{}" unfolding i_def using obt by auto  def i \<equiv> "b ` t"

  show "\<exists>e>0. cball a e \<subseteq> {y. \<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y}"
    apply(rule_tac x="Min i" in exI) unfolding subset_eq apply rule defer apply rule unfolding mem_Collect_eq
  proof-
    show "0 < Min i" unfolding i_def and Min_gr_iff[OF finite_imageI[OF obt(1)] `b \` t\<noteq>{}`]
      using b apply simp apply rule apply(erule_tac x=x in ballE) using `t\<subseteq>s` by auto
  next  fix y assume "y \<in> cball a (Min i)"
    hence y:"norm (a - y) \<le> Min i" unfolding dist_norm[symmetric] by auto
    { fix x assume "x\<in>t"
      hence "Min i \<le> b x" unfolding i_def apply(rule_tac Min_le) using obt(1) by auto
      hence "x + (y - a) \<in> cball x (b x)" using y unfolding mem_cball dist_norm by auto
      moreover from `x\<in>t` have "x\<in>s" using obt(2) by auto
      ultimately have "x + (y - a) \<in> s" using y and b[THEN bspec[where x=x]] unfolding subset_eq by fast }
    moreover
    have *:"inj_on (\<lambda>v. v + (y - a)) t" unfolding inj_on_def by auto
    have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a))) = 1"
      unfolding setsum_reindex[OF *] o_def using obt(4) by auto
    moreover have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a)) *\<^sub>R v) = y"
      unfolding setsum_reindex[OF *] o_def using obt(4,5)
      by (simp add: setsum_addf setsum_subtractf scaleR_left.setsum[symmetric] scaleR_right_distrib)
    ultimately show "\<exists>sa u. finite sa \<and> (\<forall>x\<in>sa. x \<in> s) \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
      apply(rule_tac x="(\<lambda>v. v + (y - a)) ` t" in exI) apply(rule_tac x="\<lambda>v. u (v - (y - a))" in exI)
      using obt(1, 3) by auto
  qed
qed

lemma compact_convex_combinations:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s" "compact t"
  shows "compact { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t}"
proof-
  let ?X = "{0..1} \<times> s \<times> t"
  let ?h = "(\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
  have *:"{ (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t} = ?h ` ?X"
    apply(rule set_eqI) unfolding image_iff mem_Collect_eq
    apply rule apply auto
    apply (rule_tac x=u in rev_bexI, simp)
    apply (erule rev_bexI, erule rev_bexI, simp)
    by auto
  have "continuous_on ({0..1} \<times> s \<times> t)
     (\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  thus ?thesis unfolding *
    apply (rule compact_continuous_image)
    apply (intro compact_Times compact_interval assms)
    done
qed

lemma finite_imp_compact_convex_hull:
  fixes s :: "('a::real_normed_vector) set"
  assumes "finite s" shows "compact (convex hull s)"
proof (cases "s = {}")
  case True thus ?thesis by simp
next
  case False with assms show ?thesis
  proof (induct rule: finite_ne_induct)
    case (singleton x) show ?case by simp
  next
    case (insert x A)
    let ?f = "\<lambda>(u, y::'a). u *\<^sub>R x + (1 - u) *\<^sub>R y"
    let ?T = "{0..1::real} \<times> (convex hull A)"
    have "continuous_on ?T ?f"
      unfolding split_def continuous_on by (intro ballI tendsto_intros)
    moreover have "compact ?T"
      by (intro compact_Times compact_interval insert)
    ultimately have "compact (?f ` ?T)"
      by (rule compact_continuous_image)
    also have "?f ` ?T = convex hull (insert x A)"
      unfolding convex_hull_insert [OF `A \<noteq> {}`]
      apply safe
      apply (rule_tac x=a in exI, simp)
      apply (rule_tac x="1 - a" in exI, simp)
      apply fast
      apply (rule_tac x="(u, b)" in image_eqI, simp_all)
      done
    finally show "compact (convex hull (insert x A))" .
  qed
qed

lemma compact_convex_hull: fixes s::"('a::euclidean_space) set"
  assumes "compact s"  shows "compact(convex hull s)"
proof(cases "s={}")
  case True thus ?thesis using compact_empty by simp
next
  case False then obtain w where "w\<in>s" by auto
  show ?thesis unfolding caratheodory[of s]
  proof(induct ("DIM('a) + 1"))
    have *:"{x.\<exists>sa. finite sa \<and> sa \<subseteq> s \<and> card sa \<le> 0 \<and> x \<in> convex hull sa} = {}"
      using compact_empty by auto
    case 0 thus ?case unfolding * by simp
  next
    case (Suc n)
    show ?case proof(cases "n=0")
      case True have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} = s"
        unfolding set_eq_iff and mem_Collect_eq proof(rule, rule)
        fix x assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t:"finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t" by auto
        show "x\<in>s" proof(cases "card t = 0")
          case True thus ?thesis using t(4) unfolding card_0_eq[OF t(1)] by simp
        next
          case False hence "card t = Suc 0" using t(3) `n=0` by auto
          then obtain a where "t = {a}" unfolding card_Suc_eq by auto
          thus ?thesis using t(2,4) by simp
        qed
      next
        fix x assume "x\<in>s"
        thus "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply(rule_tac x="{x}" in exI) unfolding convex_hull_singleton by auto
      qed thus ?thesis using assms by simp
    next
      case False have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} =
        { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u.
        0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> {x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> x \<in> convex hull t}}"
        unfolding set_eq_iff and mem_Collect_eq proof(rule,rule)
        fix x assume "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        then obtain u v c t where obt:"x = (1 - c) *\<^sub>R u + c *\<^sub>R v"
          "0 \<le> c \<and> c \<le> 1" "u \<in> s" "finite t" "t \<subseteq> s" "card t \<le> n"  "v \<in> convex hull t" by auto
        moreover have "(1 - c) *\<^sub>R u + c *\<^sub>R v \<in> convex hull insert u t"
          apply(rule mem_convex) using obt(2) and convex_convex_hull and hull_subset[of "insert u t" convex]
          using obt(7) and hull_mono[of t "insert u t"] by auto
        ultimately show "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply(rule_tac x="insert u t" in exI) by (auto simp add: card_insert_if)
      next
        fix x assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t:"finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t" by auto
        let ?P = "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        show ?P proof(cases "card t = Suc n")
          case False hence "card t \<le> n" using t(3) by auto
          thus ?P apply(rule_tac x=w in exI, rule_tac x=x in exI, rule_tac x=1 in exI) using `w\<in>s` and t
            by(auto intro!: exI[where x=t])
        next
          case True then obtain a u where au:"t = insert a u" "a\<notin>u" apply(drule_tac card_eq_SucD) by auto
          show ?P proof(cases "u={}")
            case True hence "x=a" using t(4)[unfolded au] by auto
            show ?P unfolding `x=a` apply(rule_tac x=a in exI, rule_tac x=a in exI, rule_tac x=1 in exI)
              using t and `n\<noteq>0` unfolding au by(auto intro!: exI[where x="{a}"])
          next
            case False obtain ux vx b where obt:"ux\<ge>0" "vx\<ge>0" "ux + vx = 1" "b \<in> convex hull u" "x = ux *\<^sub>R a + vx *\<^sub>R b"
              using t(4)[unfolded au convex_hull_insert[OF False]] by auto
            have *:"1 - vx = ux" using obt(3) by auto
            show ?P apply(rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=vx in exI)
              using obt and t(1-3) unfolding au and * using card_insert_disjoint[OF _ au(2)]
              by(auto intro!: exI[where x=u])
          qed
        qed
      qed
      thus ?thesis using compact_convex_combinations[OF assms Suc] by simp
    qed
  qed
qed

subsection {* Extremal points of a simplex are some vertices. *}

lemma dist_increases_online:
  fixes a b d :: "'a::real_inner"
  assumes "d \<noteq> 0"
  shows "dist a (b + d) > dist a b \<or> dist a (b - d) > dist a b"
proof(cases "inner a d - inner b d > 0")
  case True hence "0 < inner d d + (inner a d * 2 - inner b d * 2)"
    apply(rule_tac add_pos_pos) using assms by auto
  thus ?thesis apply(rule_tac disjI2) unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
next
  case False hence "0 < inner d d + (inner b d * 2 - inner a d * 2)"
    apply(rule_tac add_pos_nonneg) using assms by auto
  thus ?thesis apply(rule_tac disjI1) unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
qed

lemma norm_increases_online:
  fixes d :: "'a::real_inner"
  shows "d \<noteq> 0 \<Longrightarrow> norm(a + d) > norm a \<or> norm(a - d) > norm a"
  using dist_increases_online[of d a 0] unfolding dist_norm by auto

lemma simplex_furthest_lt:
  fixes s::"'a::real_inner set" assumes "finite s"
  shows "\<forall>x \<in> (convex hull s).  x \<notin> s \<longrightarrow> (\<exists>y\<in>(convex hull s). norm(x - a) < norm(y - a))"
proof(induct_tac rule: finite_induct[of s])
  fix x s assume as:"finite s" "x\<notin>s" "\<forall>x\<in>convex hull s. x \<notin> s \<longrightarrow> (\<exists>y\<in>convex hull s. norm (x - a) < norm (y - a))"
  show "\<forall>xa\<in>convex hull insert x s. xa \<notin> insert x s \<longrightarrow> (\<exists>y\<in>convex hull insert x s. norm (xa - a) < norm (y - a))"
  proof(rule,rule,cases "s = {}")
    case False fix y assume y:"y \<in> convex hull insert x s" "y \<notin> insert x s"
    obtain u v b where obt:"u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "y = u *\<^sub>R x + v *\<^sub>R b"
      using y(1)[unfolded convex_hull_insert[OF False]] by auto
    show "\<exists>z\<in>convex hull insert x s. norm (y - a) < norm (z - a)"
    proof(cases "y\<in>convex hull s")
      case True then obtain z where "z\<in>convex hull s" "norm (y - a) < norm (z - a)"
        using as(3)[THEN bspec[where x=y]] and y(2) by auto
      thus ?thesis apply(rule_tac x=z in bexI) unfolding convex_hull_insert[OF False] by auto
    next
      case False show ?thesis  using obt(3) proof(cases "u=0", case_tac[!] "v=0")
        assume "u=0" "v\<noteq>0" hence "y = b" using obt by auto
        thus ?thesis using False and obt(4) by auto
      next
        assume "u\<noteq>0" "v=0" hence "y = x" using obt by auto
        thus ?thesis using y(2) by auto
      next
        assume "u\<noteq>0" "v\<noteq>0"
        then obtain w where w:"w>0" "w<u" "w<v" using real_lbound_gt_zero[of u v] and obt(1,2) by auto
        have "x\<noteq>b" proof(rule ccontr)
          assume "\<not> x\<noteq>b" hence "y=b" unfolding obt(5)
            using obt(3) by(auto simp add: scaleR_left_distrib[symmetric])
          thus False using obt(4) and False by simp qed
        hence *:"w *\<^sub>R (x - b) \<noteq> 0" using w(1) by auto
        show ?thesis using dist_increases_online[OF *, of a y]
        proof(erule_tac disjE)
          assume "dist a y < dist a (y + w *\<^sub>R (x - b))"
          hence "norm (y - a) < norm ((u + w) *\<^sub>R x + (v - w) *\<^sub>R b - a)"
            unfolding dist_commute[of a] unfolding dist_norm obt(5) by (simp add: algebra_simps)
          moreover have "(u + w) *\<^sub>R x + (v - w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF `s\<noteq>{}`] and mem_Collect_eq
            apply(rule_tac x="u + w" in exI) apply rule defer
            apply(rule_tac x="v - w" in exI) using `u\<ge>0` and w and obt(3,4) by auto
          ultimately show ?thesis by auto
        next
          assume "dist a y < dist a (y - w *\<^sub>R (x - b))"
          hence "norm (y - a) < norm ((u - w) *\<^sub>R x + (v + w) *\<^sub>R b - a)"
            unfolding dist_commute[of a] unfolding dist_norm obt(5) by (simp add: algebra_simps)
          moreover have "(u - w) *\<^sub>R x + (v + w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF `s\<noteq>{}`] and mem_Collect_eq
            apply(rule_tac x="u - w" in exI) apply rule defer
            apply(rule_tac x="v + w" in exI) using `u\<ge>0` and w and obt(3,4) by auto
          ultimately show ?thesis by auto
        qed
      qed auto
    qed
  qed auto
qed (auto simp add: assms)

lemma simplex_furthest_le:
  fixes s :: "('a::real_inner) set"
  assumes "finite s" "s \<noteq> {}"
  shows "\<exists>y\<in>s. \<forall>x\<in>(convex hull s). norm(x - a) \<le> norm(y - a)"
proof-
  have "convex hull s \<noteq> {}" using hull_subset[of s convex] and assms(2) by auto
  then obtain x where x:"x\<in>convex hull s" "\<forall>y\<in>convex hull s. norm (y - a) \<le> norm (x - a)"
    using distance_attains_sup[OF finite_imp_compact_convex_hull[OF assms(1)], of a]
    unfolding dist_commute[of a] unfolding dist_norm by auto
  thus ?thesis proof(cases "x\<in>s")
    case False then obtain y where "y\<in>convex hull s" "norm (x - a) < norm (y - a)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=x]] and x(1) by auto
    thus ?thesis using x(2)[THEN bspec[where x=y]] by auto
  qed auto
qed

lemma simplex_furthest_le_exists:
  fixes s :: "('a::real_inner) set"
  shows "finite s \<Longrightarrow> (\<forall>x\<in>(convex hull s). \<exists>y\<in>s. norm(x - a) \<le> norm(y - a))"
  using simplex_furthest_le[of s] by (cases "s={}")auto

lemma simplex_extremal_le:
  fixes s :: "('a::real_inner) set"
  assumes "finite s" "s \<noteq> {}"
  shows "\<exists>u\<in>s. \<exists>v\<in>s. \<forall>x\<in>convex hull s. \<forall>y \<in> convex hull s. norm(x - y) \<le> norm(u - v)"
proof-
  have "convex hull s \<noteq> {}" using hull_subset[of s convex] and assms(2) by auto
  then obtain u v where obt:"u\<in>convex hull s" "v\<in>convex hull s"
    "\<forall>x\<in>convex hull s. \<forall>y\<in>convex hull s. norm (x - y) \<le> norm (u - v)"
    using compact_sup_maxdistance[OF finite_imp_compact_convex_hull[OF assms(1)]] by (auto simp: dist_norm)
  thus ?thesis proof(cases "u\<notin>s \<or> v\<notin>s", erule_tac disjE)
    assume "u\<notin>s" then obtain y where "y\<in>convex hull s" "norm (u - v) < norm (y - v)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=u]] and obt(1) by auto
    thus ?thesis using obt(3)[THEN bspec[where x=y], THEN bspec[where x=v]] and obt(2) by auto
  next
    assume "v\<notin>s" then obtain y where "y\<in>convex hull s" "norm (v - u) < norm (y - u)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=v]] and obt(2) by auto
    thus ?thesis using obt(3)[THEN bspec[where x=u], THEN bspec[where x=y]] and obt(1)
      by (auto simp add: norm_minus_commute)
  qed auto
qed

lemma simplex_extremal_le_exists:
  fixes s :: "('a::real_inner) set"
  shows "finite s \<Longrightarrow> x \<in> convex hull s \<Longrightarrow> y \<in> convex hull s
  \<Longrightarrow> (\<exists>u\<in>s. \<exists>v\<in>s. norm(x - y) \<le> norm(u - v))"
  using convex_hull_empty simplex_extremal_le[of s] by(cases "s={}")auto

subsection {* Closest point of a convex set is unique, with a continuous projection. *}

definition
  closest_point :: "'a::{real_inner,heine_borel} set \<Rightarrow> 'a \<Rightarrow> 'a" where
 "closest_point s a = (SOME x. x \<in> s \<and> (\<forall>y\<in>s. dist a x \<le> dist a y))"

lemma closest_point_exists:
  assumes "closed s" "s \<noteq> {}"
  shows  "closest_point s a \<in> s" "\<forall>y\<in>s. dist a (closest_point s a) \<le> dist a y"
  unfolding closest_point_def apply(rule_tac[!] someI2_ex)
  using distance_attains_inf[OF assms(1,2), of a] by auto

lemma closest_point_in_set:
  "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> (closest_point s a) \<in> s"
  by(meson closest_point_exists)

lemma closest_point_le:
  "closed s \<Longrightarrow> x \<in> s \<Longrightarrow> dist a (closest_point s a) \<le> dist a x"
  using closest_point_exists[of s] by auto

lemma closest_point_self:
  assumes "x \<in> s"  shows "closest_point s x = x"
  unfolding closest_point_def apply(rule some1_equality, rule ex1I[of _ x])
  using assms by auto

lemma closest_point_refl:
 "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> (closest_point s x = x \<longleftrightarrow> x \<in> s)"
  using closest_point_in_set[of s x] closest_point_self[of x s] by auto

lemma closer_points_lemma:
  assumes "inner y z > 0"
  shows "\<exists>u>0. \<forall>v>0. v \<le> u \<longrightarrow> norm(v *\<^sub>R z - y) < norm y"
proof- have z:"inner z z > 0" unfolding inner_gt_zero_iff using assms by auto
  thus ?thesis using assms apply(rule_tac x="inner y z / inner z z" in exI) apply(rule) defer proof(rule+)
    fix v assume "0<v" "v \<le> inner y z / inner z z"
    thus "norm (v *\<^sub>R z - y) < norm y" unfolding norm_lt using z and assms
      by (simp add: field_simps inner_diff inner_commute mult_strict_left_mono[OF _ `0<v`])
  qed(rule divide_pos_pos, auto) qed

lemma closer_point_lemma:
  assumes "inner (y - x) (z - x) > 0"
  shows "\<exists>u>0. u \<le> 1 \<and> dist (x + u *\<^sub>R (z - x)) y < dist x y"
proof- obtain u where "u>0" and u:"\<forall>v>0. v \<le> u \<longrightarrow> norm (v *\<^sub>R (z - x) - (y - x)) < norm (y - x)"
    using closer_points_lemma[OF assms] by auto
  show ?thesis apply(rule_tac x="min u 1" in exI) using u[THEN spec[where x="min u 1"]] and `u>0`
    unfolding dist_norm by(auto simp add: norm_minus_commute field_simps) qed

lemma any_closest_point_dot:
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "inner (a - x) (y - x) \<le> 0"
proof(rule ccontr) assume "\<not> inner (a - x) (y - x) \<le> 0"
  then obtain u where u:"u>0" "u\<le>1" "dist (x + u *\<^sub>R (y - x)) a < dist x a" using closer_point_lemma[of a x y] by auto
  let ?z = "(1 - u) *\<^sub>R x + u *\<^sub>R y" have "?z \<in> s" using mem_convex[OF assms(1,3,4), of u] using u by auto
  thus False using assms(5)[THEN bspec[where x="?z"]] and u(3) by (auto simp add: dist_commute algebra_simps) qed

lemma any_closest_point_unique:
  fixes x :: "'a::real_inner"
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s"
  "\<forall>z\<in>s. dist a x \<le> dist a z" "\<forall>z\<in>s. dist a y \<le> dist a z"
  shows "x = y" using any_closest_point_dot[OF assms(1-4,5)] and any_closest_point_dot[OF assms(1-2,4,3,6)]
  unfolding norm_pths(1) and norm_le_square
  by (auto simp add: algebra_simps)

lemma closest_point_unique:
  assumes "convex s" "closed s" "x \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "x = closest_point s a"
  using any_closest_point_unique[OF assms(1-3) _ assms(4), of "closest_point s a"]
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_dot:
  assumes "convex s" "closed s" "x \<in> s"
  shows "inner (a - closest_point s a) (x - closest_point s a) \<le> 0"
  apply(rule any_closest_point_dot[OF assms(1,2) _ assms(3)])
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_lt:
  assumes "convex s" "closed s" "x \<in> s" "x \<noteq> closest_point s a"
  shows "dist a (closest_point s a) < dist a x"
  apply(rule ccontr) apply(rule_tac notE[OF assms(4)])
  apply(rule closest_point_unique[OF assms(1-3), of a])
  using closest_point_le[OF assms(2), of _ a] by fastforce

lemma closest_point_lipschitz:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "dist (closest_point s x) (closest_point s y) \<le> dist x y"
proof-
  have "inner (x - closest_point s x) (closest_point s y - closest_point s x) \<le> 0"
       "inner (y - closest_point s y) (closest_point s x - closest_point s y) \<le> 0"
    apply(rule_tac[!] any_closest_point_dot[OF assms(1-2)])
    using closest_point_exists[OF assms(2-3)] by auto
  thus ?thesis unfolding dist_norm and norm_le
    using inner_ge_zero[of "(x - closest_point s x) - (y - closest_point s y)"]
    by (simp add: inner_add inner_diff inner_commute) qed

lemma continuous_at_closest_point:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "continuous (at x) (closest_point s)"
  unfolding continuous_at_eps_delta
  using le_less_trans[OF closest_point_lipschitz[OF assms]] by auto

lemma continuous_on_closest_point:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "continuous_on t (closest_point s)"
by(metis continuous_at_imp_continuous_on continuous_at_closest_point[OF assms])

subsubsection {* Various point-to-set separating/supporting hyperplane theorems. *}

lemma supporting_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex s" "closed s" "s \<noteq> {}" "z \<notin> s"
  shows "\<exists>a b. \<exists>y\<in>s. inner a z < b \<and> (inner a y = b) \<and> (\<forall>x\<in>s. inner a x \<ge> b)"
proof-
  from distance_attains_inf[OF assms(2-3)] obtain y where "y\<in>s" and y:"\<forall>x\<in>s. dist z y \<le> dist z x" by auto
  show ?thesis apply(rule_tac x="y - z" in exI, rule_tac x="inner (y - z) y" in exI, rule_tac x=y in bexI)
    apply rule defer apply rule defer apply(rule, rule ccontr) using `y\<in>s` proof-
    show "inner (y - z) z < inner (y - z) y" apply(subst diff_less_iff(1)[symmetric])
      unfolding inner_diff_right[symmetric] and inner_gt_zero_iff using `y\<in>s` `z\<notin>s` by auto
  next
    fix x assume "x\<in>s" have *:"\<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> dist z y \<le> dist z ((1 - u) *\<^sub>R y + u *\<^sub>R x)"
      using assms(1)[unfolded convex_alt] and y and `x\<in>s` and `y\<in>s` by auto
    assume "\<not> inner (y - z) y \<le> inner (y - z) x" then obtain v where
      "v>0" "v\<le>1" "dist (y + v *\<^sub>R (x - y)) z < dist y z" using closer_point_lemma[of z y x] apply - by (auto simp add: inner_diff)
    thus False using *[THEN spec[where x=v]] by(auto simp add: dist_commute algebra_simps)
  qed auto
qed

lemma separating_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex s" "closed s" "z \<notin> s"
  shows "\<exists>a b. inner a z < b \<and> (\<forall>x\<in>s. inner a x > b)"
proof(cases "s={}")
  case True thus ?thesis apply(rule_tac x="-z" in exI, rule_tac x=1 in exI)
    using less_le_trans[OF _ inner_ge_zero[of z]] by auto
next
  case False obtain y where "y\<in>s" and y:"\<forall>x\<in>s. dist z y \<le> dist z x"
    using distance_attains_inf[OF assms(2) False] by auto
  show ?thesis apply(rule_tac x="y - z" in exI, rule_tac x="inner (y - z) z + (norm(y - z))\<^sup>2 / 2" in exI)
    apply rule defer apply rule proof-
    fix x assume "x\<in>s"
    have "\<not> 0 < inner (z - y) (x - y)" apply(rule_tac notI) proof(drule closer_point_lemma)
      assume "\<exists>u>0. u \<le> 1 \<and> dist (y + u *\<^sub>R (x - y)) z < dist y z"
      then obtain u where "u>0" "u\<le>1" "dist (y + u *\<^sub>R (x - y)) z < dist y z" by auto
      thus False using y[THEN bspec[where x="y + u *\<^sub>R (x - y)"]]
        using assms(1)[unfolded convex_alt, THEN bspec[where x=y]]
        using `x\<in>s` `y\<in>s` by (auto simp add: dist_commute algebra_simps) qed
    moreover have "0 < (norm (y - z))\<^sup>2" using `y\<in>s` `z\<notin>s` by auto
    hence "0 < inner (y - z) (y - z)" unfolding power2_norm_eq_inner by simp
    ultimately show "inner (y - z) z + (norm (y - z))\<^sup>2 / 2 < inner (y - z) x"
      unfolding power2_norm_eq_inner and not_less by (auto simp add: field_simps inner_commute inner_diff)
  qed(insert `y\<in>s` `z\<notin>s`, auto)
qed

lemma separating_hyperplane_closed_0:
  assumes "convex (s::('a::euclidean_space) set)" "closed s" "0 \<notin> s"
  shows "\<exists>a b. a \<noteq> 0 \<and> 0 < b \<and> (\<forall>x\<in>s. inner a x > b)"
  proof(cases "s={}")
  case True
  have "norm ((SOME i. i\<in>Basis)::'a) = 1" "(SOME i. i\<in>Basis) \<noteq> (0::'a)" defer
    apply(subst norm_le_zero_iff[symmetric]) by (auto simp: SOME_Basis)
  thus ?thesis apply(rule_tac x="SOME i. i\<in>Basis" in exI, rule_tac x=1 in exI)
    using True using DIM_positive[where 'a='a] by auto
next case False thus ?thesis using False using separating_hyperplane_closed_point[OF assms]
    apply - apply(erule exE)+ unfolding inner_zero_right apply(rule_tac x=a in exI, rule_tac x=b in exI) by auto qed

subsubsection {* Now set-to-set for closed/compact sets *}

lemma separating_hyperplane_closed_compact:
  assumes "convex (s::('a::euclidean_space) set)" "closed s" "convex t" "compact t" "t \<noteq> {}" "s \<inter> t = {}"
  shows "\<exists>a b. (\<forall>x\<in>s. inner a x < b) \<and> (\<forall>x\<in>t. inner a x > b)"
proof(cases "s={}")
  case True
  obtain b where b:"b>0" "\<forall>x\<in>t. norm x \<le> b" using compact_imp_bounded[OF assms(4)] unfolding bounded_pos by auto
  obtain z::"'a" where z:"norm z = b + 1" using vector_choose_size[of "b + 1"] and b(1) by auto
  hence "z\<notin>t" using b(2)[THEN bspec[where x=z]] by auto
  then obtain a b where ab:"inner a z < b" "\<forall>x\<in>t. b < inner a x"
    using separating_hyperplane_closed_point[OF assms(3) compact_imp_closed[OF assms(4)], of z] by auto
  thus ?thesis using True by auto
next
  case False then obtain y where "y\<in>s" by auto
  obtain a b where "0 < b" "\<forall>x\<in>{x - y |x y. x \<in> s \<and> y \<in> t}. b < inner a x"
    using separating_hyperplane_closed_point[OF convex_differences[OF assms(1,3)], of 0]
    using closed_compact_differences[OF assms(2,4)] using assms(6) by(auto, blast)
  hence ab:"\<forall>x\<in>s. \<forall>y\<in>t. b + inner a y < inner a x" apply- apply(rule,rule) apply(erule_tac x="x - y" in ballE) by (auto simp add: inner_diff)
  def k \<equiv> "Sup ((\<lambda>x. inner a x) ` t)"
  show ?thesis apply(rule_tac x="-a" in exI, rule_tac x="-(k + b / 2)" in exI)
    apply(rule,rule) defer apply(rule) unfolding inner_minus_left and neg_less_iff_less proof-
    from ab have "((\<lambda>x. inner a x) ` t) *<= (inner a y - b)"
      apply(erule_tac x=y in ballE) apply(rule setleI) using `y\<in>s` by auto
    hence k:"isLub UNIV ((\<lambda>x. inner a x) ` t) k" unfolding k_def apply(rule_tac isLub_cSup) using assms(5) by auto
    fix x assume "x\<in>t" thus "inner a x < (k + b / 2)" using `0<b` and isLubD2[OF k, of "inner a x"] by auto
  next
    fix x assume "x\<in>s"
    hence "k \<le> inner a x - b" unfolding k_def apply(rule_tac cSup_least) using assms(5)
      using ab[THEN bspec[where x=x]] by auto
    thus "k + b / 2 < inner a x" using `0 < b` by auto
  qed
qed

lemma separating_hyperplane_compact_closed:
  fixes s :: "('a::euclidean_space) set"
  assumes "convex s" "compact s" "s \<noteq> {}" "convex t" "closed t" "s \<inter> t = {}"
  shows "\<exists>a b. (\<forall>x\<in>s. inner a x < b) \<and> (\<forall>x\<in>t. inner a x > b)"
proof- obtain a b where "(\<forall>x\<in>t. inner a x < b) \<and> (\<forall>x\<in>s. b < inner a x)"
    using separating_hyperplane_closed_compact[OF assms(4-5,1-2,3)] and assms(6) by auto
  thus ?thesis apply(rule_tac x="-a" in exI, rule_tac x="-b" in exI) by auto qed

subsubsection {* General case without assuming closure and getting non-strict separation *}

lemma separating_hyperplane_set_0:
  assumes "convex s" "(0::'a::euclidean_space) \<notin> s"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>x\<in>s. 0 \<le> inner a x)"
proof- let ?k = "\<lambda>c. {x::'a. 0 \<le> inner c x}"
  have "frontier (cball 0 1) \<inter> (\<Inter> (?k ` s)) \<noteq> {}"
    apply(rule compact_imp_fip) apply(rule compact_frontier[OF compact_cball])
    defer apply(rule,rule,erule conjE) proof-
    fix f assume as:"f \<subseteq> ?k ` s" "finite f"
    obtain c where c:"f = ?k ` c" "c\<subseteq>s" "finite c" using finite_subset_image[OF as(2,1)] by auto
    then obtain a b where ab:"a \<noteq> 0" "0 < b"  "\<forall>x\<in>convex hull c. b < inner a x"
      using separating_hyperplane_closed_0[OF convex_convex_hull, of c]
      using finite_imp_compact_convex_hull[OF c(3), THEN compact_imp_closed] and assms(2)
      using subset_hull[of convex, OF assms(1), symmetric, of c] by auto
    hence "\<exists>x. norm x = 1 \<and> (\<forall>y\<in>c. 0 \<le> inner y x)" apply(rule_tac x="inverse(norm a) *\<^sub>R a" in exI)
       using hull_subset[of c convex] unfolding subset_eq and inner_scaleR
       apply- apply rule defer apply rule apply(rule mult_nonneg_nonneg)
       by(auto simp add: inner_commute del: ballE elim!: ballE)
    thus "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}" unfolding c(1) frontier_cball dist_norm by auto
  qed(insert closed_halfspace_ge, auto)
  then obtain x where "norm x = 1" "\<forall>y\<in>s. x\<in>?k y" unfolding frontier_cball dist_norm by auto
  thus ?thesis apply(rule_tac x=x in exI) by(auto simp add: inner_commute) qed

lemma separating_hyperplane_sets:
  assumes "convex s" "convex (t::('a::euclidean_space) set)" "s \<noteq> {}" "t \<noteq> {}" "s \<inter> t = {}"
  shows "\<exists>a b. a \<noteq> 0 \<and> (\<forall>x\<in>s. inner a x \<le> b) \<and> (\<forall>x\<in>t. inner a x \<ge> b)"
proof- from separating_hyperplane_set_0[OF convex_differences[OF assms(2,1)]]
  obtain a where "a\<noteq>0" "\<forall>x\<in>{x - y |x y. x \<in> t \<and> y \<in> s}. 0 \<le> inner a x"
    using assms(3-5) by auto
  hence "\<forall>x\<in>t. \<forall>y\<in>s. inner a y \<le> inner a x"
    by (force simp add: inner_diff)
  thus ?thesis
    apply(rule_tac x=a in exI, rule_tac x="Sup ((\<lambda>x. inner a x) ` s)" in exI) using `a\<noteq>0`
    apply auto
    apply (rule isLub_cSup[THEN isLubD2])
    prefer 4
    apply (rule cSup_least)
     using assms(3-5) apply (auto simp add: setle_def)
    apply metis
    done
qed

subsection {* More convexity generalities *}

lemma convex_closure:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "convex(closure s)"
  unfolding convex_def Ball_def closure_sequential
  apply(rule,rule,rule,rule,rule,rule,rule,rule,rule) apply(erule_tac exE)+
  apply(rule_tac x="\<lambda>n. u *\<^sub>R xb n + v *\<^sub>R xc n" in exI) apply(rule,rule)
  apply(rule assms[unfolded convex_def, rule_format]) prefer 6
  by (auto del: tendsto_const intro!: tendsto_intros)

lemma convex_interior:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "convex(interior s)"
  unfolding convex_alt Ball_def mem_interior apply(rule,rule,rule,rule,rule,rule) apply(erule exE | erule conjE)+ proof-
  fix x y u assume u:"0 \<le> u" "u \<le> (1::real)"
  fix e d assume ed:"ball x e \<subseteq> s" "ball y d \<subseteq> s" "0<d" "0<e"
  show "\<exists>e>0. ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) e \<subseteq> s" apply(rule_tac x="min d e" in exI)
    apply rule unfolding subset_eq defer apply rule proof-
    fix z assume "z \<in> ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) (min d e)"
    hence "(1- u) *\<^sub>R (z - u *\<^sub>R (y - x)) + u *\<^sub>R (z + (1 - u) *\<^sub>R (y - x)) \<in> s"
      apply(rule_tac assms[unfolded convex_alt, rule_format])
      using ed(1,2) and u unfolding subset_eq mem_ball Ball_def dist_norm by(auto simp add: algebra_simps)
    thus "z \<in> s" using u by (auto simp add: algebra_simps) qed(insert u ed(3-4), auto) qed

lemma convex_hull_eq_empty[simp]: "convex hull s = {} \<longleftrightarrow> s = {}"
  using hull_subset[of s convex] convex_hull_empty by auto

subsection {* Moving and scaling convex hulls. *}

lemma convex_hull_translation_lemma:
  "convex hull ((\<lambda>x. a + x) ` s) \<subseteq> (\<lambda>x. a + x) ` (convex hull s)"
by (metis convex_convex_hull convex_translation hull_minimal hull_subset image_mono)

lemma convex_hull_bilemma: fixes neg
  assumes "(\<forall>s a. (convex hull (up a s)) \<subseteq> up a (convex hull s))"
  shows "(\<forall>s. up a (up (neg a) s) = s) \<and> (\<forall>s. up (neg a) (up a s) = s) \<and> (\<forall>s t a. s \<subseteq> t \<longrightarrow> up a s \<subseteq> up a t)
  \<Longrightarrow> \<forall>s. (convex hull (up a s)) = up a (convex hull s)"
  using assms by(metis subset_antisym)

lemma convex_hull_translation:
  "convex hull ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (convex hull s)"
  apply(rule convex_hull_bilemma[rule_format, of _ _ "\<lambda>a. -a"], rule convex_hull_translation_lemma) unfolding image_image by auto

lemma convex_hull_scaling_lemma:
 "(convex hull ((\<lambda>x. c *\<^sub>R x) ` s)) \<subseteq> (\<lambda>x. c *\<^sub>R x) ` (convex hull s)"
by (metis convex_convex_hull convex_scaling hull_subset subset_hull subset_image_iff)

lemma convex_hull_scaling:
  "convex hull ((\<lambda>x. c *\<^sub>R x) ` s) = (\<lambda>x. c *\<^sub>R x) ` (convex hull s)"
  apply(cases "c=0") defer apply(rule convex_hull_bilemma[rule_format, of _ _ inverse]) apply(rule convex_hull_scaling_lemma)
  unfolding image_image scaleR_scaleR by(auto simp add:image_constant_conv)

lemma convex_hull_affinity:
  "convex hull ((\<lambda>x. a + c *\<^sub>R x) ` s) = (\<lambda>x. a + c *\<^sub>R x) ` (convex hull s)"
by(simp only: image_image[symmetric] convex_hull_scaling convex_hull_translation)

subsection {* Convexity of cone hulls *}

lemma convex_cone_hull:
assumes "convex S"
shows "convex (cone hull S)"
proof-
{ fix x y assume xy_def: "x : cone hull S & y : cone hull S"
  hence "S ~= {}" using cone_hull_empty_iff[of S] by auto
  fix u v assume uv_def: "u>=0 & v>=0 & (u :: real)+v=1"
  hence *: "u *\<^sub>R x : cone hull S & v *\<^sub>R y : cone hull S"
     using cone_cone_hull[of S] xy_def cone_def[of "cone hull S"] by auto
  from * obtain cx xx where x_def: "u *\<^sub>R x = cx *\<^sub>R xx & (cx :: real)>=0 & xx : S"
     using cone_hull_expl[of S] by auto
  from * obtain cy yy where y_def: "v *\<^sub>R y = cy *\<^sub>R yy & (cy :: real)>=0 & yy : S"
     using cone_hull_expl[of S] by auto
  { assume "cx+cy<=0" hence "u *\<^sub>R x=0 & v *\<^sub>R y=0" using x_def y_def by auto
    hence "u *\<^sub>R x+ v *\<^sub>R y = 0" by auto
    hence "u *\<^sub>R x+ v *\<^sub>R y : cone hull S" using cone_hull_contains_0[of S] `S ~= {}` by auto
  }
  moreover
  { assume "cx+cy>0"
    hence "(cx/(cx+cy)) *\<^sub>R xx + (cy/(cx+cy)) *\<^sub>R yy : S"
      using assms mem_convex_alt[of S xx yy cx cy] x_def y_def by auto
    hence "cx *\<^sub>R xx + cy *\<^sub>R yy : cone hull S"
      using mem_cone_hull[of "(cx/(cx+cy)) *\<^sub>R xx + (cy/(cx+cy)) *\<^sub>R yy" S "cx+cy"]
      `cx+cy>0` by (auto simp add: scaleR_right_distrib)
    hence "u *\<^sub>R x+ v *\<^sub>R y : cone hull S" using x_def y_def by auto
  }
  moreover have "(cx+cy<=0) | (cx+cy>0)" by auto
  ultimately have "u *\<^sub>R x+ v *\<^sub>R y : cone hull S" by blast
} from this show ?thesis unfolding convex_def by auto
qed

lemma cone_convex_hull:
assumes "cone S"
shows "cone (convex hull S)"
proof-
{ assume "S = {}" hence ?thesis by auto }
moreover
{ assume "S ~= {}" hence *: "0:S & (!c. c>0 --> op *\<^sub>R c ` S = S)" using cone_iff[of S] assms by auto
  { fix c assume "(c :: real)>0"
    hence "op *\<^sub>R c ` (convex hull S) = convex hull (op *\<^sub>R c ` S)"
       using convex_hull_scaling[of _ S] by auto
    also have "...=convex hull S" using * `c>0` by auto
    finally have "op *\<^sub>R c ` (convex hull S) = convex hull S" by auto
  }
  hence "0 : convex hull S & (!c. c>0 --> (op *\<^sub>R c ` (convex hull S)) = (convex hull S))"
     using * hull_subset[of S convex] by auto
  hence ?thesis using `S ~= {}` cone_iff[of "convex hull S"] by auto
}
ultimately show ?thesis by blast
qed

subsection {* Convex set as intersection of halfspaces *}

lemma convex_halfspace_intersection:
  fixes s :: "('a::euclidean_space) set"
  assumes "closed s" "convex s"
  shows "s = \<Inter> {h. s \<subseteq> h \<and> (\<exists>a b. h = {x. inner a x \<le> b})}"
  apply(rule set_eqI, rule) unfolding Inter_iff Ball_def mem_Collect_eq apply(rule,rule,erule conjE) proof-
  fix x  assume "\<forall>xa. s \<subseteq> xa \<and> (\<exists>a b. xa = {x. inner a x \<le> b}) \<longrightarrow> x \<in> xa"
  hence "\<forall>a b. s \<subseteq> {x. inner a x \<le> b} \<longrightarrow> x \<in> {x. inner a x \<le> b}" by blast
  thus "x\<in>s" apply(rule_tac ccontr) apply(drule separating_hyperplane_closed_point[OF assms(2,1)])
    apply(erule exE)+ apply(erule_tac x="-a" in allE, erule_tac x="-b" in allE) by auto
qed auto

subsection {* Radon's theorem (from Lars Schewe) *}

lemma radon_ex_lemma:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>u. setsum u c = 0 \<and> (\<exists>v\<in>c. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) c = 0"
proof- from assms(2)[unfolded affine_dependent_explicit] guess s .. then guess u ..
  thus ?thesis apply(rule_tac x="\<lambda>v. if v\<in>s then u v else 0" in exI) unfolding if_smult scaleR_zero_left
    and setsum_restrict_set[OF assms(1), symmetric] by(auto simp add: Int_absorb1) qed

lemma radon_s_lemma:
  assumes "finite s" "setsum f s = (0::real)"
  shows "setsum f {x\<in>s. 0 < f x} = - setsum f {x\<in>s. f x < 0}"
proof- have *:"\<And>x. (if f x < 0 then f x else 0) + (if 0 < f x then f x else 0) = f x" by auto
  show ?thesis unfolding real_add_eq_0_iff[symmetric] and setsum_restrict_set''[OF assms(1)] and setsum_addf[symmetric] and *
    using assms(2) by assumption qed

lemma radon_v_lemma:
  assumes "finite s" "setsum f s = 0" "\<forall>x. g x = (0::real) \<longrightarrow> f x = (0::'a::euclidean_space)"
  shows "(setsum f {x\<in>s. 0 < g x}) = - setsum f {x\<in>s. g x < 0}"
proof-
  have *:"\<And>x. (if 0 < g x then f x else 0) + (if g x < 0 then f x else 0) = f x" using assms(3) by auto
  show ?thesis unfolding eq_neg_iff_add_eq_0 and setsum_restrict_set''[OF assms(1)] and setsum_addf[symmetric] and *
    using assms(2) by assumption qed

lemma radon_partition:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>m p. m \<inter> p = {} \<and> m \<union> p = c \<and> (convex hull m) \<inter> (convex hull p) \<noteq> {}" proof-
  obtain u v where uv:"setsum u c = 0" "v\<in>c" "u v \<noteq> 0"  "(\<Sum>v\<in>c. u v *\<^sub>R v) = 0" using radon_ex_lemma[OF assms] by auto
  have fin:"finite {x \<in> c. 0 < u x}" "finite {x \<in> c. 0 > u x}" using assms(1) by auto
  def z \<equiv> "(inverse (setsum u {x\<in>c. u x > 0})) *\<^sub>R setsum (\<lambda>x. u x *\<^sub>R x) {x\<in>c. u x > 0}"
  have "setsum u {x \<in> c. 0 < u x} \<noteq> 0" proof(cases "u v \<ge> 0")
    case False hence "u v < 0" by auto
    thus ?thesis proof(cases "\<exists>w\<in>{x \<in> c. 0 < u x}. u w > 0")
      case True thus ?thesis using setsum_nonneg_eq_0_iff[of _ u, OF fin(1)] by auto
    next
      case False hence "setsum u c \<le> setsum (\<lambda>x. if x=v then u v else 0) c" apply(rule_tac setsum_mono) by auto
      thus ?thesis unfolding setsum_delta[OF assms(1)] using uv(2) and `u v < 0` and uv(1) by auto qed
  qed (insert setsum_nonneg_eq_0_iff[of _ u, OF fin(1)] uv(2-3), auto)

  hence *:"setsum u {x\<in>c. u x > 0} > 0" unfolding less_le apply(rule_tac conjI, rule_tac setsum_nonneg) by auto
  moreover have "setsum u ({x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}) = setsum u c"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}. u x *\<^sub>R x) = (\<Sum>x\<in>c. u x *\<^sub>R x)"
    using assms(1) apply(rule_tac[!] setsum_mono_zero_left) by auto
  hence "setsum u {x \<in> c. 0 < u x} = - setsum u {x \<in> c. 0 > u x}"
   "(\<Sum>x\<in>{x \<in> c. 0 < u x}. u x *\<^sub>R x) = - (\<Sum>x\<in>{x \<in> c. 0 > u x}. u x *\<^sub>R x)"
    unfolding eq_neg_iff_add_eq_0 using uv(1,4) by (auto simp add:  setsum_Un_zero[OF fin, symmetric])
  moreover have "\<forall>x\<in>{v \<in> c. u v < 0}. 0 \<le> inverse (setsum u {x \<in> c. 0 < u x}) * - u x"
    apply (rule) apply (rule mult_nonneg_nonneg) using * by auto

  ultimately have "z \<in> convex hull {v \<in> c. u v \<le> 0}" unfolding convex_hull_explicit mem_Collect_eq
    apply(rule_tac x="{v \<in> c. u v < 0}" in exI, rule_tac x="\<lambda>y. inverse (setsum u {x\<in>c. u x > 0}) * - u y" in exI)
    using assms(1) unfolding scaleR_scaleR[symmetric] scaleR_right.setsum [symmetric] and z_def
    by(auto simp add: setsum_negf setsum_right_distrib[symmetric])
  moreover have "\<forall>x\<in>{v \<in> c. 0 < u v}. 0 \<le> inverse (setsum u {x \<in> c. 0 < u x}) * u x"
    apply (rule) apply (rule mult_nonneg_nonneg) using * by auto
  hence "z \<in> convex hull {v \<in> c. u v > 0}" unfolding convex_hull_explicit mem_Collect_eq
    apply(rule_tac x="{v \<in> c. 0 < u v}" in exI, rule_tac x="\<lambda>y. inverse (setsum u {x\<in>c. u x > 0}) * u y" in exI)
    using assms(1) unfolding scaleR_scaleR[symmetric] scaleR_right.setsum [symmetric] and z_def using *
    by(auto simp add: setsum_negf setsum_right_distrib[symmetric])
  ultimately show ?thesis apply(rule_tac x="{v\<in>c. u v \<le> 0}" in exI, rule_tac x="{v\<in>c. u v > 0}" in exI) by auto
qed

lemma radon: assumes "affine_dependent c"
  obtains m p where "m\<subseteq>c" "p\<subseteq>c" "m \<inter> p = {}" "(convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof- from assms[unfolded affine_dependent_explicit] guess s .. then guess u ..
  hence *:"finite s" "affine_dependent s" and s:"s \<subseteq> c" unfolding affine_dependent_explicit by auto
  from radon_partition[OF *] guess m .. then guess p ..
  thus ?thesis apply(rule_tac that[of p m]) using s by auto qed

subsection {* Helly's theorem *}

lemma helly_induct: fixes f::"('a::euclidean_space) set set"
  assumes "card f = n" "n \<ge> DIM('a) + 1"
  "\<forall>s\<in>f. convex s" "\<forall>t\<subseteq>f. card t = DIM('a) + 1 \<longrightarrow> \<Inter> t \<noteq> {}"
  shows "\<Inter> f \<noteq> {}"
using assms proof(induct n arbitrary: f)
case (Suc n)
have "finite f" using `card f = Suc n` by (auto intro: card_ge_0_finite)
show "\<Inter> f \<noteq> {}" apply(cases "n = DIM('a)") apply(rule Suc(5)[rule_format])
  unfolding `card f = Suc n` proof-
  assume ng:"n \<noteq> DIM('a)" hence "\<exists>X. \<forall>s\<in>f. X s \<in> \<Inter>(f - {s})" apply(rule_tac bchoice) unfolding ex_in_conv
    apply(rule, rule Suc(1)[rule_format]) unfolding card_Diff_singleton_if[OF `finite f`] `card f = Suc n`
    defer defer apply(rule Suc(4)[rule_format]) defer apply(rule Suc(5)[rule_format]) using Suc(3) `finite f` by auto
  then obtain X where X:"\<forall>s\<in>f. X s \<in> \<Inter>(f - {s})" by auto
  show ?thesis proof(cases "inj_on X f")
    case False then obtain s t where st:"s\<noteq>t" "s\<in>f" "t\<in>f" "X s = X t" unfolding inj_on_def by auto
    hence *:"\<Inter> f = \<Inter> (f - {s}) \<inter> \<Inter> (f - {t})" by auto
    show ?thesis unfolding * unfolding ex_in_conv[symmetric] apply(rule_tac x="X s" in exI)
      apply(rule, rule X[rule_format]) using X st by auto
  next case True then obtain m p where mp:"m \<inter> p = {}" "m \<union> p = X ` f" "convex hull m \<inter> convex hull p \<noteq> {}"
      using radon_partition[of "X ` f"] and affine_dependent_biggerset[of "X ` f"]
      unfolding card_image[OF True] and `card f = Suc n` using Suc(3) `finite f` and ng by auto
    have "m \<subseteq> X ` f" "p \<subseteq> X ` f" using mp(2) by auto
    then obtain g h where gh:"m = X ` g" "p = X ` h" "g \<subseteq> f" "h \<subseteq> f" unfolding subset_image_iff by auto
    hence "f \<union> (g \<union> h) = f" by auto
    hence f:"f = g \<union> h" using inj_on_Un_image_eq_iff[of X f "g \<union> h"] and True
      unfolding mp(2)[unfolded image_Un[symmetric] gh] by auto
    have *:"g \<inter> h = {}" using mp(1) unfolding gh using inj_on_image_Int[OF True gh(3,4)] by auto
    have "convex hull (X ` h) \<subseteq> \<Inter> g" "convex hull (X ` g) \<subseteq> \<Inter> h"
      apply(rule_tac [!] hull_minimal) using Suc gh(3-4)  unfolding subset_eq
      apply(rule_tac [2] convex_Inter, rule_tac [4] convex_Inter) apply rule prefer 3 apply rule proof-
      fix x assume "x\<in>X ` g" then guess y unfolding image_iff ..
      thus "x\<in>\<Inter>h" using X[THEN bspec[where x=y]] using * f by auto next
      fix x assume "x\<in>X ` h" then guess y unfolding image_iff ..
      thus "x\<in>\<Inter>g" using X[THEN bspec[where x=y]] using * f by auto
    qed(auto)
    thus ?thesis unfolding f using mp(3)[unfolded gh] by blast qed
qed(auto) qed(auto)

lemma helly: fixes f::"('a::euclidean_space) set set"
  assumes "card f \<ge> DIM('a) + 1" "\<forall>s\<in>f. convex s"
          "\<forall>t\<subseteq>f. card t = DIM('a) + 1 \<longrightarrow> \<Inter> t \<noteq> {}"
  shows "\<Inter> f \<noteq>{}"
  apply(rule helly_induct) using assms by auto

subsection {* Homeomorphism of all convex compact sets with nonempty interior *}

lemma compact_frontier_line_lemma:
  fixes s :: "('a::euclidean_space) set"
  assumes "compact s" "0 \<in> s" "x \<noteq> 0"
  obtains u where "0 \<le> u" "(u *\<^sub>R x) \<in> frontier s" "\<forall>v>u. (v *\<^sub>R x) \<notin> s"
proof-
  obtain b where b:"b>0" "\<forall>x\<in>s. norm x \<le> b" using compact_imp_bounded[OF assms(1), unfolded bounded_pos] by auto
  let ?A = "{y. \<exists>u. 0 \<le> u \<and> u \<le> b / norm(x) \<and> (y = u *\<^sub>R x)}"
  have A:"?A = (\<lambda>u. u *\<^sub>R x) ` {0 .. b / norm x}"
    by auto
  have *:"\<And>x A B. x\<in>A \<Longrightarrow> x\<in>B \<Longrightarrow> A\<inter>B \<noteq> {}" by blast
  have "compact ?A" unfolding A apply(rule compact_continuous_image, rule continuous_at_imp_continuous_on)
    apply(rule, intro continuous_intros)
    by(rule compact_interval)
  moreover have "{y. \<exists>u\<ge>0. u \<le> b / norm x \<and> y = u *\<^sub>R x} \<inter> s \<noteq> {}" apply(rule *[OF _ assms(2)])
    unfolding mem_Collect_eq using `b>0` assms(3) by(auto intro!: divide_nonneg_pos)
  ultimately obtain u y where obt: "u\<ge>0" "u \<le> b / norm x" "y = u *\<^sub>R x"
    "y\<in>?A" "y\<in>s" "\<forall>z\<in>?A \<inter> s. dist 0 z \<le> dist 0 y" using distance_attains_sup[OF compact_inter[OF _ assms(1), of ?A], of 0] by auto

  have "norm x > 0" using assms(3)[unfolded zero_less_norm_iff[symmetric]] by auto
  { fix v assume as:"v > u" "v *\<^sub>R x \<in> s"
    hence "v \<le> b / norm x" using b(2)[rule_format, OF as(2)]
      using `u\<ge>0` unfolding pos_le_divide_eq[OF `norm x > 0`] by auto
    hence "norm (v *\<^sub>R x) \<le> norm y" apply(rule_tac obt(6)[rule_format, unfolded dist_0_norm]) apply(rule IntI) defer
      apply(rule as(2)) unfolding mem_Collect_eq apply(rule_tac x=v in exI)
      using as(1) `u\<ge>0` by(auto simp add:field_simps)
    hence False unfolding obt(3) using `u\<ge>0` `norm x > 0` `v>u` by(auto simp add:field_simps)
  } note u_max = this

  have "u *\<^sub>R x \<in> frontier s" unfolding frontier_straddle apply(rule,rule,rule) apply(rule_tac x="u *\<^sub>R x" in bexI) unfolding obt(3)[symmetric]
    prefer 3 apply(rule_tac x="(u + (e / 2) / norm x) *\<^sub>R x" in exI) apply(rule, rule) proof-
    fix e  assume "0 < e" and as:"(u + e / 2 / norm x) *\<^sub>R x \<in> s"
    hence "u + e / 2 / norm x > u" using`norm x > 0` by(auto simp del:zero_less_norm_iff intro!: divide_pos_pos)
    thus False using u_max[OF _ as] by auto
  qed(insert `y\<in>s`, auto simp add: dist_norm scaleR_left_distrib obt(3))
  thus ?thesis by(metis that[of u] u_max obt(1))
qed

lemma starlike_compact_projective:
  assumes "compact s" "cball (0::'a::euclidean_space) 1 \<subseteq> s "
  "\<forall>x\<in>s. \<forall>u. 0 \<le> u \<and> u < 1 \<longrightarrow> (u *\<^sub>R x) \<in> (s - frontier s )"
  shows "s homeomorphic (cball (0::'a::euclidean_space) 1)"
proof-
  have fs:"frontier s \<subseteq> s" apply(rule frontier_subset_closed) using compact_imp_closed[OF assms(1)] by simp
  def pi \<equiv> "\<lambda>x::'a. inverse (norm x) *\<^sub>R x"
  have "0 \<notin> frontier s" unfolding frontier_straddle apply(rule ccontr) unfolding not_not apply(erule_tac x=1 in allE)
    using assms(2)[unfolded subset_eq Ball_def mem_cball] by auto
  have injpi:"\<And>x y. pi x = pi y \<and> norm x = norm y \<longleftrightarrow> x = y" unfolding pi_def by auto

  have contpi:"continuous_on (UNIV - {0}) pi" apply(rule continuous_at_imp_continuous_on)
    apply rule unfolding pi_def
    apply (intro continuous_intros)
    apply simp
    done
  def sphere \<equiv> "{x::'a. norm x = 1}"
  have pi:"\<And>x. x \<noteq> 0 \<Longrightarrow> pi x \<in> sphere" "\<And>x u. u>0 \<Longrightarrow> pi (u *\<^sub>R x) = pi x" unfolding pi_def sphere_def by auto

  have "0\<in>s" using assms(2) and centre_in_cball[of 0 1] by auto
  have front_smul:"\<forall>x\<in>frontier s. \<forall>u\<ge>0. u *\<^sub>R x \<in> s \<longleftrightarrow> u \<le> 1" proof(rule,rule,rule)
    fix x u assume x:"x\<in>frontier s" and "(0::real)\<le>u"
    hence "x\<noteq>0" using `0\<notin>frontier s` by auto
    obtain v where v:"0 \<le> v" "v *\<^sub>R x \<in> frontier s" "\<forall>w>v. w *\<^sub>R x \<notin> s"
      using compact_frontier_line_lemma[OF assms(1) `0\<in>s` `x\<noteq>0`] by auto
    have "v=1" apply(rule ccontr) unfolding neq_iff apply(erule disjE) proof-
      assume "v<1" thus False using v(3)[THEN spec[where x=1]] using x and fs by auto next
      assume "v>1" thus False using assms(3)[THEN bspec[where x="v *\<^sub>R x"], THEN spec[where x="inverse v"]]
        using v and x and fs unfolding inverse_less_1_iff by auto qed
    show "u *\<^sub>R x \<in> s \<longleftrightarrow> u \<le> 1" apply rule  using v(3)[unfolded `v=1`, THEN spec[where x=u]] proof-
      assume "u\<le>1" thus "u *\<^sub>R x \<in> s" apply(cases "u=1")
        using assms(3)[THEN bspec[where x=x], THEN spec[where x=u]] using `0\<le>u` and x and fs by auto qed auto qed

  have "\<exists>surf. homeomorphism (frontier s) sphere pi surf"
    apply(rule homeomorphism_compact) apply(rule compact_frontier[OF assms(1)])
    apply(rule continuous_on_subset[OF contpi]) defer apply(rule set_eqI,rule)
    unfolding inj_on_def prefer 3 apply(rule,rule,rule)
  proof- fix x assume "x\<in>pi ` frontier s" then obtain y where "y\<in>frontier s" "x = pi y" by auto
    thus "x \<in> sphere" using pi(1)[of y] and `0 \<notin> frontier s` by auto
  next fix x assume "x\<in>sphere" hence "norm x = 1" "x\<noteq>0" unfolding sphere_def by auto
    then obtain u where "0 \<le> u" "u *\<^sub>R x \<in> frontier s" "\<forall>v>u. v *\<^sub>R x \<notin> s"
      using compact_frontier_line_lemma[OF assms(1) `0\<in>s`, of x] by auto
    thus "x \<in> pi ` frontier s" unfolding image_iff le_less pi_def apply(rule_tac x="u *\<^sub>R x" in bexI) using `norm x = 1` `0\<notin>frontier s` by auto
  next fix x y assume as:"x \<in> frontier s" "y \<in> frontier s" "pi x = pi y"
    hence xys:"x\<in>s" "y\<in>s" using fs by auto
    from as(1,2) have nor:"norm x \<noteq> 0" "norm y \<noteq> 0" using `0\<notin>frontier s` by auto
    from nor have x:"x = norm x *\<^sub>R ((inverse (norm y)) *\<^sub>R y)" unfolding as(3)[unfolded pi_def, symmetric] by auto
    from nor have y:"y = norm y *\<^sub>R ((inverse (norm x)) *\<^sub>R x)" unfolding as(3)[unfolded pi_def] by auto
    have "0 \<le> norm y * inverse (norm x)" "0 \<le> norm x * inverse (norm y)"
      unfolding divide_inverse[symmetric] apply(rule_tac[!] divide_nonneg_pos) using nor by auto
    hence "norm x = norm y" apply(rule_tac ccontr) unfolding neq_iff
      using x y and front_smul[THEN bspec, OF as(1), THEN spec[where x="norm y * (inverse (norm x))"]]
      using front_smul[THEN bspec, OF as(2), THEN spec[where x="norm x * (inverse (norm y))"]]
      using xys nor by(auto simp add:field_simps divide_le_eq_1 divide_inverse[symmetric])
    thus "x = y" apply(subst injpi[symmetric]) using as(3) by auto
  qed(insert `0 \<notin> frontier s`, auto)
  then obtain surf where surf:"\<forall>x\<in>frontier s. surf (pi x) = x"  "pi ` frontier s = sphere" "continuous_on (frontier s) pi"
    "\<forall>y\<in>sphere. pi (surf y) = y" "surf ` sphere = frontier s" "continuous_on sphere surf" unfolding homeomorphism_def by auto

  have cont_surfpi:"continuous_on (UNIV -  {0}) (surf \<circ> pi)" apply(rule continuous_on_compose, rule contpi)
    apply(rule continuous_on_subset[of sphere], rule surf(6)) using pi(1) by auto

  { fix x assume as:"x \<in> cball (0::'a) 1"
    have "norm x *\<^sub>R surf (pi x) \<in> s" proof(cases "x=0 \<or> norm x = 1")
      case False hence "pi x \<in> sphere" "norm x < 1" using pi(1)[of x] as by(auto simp add: dist_norm)
      thus ?thesis apply(rule_tac assms(3)[rule_format, THEN DiffD1])
        apply(rule_tac fs[unfolded subset_eq, rule_format])
        unfolding surf(5)[symmetric] by auto
    next case True thus ?thesis apply rule defer unfolding pi_def apply(rule fs[unfolded subset_eq, rule_format])
        unfolding  surf(5)[unfolded sphere_def, symmetric] using `0\<in>s` by auto qed } note hom = this

  { fix x assume "x\<in>s"
    hence "x \<in> (\<lambda>x. norm x *\<^sub>R surf (pi x)) ` cball 0 1" proof(cases "x=0")
      case True show ?thesis unfolding image_iff True apply(rule_tac x=0 in bexI) by auto
    next let ?a = "inverse (norm (surf (pi x)))"
      case False hence invn:"inverse (norm x) \<noteq> 0" by auto
      from False have pix:"pi x\<in>sphere" using pi(1) by auto
      hence "pi (surf (pi x)) = pi x" apply(rule_tac surf(4)[rule_format]) by assumption
      hence **:"norm x *\<^sub>R (?a *\<^sub>R surf (pi x)) = x" apply(rule_tac scaleR_left_imp_eq[OF invn]) unfolding pi_def using invn by auto
      hence *:"?a * norm x > 0" and"?a > 0" "?a \<noteq> 0" using surf(5) `0\<notin>frontier s` apply -
        apply(rule_tac mult_pos_pos) using False[unfolded zero_less_norm_iff[symmetric]] by auto
      have "norm (surf (pi x)) \<noteq> 0" using ** False by auto
      hence "norm x = norm ((?a * norm x) *\<^sub>R surf (pi x))"
        unfolding norm_scaleR abs_mult abs_norm_cancel abs_of_pos[OF `?a > 0`] by auto
      moreover have "pi x = pi ((inverse (norm (surf (pi x))) * norm x) *\<^sub>R surf (pi x))"
        unfolding pi(2)[OF *] surf(4)[rule_format, OF pix] ..
      moreover have "surf (pi x) \<in> frontier s" using surf(5) pix by auto
      hence "dist 0 (inverse (norm (surf (pi x))) *\<^sub>R x) \<le> 1" unfolding dist_norm
        using ** and * using front_smul[THEN bspec[where x="surf (pi x)"], THEN spec[where x="norm x * ?a"]]
        using False `x\<in>s` by(auto simp add:field_simps)
      ultimately show ?thesis unfolding image_iff apply(rule_tac x="inverse (norm (surf(pi x))) *\<^sub>R x" in bexI)
        apply(subst injpi[symmetric]) unfolding abs_mult abs_norm_cancel abs_of_pos[OF `?a > 0`]
        unfolding pi(2)[OF `?a > 0`] by auto
    qed } note hom2 = this

  show ?thesis apply(subst homeomorphic_sym) apply(rule homeomorphic_compact[where f="\<lambda>x. norm x *\<^sub>R surf (pi x)"])
    apply(rule compact_cball) defer apply(rule set_eqI, rule, erule imageE, drule hom)
    prefer 4 apply(rule continuous_at_imp_continuous_on, rule) apply(rule_tac [3] hom2) proof-
    fix x::"'a" assume as:"x \<in> cball 0 1"
    thus "continuous (at x) (\<lambda>x. norm x *\<^sub>R surf (pi x))" proof(cases "x=0")
      case False thus ?thesis apply (intro continuous_intros)
        using cont_surfpi unfolding continuous_on_eq_continuous_at[OF open_delete[OF open_UNIV]] o_def by auto
    next obtain B where B:"\<forall>x\<in>s. norm x \<le> B" using compact_imp_bounded[OF assms(1)] unfolding bounded_iff by auto
      hence "B > 0" using assms(2) unfolding subset_eq apply(erule_tac x="SOME i. i\<in>Basis" in ballE) defer
        apply(erule_tac x="SOME i. i\<in>Basis" in ballE)
        unfolding Ball_def mem_cball dist_norm using DIM_positive[where 'a='a]
        by (auto simp: SOME_Basis)
      case True show ?thesis unfolding True continuous_at Lim_at apply(rule,rule) apply(rule_tac x="e / B" in exI)
        apply(rule) apply(rule divide_pos_pos) prefer 3 apply(rule,rule,erule conjE)
        unfolding norm_zero scaleR_zero_left dist_norm diff_0_right norm_scaleR abs_norm_cancel proof-
        fix e and x::"'a" assume as:"norm x < e / B" "0 < norm x" "0<e"
        hence "surf (pi x) \<in> frontier s" using pi(1)[of x] unfolding surf(5)[symmetric] by auto
        hence "norm (surf (pi x)) \<le> B" using B fs by auto
        hence "norm x * norm (surf (pi x)) \<le> norm x * B" using as(2) by auto
        also have "\<dots> < e / B * B" apply(rule mult_strict_right_mono) using as(1) `B>0` by auto
        also have "\<dots> = e" using `B>0` by auto
        finally show "norm x * norm (surf (pi x)) < e" by assumption
      qed(insert `B>0`, auto) qed
  next { fix x assume as:"surf (pi x) = 0"
      have "x = 0" proof(rule ccontr)
        assume "x\<noteq>0" hence "pi x \<in> sphere" using pi(1) by auto
        hence "surf (pi x) \<in> frontier s" using surf(5) by auto
        thus False using `0\<notin>frontier s` unfolding as by simp qed
    } note surf_0 = this
    show "inj_on (\<lambda>x. norm x *\<^sub>R surf (pi x)) (cball 0 1)" unfolding inj_on_def proof(rule,rule,rule)
      fix x y assume as:"x \<in> cball 0 1" "y \<in> cball 0 1" "norm x *\<^sub>R surf (pi x) = norm y *\<^sub>R surf (pi y)"
      thus "x=y" proof(cases "x=0 \<or> y=0")
        case True thus ?thesis using as by(auto elim: surf_0) next
        case False
        hence "pi (surf (pi x)) = pi (surf (pi y))" using as(3)
          using pi(2)[of "norm x" "surf (pi x)"] pi(2)[of "norm y" "surf (pi y)"] by auto
        moreover have "pi x \<in> sphere" "pi y \<in> sphere" using pi(1) False by auto
        ultimately have *:"pi x = pi y" using surf(4)[THEN bspec[where x="pi x"]] surf(4)[THEN bspec[where x="pi y"]] by auto
        moreover have "norm x = norm y" using as(3)[unfolded *] using False by(auto dest:surf_0)
        ultimately show ?thesis using injpi by auto qed qed
  qed auto qed

lemma homeomorphic_convex_compact_lemma:
  fixes s :: "('a::euclidean_space) set"
  assumes "convex s" and "compact s" and "cball 0 1 \<subseteq> s"
  shows "s homeomorphic (cball (0::'a) 1)"
proof (rule starlike_compact_projective[OF assms(2-3)], clarify)
  fix x u assume "x \<in> s" and "0 \<le> u" and "u < (1::real)"
  have "open (ball (u *\<^sub>R x) (1 - u))" by (rule open_ball)
  moreover have "u *\<^sub>R x \<in> ball (u *\<^sub>R x) (1 - u)"
    unfolding centre_in_ball using `u < 1` by simp
  moreover have "ball (u *\<^sub>R x) (1 - u) \<subseteq> s"
  proof
    fix y assume "y \<in> ball (u *\<^sub>R x) (1 - u)"
    hence "dist (u *\<^sub>R x) y < 1 - u" unfolding mem_ball .
    with `u < 1` have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> cball 0 1"
      by (simp add: dist_norm inverse_eq_divide norm_minus_commute)
    with assms(3) have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> s" ..
    with assms(1) have "(1 - u) *\<^sub>R ((y - u *\<^sub>R x) /\<^sub>R (1 - u)) + u *\<^sub>R x \<in> s"
      using `x \<in> s` `0 \<le> u` `u < 1` [THEN less_imp_le] by (rule mem_convex)
    thus "y \<in> s" using `u < 1` by simp
  qed
  ultimately have "u *\<^sub>R x \<in> interior s" ..
  thus "u *\<^sub>R x \<in> s - frontier s" using frontier_def and interior_subset by auto qed

lemma homeomorphic_convex_compact_cball: fixes e::real and s::"('a::euclidean_space) set"
  assumes "convex s" "compact s" "interior s \<noteq> {}" "0 < e"
  shows "s homeomorphic (cball (b::'a) e)"
proof- obtain a where "a\<in>interior s" using assms(3) by auto
  then obtain d where "d>0" and d:"cball a d \<subseteq> s" unfolding mem_interior_cball by auto
  let ?d = "inverse d" and ?n = "0::'a"
  have "cball ?n 1 \<subseteq> (\<lambda>x. inverse d *\<^sub>R (x - a)) ` s"
    apply(rule, rule_tac x="d *\<^sub>R x + a" in image_eqI) defer
    apply(rule d[unfolded subset_eq, rule_format]) using `d>0` unfolding mem_cball dist_norm
    by(auto simp add: mult_right_le_one_le)
  hence "(\<lambda>x. inverse d *\<^sub>R (x - a)) ` s homeomorphic cball ?n 1"
    using homeomorphic_convex_compact_lemma[of "(\<lambda>x. ?d *\<^sub>R -a + ?d *\<^sub>R x) ` s", OF convex_affinity compact_affinity]
    using assms(1,2) by(auto simp add: uminus_add_conv_diff scaleR_right_diff_distrib)
  thus ?thesis apply(rule_tac homeomorphic_trans[OF _ homeomorphic_balls(2)[of 1 _ ?n]])
    apply(rule homeomorphic_trans[OF homeomorphic_affinity[of "?d" s "?d *\<^sub>R -a"]])
    using `d>0` `e>0` by(auto simp add: uminus_add_conv_diff scaleR_right_diff_distrib) qed

lemma homeomorphic_convex_compact: fixes s::"('a::euclidean_space) set" and t::"('a) set"
  assumes "convex s" "compact s" "interior s \<noteq> {}"
          "convex t" "compact t" "interior t \<noteq> {}"
  shows "s homeomorphic t"
  using assms by(meson zero_less_one homeomorphic_trans homeomorphic_convex_compact_cball homeomorphic_sym)

subsection {* Epigraphs of convex functions *}

definition "epigraph s (f::_ \<Rightarrow> real) = {xy. fst xy \<in> s \<and> f (fst xy) \<le> snd xy}"

lemma mem_epigraph: "(x, y) \<in> epigraph s f \<longleftrightarrow> x \<in> s \<and> f x \<le> y" unfolding epigraph_def by auto

(** This might break sooner or later. In fact it did already once. **)
lemma convex_epigraph:
  "convex(epigraph s f) \<longleftrightarrow> convex_on s f \<and> convex s"
  unfolding convex_def convex_on_def
  unfolding Ball_def split_paired_All epigraph_def
  unfolding mem_Collect_eq fst_conv snd_conv fst_add snd_add fst_scaleR snd_scaleR Ball_def[symmetric]
  apply safe defer apply(erule_tac x=x in allE,erule_tac x="f x" in allE) apply safe
  apply(erule_tac x=xa in allE,erule_tac x="f xa" in allE) prefer 3
  apply(rule_tac y="u * f a + v * f aa" in order_trans) defer by(auto intro!:mult_left_mono add_mono)

lemma convex_epigraphI:
  "convex_on s f \<Longrightarrow> convex s \<Longrightarrow> convex(epigraph s f)"
unfolding convex_epigraph by auto

lemma convex_epigraph_convex:
  "convex s \<Longrightarrow> convex_on s f \<longleftrightarrow> convex(epigraph s f)"
by(simp add: convex_epigraph)

subsubsection {* Use this to derive general bound property of convex function *}

lemma convex_on:
  assumes "convex s"
  shows "convex_on s f \<longleftrightarrow> (\<forall>k u x. (\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1 \<longrightarrow>
   f (setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} ) \<le> setsum (\<lambda>i. u i * f(x i)) {1..k} ) "
  unfolding convex_epigraph_convex[OF assms] convex epigraph_def Ball_def mem_Collect_eq
  unfolding fst_setsum snd_setsum fst_scaleR snd_scaleR
  apply safe
  apply (drule_tac x=k in spec)
  apply (drule_tac x=u in spec)
  apply (drule_tac x="\<lambda>i. (x i, f (x i))" in spec)
  apply simp
  using assms[unfolded convex] apply simp
  apply(rule_tac y="\<Sum>i = 1..k. u i * f (fst (x i))" in order_trans)
  defer apply(rule setsum_mono) apply(erule_tac x=i in allE) unfolding real_scaleR_def
  apply(rule mult_left_mono)using assms[unfolded convex] by auto


subsection {* Convexity of general and special intervals *}

lemma convexI: (* TODO: move to Library/Convex.thy *)
  assumes "\<And>x y u v. \<lbrakk>x \<in> s; y \<in> s; 0 \<le> u; 0 \<le> v; u + v = 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
  shows "convex s"
using assms unfolding convex_def by fast

lemma is_interval_convex:
  fixes s :: "('a::euclidean_space) set"
  assumes "is_interval s" shows "convex s"
proof (rule convexI)
  fix x y u v assume as:"x \<in> s" "y \<in> s" "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  hence *:"u = 1 - v" "1 - v \<ge> 0" and **:"v = 1 - u" "1 - u \<ge> 0" by auto
  { fix a b assume "\<not> b \<le> u * a + v * b"
    hence "u * a < (1 - v) * b" unfolding not_le using as(4) by(auto simp add: field_simps)
    hence "a < b" unfolding * using as(4) *(2) apply(rule_tac mult_left_less_imp_less[of "1 - v"]) by(auto simp add: field_simps)
    hence "a \<le> u * a + v * b" unfolding * using as(4) by (auto simp add: field_simps intro!:mult_right_mono)
  } moreover
  { fix a b assume "\<not> u * a + v * b \<le> a"
    hence "v * b > (1 - u) * a" unfolding not_le using as(4) by(auto simp add: field_simps)
    hence "a < b" unfolding * using as(4) apply(rule_tac mult_left_less_imp_less) by(auto simp add: field_simps)
    hence "u * a + v * b \<le> b" unfolding ** using **(2) as(3) by(auto simp add: field_simps intro!:mult_right_mono) }
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> s" apply- apply(rule assms[unfolded is_interval_def, rule_format, OF as(1,2)])
    using as(3-) DIM_positive[where 'a='a] by (auto simp: inner_simps)
qed

lemma is_interval_connected:
  fixes s :: "('a::euclidean_space) set"
  shows "is_interval s \<Longrightarrow> connected s"
  using is_interval_convex convex_connected by auto

lemma convex_interval: "convex {a .. b}" "convex {a<..<b::'a::ordered_euclidean_space}"
  apply(rule_tac[!] is_interval_convex) using is_interval_interval by auto

(* FIXME: rewrite these lemmas without using vec1
subsection {* On @{text "real^1"}, @{text "is_interval"}, @{text "convex"} and @{text "connected"} are all equivalent. *}

lemma is_interval_1:
  "is_interval s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b \<longrightarrow> x \<in> s)"
  unfolding is_interval_def forall_1 by auto

lemma is_interval_connected_1: "is_interval s \<longleftrightarrow> connected (s::(real^1) set)"
  apply(rule, rule is_interval_connected, assumption) unfolding is_interval_1
  apply(rule,rule,rule,rule,erule conjE,rule ccontr) proof-
  fix a b x assume as:"connected s" "a \<in> s" "b \<in> s" "dest_vec1 a \<le> dest_vec1 x" "dest_vec1 x \<le> dest_vec1 b" "x\<notin>s"
  hence *:"dest_vec1 a < dest_vec1 x" "dest_vec1 x < dest_vec1 b" apply(rule_tac [!] ccontr) unfolding not_less by auto
  let ?halfl = "{z. inner (basis 1) z < dest_vec1 x} " and ?halfr = "{z. inner (basis 1) z > dest_vec1 x} "
  { fix y assume "y \<in> s" have "y \<in> ?halfr \<union> ?halfl" apply(rule ccontr)
    using as(6) `y\<in>s` by (auto simp add: inner_vector_def) }
  moreover have "a\<in>?halfl" "b\<in>?halfr" using * by (auto simp add: inner_vector_def)
  hence "?halfl \<inter> s \<noteq> {}" "?halfr \<inter> s \<noteq> {}"  using as(2-3) by auto
  ultimately show False apply(rule_tac notE[OF as(1)[unfolded connected_def]])
    apply(rule_tac x="?halfl" in exI, rule_tac x="?halfr" in exI)
    apply(rule, rule open_halfspace_lt, rule, rule open_halfspace_gt)
    by(auto simp add: field_simps) qed

lemma is_interval_convex_1:
  "is_interval s \<longleftrightarrow> convex (s::(real^1) set)"
by(metis is_interval_convex convex_connected is_interval_connected_1)

lemma convex_connected_1:
  "connected s \<longleftrightarrow> convex (s::(real^1) set)"
by(metis is_interval_convex convex_connected is_interval_connected_1)
*)
subsection {* Another intermediate value theorem formulation *}

lemma ivt_increasing_component_on_1: fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b" "continuous_on {a .. b} f" "(f a)\<bullet>k \<le> y" "y \<le> (f b)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
proof- have "f a \<in> f ` {a..b}" "f b \<in> f ` {a..b}" apply(rule_tac[!] imageI)
    using assms(1) by auto
  thus ?thesis using connected_ivt_component[of "f ` {a..b}" "f a" "f b" k y]
    using connected_continuous_image[OF assms(2) convex_connected[OF convex_real_interval(5)]]
    using assms by(auto intro!: imageI) qed

lemma ivt_increasing_component_1: fixes f::"real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a .. b}. continuous (at x) f
   \<Longrightarrow> f a\<bullet>k \<le> y \<Longrightarrow> y \<le> f b\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
by(rule ivt_increasing_component_on_1)
  (auto simp add: continuous_at_imp_continuous_on)

lemma ivt_decreasing_component_on_1: fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b" "continuous_on {a .. b} f" "(f b)\<bullet>k \<le> y" "y \<le> (f a)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  apply(subst neg_equal_iff_equal[symmetric])
  using ivt_increasing_component_on_1[of a b "\<lambda>x. - f x" k "- y"]
  using assms using continuous_on_minus by auto

lemma ivt_decreasing_component_1: fixes f::"real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a .. b}. continuous (at x) f
    \<Longrightarrow> f b\<bullet>k \<le> y \<Longrightarrow> y \<le> f a\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
by(rule ivt_decreasing_component_on_1)
  (auto simp: continuous_at_imp_continuous_on)

subsection {* A bound within a convex hull, and so an interval *}

lemma convex_on_convex_hull_bound:
  assumes "convex_on (convex hull s) f" "\<forall>x\<in>s. f x \<le> b"
  shows "\<forall>x\<in> convex hull s. f x \<le> b" proof
  fix x assume "x\<in>convex hull s"
  then obtain k u v where obt:"\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> v i \<in> s" "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R v i) = x"
    unfolding convex_hull_indexed mem_Collect_eq by auto
  have "(\<Sum>i = 1..k. u i * f (v i)) \<le> b" using setsum_mono[of "{1..k}" "\<lambda>i. u i * f (v i)" "\<lambda>i. u i * b"]
    unfolding setsum_left_distrib[symmetric] obt(2) mult_1 apply(drule_tac meta_mp) apply(rule mult_left_mono)
    using assms(2) obt(1) by auto
  thus "f x \<le> b" using assms(1)[unfolded convex_on[OF convex_convex_hull], rule_format, of k u v]
    unfolding obt(2-3) using obt(1) and hull_subset[unfolded subset_eq, rule_format, of _ s] by auto qed

lemma inner_setsum_Basis[simp]: "\<And>i. i \<in> Basis \<Longrightarrow> (\<Sum>Basis) \<bullet> i = 1"
  by (simp add: One_def inner_setsum_left setsum_cases inner_Basis)

lemma unit_interval_convex_hull:
  defines "One \<equiv> (\<Sum>Basis)"
  shows "{0::'a::ordered_euclidean_space .. One} =
    convex hull {x. \<forall>i\<in>Basis. (x\<bullet>i = 0) \<or> (x\<bullet>i = 1)}"
  (is "?int = convex hull ?points")
proof -
  have One[simp]: "\<And>i. i \<in> Basis \<Longrightarrow> One \<bullet> i = 1"
    by (simp add: One_def inner_setsum_left setsum_cases inner_Basis)
  have 01:"{0,One} \<subseteq> convex hull ?points" 
    apply rule apply(rule_tac hull_subset[unfolded subset_eq, rule_format]) by auto
  { fix n x assume "x\<in>{0::'a::ordered_euclidean_space .. One}" "n \<le> DIM('a)" "card {i. i\<in>Basis \<and> x\<bullet>i \<noteq> 0} \<le> n"
  hence "x\<in>convex hull ?points" proof(induct n arbitrary: x)
    case 0 hence "x = 0" apply(subst euclidean_eq_iff) apply rule by auto
    thus "x\<in>convex hull ?points" using 01 by auto
  next
    case (Suc n) show "x\<in>convex hull ?points" proof(cases "{i. i\<in>Basis \<and> x\<bullet>i \<noteq> 0} = {}")
      case True hence "x = 0" apply(subst euclidean_eq_iff) by auto
      thus "x\<in>convex hull ?points" using 01 by auto
    next
      case False def xi \<equiv> "Min ((\<lambda>i. x\<bullet>i) ` {i. i\<in>Basis \<and> x\<bullet>i \<noteq> 0})"
      have "xi \<in> (\<lambda>i. x\<bullet>i) ` {i. i\<in>Basis \<and> x\<bullet>i \<noteq> 0}" unfolding xi_def apply(rule Min_in) using False by auto
      then obtain i where i':"x\<bullet>i = xi" "x\<bullet>i \<noteq> 0" "i\<in>Basis" by auto
      have i:"\<And>j. j\<in>Basis \<Longrightarrow> x\<bullet>j > 0 \<Longrightarrow> x\<bullet>i \<le> x\<bullet>j"
        unfolding i'(1) xi_def apply(rule_tac Min_le) unfolding image_iff
        defer apply(rule_tac x=j in bexI) using i' by auto
      have i01:"x\<bullet>i \<le> 1" "x\<bullet>i > 0" using Suc(2)[unfolded mem_interval,rule_format,of i]
        using i'(2-) `x\<bullet>i \<noteq> 0` by auto
      show ?thesis proof(cases "x\<bullet>i=1")
        case True have "\<forall>j\<in>{i. i\<in>Basis \<and> x\<bullet>i \<noteq> 0}. x\<bullet>j = 1" apply(rule, rule ccontr) unfolding mem_Collect_eq
        proof(erule conjE) fix j assume as:"x \<bullet> j \<noteq> 0" "x \<bullet> j \<noteq> 1" "j\<in>Basis"
          hence j:"x\<bullet>j \<in> {0<..<1}" using Suc(2)
            by (auto simp add: eucl_le[where 'a='a] elim!:allE[where x=j])
          hence "x\<bullet>j \<in> op \<bullet> x ` {i. i\<in>Basis \<and> x \<bullet> i \<noteq> 0}" using as(3) by auto
          hence "x\<bullet>j \<ge> x\<bullet>i" unfolding i'(1) xi_def apply(rule_tac Min_le) by auto
          thus False using True Suc(2) j by(auto simp add: elim!:ballE[where x=j]) qed
        thus "x\<in>convex hull ?points" apply(rule_tac hull_subset[unfolded subset_eq, rule_format])
          by auto
      next
        let ?y = "\<Sum>j\<in>Basis. (if x\<bullet>j = 0 then 0 else (x\<bullet>j - x\<bullet>i) / (1 - x\<bullet>i)) *\<^sub>R j"
        case False
        then have *: "x = (x\<bullet>i) *\<^sub>R (\<Sum>j\<in>Basis. (if x\<bullet>j = 0 then 0 else 1) *\<^sub>R j) + (1 - x\<bullet>i) *\<^sub>R ?y"
          by (subst euclidean_eq_iff) (simp add: inner_simps)
        { fix j :: 'a assume j:"j\<in>Basis"
          have "x\<bullet>j \<noteq> 0 \<Longrightarrow> 0 \<le> (x \<bullet> j - x \<bullet> i) / (1 - x \<bullet> i)" "(x \<bullet> j - x \<bullet> i) / (1 - x \<bullet> i) \<le> 1"
            apply(rule_tac divide_nonneg_pos) using i(1)[of j] using False i01
            using Suc(2)[unfolded mem_interval, rule_format, of j] using j
            by(auto simp add: field_simps)
          with j have "0 \<le> ?y \<bullet> j \<and> ?y \<bullet> j \<le> 1" by (auto simp: inner_simps) }
        moreover have "i\<in>{j. j\<in>Basis \<and> x\<bullet>j \<noteq> 0} - {j. j\<in>Basis \<and> ?y \<bullet> j \<noteq> 0}"
          using i01 using i'(3) by auto
        hence "{j. j\<in>Basis \<and> x\<bullet>j \<noteq> 0} \<noteq> {j. j\<in>Basis \<and> ?y \<bullet> j \<noteq> 0}" using i'(3) by blast
        hence **:"{j. j\<in>Basis \<and> ?y \<bullet> j \<noteq> 0} \<subset> {j. j\<in>Basis \<and> x\<bullet>j \<noteq> 0}"
          by auto
        have "card {j. j\<in>Basis \<and> ?y \<bullet> j \<noteq> 0} \<le> n"
          using less_le_trans[OF psubset_card_mono[OF _ **] Suc(4)] by auto
        ultimately show ?thesis
          apply(subst *)
          apply(rule convex_convex_hull[unfolded convex_def, rule_format])
          apply(rule_tac hull_subset[unfolded subset_eq, rule_format]) 
          defer 
          apply(rule Suc(1))
          unfolding mem_interval 
          using i01 Suc(3)
          by auto
      qed
    qed
  qed } note * = this
  show ?thesis 
    apply rule defer apply(rule hull_minimal) unfolding subset_eq prefer 3 apply rule
    apply(rule_tac n2="DIM('a)" in *) prefer 3
    apply(rule card_mono) using 01 and convex_interval(1) prefer 5 apply - apply rule
    unfolding mem_interval apply rule unfolding mem_Collect_eq apply(erule_tac x=i in ballE)
    by auto
qed

text {* And this is a finite set of vertices. *}

lemma unit_cube_convex_hull:
  obtains s :: "'a::ordered_euclidean_space set" where "finite s" "{0 .. \<Sum>Basis} = convex hull s"
  apply(rule that[of "{x::'a. \<forall>i\<in>Basis. x\<bullet>i=0 \<or> x\<bullet>i=1}"])
  apply(rule finite_subset[of _ "(\<lambda>s. (\<Sum>i\<in>Basis. (if i\<in>s then 1 else 0) *\<^sub>R i)::'a) ` Pow Basis"])
  prefer 3 apply(rule unit_interval_convex_hull) apply rule unfolding mem_Collect_eq proof-
  fix x::"'a" assume as:"\<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1"
  show "x \<in> (\<lambda>s. \<Sum>i\<in>Basis. (if i\<in>s then 1 else 0) *\<^sub>R i) ` Pow Basis"
    apply(rule image_eqI[where x="{i. i\<in>Basis \<and> x\<bullet>i = 1}"])
    using as apply(subst euclidean_eq_iff) by (auto simp: inner_setsum_left_Basis)
qed auto

text {* Hence any cube (could do any nonempty interval). *}

lemma cube_convex_hull:
  assumes "0 < d" obtains s::"('a::ordered_euclidean_space) set" where
  "finite s" "{x - (\<Sum>i\<in>Basis. d*\<^sub>Ri) .. x + (\<Sum>i\<in>Basis. d*\<^sub>Ri)} = convex hull s" proof-
  let ?d = "(\<Sum>i\<in>Basis. d*\<^sub>Ri)::'a"
  have *:"{x - ?d .. x + ?d} = (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` {0 .. \<Sum>Basis}" apply(rule set_eqI, rule)
    unfolding image_iff defer apply(erule bexE) proof-
    fix y assume as:"y\<in>{x - ?d .. x + ?d}"
    { fix i :: 'a assume i:"i\<in>Basis" have "x \<bullet> i \<le> d + y \<bullet> i" "y \<bullet> i \<le> d + x \<bullet> i"
        using as[unfolded mem_interval, THEN bspec[where x=i]] i
        by (auto simp: inner_simps)
      hence "1 \<ge> inverse d * (x \<bullet> i - y \<bullet> i)" "1 \<ge> inverse d * (y \<bullet> i - x \<bullet> i)"
        apply(rule_tac[!] mult_left_le_imp_le[OF _ assms]) unfolding mult_assoc[symmetric]
        using assms by(auto simp add: field_simps)
      hence "inverse d * (x \<bullet> i * 2) \<le> 2 + inverse d * (y \<bullet> i * 2)"
            "inverse d * (y \<bullet> i * 2) \<le> 2 + inverse d * (x \<bullet> i * 2)" by(auto simp add:field_simps) }
    hence "inverse (2 * d) *\<^sub>R (y - (x - ?d)) \<in> {0..\<Sum>Basis}" unfolding mem_interval using assms
      by(auto simp add: field_simps inner_simps)
    thus "\<exists>z\<in>{0..\<Sum>Basis}. y = x - ?d + (2 * d) *\<^sub>R z" apply- apply(rule_tac x="inverse (2 * d) *\<^sub>R (y - (x - ?d))" in bexI)
      using assms by auto
  next
    fix y z assume as:"z\<in>{0..\<Sum>Basis}" "y = x - ?d + (2*d) *\<^sub>R z"
    have "\<And>i. i\<in>Basis \<Longrightarrow> 0 \<le> d * (z \<bullet> i) \<and> d * (z \<bullet> i) \<le> d"
      using assms as(1)[unfolded mem_interval] apply(erule_tac x=i in ballE)
      apply rule apply(rule mult_nonneg_nonneg) prefer 3 apply(rule mult_right_le_one_le)
      using assms by auto
    thus "y \<in> {x - ?d..x + ?d}" unfolding as(2) mem_interval apply- apply rule using as(1)[unfolded mem_interval]
      apply(erule_tac x=i in ballE) using assms by (auto simp: inner_simps) qed
  obtain s where "finite s" "{0::'a..\<Sum>Basis} = convex hull s" using unit_cube_convex_hull by auto
  thus ?thesis apply(rule_tac that[of "(\<lambda>y. x - ?d + (2 * d) *\<^sub>R y)` s"]) unfolding * and convex_hull_affinity by auto qed

subsection {* Bounded convex function on open set is continuous *}

lemma convex_on_bounded_continuous:
  fixes s :: "('a::real_normed_vector) set"
  assumes "open s" "convex_on s f" "\<forall>x\<in>s. abs(f x) \<le> b"
  shows "continuous_on s f"
  apply(rule continuous_at_imp_continuous_on) unfolding continuous_at_real_range proof(rule,rule,rule)
  fix x e assume "x\<in>s" "(0::real) < e"
  def B \<equiv> "abs b + 1"
  have B:"0 < B" "\<And>x. x\<in>s \<Longrightarrow> abs (f x) \<le> B"
    unfolding B_def defer apply(drule assms(3)[rule_format]) by auto
  obtain k where "k>0"and k:"cball x k \<subseteq> s" using assms(1)[unfolded open_contains_cball, THEN bspec[where x=x]] using `x\<in>s` by auto
  show "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e"
    apply(rule_tac x="min (k / 2) (e / (2 * B) * k)" in exI) apply rule defer proof(rule,rule)
    fix y assume as:"norm (y - x) < min (k / 2) (e / (2 * B) * k)"
    show "\<bar>f y - f x\<bar> < e" proof(cases "y=x")
      case False def t \<equiv> "k / norm (y - x)"
      have "2 < t" "0<t" unfolding t_def using as False and `k>0` by(auto simp add:field_simps)
      have "y\<in>s" apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm
        apply(rule order_trans[of _ "2 * norm (x - y)"]) using as by(auto simp add: field_simps norm_minus_commute)
      { def w \<equiv> "x + t *\<^sub>R (y - x)"
        have "w\<in>s" unfolding w_def apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm
          unfolding t_def using `k>0` by auto
        have "(1 / t) *\<^sub>R x + - x + ((t - 1) / t) *\<^sub>R x = (1 / t - 1 + (t - 1) / t) *\<^sub>R x" by (auto simp add: algebra_simps)
        also have "\<dots> = 0"  using `t>0` by(auto simp add:field_simps)
        finally have w:"(1 / t) *\<^sub>R w + ((t - 1) / t) *\<^sub>R x = y" unfolding w_def using False and `t>0` by (auto simp add: algebra_simps)
        have  "2 * B < e * t" unfolding t_def using `0<e` `0<k` `B>0` and as and False by (auto simp add:field_simps)
        hence "(f w - f x) / t < e"
          using B(2)[OF `w\<in>s`] and B(2)[OF `x\<in>s`] using `t>0` by(auto simp add:field_simps)
        hence th1:"f y - f x < e" apply- apply(rule le_less_trans) defer apply assumption
          using assms(2)[unfolded convex_on_def,rule_format,of w x "1/t" "(t - 1)/t", unfolded w]
          using `0<t` `2<t` and `x\<in>s` `w\<in>s` by(auto simp add:field_simps) }
      moreover
      { def w \<equiv> "x - t *\<^sub>R (y - x)"
        have "w\<in>s" unfolding w_def apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm
          unfolding t_def using `k>0` by auto
        have "(1 / (1 + t)) *\<^sub>R x + (t / (1 + t)) *\<^sub>R x = (1 / (1 + t) + t / (1 + t)) *\<^sub>R x" by (auto simp add: algebra_simps)
        also have "\<dots>=x" using `t>0` by (auto simp add:field_simps)
        finally have w:"(1 / (1+t)) *\<^sub>R w + (t / (1 + t)) *\<^sub>R y = x" unfolding w_def using False and `t>0` by (auto simp add: algebra_simps)
        have  "2 * B < e * t" unfolding t_def using `0<e` `0<k` `B>0` and as and False by (auto simp add:field_simps)
        hence *:"(f w - f y) / t < e" using B(2)[OF `w\<in>s`] and B(2)[OF `y\<in>s`] using `t>0` by(auto simp add:field_simps)
        have "f x \<le> 1 / (1 + t) * f w + (t / (1 + t)) * f y"
          using assms(2)[unfolded convex_on_def,rule_format,of w y "1/(1+t)" "t / (1+t)",unfolded w]
          using `0<t` `2<t` and `y\<in>s` `w\<in>s` by (auto simp add:field_simps)
        also have "\<dots> = (f w + t * f y) / (1 + t)" using `t>0` unfolding divide_inverse by (auto simp add:field_simps)
        also have "\<dots> < e + f y" using `t>0` * `e>0` by(auto simp add:field_simps)
        finally have "f x - f y < e" by auto }
      ultimately show ?thesis by auto
    qed(insert `0<e`, auto)
  qed(insert `0<e` `0<k` `0<B`, auto simp add:field_simps intro!:mult_pos_pos) qed

subsection {* Upper bound on a ball implies upper and lower bounds *}

lemma convex_bounds_lemma:
  fixes x :: "'a::real_normed_vector"
  assumes "convex_on (cball x e) f"  "\<forall>y \<in> cball x e. f y \<le> b"
  shows "\<forall>y \<in> cball x e. abs(f y) \<le> b + 2 * abs(f x)"
  apply(rule) proof(cases "0 \<le> e") case True
  fix y assume y:"y\<in>cball x e" def z \<equiv> "2 *\<^sub>R x - y"
  have *:"x - (2 *\<^sub>R x - y) = y - x" by (simp add: scaleR_2)
  have z:"z\<in>cball x e" using y unfolding z_def mem_cball dist_norm * by(auto simp add: norm_minus_commute)
  have "(1 / 2) *\<^sub>R y + (1 / 2) *\<^sub>R z = x" unfolding z_def by (auto simp add: algebra_simps)
  thus "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>" using assms(1)[unfolded convex_on_def,rule_format, OF y z, of "1/2" "1/2"]
    using assms(2)[rule_format,OF y] assms(2)[rule_format,OF z] by(auto simp add:field_simps)
next case False fix y assume "y\<in>cball x e"
  hence "dist x y < 0" using False unfolding mem_cball not_le by (auto simp del: dist_not_less_zero)
  thus "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>" using zero_le_dist[of x y] by auto qed

subsubsection {* Hence a convex function on an open set is continuous *}

lemma real_of_nat_ge_one_iff: "1 \<le> real (n::nat) \<longleftrightarrow> 1 \<le> n"
  by auto

lemma convex_on_continuous:
  assumes "open (s::('a::ordered_euclidean_space) set)" "convex_on s f"
  (* FIXME: generalize to euclidean_space *)
  shows "continuous_on s f"
  unfolding continuous_on_eq_continuous_at[OF assms(1)] proof
  note dimge1 = DIM_positive[where 'a='a]
  fix x assume "x\<in>s"
  then obtain e where e:"cball x e \<subseteq> s" "e>0" using assms(1) unfolding open_contains_cball by auto
  def d \<equiv> "e / real DIM('a)"
  have "0 < d" unfolding d_def using `e>0` dimge1 by(rule_tac divide_pos_pos, auto)
  let ?d = "(\<Sum>i\<in>Basis. d *\<^sub>R i)::'a"
  obtain c where c:"finite c" "{x - ?d..x + ?d} = convex hull c" using cube_convex_hull[OF `d>0`, of x] by auto
  have "x\<in>{x - ?d..x + ?d}" using `d>0` unfolding mem_interval by (auto simp: inner_setsum_left_Basis inner_simps)
  hence "c\<noteq>{}" using c by auto
  def k \<equiv> "Max (f ` c)"
  have "convex_on {x - ?d..x + ?d} f"
    apply(rule convex_on_subset[OF assms(2)])
    apply(rule subset_trans[OF _ e(1)])
    unfolding subset_eq mem_cball
  proof
    fix z assume z:"z\<in>{x - ?d..x + ?d}"
    have e:"e = setsum (\<lambda>i::'a. d) Basis" unfolding setsum_constant d_def using dimge1
      unfolding real_eq_of_nat by auto
    show "dist x z \<le> e" unfolding dist_norm e apply(rule_tac order_trans[OF norm_le_l1], rule setsum_mono)
      using z[unfolded mem_interval] apply(erule_tac x=b in ballE) by (auto simp: inner_simps)
  qed
  hence k:"\<forall>y\<in>{x - ?d..x + ?d}. f y \<le> k" unfolding c(2) apply(rule_tac convex_on_convex_hull_bound) apply assumption
    unfolding k_def apply(rule, rule Max_ge) using c(1) by auto
  have "d \<le> e"
    unfolding d_def
    apply(rule mult_imp_div_pos_le)
    using `e>0`
    unfolding mult_le_cancel_left1
    apply (auto simp: real_of_nat_ge_one_iff Suc_le_eq DIM_positive)
    done
  hence dsube:"cball x d \<subseteq> cball x e" unfolding subset_eq Ball_def mem_cball by auto
  have conv:"convex_on (cball x d) f" apply(rule convex_on_subset, rule convex_on_subset[OF assms(2)]) apply(rule e(1)) using dsube by auto
  hence "\<forall>y\<in>cball x d. abs (f y) \<le> k + 2 * abs (f x)" apply(rule_tac convex_bounds_lemma) apply assumption proof
    fix y assume y:"y\<in>cball x d"
    { fix i :: 'a assume "i\<in>Basis" hence "x \<bullet> i - d \<le> y \<bullet> i"  "y \<bullet> i \<le> x \<bullet> i + d"
        using order_trans[OF Basis_le_norm y[unfolded mem_cball dist_norm], of i] by (auto simp: inner_diff_left)  }
    thus "f y \<le> k" apply(rule_tac k[rule_format]) unfolding mem_cball mem_interval dist_norm
      by (auto simp: inner_simps)
  qed
  hence "continuous_on (ball x d) f" apply(rule_tac convex_on_bounded_continuous)
    apply(rule open_ball, rule convex_on_subset[OF conv], rule ball_subset_cball)
    apply force
    done
  thus "continuous (at x) f" unfolding continuous_on_eq_continuous_at[OF open_ball]
    using `d>0` by auto
qed

subsection {* Line segments, Starlike Sets, etc. *}

(* Use the same overloading tricks as for intervals, so that
   segment[a,b] is closed and segment(a,b) is open relative to affine hull. *)

definition
  midpoint :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a" where
  "midpoint a b = (inverse (2::real)) *\<^sub>R (a + b)"

definition
  open_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real.  0 < u \<and> u < 1}"

definition
  closed_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "closed_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real. 0 \<le> u \<and> u \<le> 1}"

definition "between = (\<lambda> (a,b) x. x \<in> closed_segment a b)"

lemmas segment = open_segment_def closed_segment_def

definition "starlike s \<longleftrightarrow> (\<exists>a\<in>s. \<forall>x\<in>s. closed_segment a x \<subseteq> s)"

lemma midpoint_refl: "midpoint x x = x"
  unfolding midpoint_def unfolding scaleR_right_distrib unfolding scaleR_left_distrib[symmetric] by auto

lemma midpoint_sym: "midpoint a b = midpoint b a" unfolding midpoint_def by (auto simp add: scaleR_right_distrib)

lemma midpoint_eq_iff: "midpoint a b = c \<longleftrightarrow> a + b = c + c"
proof -
  have "midpoint a b = c \<longleftrightarrow> scaleR 2 (midpoint a b) = scaleR 2 c"
    by simp
  thus ?thesis
    unfolding midpoint_def scaleR_2 [symmetric] by simp
qed

lemma dist_midpoint:
  fixes a b :: "'a::real_normed_vector" shows
  "dist a (midpoint a b) = (dist a b) / 2" (is ?t1)
  "dist b (midpoint a b) = (dist a b) / 2" (is ?t2)
  "dist (midpoint a b) a = (dist a b) / 2" (is ?t3)
  "dist (midpoint a b) b = (dist a b) / 2" (is ?t4)
proof-
  have *: "\<And>x y::'a. 2 *\<^sub>R x = - y \<Longrightarrow> norm x = (norm y) / 2" unfolding equation_minus_iff by auto
  have **:"\<And>x y::'a. 2 *\<^sub>R x =   y \<Longrightarrow> norm x = (norm y) / 2" by auto
  note scaleR_right_distrib [simp]
  show ?t1 unfolding midpoint_def dist_norm apply (rule **)
    by (simp add: scaleR_right_diff_distrib, simp add: scaleR_2)
  show ?t2 unfolding midpoint_def dist_norm apply (rule *)
    by (simp add: scaleR_right_diff_distrib, simp add: scaleR_2)
  show ?t3 unfolding midpoint_def dist_norm apply (rule *)
    by (simp add: scaleR_right_diff_distrib, simp add: scaleR_2)
  show ?t4 unfolding midpoint_def dist_norm apply (rule **)
    by (simp add: scaleR_right_diff_distrib, simp add: scaleR_2)
qed

lemma midpoint_eq_endpoint:
  "midpoint a b = a \<longleftrightarrow> a = b"
  "midpoint a b = b \<longleftrightarrow> a = b"
  unfolding midpoint_eq_iff by auto

lemma convex_contains_segment:
  "convex s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. closed_segment a b \<subseteq> s)"
  unfolding convex_alt closed_segment_def by auto

lemma convex_imp_starlike:
  "convex s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> starlike s"
  unfolding convex_contains_segment starlike_def by auto

lemma segment_convex_hull:
 "closed_segment a b = convex hull {a,b}" proof-
  have *:"\<And>x. {x} \<noteq> {}" by auto
  have **:"\<And>u v. u + v = 1 \<longleftrightarrow> u = 1 - (v::real)" by auto
  show ?thesis unfolding segment convex_hull_insert[OF *] convex_hull_singleton apply(rule set_eqI)
    unfolding mem_Collect_eq apply(rule,erule exE)
    apply(rule_tac x="1 - u" in exI) apply rule defer apply(rule_tac x=u in exI) defer
    apply(erule exE, (erule conjE)?)+ apply(rule_tac x="1 - u" in exI) unfolding ** by auto qed

lemma convex_segment: "convex (closed_segment a b)"
  unfolding segment_convex_hull by(rule convex_convex_hull)

lemma ends_in_segment: "a \<in> closed_segment a b" "b \<in> closed_segment a b"
  unfolding segment_convex_hull apply(rule_tac[!] hull_subset[unfolded subset_eq, rule_format]) by auto

lemma segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> closed_segment a b" shows "norm(y - x) \<le> norm(y - a) \<or>  norm(y - x) \<le> norm(y - b)" proof-
  obtain z where "z\<in>{a, b}" "norm (x - y) \<le> norm (z - y)" using simplex_furthest_le[of "{a, b}" y]
    using assms[unfolded segment_convex_hull] by auto
  thus ?thesis by(auto simp add:norm_minus_commute) qed

lemma segment_bound:
  fixes x a b :: "'a::euclidean_space"
  assumes "x \<in> closed_segment a b"
  shows "norm(x - a) \<le> norm(b - a)" "norm(x - b) \<le> norm(b - a)"
  using segment_furthest_le[OF assms, of a]
  using segment_furthest_le[OF assms, of b]
  by (auto simp add:norm_minus_commute)

lemma segment_refl:"closed_segment a a = {a}" unfolding segment by (auto simp add: algebra_simps)

lemma between_mem_segment: "between (a,b) x \<longleftrightarrow> x \<in> closed_segment a b"
  unfolding between_def by auto

lemma between:"between (a,b) (x::'a::euclidean_space) \<longleftrightarrow> dist a b = (dist a x) + (dist x b)"
proof(cases "a = b")
  case True thus ?thesis unfolding between_def split_conv
    by(auto simp add:segment_refl dist_commute) next
  case False hence Fal:"norm (a - b) \<noteq> 0" and Fal2: "norm (a - b) > 0" by auto
  have *:"\<And>u. a - ((1 - u) *\<^sub>R a + u *\<^sub>R b) = u *\<^sub>R (a - b)" by (auto simp add: algebra_simps)
  show ?thesis unfolding between_def split_conv closed_segment_def mem_Collect_eq
    apply rule apply(erule exE, (erule conjE)+) apply(subst dist_triangle_eq) proof-
      fix u assume as:"x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
      hence *:"a - x = u *\<^sub>R (a - b)" "x - b = (1 - u) *\<^sub>R (a - b)"
        unfolding as(1) by(auto simp add:algebra_simps)
      show "norm (a - x) *\<^sub>R (x - b) = norm (x - b) *\<^sub>R (a - x)"
        unfolding norm_minus_commute[of x a] * using as(2,3)
        by(auto simp add: field_simps)
    next assume as:"dist a b = dist a x + dist x b"
      have "norm (a - x) / norm (a - b) \<le> 1" unfolding divide_le_eq_1_pos[OF Fal2]
        unfolding as[unfolded dist_norm] norm_ge_zero by auto
      thus "\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1" apply(rule_tac x="dist a x / dist a b" in exI)
        unfolding dist_norm apply(subst euclidean_eq_iff) apply rule defer apply(rule, rule divide_nonneg_pos) prefer 4
      proof(rule) fix i :: 'a assume i:"i\<in>Basis"
          have "((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) \<bullet> i =
            ((norm (a - b) - norm (a - x)) * (a \<bullet> i) + norm (a - x) * (b \<bullet> i)) / norm (a - b)"
            using Fal by(auto simp add: field_simps inner_simps)
          also have "\<dots> = x\<bullet>i" apply(rule divide_eq_imp[OF Fal])
            unfolding as[unfolded dist_norm] using as[unfolded dist_triangle_eq] apply-
            apply(subst (asm) euclidean_eq_iff) using i apply(erule_tac x=i in ballE) by(auto simp add:field_simps inner_simps)
          finally show "x \<bullet> i = ((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) \<bullet> i"
            by auto
        qed(insert Fal2, auto) qed
qed

lemma between_midpoint: fixes a::"'a::euclidean_space" shows
  "between (a,b) (midpoint a b)" (is ?t1)
  "between (b,a) (midpoint a b)" (is ?t2)
proof- have *:"\<And>x y z. x = (1/2::real) *\<^sub>R z \<Longrightarrow> y = (1/2) *\<^sub>R z \<Longrightarrow> norm z = norm x + norm y" by auto
  show ?t1 ?t2 unfolding between midpoint_def dist_norm apply(rule_tac[!] *)
    unfolding euclidean_eq_iff[where 'a='a]
    by(auto simp add:field_simps inner_simps) qed

lemma between_mem_convex_hull:
  "between (a,b) x \<longleftrightarrow> x \<in> convex hull {a,b}"
  unfolding between_mem_segment segment_convex_hull ..

subsection {* Shrinking towards the interior of a convex set *}

lemma mem_interior_convex_shrink:
  fixes s :: "('a::euclidean_space) set"
  assumes "convex s" "c \<in> interior s" "x \<in> s" "0 < e" "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof- obtain d where "d>0" and d:"ball c d \<subseteq> s" using assms(2) unfolding mem_interior by auto
  show ?thesis unfolding mem_interior apply(rule_tac x="e*d" in exI)
    apply(rule) defer unfolding subset_eq Ball_def mem_ball proof(rule,rule)
    fix y assume as:"dist (x - e *\<^sub>R (x - c)) y < e * d"
    have *:"y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x" using `e>0` by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = abs(1/e) * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm unfolding norm_scaleR[symmetric] apply(rule arg_cong[where f=norm]) using `e>0`
      by(auto simp add: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    also have "\<dots> = abs(1/e) * norm (x - e *\<^sub>R (x - c) - y)" by(auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d" using as[unfolded dist_norm] and `e>0`
      by(auto simp add:pos_divide_less_eq[OF `e>0`] mult_commute)
    finally show "y \<in> s" apply(subst *) apply(rule assms(1)[unfolded convex_alt,rule_format])
      apply(rule d[unfolded subset_eq,rule_format]) unfolding mem_ball using assms(3-5) by auto
  qed(rule mult_pos_pos, insert `e>0` `d>0`, auto) qed

lemma mem_interior_closure_convex_shrink:
  fixes s :: "('a::euclidean_space) set"
  assumes "convex s" "c \<in> interior s" "x \<in> closure s" "0 < e" "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof- obtain d where "d>0" and d:"ball c d \<subseteq> s" using assms(2) unfolding mem_interior by auto
  have "\<exists>y\<in>s. norm (y - x) * (1 - e) < e * d" proof(cases "x\<in>s")
    case True thus ?thesis using `e>0` `d>0` by(rule_tac bexI[where x=x], auto intro!: mult_pos_pos) next
    case False hence x:"x islimpt s" using assms(3)[unfolded closure_def] by auto
    show ?thesis proof(cases "e=1")
      case True obtain y where "y\<in>s" "y \<noteq> x" "dist y x < 1"
        using x[unfolded islimpt_approachable,THEN spec[where x=1]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding True using `d>0` by auto next
      case False hence "0 < e * d / (1 - e)" and *:"1 - e > 0"
        using `e\<le>1` `e>0` `d>0` by(auto intro!:mult_pos_pos divide_pos_pos)
      then obtain y where "y\<in>s" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding dist_norm using pos_less_divide_eq[OF *] by auto qed qed
  then obtain y where "y\<in>s" and y:"norm (y - x) * (1 - e) < e * d" by auto
  def z \<equiv> "c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *:"x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)" unfolding z_def using `e>0` by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have "z\<in>interior s" apply(rule interior_mono[OF d,unfolded subset_eq,rule_format])
    unfolding interior_open[OF open_ball] mem_ball z_def dist_norm using y and assms(4,5)
    by(auto simp add:field_simps norm_minus_commute)
  thus ?thesis unfolding * apply - apply(rule mem_interior_convex_shrink)
    using assms(1,4-5) `y\<in>s` by auto qed

subsection {* Some obvious but surprisingly hard simplex lemmas *}

lemma simplex:
  assumes "finite s" "0 \<notin> s"
  shows "convex hull (insert 0 s) =  { y. (\<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s \<le> 1 \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y)}"
  unfolding convex_hull_finite[OF finite.insertI[OF assms(1)]] apply(rule set_eqI, rule) unfolding mem_Collect_eq
  apply(erule_tac[!] exE) apply(erule_tac[!] conjE)+ unfolding setsum_clauses(2)[OF assms(1)]
  apply(rule_tac x=u in exI) defer apply(rule_tac x="\<lambda>x. if x = 0 then 1 - setsum u s else u x" in exI) using assms(2)
  unfolding if_smult and setsum_delta_notmem[OF assms(2)] by auto

lemma substd_simplex:
  assumes d: "d \<subseteq> Basis"
  shows "convex hull (insert 0 d) = {x. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> (\<Sum>i\<in>d. x\<bullet>i) \<le> 1 \<and> (\<forall>i\<in>Basis. i \<notin> d --> x\<bullet>i = 0)}"
  (is "convex hull (insert 0 ?p) = ?s")
proof- let ?D = d
  have "0 ~: ?p" using assms by (auto simp: image_def)
  from d have "finite d" by (blast intro: finite_subset finite_Basis)
  show ?thesis unfolding simplex[OF `finite d` `0 ~: ?p`]
    apply(rule set_eqI) unfolding mem_Collect_eq apply rule
    apply(erule exE, (erule conjE)+) apply(erule_tac[2] conjE)+ proof-
    fix x::"'a::euclidean_space" and u assume as: "\<forall>x\<in>?D. 0 \<le> u x"
      "setsum u ?D \<le> 1" "(\<Sum>x\<in>?D. u x *\<^sub>R x) = x"
    have *:"\<forall>i\<in>Basis. i:d --> u i = x\<bullet>i" and "(\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)" using as(3)
      unfolding substdbasis_expansion_unique[OF assms] by auto
    hence **:"setsum u ?D = setsum (op \<bullet> x) ?D"
      apply-apply(rule setsum_cong2) using assms by auto
    have " (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> setsum (op \<bullet> x) ?D \<le> 1"
      apply - proof(rule,rule)
      fix i :: 'a assume i:"i\<in>Basis" have "i : d ==> 0 \<le> x\<bullet>i" unfolding *[rule_format,OF i,symmetric]
         apply(rule_tac as(1)[rule_format]) by auto
      moreover have "i ~: d ==> 0 \<le> x\<bullet>i"
        using `(\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)`[rule_format, OF i] by auto
      ultimately show "0 \<le> x\<bullet>i" by auto
    qed(insert as(2)[unfolded **], auto)
    from this show " (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> setsum (op \<bullet> x) ?D \<le> 1 & (\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)"
      using `(\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)` by auto
  next fix x::"'a::euclidean_space" assume as:"\<forall>i\<in>Basis. 0 \<le> x \<bullet> i" "setsum (op \<bullet> x) ?D \<le> 1"
      "(\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)"
    show "\<exists>u. (\<forall>x\<in>?D. 0 \<le> u x) \<and> setsum u ?D \<le> 1 \<and> (\<Sum>x\<in>?D. u x *\<^sub>R x) = x"
      using as d unfolding substdbasis_expansion_unique[OF assms]
      by (rule_tac x="inner x" in exI) auto
  qed
qed

lemma std_simplex:
  "convex hull (insert 0 Basis) =
        {x::'a::euclidean_space . (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> setsum (\<lambda>i. x\<bullet>i) Basis \<le> 1 }"
  using substd_simplex[of Basis] by auto

lemma interior_std_simplex:
  "interior (convex hull (insert 0 Basis)) =
  {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 < x\<bullet>i) \<and> setsum (\<lambda>i. x\<bullet>i) Basis < 1 }"
  apply(rule set_eqI) unfolding mem_interior std_simplex unfolding subset_eq mem_Collect_eq Ball_def mem_ball
  unfolding Ball_def[symmetric] apply rule apply(erule exE, (erule conjE)+) defer apply(erule conjE) proof-
  fix x::"'a" and e assume "0<e" and as:"\<forall>xa. dist x xa < e \<longrightarrow> (\<forall>x\<in>Basis. 0 \<le> xa \<bullet> x) \<and> setsum (op \<bullet> xa) Basis \<le> 1"
  show "(\<forall>xa\<in>Basis. 0 < x \<bullet> xa) \<and> setsum (op \<bullet> x) Basis < 1" apply(safe) proof-
    fix i :: 'a assume i:"i\<in>Basis" thus "0 < x \<bullet> i" using as[THEN spec[where x="x - (e / 2) *\<^sub>R i"]] and `e>0`
      unfolding dist_norm
      by (auto elim!:ballE[where x=i] simp: inner_simps)
  next have **:"dist x (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) < e" using  `e>0`
      unfolding dist_norm by(auto intro!: mult_strict_left_mono simp: SOME_Basis)
    have "\<And>i. i\<in>Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) \<bullet> i = x\<bullet>i + (if i = (SOME i. i\<in>Basis) then e/2 else 0)"
      by (auto simp: SOME_Basis inner_Basis inner_simps)
    hence *:"setsum (op \<bullet> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis = setsum (\<lambda>i. x\<bullet>i + (if (SOME i. i\<in>Basis) = i then e/2 else 0)) Basis"
      apply(rule_tac setsum_cong) by auto
    have "setsum (op \<bullet> x) Basis < setsum (op \<bullet> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis" unfolding * setsum_addf
      using `0<e` DIM_positive[where 'a='a] apply(subst setsum_delta') by (auto simp: SOME_Basis)
    also have "\<dots> \<le> 1" using ** apply(drule_tac as[rule_format]) by auto
    finally show "setsum (op \<bullet> x) Basis < 1" by auto qed
next fix x::"'a" assume as:"\<forall>i\<in>Basis. 0 < x \<bullet> i" "setsum (op \<bullet> x) Basis < 1"
  guess a using UNIV_witness[where 'a='b] ..
  let ?d = "(1 - setsum (op \<bullet> x) Basis) / real (DIM('a))"
  have "Min ((op \<bullet> x) ` Basis) > 0" apply(rule Min_grI) using as(1) by auto
  moreover have"?d > 0" apply(rule divide_pos_pos) using as(2) by (auto simp add: Suc_le_eq DIM_positive)
  ultimately show "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> (\<forall>i\<in>Basis. 0 \<le> y \<bullet> i) \<and> setsum (op \<bullet> y) Basis \<le> 1"
    apply(rule_tac x="min (Min ((op \<bullet> x) ` Basis)) ?D" in exI) apply rule defer apply(rule,rule) proof-
    fix y assume y:"dist x y < min (Min (op \<bullet> x ` Basis)) ?d"
    have "setsum (op \<bullet> y) Basis \<le> setsum (\<lambda>i. x\<bullet>i + ?d) Basis" proof(rule setsum_mono)
      fix i :: 'a assume i: "i\<in>Basis" hence "abs (y\<bullet>i - x\<bullet>i) < ?d" apply-apply(rule le_less_trans)
        using Basis_le_norm[OF i, of "y - x"]
        using y[unfolded min_less_iff_conj dist_norm, THEN conjunct2] by(auto simp add: norm_minus_commute inner_diff_left)
      thus "y \<bullet> i \<le> x \<bullet> i + ?d" by auto qed
    also have "\<dots> \<le> 1" unfolding setsum_addf setsum_constant real_eq_of_nat by(auto simp add: Suc_le_eq)
    finally show "(\<forall>i\<in>Basis. 0 \<le> y \<bullet> i) \<and> setsum (op \<bullet> y) Basis \<le> 1"
    proof safe fix i :: 'a assume i:"i\<in>Basis"
      have "norm (x - y) < x\<bullet>i" apply(rule less_le_trans)
        apply(rule y[unfolded min_less_iff_conj dist_norm, THEN conjunct1]) using i by auto
      thus "0 \<le> y\<bullet>i" using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format, OF i]
        by (auto simp: inner_simps)
    qed qed auto qed

lemma interior_std_simplex_nonempty: obtains a::"'a::euclidean_space" where
  "a \<in> interior(convex hull (insert 0 Basis))" proof-
  let ?D = "Basis :: 'a set" let ?a = "setsum (\<lambda>b::'a. inverse (2 * real DIM('a)) *\<^sub>R b) Basis"
  { fix i :: 'a assume i:"i\<in>Basis" have "?a \<bullet> i = inverse (2 * real DIM('a))"
      by (rule trans[of _ "setsum (\<lambda>j. if i = j then inverse (2 * real DIM('a)) else 0) ?D"])
         (simp_all add: setsum_cases i) }
  note ** = this
  show ?thesis apply(rule that[of ?a]) unfolding interior_std_simplex mem_Collect_eq proof safe
    fix i :: 'a assume i:"i\<in>Basis" show "0 < ?a \<bullet> i" unfolding **[OF i] by(auto simp add: Suc_le_eq DIM_positive)
  next have "setsum (op \<bullet> ?a) ?D = setsum (\<lambda>i. inverse (2 * real DIM('a))) ?D" apply(rule setsum_cong2, rule **) by auto
    also have "\<dots> < 1" unfolding setsum_constant real_eq_of_nat divide_inverse[symmetric] by (auto simp add:field_simps)
    finally show "setsum (op \<bullet> ?a) ?D < 1" by auto qed qed

lemma rel_interior_substd_simplex: assumes d: "d\<subseteq>Basis"
  shows "rel_interior (convex hull (insert 0 d)) =
  {x::'a::euclidean_space. (\<forall>i\<in>d. 0 < x\<bullet>i) \<and> (\<Sum>i\<in>d. x\<bullet>i) < 1 \<and> (\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)}"
  (is "rel_interior (convex hull (insert 0 ?p)) = ?s")
(* Proof is a modified copy of the proof of similar lemma interior_std_simplex in Convex_Euclidean_Space.thy *)
proof-
have "finite d" apply(rule finite_subset) using assms by auto
{ assume "d={}" hence ?thesis using rel_interior_sing using euclidean_eq_iff[of _ 0] by auto }
moreover
{ assume "d~={}"
have h0: "affine hull (convex hull (insert 0 ?p))={x::'a::euclidean_space. (\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)}"
   using affine_hull_convex_hull affine_hull_substd_basis assms by auto
have aux: "!!x::'a. \<forall>i\<in>Basis. ((\<forall>i\<in>d. 0 \<le> x\<bullet>i) \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)) \<longrightarrow> 0 \<le> x\<bullet>i" 
  by auto
{ fix x::"'a::euclidean_space" assume x_def: "x : rel_interior (convex hull (insert 0 ?p))"
  from this obtain e where e0: "e>0" and
       "ball x e Int {xa. (\<forall>i\<in>Basis. i ~: d --> xa\<bullet>i = 0)} <= convex hull (insert 0 ?p)"
       using mem_rel_interior_ball[of x "convex hull (insert 0 ?p)"] h0 by auto
  hence as: "ALL xa. (dist x xa < e & (\<forall>i\<in>Basis. i ~: d --> xa\<bullet>i = 0)) -->
    (!i : d. 0 <= xa \<bullet> i) & setsum (op \<bullet> xa) d <= 1"
    unfolding ball_def unfolding substd_simplex[OF assms] using assms by auto
  have x0: "(\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)"
    using x_def rel_interior_subset  substd_simplex[OF assms] by auto
  have "(\<forall>i\<in>d. 0 < x \<bullet> i) & setsum (op \<bullet> x) d < 1 & (\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)" apply(rule,rule)
  proof-
    fix i::'a assume "i\<in>d"
    hence "\<forall>ia\<in>d. 0 \<le> (x - (e / 2) *\<^sub>R i) \<bullet> ia" apply-apply(rule as[rule_format,THEN conjunct1])
      unfolding dist_norm using d `e>0` x0 by (auto simp: inner_simps inner_Basis)
    thus "0 < x \<bullet> i" apply(erule_tac x=i in ballE) using `e>0` `i\<in>d` d
    by (auto simp: inner_simps inner_Basis)
  next obtain a where a:"a:d" using `d ~= {}` by auto
    then have **:"dist x (x + (e / 2) *\<^sub>R a) < e"
      using  `e>0` norm_Basis[of a] d
      unfolding dist_norm by auto
    have "\<And>i. i\<in>Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R a) \<bullet> i = x\<bullet>i + (if i = a then e/2 else 0)"
      using a d by (auto simp: inner_simps inner_Basis)
    hence *:"setsum (op \<bullet> (x + (e / 2) *\<^sub>R a)) d =
      setsum (\<lambda>i. x\<bullet>i + (if a = i then e/2 else 0)) d" using d by (intro setsum_cong) auto
    have "a \<in> Basis" using `a \<in> d` d by auto
    then have h1: "(\<forall>i\<in>Basis. i ~: d --> (x + (e / 2) *\<^sub>R a) \<bullet> i = 0)"
      using x0 d `a\<in>d` by (auto simp add: inner_add_left inner_Basis)
    have "setsum (op \<bullet> x) d < setsum (op \<bullet> (x + (e / 2) *\<^sub>R a)) d" unfolding * setsum_addf
      using `0<e` `a:d` using `finite d` by(auto simp add: setsum_delta')
    also have "\<dots> \<le> 1" using ** h1 as[rule_format, of "x + (e / 2) *\<^sub>R a"] by auto
    finally show "setsum (op \<bullet> x) d < 1 & (\<forall>i\<in>Basis. i ~: d --> x\<bullet>i = 0)" using x0 by auto
  qed
}
moreover
{
  fix x::"'a::euclidean_space" assume as: "x : ?s"
  have "!i. ((0<x\<bullet>i) | (0=x\<bullet>i) --> 0<=x\<bullet>i)" by auto
  moreover have "!i. (i:d) | (i ~: d)" by auto
  ultimately
  have "!i. ( (ALL i:d. 0 < x\<bullet>i) & (ALL i. i ~: d --> x\<bullet>i = 0) ) --> 0 <= x\<bullet>i" by metis
  hence h2: "x : convex hull (insert 0 ?p)" using as assms
    unfolding substd_simplex[OF assms] by fastforce
  obtain a where a:"a:d" using `d ~= {}` by auto
  let ?d = "(1 - setsum (op \<bullet> x) d) / real (card d)"
  have "0 < card d" using `d ~={}` `finite d` by (simp add: card_gt_0_iff)
  have "Min ((op \<bullet> x) ` d) > 0" using as `d \<noteq> {}` `finite d` by (simp add: Min_grI)
  moreover have "?d > 0" apply(rule divide_pos_pos) using as using `0 < card d` by auto
  ultimately have h3: "min (Min ((op \<bullet> x) ` d)) ?d > 0" by auto

  have "x : rel_interior (convex hull (insert 0 ?p))"
    unfolding rel_interior_ball mem_Collect_eq h0 apply(rule,rule h2)
    unfolding substd_simplex[OF assms]
    apply(rule_tac x="min (Min ((op \<bullet> x) ` d)) ?d" in exI) apply(rule,rule h3) apply safe unfolding mem_ball
  proof-
    fix y::'a assume y:"dist x y < min (Min (op \<bullet> x ` d)) ?d" and y2: "\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> y\<bullet>i = 0"
    have "setsum (op \<bullet> y) d \<le> setsum (\<lambda>i. x\<bullet>i + ?d) d"
    proof(rule setsum_mono)
      fix i assume "i \<in> d"
      with d have i: "i \<in> Basis" by auto
      have "abs (y\<bullet>i - x\<bullet>i) < ?d" apply(rule le_less_trans) using Basis_le_norm[OF i, of "y - x"]
        using y[unfolded min_less_iff_conj dist_norm, THEN conjunct2]
        by (auto simp add: norm_minus_commute inner_simps)
      thus "y \<bullet> i \<le> x \<bullet> i + ?d" by auto
    qed
    also have "\<dots> \<le> 1" unfolding setsum_addf setsum_constant real_eq_of_nat
      using `0 < card d` by auto
    finally show "setsum (op \<bullet> y) d \<le> 1" .

    fix i :: 'a assume i: "i \<in> Basis" thus "0 \<le> y\<bullet>i"
    proof(cases "i\<in>d") case True
      have "norm (x - y) < x\<bullet>i" using y[unfolded min_less_iff_conj dist_norm, THEN conjunct1]
        using Min_gr_iff[of "op \<bullet> x ` d" "norm (x - y)"] `0 < card d` `i:d`
        by (simp add: card_gt_0_iff)
      thus "0 \<le> y\<bullet>i" using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format]
        by (auto simp: inner_simps)
    qed(insert y2, auto)
  qed
} ultimately have
    "\<And>x. (x : rel_interior (convex hull insert 0 d)) = (x \<in> {x. (ALL i:d. 0 < x \<bullet> i) &
    setsum (op \<bullet> x) d < 1 & (\<forall>i\<in>Basis. i ~: d --> x \<bullet> i = 0)})" by blast
from this have ?thesis by (rule set_eqI)
} ultimately show ?thesis by blast
qed

lemma rel_interior_substd_simplex_nonempty: assumes "d ~={}" "d\<subseteq>Basis"
  obtains a::"'a::euclidean_space" where
  "a : rel_interior(convex hull (insert 0 d))" proof-
(* Proof is a modified copy of the proof of similar lemma interior_std_simplex_nonempty in Convex_Euclidean_Space.thy *)
  let ?D = d let ?a = "setsum (\<lambda>b::'a::euclidean_space. inverse (2 * real (card d)) *\<^sub>R b) ?D"
  have "finite d" apply(rule finite_subset) using assms(2) by auto
  hence d1: "0 < real(card d)" using `d ~={}` by auto
  { fix i assume "i:d"
    have "?a \<bullet> i = inverse (2 * real (card d))"
      apply(rule trans[of _ "setsum (\<lambda>j. if i = j then inverse (2 * real (card d)) else 0) ?D"])
      unfolding inner_setsum_left
      apply(rule setsum_cong2)
      using `i:d` `finite d` setsum_delta'[of d i "(%k. inverse (2 * real (card d)))"] d1 assms(2)
      by (auto simp: inner_simps inner_Basis set_rev_mp[OF _ assms(2)]) }
  note ** = this
  show ?thesis apply(rule that[of ?a]) unfolding rel_interior_substd_simplex[OF assms(2)] mem_Collect_eq
  proof safe fix i assume "i:d"
    have "0 < inverse (2 * real (card d))" using d1 by auto
    also have "...=?a \<bullet> i" using **[of i] `i:d` by auto
    finally show "0 < ?a \<bullet> i" by auto
  next have "setsum (op \<bullet> ?a) ?D = setsum (\<lambda>i. inverse (2 * real (card d))) ?D"
      by(rule setsum_cong2, rule **)
    also have "\<dots> < 1" unfolding setsum_constant real_eq_of_nat divide_real_def[symmetric]
      by (auto simp add:field_simps)
    finally show "setsum (op \<bullet> ?a) ?D < 1" by auto
  next fix i assume "i\<in>Basis" and "i~:d"
    have "?a : (span d)"
      apply (rule span_setsum[of d "(%b. b /\<^sub>R (2 * real (card d)))" d])
      using finite_subset[OF assms(2) finite_Basis]
      apply blast
    proof-
      { fix x assume "(x :: 'a::euclidean_space): d"
        hence "x : span d"
          using span_superset[of _ "d"] by auto
        hence "(x /\<^sub>R (2 * real (card d))) : (span d)"
          using span_mul[of x "d" "(inverse (real (card d)) / 2)"] by auto
      } thus "\<forall>x\<in>d. x /\<^sub>R (2 * real (card d)) \<in> span d" by auto
    qed
    thus "?a \<bullet> i = 0 " using `i~:d` unfolding span_substd_basis[OF assms(2)] using `i\<in>Basis` by auto
  qed
qed

subsection {* Relative interior of convex set *}

lemma rel_interior_convex_nonempty_aux:
fixes S :: "('n::euclidean_space) set"
assumes "convex S" and "0 : S"
shows "rel_interior S ~= {}"
proof-
{ assume "S = {0}" hence ?thesis using rel_interior_sing by auto }
moreover {
assume "S ~= {0}"
obtain B where B_def: "independent B & B<=S & (S <= span B) & card B = dim S" using basis_exists[of S] by auto
hence "B~={}" using B_def assms `S ~= {0}` span_empty by auto
have "insert 0 B <= span B" using subspace_span[of B] subspace_0[of "span B"] span_inc by auto
hence "span (insert 0 B) <= span B"
    using span_span[of B] span_mono[of "insert 0 B" "span B"] by blast
hence "convex hull insert 0 B <= span B"
    using convex_hull_subset_span[of "insert 0 B"] by auto
hence "span (convex hull insert 0 B) <= span B"
    using span_span[of B] span_mono[of "convex hull insert 0 B" "span B"] by blast
hence *: "span (convex hull insert 0 B) = span B"
    using span_mono[of B "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
hence "span (convex hull insert 0 B) = span S"
    using B_def span_mono[of B S] span_mono[of S "span B"] span_span[of B] by auto
moreover have "0 : affine hull (convex hull insert 0 B)"
    using hull_subset[of "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
ultimately have **: "affine hull (convex hull insert 0 B) = affine hull S"
    using affine_hull_span_0[of "convex hull insert 0 B"] affine_hull_span_0[of "S"]
    assms  hull_subset[of S] by auto
obtain d and f::"'n=>'n" where fd: "card d = card B & linear f & f ` B = d &
       f ` span B = {x. \<forall>i\<in>Basis. i ~: d --> x \<bullet> i = (0::real)} &  inj_on f (span B)" and d:"d\<subseteq>Basis"
    using basis_to_substdbasis_subspace_isomorphism[of B,OF _ ] B_def by auto
hence "bounded_linear f" using linear_conv_bounded_linear by auto
have "d ~={}" using fd B_def `B ~={}` by auto
have "(insert 0 d) = f ` (insert 0 B)" using fd linear_0 by auto
hence "(convex hull (insert 0 d)) = f ` (convex hull (insert 0 B))"
   using convex_hull_linear_image[of f "(insert 0 d)"]
   convex_hull_linear_image[of f "(insert 0 B)"] `bounded_linear f` by auto
moreover have "rel_interior (f ` (convex hull insert 0 B)) =
   f ` rel_interior (convex hull insert 0 B)"
   apply (rule  rel_interior_injective_on_span_linear_image[of f "(convex hull insert 0 B)"])
   using `bounded_linear f` fd * by auto
ultimately have "rel_interior (convex hull insert 0 B) ~= {}"
   using rel_interior_substd_simplex_nonempty[OF `d~={}` d] apply auto by blast
moreover have "convex hull (insert 0 B) <= S"
   using B_def assms hull_mono[of "insert 0 B" "S" "convex"] convex_hull_eq by auto
ultimately have ?thesis using subset_rel_interior[of "convex hull insert 0 B" S] ** by auto
} ultimately show ?thesis by auto
qed

lemma rel_interior_convex_nonempty:
fixes S :: "('n::euclidean_space) set"
assumes "convex S"
shows "rel_interior S = {} <-> S = {}"
proof-
{ assume "S ~= {}" from this obtain a where "a : S" by auto
  hence "0 : op + (-a) ` S" using assms exI[of "(%x. x:S & -a+x=0)" a] by auto
  hence "rel_interior (op + (-a) ` S) ~= {}"
    using rel_interior_convex_nonempty_aux[of "op + (-a) ` S"]
          convex_translation[of S "-a"] assms by auto
  hence "rel_interior S ~= {}" using rel_interior_translation by auto
} from this show ?thesis using rel_interior_empty by auto
qed

lemma convex_rel_interior:
fixes S :: "(_::euclidean_space) set"
assumes "convex S"
shows "convex (rel_interior S)"
proof-
{ fix "x" "y" "u"
  assume assm: "x:rel_interior S" "y:rel_interior S" "0<=u" "(u :: real) <= 1"
  hence "x:S" using rel_interior_subset by auto
  have "x - u *\<^sub>R (x-y) : rel_interior S"
  proof(cases "0=u")
     case False hence "0<u" using assm by auto
        thus ?thesis
        using assm rel_interior_convex_shrink[of S y x u] assms `x:S` by auto
     next
     case True thus ?thesis using assm by auto
  qed
  hence "(1-u) *\<^sub>R x + u *\<^sub>R y : rel_interior S" by (simp add: algebra_simps)
} from this show ?thesis unfolding convex_alt by auto
qed

lemma convex_closure_rel_interior:
fixes S :: "('n::euclidean_space) set"
assumes "convex S"
shows "closure(rel_interior S) = closure S"
proof-
have h1: "closure(rel_interior S) <= closure S"
   using closure_mono[of "rel_interior S" S] rel_interior_subset[of S] by auto
{ assume "S ~= {}" from this obtain a where a_def: "a : rel_interior S"
    using rel_interior_convex_nonempty assms by auto
  { fix x assume x_def: "x : closure S"
    { assume "x=a" hence "x : closure(rel_interior S)" using a_def unfolding closure_def by auto }
    moreover
    { assume "x ~= a"
       { fix e :: real assume e_def: "e>0"
         def e1 == "min 1 (e/norm (x - a))" hence e1_def: "e1>0 & e1<=1 & e1*norm(x-a)<=e"
            using `x ~= a` `e>0` divide_pos_pos[of e] le_divide_eq[of e1 e "norm(x-a)"] by simp
         hence *: "x - e1 *\<^sub>R (x - a) : rel_interior S"
            using rel_interior_closure_convex_shrink[of S a x e1] assms x_def a_def e1_def by auto
         have "EX y. y:rel_interior S & y ~= x & (dist y x) <= e"
            apply (rule_tac x="x - e1 *\<^sub>R (x - a)" in exI)
            using * e1_def dist_norm[of "x - e1 *\<^sub>R (x - a)" x] `x ~= a` by simp
      } hence "x islimpt rel_interior S" unfolding islimpt_approachable_le by auto
      hence "x : closure(rel_interior S)" unfolding closure_def by auto
    } ultimately have "x : closure(rel_interior S)" by auto
  } hence ?thesis using h1 by auto
}
moreover
{ assume "S = {}" hence "rel_interior S = {}" using rel_interior_empty by auto
  hence "closure(rel_interior S) = {}" using closure_empty by auto
  hence ?thesis using `S={}` by auto
} ultimately show ?thesis by blast
qed

lemma rel_interior_same_affine_hull:
  fixes S :: "('n::euclidean_space) set"
  assumes "convex S"
  shows "affine hull (rel_interior S) = affine hull S"
by (metis assms closure_same_affine_hull convex_closure_rel_interior)

lemma rel_interior_aff_dim:
  fixes S :: "('n::euclidean_space) set"
  assumes "convex S"
  shows "aff_dim (rel_interior S) = aff_dim S"
by (metis aff_dim_affine_hull2 assms rel_interior_same_affine_hull)

lemma rel_interior_rel_interior:
  fixes S :: "('n::euclidean_space) set"
  assumes "convex S"
  shows "rel_interior (rel_interior S) = rel_interior S"
proof-
have "openin (subtopology euclidean (affine hull (rel_interior S))) (rel_interior S)"
  using opein_rel_interior[of S] rel_interior_same_affine_hull[of S] assms by auto
from this show ?thesis using rel_interior_def by auto
qed

lemma rel_interior_rel_open:
  fixes S :: "('n::euclidean_space) set"
  assumes "convex S"
  shows "rel_open (rel_interior S)"
unfolding rel_open_def using rel_interior_rel_interior assms by auto

lemma convex_rel_interior_closure_aux:
  fixes x y z :: "_::euclidean_space"
  assumes "0 < a" "0 < b" "(a+b) *\<^sub>R z = a *\<^sub>R x + b *\<^sub>R y"
  obtains e where "0 < e" "e <= 1" "z = y - e *\<^sub>R (y-x)"
proof-
def e == "a/(a+b)"
have "z = (1 / (a + b)) *\<^sub>R ((a + b) *\<^sub>R z)" apply auto using assms by simp
also have "... = (1 / (a + b)) *\<^sub>R (a *\<^sub>R x + b *\<^sub>R y)" using assms
   scaleR_cancel_left[of "1/(a+b)" "(a + b) *\<^sub>R z" "a *\<^sub>R x + b *\<^sub>R y"] by auto
also have "... = y - e *\<^sub>R (y-x)" using e_def apply (simp add: algebra_simps)
   using scaleR_left_distrib[of "a/(a+b)" "b/(a+b)" y] assms add_divide_distrib[of a b "a+b"] by auto
finally have "z = y - e *\<^sub>R (y-x)" by auto
moreover have "0<e" using e_def assms divide_pos_pos[of a "a+b"] by auto
moreover have "e<=1" using e_def assms by auto
ultimately show ?thesis using that[of e] by auto
qed

lemma convex_rel_interior_closure:
  fixes S :: "('n::euclidean_space) set"
  assumes "convex S"
  shows "rel_interior (closure S) = rel_interior S"
proof-
{ assume "S={}" hence ?thesis using assms rel_interior_convex_nonempty by auto }
moreover
{ assume "S ~= {}"
  have "rel_interior (closure S) >= rel_interior S"
    using subset_rel_interior[of S "closure S"] closure_same_affine_hull closure_subset by auto
  moreover
  { fix z assume z_def: "z : rel_interior (closure S)"
    obtain x where x_def: "x : rel_interior S"
      using `S ~= {}` assms rel_interior_convex_nonempty by auto
    { assume "x=z" hence "z : rel_interior S" using x_def by auto }
    moreover
    { assume "x ~= z"
      obtain e where e_def: "e > 0 & cball z e Int affine hull closure S <= closure S"
        using z_def rel_interior_cball[of "closure S"] by auto
      hence *: "0 < e/norm(z-x)" using e_def `x ~= z` divide_pos_pos[of e "norm(z-x)"] by auto
      def y == "z + (e/norm(z-x)) *\<^sub>R (z-x)"
      have yball: "y : cball z e"
        using mem_cball y_def dist_norm[of z y] e_def by auto
      have "x : affine hull closure S"
        using x_def rel_interior_subset_closure hull_inc[of x "closure S"] by auto
      moreover have "z : affine hull closure S"
        using z_def rel_interior_subset hull_subset[of "closure S"] by auto
      ultimately have "y : affine hull closure S"
        using y_def affine_affine_hull[of "closure S"]
          mem_affine_3_minus [of "affine hull closure S" z z x "e/norm(z-x)"] by auto
      hence "y : closure S" using e_def yball by auto
      have "(1+(e/norm(z-x))) *\<^sub>R z = (e/norm(z-x)) *\<^sub>R x + y"
        using y_def by (simp add: algebra_simps)
      from this obtain e1 where "0 < e1 & e1 <= 1 & z = y - e1 *\<^sub>R (y - x)"
        using * convex_rel_interior_closure_aux[of "e / norm (z - x)" 1 z x y]
          by (auto simp add: algebra_simps)
      hence "z : rel_interior S"
        using rel_interior_closure_convex_shrink assms x_def `y : closure S` by auto
    } ultimately have "z : rel_interior S" by auto
  } ultimately have ?thesis by auto
} ultimately show ?thesis by blast
qed

lemma convex_interior_closure:
fixes S :: "('n::euclidean_space) set"
assumes "convex S"
shows "interior (closure S) = interior S"
using closure_aff_dim[of S] interior_rel_interior_gen[of S] interior_rel_interior_gen[of "closure S"]
      convex_rel_interior_closure[of S] assms by auto

lemma closure_eq_rel_interior_eq:
fixes S1 S2 ::  "('n::euclidean_space) set"
assumes "convex S1" "convex S2"
shows "(closure S1 = closure S2) <-> (rel_interior S1 = rel_interior S2)"
 by (metis convex_rel_interior_closure convex_closure_rel_interior assms)


lemma closure_eq_between:
fixes S1 S2 ::  "('n::euclidean_space) set"
assumes "convex S1" "convex S2"
shows "(closure S1 = closure S2) <->
      ((rel_interior S1 <= S2) & (S2 <= closure S1))" (is "?A <-> ?B")
proof-
have "?A --> ?B" by (metis assms closure_subset convex_rel_interior_closure rel_interior_subset)
moreover have "?B --> (closure S1 <= closure S2)"
     by (metis assms(1) convex_closure_rel_interior closure_mono)
moreover have "?B --> (closure S1 >= closure S2)" by (metis closed_closure closure_minimal)
ultimately show ?thesis by blast
qed

lemma open_inter_closure_rel_interior:
fixes S A ::  "('n::euclidean_space) set"
assumes "convex S" "open A"
shows "((A Int closure S) = {}) <-> ((A Int rel_interior S) = {})"
by (metis assms convex_closure_rel_interior open_inter_closure_eq_empty)

definition "rel_frontier S = closure S - rel_interior S"

lemma closed_affine_hull: "closed (affine hull ((S :: ('n::euclidean_space) set)))"
by (metis affine_affine_hull affine_closed)

lemma closed_rel_frontier: "closed(rel_frontier (S :: ('n::euclidean_space) set))"
proof-
have *: "closedin (subtopology euclidean (affine hull S)) (closure S - rel_interior S)"
apply (rule closedin_diff[of "subtopology euclidean (affine hull S)""closure S" "rel_interior S"])  using closed_closedin_trans[of "affine hull S" "closure S"] closed_affine_hull[of S]
  closure_affine_hull[of S] opein_rel_interior[of S] by auto
show ?thesis apply (rule closedin_closed_trans[of "affine hull S" "rel_frontier S"])
  unfolding rel_frontier_def using * closed_affine_hull by auto
qed


lemma convex_rel_frontier_aff_dim:
fixes S1 S2 ::  "('n::euclidean_space) set"
assumes "convex S1" "convex S2" "S2 ~= {}"
assumes "S1 <= rel_frontier S2"
shows "aff_dim S1 < aff_dim S2"
proof-
have "S1 <= closure S2" using assms unfolding rel_frontier_def by auto
hence *: "affine hull S1 <= affine hull S2"
   using hull_mono[of "S1" "closure S2"] closure_same_affine_hull[of S2] by auto
hence "aff_dim S1 <= aff_dim S2" using * aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2]
    aff_dim_subset[of "affine hull S1" "affine hull S2"] by auto
moreover
{ assume eq: "aff_dim S1 = aff_dim S2"
  hence "S1 ~= {}" using aff_dim_empty[of S1] aff_dim_empty[of S2] `S2 ~= {}` by auto
  have **: "affine hull S1 = affine hull S2"
     apply (rule affine_dim_equal) using * affine_affine_hull apply auto
     using `S1 ~= {}` hull_subset[of S1] apply auto
     using eq aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2] by auto
  obtain a where a_def: "a : rel_interior S1"
     using  `S1 ~= {}` rel_interior_convex_nonempty assms by auto
  obtain T where T_def: "open T & a : T Int S1 & T Int affine hull S1 <= S1"
     using mem_rel_interior[of a S1] a_def by auto
  hence "a : T Int closure S2" using a_def assms unfolding rel_frontier_def by auto
  from this obtain b where b_def: "b : T Int rel_interior S2"
     using open_inter_closure_rel_interior[of S2 T] assms T_def by auto
  hence "b : affine hull S1" using rel_interior_subset hull_subset[of S2] ** by auto
  hence "b : S1" using T_def b_def by auto
  hence False using b_def assms unfolding rel_frontier_def by auto
} ultimately show ?thesis using less_le by auto
qed


lemma convex_rel_interior_if:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S"
assumes "z : rel_interior S"
shows "(!x:affine hull S. EX m. m>1 & (!e. (e>1 & e<=m) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S ))"
proof-
obtain e1 where e1_def: "e1>0 & cball z e1 Int affine hull S <= S"
    using mem_rel_interior_cball[of z S] assms by auto
{ fix x assume x_def: "x:affine hull S"
  { assume "x ~= z"
    def m == "1+e1/norm(x-z)"
    hence "m>1" using e1_def `x ~= z` divide_pos_pos[of e1 "norm (x - z)"] by auto
    { fix e assume e_def: "e>1 & e<=m"
      have "z : affine hull S" using assms rel_interior_subset hull_subset[of S] by auto
      hence *: "(1-e)*\<^sub>R x+ e *\<^sub>R z : affine hull S"
         using mem_affine[of "affine hull S" x z "(1-e)" e] affine_affine_hull[of S] x_def by auto
      have "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) = norm ((e - 1) *\<^sub>R (x-z))" by (simp add: algebra_simps)
      also have "...= (e - 1) * norm(x-z)" using norm_scaleR e_def by auto
      also have "...<=(m - 1) * norm(x-z)" using e_def mult_right_mono[of _ _ "norm(x-z)"] by auto
      also have "...= (e1 / norm (x - z)) * norm (x - z)" using m_def by auto
      also have "...=e1" using `x ~= z` e1_def by simp
      finally have **: "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) <= e1" by auto
      have "(1-e)*\<^sub>R x+ e *\<^sub>R z : cball z e1"
         using m_def ** unfolding cball_def dist_norm by (auto simp add: algebra_simps)
      hence "(1-e)*\<^sub>R x+ e *\<^sub>R z : S" using e_def * e1_def by auto
    } hence "EX m. m>1 & (!e. (e>1 & e<=m) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S )" using `m>1` by auto
  }
  moreover
  { assume "x=z" def m == "1+e1" hence "m>1" using e1_def by auto
    { fix e assume e_def: "e>1 & e<=m"
      hence "(1-e)*\<^sub>R x+ e *\<^sub>R z : S"
        using e1_def x_def `x=z` by (auto simp add: algebra_simps)
      hence "(1-e)*\<^sub>R x+ e *\<^sub>R z : S" using e_def by auto
    } hence "EX m. m>1 & (!e. (e>1 & e<=m) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S )" using `m>1` by auto
  } ultimately have "EX m. m>1 & (!e. (e>1 & e<=m) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S )" by auto
} from this show ?thesis by auto
qed

lemma convex_rel_interior_if2:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S"
assumes "z : rel_interior S"
shows "(!x:affine hull S. EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S)"
using convex_rel_interior_if[of S z] assms by auto

lemma convex_rel_interior_only_if:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S" "S ~= {}"
assumes "(!x:S. EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S)"
shows "z : rel_interior S"
proof-
obtain x where x_def: "x : rel_interior S" using rel_interior_convex_nonempty assms by auto
hence "x:S" using rel_interior_subset by auto
from this obtain e where e_def: "e>1 & (1 - e) *\<^sub>R x + e *\<^sub>R z : S" using assms by auto
def y == "(1 - e) *\<^sub>R x + e *\<^sub>R z" hence "y:S" using e_def by auto
def e1 == "1/e" hence "0<e1 & e1<1" using e_def by auto
hence "z=y-(1-e1)*\<^sub>R (y-x)" using e1_def y_def by (auto simp add: algebra_simps)
from this show ?thesis
    using rel_interior_convex_shrink[of S x y "1-e1"] `0<e1 & e1<1` `y:S` x_def assms by auto
qed

lemma convex_rel_interior_iff:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S" "S ~= {}"
shows "z : rel_interior S <-> (!x:S. EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S)"
using assms hull_subset[of S "affine"]
      convex_rel_interior_if[of S z] convex_rel_interior_only_if[of S z] by auto

lemma convex_rel_interior_iff2:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S" "S ~= {}"
shows "z : rel_interior S <-> (!x:affine hull S. EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S)"
using assms hull_subset[of S]
      convex_rel_interior_if2[of S z] convex_rel_interior_only_if[of S z] by auto


lemma convex_interior_iff:
fixes S ::  "('n::euclidean_space) set"
assumes "convex S"
shows "z : interior S <-> (!x. EX e. e>0 & z+ e *\<^sub>R x : S)"
proof-
{ assume a: "~(aff_dim S = int DIM('n))"
  { assume "z : interior S"
    hence False using a interior_rel_interior_gen[of S] by auto
  }
  moreover
  { assume r: "!x. EX e. e>0 & z+ e *\<^sub>R x : S"
    { fix x obtain e1 where e1_def: "e1>0 & z+ e1 *\<^sub>R (x-z) : S" using r by auto
      obtain e2 where e2_def: "e2>0 & z+ e2 *\<^sub>R (z-x) : S" using r by auto
      def x1 == "z+ e1 *\<^sub>R (x-z)"
         hence x1: "x1 : affine hull S" using e1_def hull_subset[of S] by auto
      def x2 == "z+ e2 *\<^sub>R (z-x)"
         hence x2: "x2 : affine hull S" using e2_def hull_subset[of S] by auto
      have *: "e1/(e1+e2) + e2/(e1+e2) = 1" using add_divide_distrib[of e1 e2 "e1+e2"] e1_def e2_def by simp
      hence "z = (e2/(e1+e2)) *\<^sub>R x1 + (e1/(e1+e2)) *\<^sub>R x2"
         using x1_def x2_def apply (auto simp add: algebra_simps)
         using scaleR_left_distrib[of "e1/(e1+e2)" "e2/(e1+e2)" z] by auto
      hence z: "z : affine hull S"
         using mem_affine[of "affine hull S" x1 x2 "e2/(e1+e2)" "e1/(e1+e2)"]
         x1 x2 affine_affine_hull[of S] * by auto
      have "x1-x2 = (e1+e2) *\<^sub>R (x-z)"
         using x1_def x2_def by (auto simp add: algebra_simps)
      hence "x=z+(1/(e1+e2)) *\<^sub>R (x1-x2)" using e1_def e2_def by simp
      hence "x : affine hull S" using mem_affine_3_minus[of "affine hull S" z x1 x2 "1/(e1+e2)"]
          x1 x2 z affine_affine_hull[of S] by auto
    } hence "affine hull S = UNIV" by auto
    hence "aff_dim S = int DIM('n)" using aff_dim_affine_hull[of S] by (simp add: aff_dim_univ)
    hence False using a by auto
  } ultimately have ?thesis by auto
}
moreover
{ assume a: "aff_dim S = int DIM('n)"
  hence "S ~= {}" using aff_dim_empty[of S] by auto
  have *: "affine hull S=UNIV" using a affine_hull_univ by auto
  { assume "z : interior S"
    hence "z : rel_interior S" using a interior_rel_interior_gen[of S] by auto
    hence **: "(!x. EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S)"
      using convex_rel_interior_iff2[of S z] assms `S~={}` * by auto
    fix x obtain e1 where e1_def: "e1>1 & (1-e1)*\<^sub>R (z-x)+ e1 *\<^sub>R z : S"
      using **[rule_format, of "z-x"] by auto
    def e == "e1 - 1"
    hence "(1-e1)*\<^sub>R (z-x)+ e1 *\<^sub>R z = z+ e *\<^sub>R x" by (simp add: algebra_simps)
    hence "e>0 & z+ e *\<^sub>R x : S" using e1_def e_def by auto
    hence "EX e. e>0 & z+ e *\<^sub>R x : S" by auto
  }
  moreover
  { assume r: "(!x. EX e. e>0 & z+ e *\<^sub>R x : S)"
    { fix x obtain e1 where e1_def: "e1>0 & z + e1*\<^sub>R (z-x) : S"
         using r[rule_format, of "z-x"] by auto
      def e == "e1 + 1"
      hence "z + e1*\<^sub>R (z-x) = (1-e)*\<^sub>R x+ e *\<^sub>R z" by (simp add: algebra_simps)
      hence "e > 1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S" using e1_def e_def by auto
      hence "EX e. e>1 & (1-e)*\<^sub>R x+ e *\<^sub>R z : S" by auto
    }
    hence "z : rel_interior S" using convex_rel_interior_iff2[of S z] assms `S~={}` by auto
    hence "z : interior S" using a interior_rel_interior_gen[of S] by auto
  } ultimately have ?thesis by auto
} ultimately show ?thesis by auto
qed

subsubsection {* Relative interior and closure under common operations *}

lemma rel_interior_inter_aux: "Inter {rel_interior S |S. S : I} <= Inter I"
proof-
{ fix y assume "y : Inter {rel_interior S |S. S : I}"
  hence y_def: "!S : I. y : rel_interior S" by auto
  { fix S assume "S : I" hence "y : S" using rel_interior_subset y_def by auto }
  hence "y : Inter I" by auto
} thus ?thesis by auto
qed

lemma closure_inter: "closure (Inter I) <= Inter {closure S |S. S : I}"
proof-
{ fix y assume "y : Inter I" hence y_def: "!S : I. y : S" by auto
  { fix S assume "S : I" hence "y : closure S" using closure_subset y_def by auto }
  hence "y : Inter {closure S |S. S : I}" by auto
} hence "Inter I <= Inter {closure S |S. S : I}" by auto
moreover have "closed (Inter {closure S |S. S : I})"
  unfolding closed_Inter closed_closure by auto
ultimately show ?thesis using closure_hull[of "Inter I"]
  hull_minimal[of "Inter I" "Inter {closure S |S. S : I}" "closed"] by auto
qed

lemma convex_closure_rel_interior_inter:
assumes "!S : I. convex (S :: ('n::euclidean_space) set)"
assumes "Inter {rel_interior S |S. S : I} ~= {}"
shows "Inter {closure S |S. S : I} <= closure (Inter {rel_interior S |S. S : I})"
proof-
obtain x where x_def: "!S : I. x : rel_interior S" using assms by auto
{ fix y assume "y : Inter {closure S |S. S : I}" hence y_def: "!S : I. y : closure S" by auto
  { assume "y = x"
    hence "y : closure (Inter {rel_interior S |S. S : I})"
       using x_def closure_subset[of "Inter {rel_interior S |S. S : I}"] by auto
  }
  moreover
  { assume "y ~= x"
    { fix e :: real assume e_def: "0 < e"
      def e1 == "min 1 (e/norm (y - x))" hence e1_def: "e1>0 & e1<=1 & e1*norm(y-x)<=e"
        using `y ~= x` `e>0` divide_pos_pos[of e] le_divide_eq[of e1 e "norm(y-x)"] by simp
      def z == "y - e1 *\<^sub>R (y - x)"
      { fix S assume "S : I"
        hence "z : rel_interior S" using rel_interior_closure_convex_shrink[of S x y e1]
           assms x_def y_def e1_def z_def by auto
      } hence *: "z : Inter {rel_interior S |S. S : I}" by auto
      have "EX z. z:Inter {rel_interior S |S. S : I} & z ~= y & (dist z y) <= e"
           apply (rule_tac x="z" in exI) using `y ~= x` z_def * e1_def e_def dist_norm[of z y] by simp
    } hence "y islimpt Inter {rel_interior S |S. S : I}" unfolding islimpt_approachable_le by blast
    hence "y : closure (Inter {rel_interior S |S. S : I})" unfolding closure_def by auto
  } ultimately have "y : closure (Inter {rel_interior S |S. S : I})" by auto
} from this show ?thesis by auto
qed


lemma convex_closure_inter:
assumes "!S : I. convex (S :: ('n::euclidean_space) set)"
assumes "Inter {rel_interior S |S. S : I} ~= {}"
shows "closure (Inter I) = Inter {closure S |S. S : I}"
proof-
have "Inter {closure S |S. S : I} <= closure (Inter {rel_interior S |S. S : I})"
  using convex_closure_rel_interior_inter assms by auto
moreover have "closure (Inter {rel_interior S |S. S : I}) <= closure (Inter I)"
    using rel_interior_inter_aux
          closure_mono[of "Inter {rel_interior S |S. S : I}" "Inter I"] by auto
ultimately show ?thesis using closure_inter[of I] by auto
qed

lemma convex_inter_rel_interior_same_closure:
assumes "!S : I. convex (S :: ('n::euclidean_space) set)"
assumes "Inter {rel_interior S |S. S : I} ~= {}"
shows "closure (Inter {rel_interior S |S. S : I}) = closure (Inter I)"
proof-
have "Inter {closure S |S. S : I} <= closure (Inter {rel_interior S |S. S : I})"
  using convex_closure_rel_interior_inter assms by auto
moreover have "closure (Inter {rel_interior S |S. S : I}) <= closure (Inter I)"
    using rel_interior_inter_aux
          closure_mono[of "Inter {rel_interior S |S. S : I}" "Inter I"] by auto
ultimately show ?thesis using closure_inter[of I] by auto
qed

lemma convex_rel_interior_inter:
assumes "!S : I. convex (S :: ('n::euclidean_space) set)"
assumes "Inter {rel_interior S |S. S : I} ~= {}"
shows "rel_interior (Inter I) <= Inter {rel_interior S |S. S : I}"
proof-
have "convex(Inter I)" using assms convex_Inter by auto
moreover have "convex(Inter {rel_interior S |S. S : I})" apply (rule convex_Inter)
   using assms convex_rel_interior by auto
ultimately have "rel_interior (Inter {rel_interior S |S. S : I}) = rel_interior (Inter I)"
   using convex_inter_rel_interior_same_closure assms
   closure_eq_rel_interior_eq[of "Inter {rel_interior S |S. S : I}" "Inter I"] by blast
from this show ?thesis using rel_interior_subset[of "Inter {rel_interior S |S. S : I}"] by auto
qed

lemma convex_rel_interior_finite_inter:
assumes "!S : I. convex (S :: ('n::euclidean_space) set)"
assumes "Inter {rel_interior S |S. S : I} ~= {}"
assumes "finite I"
shows "rel_interior (Inter I) = Inter {rel_interior S |S. S : I}"
proof-
have "Inter I ~= {}" using assms rel_interior_inter_aux[of I] by auto
have "convex (Inter I)" using convex_Inter assms by auto
{ assume "I={}" hence ?thesis using Inter_empty rel_interior_univ2 by auto }
moreover
{ assume "I ~= {}"
{ fix z assume z_def: "z : Inter {rel_interior S |S. S : I}"
  { fix x assume x_def: "x : Inter I"
    { fix S assume S_def: "S : I" hence "z : rel_interior S" "x : S" using z_def x_def by auto
      (*from this obtain e where e_def: "e>1 & (1 - e) *\<^sub>R x + e *\<^sub>R z : S"*)
      hence "EX m. m>1 & (!e. (e>1 & e<=m) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S )"
         using convex_rel_interior_if[of S z] S_def assms hull_subset[of S] by auto
    } from this obtain mS where mS_def: "!S : I. (mS(S) > (1 :: real) &
         (!e. (e>1 & e<=mS(S)) --> (1-e)*\<^sub>R x+ e *\<^sub>R z : S))" by metis
    obtain e where e_def: "e=Min (mS ` I)" by auto
    have "e : (mS ` I)" using e_def assms `I ~= {}` by simp
    hence "e>(1 :: real)" using mS_def by auto
    moreover have "!S : I. e<=mS(S)" using e_def assms by auto
    ultimately have "EX e>1. (1 - e) *\<^sub>R x + e *\<^sub>R z : Inter I" using mS_def by auto
  } hence "z : rel_interior (Inter I)" using convex_rel_interior_iff[of "Inter I" z]
       `Inter I ~= {}` `convex (Inter I)` by auto
} from this have ?thesis using convex_rel_interior_inter[of I] assms by auto
} ultimately show ?thesis by blast
qed

lemma convex_closure_inter_two:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "convex T"
assumes "(rel_interior S) Int (rel_interior T) ~= {}"
shows "closure (S Int T) = (closure S) Int (closure T)"
using convex_closure_inter[of "{S,T}"] assms by auto

lemma convex_rel_interior_inter_two:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "convex T"
assumes "(rel_interior S) Int (rel_interior T) ~= {}"
shows "rel_interior (S Int T) = (rel_interior S) Int (rel_interior T)"
using convex_rel_interior_finite_inter[of "{S,T}"] assms by auto


lemma convex_affine_closure_inter:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "affine T"
assumes "(rel_interior S) Int T ~= {}"
shows "closure (S Int T) = (closure S) Int T"
proof-
have "affine hull T = T" using assms by auto
hence "rel_interior T = T" using rel_interior_univ[of T] by metis
moreover have "closure T = T" using assms affine_closed[of T] by auto
ultimately show ?thesis using convex_closure_inter_two[of S T] assms affine_imp_convex by auto
qed

lemma convex_affine_rel_interior_inter:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "affine T"
assumes "(rel_interior S) Int T ~= {}"
shows "rel_interior (S Int T) = (rel_interior S) Int T"
proof-
have "affine hull T = T" using assms by auto
hence "rel_interior T = T" using rel_interior_univ[of T] by metis
moreover have "closure T = T" using assms affine_closed[of T] by auto
ultimately show ?thesis using convex_rel_interior_inter_two[of S T] assms affine_imp_convex by auto
qed

lemma subset_rel_interior_convex:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "convex T"
assumes "S <= closure T"
assumes "~(S <= rel_frontier T)"
shows "rel_interior S <= rel_interior T"
proof-
have *: "S Int closure T = S" using assms by auto
have "~(rel_interior S <= rel_frontier T)"
     using closure_mono[of "rel_interior S" "rel_frontier T"] closed_rel_frontier[of T]
     closure_closed[of S] convex_closure_rel_interior[of S] closure_subset[of S] assms by auto
hence "(rel_interior S) Int (rel_interior (closure T)) ~= {}"
     using assms rel_frontier_def[of T] rel_interior_subset convex_rel_interior_closure[of T] by auto
hence "rel_interior S Int rel_interior T = rel_interior (S Int closure T)" using assms convex_closure
     convex_rel_interior_inter_two[of S "closure T"] convex_rel_interior_closure[of T] by auto
also have "...=rel_interior (S)" using * by auto
finally show ?thesis by auto
qed


lemma rel_interior_convex_linear_image:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
assumes "linear f"
assumes "convex S"
shows "f ` (rel_interior S) = rel_interior (f ` S)"
proof-
{ assume "S = {}" hence ?thesis using assms rel_interior_empty rel_interior_convex_nonempty by auto }
moreover
{ assume "S ~= {}"
have *: "f ` (rel_interior S) <= f ` S" unfolding image_mono using rel_interior_subset by auto
have "f ` S <= f ` (closure S)" unfolding image_mono using closure_subset by auto
also have "... = f ` (closure (rel_interior S))" using convex_closure_rel_interior assms by auto
also have "... <= closure (f ` (rel_interior S))" using closure_linear_image assms by auto
finally have "closure (f ` S) = closure (f ` rel_interior S)"
   using closure_mono[of "f ` S" "closure (f ` rel_interior S)"] closure_closure
         closure_mono[of "f ` rel_interior S" "f ` S"] * by auto
hence "rel_interior (f ` S) = rel_interior (f ` rel_interior S)" using assms convex_rel_interior
   linear_conv_bounded_linear[of f] convex_linear_image[of S] convex_linear_image[of "rel_interior S"]
   closure_eq_rel_interior_eq[of "f ` S" "f ` rel_interior S"] by auto
hence "rel_interior (f ` S) <= f ` rel_interior S" using rel_interior_subset by auto
moreover
{ fix z assume z_def: "z : f ` rel_interior S"
  from this obtain z1 where z1_def: "z1 : rel_interior S & (f z1 = z)" by auto
  { fix x assume "x : f ` S"
    from this obtain x1 where x1_def: "x1 : S & (f x1 = x)" by auto
    from this obtain e where e_def: "e>1 & (1 - e) *\<^sub>R x1 + e *\<^sub>R z1 : S"
       using convex_rel_interior_iff[of S z1] `convex S` x1_def z1_def by auto
    moreover have "f ((1 - e) *\<^sub>R x1 + e *\<^sub>R z1) = (1 - e) *\<^sub>R x + e *\<^sub>R z"
        using x1_def z1_def `linear f` by (simp add: linear_add_cmul)
    ultimately have "(1 - e) *\<^sub>R x + e *\<^sub>R z : f ` S"
        using imageI[of "(1 - e) *\<^sub>R x1 + e *\<^sub>R z1" S f] by auto
    hence "EX e. (e>1 & (1 - e) *\<^sub>R x + e *\<^sub>R z : f ` S)" using e_def by auto
  } from this have "z : rel_interior (f ` S)" using convex_rel_interior_iff[of "f ` S" z] `convex S`
       `linear f` `S ~= {}` convex_linear_image[of S f]  linear_conv_bounded_linear[of f] by auto
} ultimately have ?thesis by auto
} ultimately show ?thesis by blast
qed


lemma convex_linear_preimage:
  assumes c:"convex S" and l:"bounded_linear f"
  shows "convex(f -` S)"
proof(auto simp add: convex_def)
  interpret f: bounded_linear f by fact
  fix x y assume xy:"f x : S" "f y : S"
  fix u v ::real assume uv:"0 <= u" "0 <= v" "u + v = 1"
  show "f (u *\<^sub>R x + v *\<^sub>R y) : S" unfolding image_iff
    using bexI[of _ "u *\<^sub>R x + v *\<^sub>R y"] f.add f.scaleR
      c[unfolded convex_def] xy uv by auto
qed


lemma rel_interior_convex_linear_preimage:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
assumes "linear f"
assumes "convex S"
assumes "f -` (rel_interior S) ~= {}"
shows "rel_interior (f -` S) = f -` (rel_interior S)"
proof-
have "S ~= {}" using assms rel_interior_empty by auto
have nonemp: "f -` S ~= {}" by (metis assms(3) rel_interior_subset subset_empty vimage_mono)
hence "S Int (range f) ~= {}" by auto
have conv: "convex (f -` S)" using convex_linear_preimage assms linear_conv_bounded_linear by auto
hence "convex (S Int (range f))"
  by (metis assms(1) assms(2) convex_Int subspace_UNIV subspace_imp_convex subspace_linear_image)
{ fix z assume "z : f -` (rel_interior S)"
  hence z_def: "f z : rel_interior S" by auto
  { fix x assume "x : f -` S" from this have x_def: "f x : S" by auto
    from this obtain e where e_def: "e>1 & (1-e)*\<^sub>R (f x)+ e *\<^sub>R (f z) : S"
      using convex_rel_interior_iff[of S "f z"] z_def assms `S ~= {}` by auto
    moreover have "(1-e)*\<^sub>R (f x)+ e *\<^sub>R (f z) = f ((1-e)*\<^sub>R x + e *\<^sub>R z)"
      using `linear f` by (simp add: linear_def)
    ultimately have "EX e. e>1 & (1-e)*\<^sub>R x + e *\<^sub>R z : f -` S" using e_def by auto
  } hence "z : rel_interior (f -` S)"
       using convex_rel_interior_iff[of "f -` S" z] conv nonemp by auto
}
moreover
{ fix z assume z_def: "z : rel_interior (f -` S)"
  { fix x assume x_def: "x: S Int (range f)"
    from this obtain y where y_def: "(f y = x) & (y : f -` S)" by auto
    from this obtain e where e_def: "e>1 & (1-e)*\<^sub>R y+ e *\<^sub>R z : f -` S"
      using convex_rel_interior_iff[of "f -` S" z] z_def conv by auto
    moreover have "(1-e)*\<^sub>R x+ e *\<^sub>R (f z) = f ((1-e)*\<^sub>R y + e *\<^sub>R z)"
      using `linear f` y_def by (simp add: linear_def)
    ultimately have "EX e. e>1 & (1-e)*\<^sub>R x + e *\<^sub>R (f z) : S Int (range f)"
      using e_def by auto
  } hence "f z : rel_interior (S Int (range f))" using `convex (S Int (range f))`
    `S Int (range f) ~= {}` convex_rel_interior_iff[of "S Int (range f)" "f z"] by auto
  moreover have "affine (range f)"
    by (metis assms(1) subspace_UNIV subspace_imp_affine subspace_linear_image)
  ultimately have "f z : rel_interior S"
    using convex_affine_rel_interior_inter[of S "range f"] assms by auto
  hence "z : f -` (rel_interior S)" by auto
}
ultimately show ?thesis by auto
qed


lemma convex_direct_sum:
fixes S :: "('n::euclidean_space) set"
fixes T :: "('m::euclidean_space) set"
assumes "convex S" "convex T"
shows "convex (S <*> T)"
proof-
{
fix x assume "x : S <*> T"
from this obtain xs xt where xst_def: "xs : S & xt : T & (xs,xt) = x" by auto
fix y assume "y : S <*> T"
from this obtain ys yt where yst_def: "ys : S & yt : T & (ys,yt) = y" by auto
fix u v assume uv_def: "(u :: real)>=0 & (v :: real)>=0 & u+v=1"
have "u *\<^sub>R x + v *\<^sub>R y = (u *\<^sub>R xs + v *\<^sub>R ys, u *\<^sub>R xt + v *\<^sub>R yt)" using xst_def yst_def by auto
moreover have "u *\<^sub>R xs + v *\<^sub>R ys : S"
   using uv_def xst_def yst_def convex_def[of S] assms by auto
moreover have "u *\<^sub>R xt + v *\<^sub>R yt : T"
   using uv_def xst_def yst_def convex_def[of T] assms by auto
ultimately have "u *\<^sub>R x + v *\<^sub>R y : S <*> T" by auto
} from this show ?thesis unfolding convex_def by auto
qed


lemma convex_hull_direct_sum:
fixes S :: "('n::euclidean_space) set"
fixes T :: "('m::euclidean_space) set"
shows "convex hull (S <*> T) = (convex hull S) <*> (convex hull T)"
proof-
{ fix x assume "x : (convex hull S) <*> (convex hull T)"
  from this obtain xs xt where xst_def: "xs : convex hull S & xt : convex hull T & (xs,xt) = x" by auto
  from xst_def obtain sI su where s: "finite sI & sI <= S & (ALL x:sI. 0 <= su x) & setsum su sI = 1
     & (SUM v:sI. su v *\<^sub>R v) = xs" using convex_hull_explicit[of S] by auto
  from xst_def obtain tI tu where t: "finite tI & tI <= T & (ALL x:tI. 0 <= tu x) & setsum tu tI = 1
     & (SUM v:tI. tu v *\<^sub>R v) = xt" using convex_hull_explicit[of T] by auto
  def I == "(sI <*> tI)"
  def u == "(%i. (su (fst i))*(tu(snd i)))"
  have "fst (SUM v:sI <*> tI. (su (fst v) * tu (snd v)) *\<^sub>R v)=
     (SUM vs:sI. SUM vt:tI. (su vs * tu vt) *\<^sub>R vs)"
     using fst_setsum[of "(%v. (su (fst v) * tu (snd v)) *\<^sub>R v)" "sI <*> tI"]
     by (simp add: split_def scaleR_prod_def setsum_cartesian_product)
  also have "...=(SUM vt:tI. tu vt *\<^sub>R (SUM vs:sI. su vs *\<^sub>R vs))"
     using setsum_commute[of "(%vt vs. (su vs * tu vt) *\<^sub>R vs)" sI tI]
     by (simp add: mult_commute scaleR_right.setsum)
  also have "...=(SUM vt:tI. tu vt *\<^sub>R xs)" using s by auto
  also have "...=(SUM vt:tI. tu vt) *\<^sub>R xs" by (simp add: scaleR_left.setsum)
  also have "...=xs" using t by auto
  finally have h1: "fst (SUM v:sI <*> tI. (su (fst v) * tu (snd v)) *\<^sub>R v)=xs" by auto
  have "snd (SUM v:sI <*> tI. (su (fst v) * tu (snd v)) *\<^sub>R v)=
     (SUM vs:sI. SUM vt:tI. (su vs * tu vt) *\<^sub>R vt)"
     using snd_setsum[of "(%v. (su (fst v) * tu (snd v)) *\<^sub>R v)" "sI <*> tI"]
     by (simp add: split_def scaleR_prod_def setsum_cartesian_product)
  also have "...=(SUM vs:sI. su vs *\<^sub>R (SUM vt:tI. tu vt *\<^sub>R vt))"
     by (simp add: mult_commute scaleR_right.setsum)
  also have "...=(SUM vs:sI. su vs *\<^sub>R xt)" using t by auto
  also have "...=(SUM vs:sI. su vs) *\<^sub>R xt" by (simp add: scaleR_left.setsum)
  also have "...=xt" using s by auto
  finally have h2: "snd (SUM v:sI <*> tI. (su (fst v) * tu (snd v)) *\<^sub>R v)=xt" by auto
  from h1 h2 have "(SUM v:sI <*> tI. (su (fst v) * tu (snd v)) *\<^sub>R v) = x" using xst_def by auto

  moreover have "finite I & (I <= S <*> T)" using s t I_def by auto
  moreover have "!i:I. 0 <= u i" using s t I_def u_def by (simp add: mult_nonneg_nonneg)
  moreover have "setsum u I = 1" using u_def I_def setsum_cartesian_product[of "(% x y. (su x)*(tu y))"]
     s t setsum_product[of su sI tu tI] by (auto simp add: split_def)
  ultimately have "x : convex hull (S <*> T)"
     apply (subst convex_hull_explicit[of "S <*> T"]) apply rule
     apply (rule_tac x="I" in exI) apply (rule_tac x="u" in exI)
     using I_def u_def by auto
}
hence "convex hull (S <*> T) >= (convex hull S) <*> (convex hull T)" by auto
moreover have "convex ((convex hull S) <*> (convex hull T))"
   by (simp add: convex_direct_sum convex_convex_hull)
ultimately show ?thesis
   using hull_minimal[of "S <*> T" "(convex hull S) <*> (convex hull T)" "convex"]
         hull_subset[of S convex] hull_subset[of T convex] by auto
qed

lemma rel_interior_direct_sum:
fixes S :: "('n::euclidean_space) set"
fixes T :: "('m::euclidean_space) set"
assumes "convex S" "convex T"
shows "rel_interior (S <*> T) = rel_interior S <*> rel_interior T"
proof-
{ assume "S={}" hence ?thesis apply auto using rel_interior_empty by auto }
moreover
{ assume "T={}" hence ?thesis apply auto using rel_interior_empty by auto }
moreover {
assume "S ~={}" "T ~={}"
hence ri: "rel_interior S ~= {}" "rel_interior T ~= {}" using rel_interior_convex_nonempty assms by auto
hence "fst -` rel_interior S ~= {}" using fst_vimage_eq_Times[of "rel_interior S"] by auto
hence "rel_interior ((fst :: 'n * 'm => 'n) -` S) = fst -` rel_interior S"
  using fst_linear `convex S` rel_interior_convex_linear_preimage[of fst S] by auto
hence s: "rel_interior (S <*> (UNIV :: 'm set)) = rel_interior S <*> UNIV" by (simp add: fst_vimage_eq_Times)
from ri have "snd -` rel_interior T ~= {}" using snd_vimage_eq_Times[of "rel_interior T"] by auto
hence "rel_interior ((snd :: 'n * 'm => 'm) -` T) = snd -` rel_interior T"
  using snd_linear `convex T` rel_interior_convex_linear_preimage[of snd T] by auto
hence t: "rel_interior ((UNIV :: 'n set) <*> T) = UNIV <*> rel_interior T" by (simp add: snd_vimage_eq_Times)
from s t have *: "rel_interior (S <*> (UNIV :: 'm set)) Int rel_interior ((UNIV :: 'n set) <*> T)
  = rel_interior S <*> rel_interior T" by auto
have "(S <*> T) = (S <*> (UNIV :: 'm set)) Int ((UNIV :: 'n set) <*> T)" by auto
hence "rel_interior (S <*> T) = rel_interior ((S <*> (UNIV :: 'm set)) Int ((UNIV :: 'n set) <*> T))" by auto
also have "...=rel_interior (S <*> (UNIV :: 'm set)) Int rel_interior ((UNIV :: 'n set) <*> T)"
   apply (subst convex_rel_interior_inter_two[of "S <*> (UNIV :: 'm set)" "(UNIV :: 'n set) <*> T"])
   using * ri assms convex_direct_sum by auto
finally have ?thesis using * by auto
}
ultimately show ?thesis by blast
qed

lemma rel_interior_scaleR:
fixes S :: "('n::euclidean_space) set"
assumes "c ~= 0"
shows "(op *\<^sub>R c) ` (rel_interior S) = rel_interior ((op *\<^sub>R c) ` S)"
using rel_interior_injective_linear_image[of "(op *\<^sub>R c)" S]
      linear_conv_bounded_linear[of "op *\<^sub>R c"] linear_scaleR injective_scaleR[of c] assms by auto

lemma rel_interior_convex_scaleR:
fixes S :: "('n::euclidean_space) set"
assumes "convex S"
shows "(op *\<^sub>R c) ` (rel_interior S) = rel_interior ((op *\<^sub>R c) ` S)"
by (metis assms linear_scaleR rel_interior_convex_linear_image)

lemma convex_rel_open_scaleR:
fixes S :: "('n::euclidean_space) set"
assumes "convex S" "rel_open S"
shows "convex ((op *\<^sub>R c) ` S) & rel_open ((op *\<^sub>R c) ` S)"
by (metis assms convex_scaling rel_interior_convex_scaleR rel_open_def)


lemma convex_rel_open_finite_inter:
assumes "!S : I. (convex (S :: ('n::euclidean_space) set) & rel_open S)"
assumes "finite I"
shows "convex (Inter I) & rel_open (Inter I)"
proof-
{ assume "Inter {rel_interior S |S. S : I} = {}"
  hence "Inter I = {}" using assms unfolding rel_open_def by auto
  hence ?thesis unfolding rel_open_def using rel_interior_empty by auto
}
moreover
{ assume "Inter {rel_interior S |S. S : I} ~= {}"
  hence "rel_open (Inter I)" using assms unfolding rel_open_def
    using convex_rel_interior_finite_inter[of I] by auto
  hence ?thesis using convex_Inter assms by auto
} ultimately show ?thesis by auto
qed

lemma convex_rel_open_linear_image:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
assumes "linear f"
assumes "convex S" "rel_open S"
shows "convex (f ` S) & rel_open (f ` S)"
by (metis assms convex_linear_image rel_interior_convex_linear_image
   linear_conv_bounded_linear rel_open_def)

lemma convex_rel_open_linear_preimage:
fixes f :: "('m::euclidean_space) => ('n::euclidean_space)"
assumes "linear f"
assumes "convex S" "rel_open S"
shows "convex (f -` S) & rel_open (f -` S)"
proof-
{ assume "f -` (rel_interior S) = {}"
  hence "f -` S = {}" using assms unfolding rel_open_def by auto
  hence ?thesis unfolding rel_open_def using rel_interior_empty by auto
}
moreover
{ assume "f -` (rel_interior S) ~= {}"
  hence "rel_open (f -` S)" using assms unfolding rel_open_def
    using rel_interior_convex_linear_preimage[of f S] by auto
  hence ?thesis using convex_linear_preimage assms linear_conv_bounded_linear by auto
} ultimately show ?thesis by auto
qed

lemma rel_interior_projection:
fixes S :: "('m::euclidean_space*'n::euclidean_space) set"
fixes f :: "'m::euclidean_space => ('n::euclidean_space) set"
assumes "convex S"
assumes "f = (%y. {z. (y,z) : S})"
shows "(y,z) : rel_interior S <-> (y : rel_interior {y. (f y ~= {})} & z : rel_interior (f y))"
proof-
{ fix y assume "y : {y. (f y ~= {})}" from this obtain z where "(y,z) : S" using assms by auto
  hence "EX x. x : S & y = fst x" apply (rule_tac x="(y,z)" in exI) by auto
  from this obtain x where "x : S & y = fst x" by blast
  hence "y : fst ` S" unfolding image_def by auto
}
hence "fst ` S = {y. (f y ~= {})}" unfolding fst_def using assms by auto
hence h1: "fst ` rel_interior S = rel_interior {y. (f y ~= {})}"
   using rel_interior_convex_linear_image[of fst S] assms fst_linear by auto
{ fix y assume "y : rel_interior {y. (f y ~= {})}"
  hence "y : fst ` rel_interior S" using h1 by auto
  hence *: "rel_interior S Int fst -` {y} ~= {}" by auto
  moreover have aff: "affine (fst -` {y})" unfolding affine_alt by (simp add: algebra_simps)
  ultimately have **: "rel_interior (S Int fst -` {y}) = rel_interior S Int fst -` {y}"
    using convex_affine_rel_interior_inter[of S "fst -` {y}"] assms by auto
  have conv: "convex (S Int fst -` {y})" using convex_Int assms aff affine_imp_convex by auto
  { fix x assume "x : f y"
    hence "(y,x) : S Int (fst -` {y})" using assms by auto
    moreover have "x = snd (y,x)" by auto
    ultimately have "x : snd ` (S Int fst -` {y})" by blast
  }
  hence "snd ` (S Int fst -` {y}) = f y" using assms by auto
  hence ***: "rel_interior (f y) = snd ` rel_interior (S Int fst -` {y})"
    using rel_interior_convex_linear_image[of snd "S Int fst -` {y}"] snd_linear conv by auto
  { fix z assume "z : rel_interior (f y)"
    hence "z : snd ` rel_interior (S Int fst -` {y})" using *** by auto
    moreover have "{y} = fst ` rel_interior (S Int fst -` {y})" using * ** rel_interior_subset by auto
    ultimately have "(y,z) : rel_interior (S Int fst -` {y})" by force
    hence "(y,z) : rel_interior S" using ** by auto
  }
  moreover
  { fix z assume "(y,z) : rel_interior S"
    hence "(y,z) : rel_interior (S Int fst -` {y})" using ** by auto
    hence "z : snd ` rel_interior (S Int fst -` {y})" by (metis Range_iff snd_eq_Range)
    hence "z : rel_interior (f y)" using *** by auto
  }
  ultimately have "!!z. (y,z) : rel_interior S <-> z : rel_interior (f y)" by auto
}
hence h2: "!!y z. y : rel_interior {t. f t ~= {}} ==> ((y, z) : rel_interior S) = (z : rel_interior (f y))"
  by auto
{ fix y z assume asm: "(y, z) : rel_interior S"
  hence "y : fst ` rel_interior S" by (metis Domain_iff fst_eq_Domain)
  hence "y : rel_interior {t. f t ~= {}}" using h1 by auto
  hence "y : rel_interior {t. f t ~= {}} & (z : rel_interior (f y))" using h2 asm by auto
} from this show ?thesis using h2 by blast
qed

subsubsection {* Relative interior of convex cone *}

lemma cone_rel_interior:
fixes S :: "('m::euclidean_space) set"
assumes "cone S"
shows "cone ({0} Un (rel_interior S))"
proof-
{ assume "S = {}" hence ?thesis by (simp add: rel_interior_empty cone_0) }
moreover
{ assume "S ~= {}" hence *: "0:S & (!c. c>0 --> op *\<^sub>R c ` S = S)" using cone_iff[of S] assms by auto
  hence *: "0:({0} Un (rel_interior S)) &
           (!c. c>0 --> op *\<^sub>R c ` ({0} Un rel_interior S) = ({0} Un rel_interior S))"
           by (auto simp add: rel_interior_scaleR)
  hence ?thesis using cone_iff[of "{0} Un rel_interior S"] by auto
}
ultimately show ?thesis by blast
qed

lemma rel_interior_convex_cone_aux:
fixes S :: "('m::euclidean_space) set"
assumes "convex S"
shows "(c,x) : rel_interior (cone hull ({(1 :: real)} <*> S)) <->
       c>0 & x : ((op *\<^sub>R c) ` (rel_interior S))"
proof-
{ assume "S={}" hence ?thesis by (simp add: rel_interior_empty cone_hull_empty) }
moreover
{ assume "S ~= {}" from this obtain s where "s : S" by auto
have conv: "convex ({(1 :: real)} <*> S)" using convex_direct_sum[of "{(1 :: real)}" S]
   assms convex_singleton[of "1 :: real"] by auto
def f == "(%y. {z. (y,z) : cone hull ({(1 :: real)} <*> S)})"
hence *: "(c, x) : rel_interior (cone hull ({(1 :: real)} <*> S)) =
      (c : rel_interior {y. f y ~= {}} & x : rel_interior (f c))"
  apply (subst rel_interior_projection[of "cone hull ({(1 :: real)} <*> S)" f c x])
  using convex_cone_hull[of "{(1 :: real)} <*> S"] conv by auto
{ fix y assume "(y :: real)>=0"
  hence "y *\<^sub>R (1,s) : cone hull ({(1 :: real)} <*> S)"
     using cone_hull_expl[of "{(1 :: real)} <*> S"] `s:S` by auto
  hence "f y ~= {}" using f_def by auto
}
hence "{y. f y ~= {}} = {0..}" using f_def cone_hull_expl[of "{(1 :: real)} <*> S"] by auto
hence **: "rel_interior {y. f y ~= {}} = {0<..}" using rel_interior_real_semiline by auto
{ fix c assume "c>(0 :: real)"
  hence "f c = (op *\<^sub>R c ` S)" using f_def cone_hull_expl[of "{(1 :: real)} <*> S"] by auto
  hence "rel_interior (f c)= (op *\<^sub>R c ` rel_interior S)"
     using rel_interior_convex_scaleR[of S c] assms by auto
}
hence ?thesis using * ** by auto
} ultimately show ?thesis by blast
qed


lemma rel_interior_convex_cone:
fixes S :: "('m::euclidean_space) set"
assumes "convex S"
shows "rel_interior (cone hull ({(1 :: real)} <*> S)) =
       {(c,c *\<^sub>R x) |c x. c>0 & x : (rel_interior S)}"
(is "?lhs=?rhs")
proof-
{ fix z assume "z:?lhs"
  have *: "z=(fst z,snd z)" by auto
  have "z:?rhs" using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms `z:?lhs` apply auto
     apply (rule_tac x="fst z" in exI) apply (rule_tac x="x" in exI) using * by auto
}
moreover
{ fix z assume "z:?rhs" hence "z:?lhs"
  using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms by auto
}
ultimately show ?thesis by blast
qed

lemma convex_hull_finite_union:
assumes "finite I"
assumes "!i:I. (convex (S i) & (S i) ~= {})"
shows "convex hull (Union (S ` I)) =
       {setsum (%i. c i *\<^sub>R s i) I |c s. (!i:I. c i >= 0) & (setsum c I = 1) & (!i:I. s i : S i)}"
  (is "?lhs = ?rhs")
proof-
{ fix x assume "x : ?rhs"
  from this obtain c s
    where *: "setsum (%i. c i *\<^sub>R s i) I=x" "(setsum c I = 1)"
     "(!i:I. c i >= 0) & (!i:I. s i : S i)" by auto
  hence "!i:I. s i : convex hull (Union (S ` I))" using hull_subset[of "Union (S ` I)" convex] by auto
  hence "x : ?lhs" unfolding *(1)[symmetric]
     apply (subst convex_setsum[of I "convex hull Union (S ` I)" c s])
     using * assms convex_convex_hull by auto
} hence "?lhs >= ?rhs" by auto

{ fix i assume "i:I"
    from this assms have "EX p. p : S i" by auto
}
from this obtain p where p_def: "!i:I. p i : S i" by metis

{ fix i assume "i:I"
  { fix x assume "x : S i"
    def c == "(%j. if (j=i) then (1::real) else 0)"
    hence *: "setsum c I = 1" using `finite I` `i:I` setsum_delta[of I i "(%(j::'a). (1::real))"] by auto
    def s == "(%j. if (j=i) then x else p j)"
    hence "!j. c j *\<^sub>R s j = (if (j=i) then x else 0)" using c_def by (auto simp add: algebra_simps)
    hence "x = setsum (%i. c i *\<^sub>R s i) I"
       using s_def c_def `finite I` `i:I` setsum_delta[of I i "(%(j::'a). x)"] by auto
    hence "x : ?rhs" apply auto
      apply (rule_tac x="c" in exI)
      apply (rule_tac x="s" in exI) using * c_def s_def p_def `x : S i` by auto
  } hence "?rhs >= S i" by auto
} hence *: "?rhs >= Union (S ` I)" by auto

{ fix u v assume uv: "(u :: real)>=0 & v>=0 & u+v=1"
  fix x y assume xy: "(x : ?rhs) & (y : ?rhs)"
  from xy obtain c s where xc: "x=setsum (%i. c i *\<^sub>R s i) I &
     (!i:I. c i >= 0) & (setsum c I = 1) & (!i:I. s i : S i)" by auto
  from xy obtain d t where yc: "y=setsum (%i. d i *\<^sub>R t i) I &
     (!i:I. d i >= 0) & (setsum d I = 1) & (!i:I. t i : S i)" by auto
  def e == "(%i. u * (c i)+v * (d i))"
  have ge0: "!i:I. e i >= 0"  using e_def xc yc uv by (simp add: mult_nonneg_nonneg)
  have "setsum (%i. u * c i) I = u * setsum c I" by (simp add: setsum_right_distrib)
  moreover have "setsum (%i. v * d i) I = v * setsum d I" by (simp add: setsum_right_distrib)
  ultimately have sum1: "setsum e I = 1" using e_def xc yc uv by (simp add: setsum_addf)
  def q == "(%i. if (e i = 0) then (p i)
                 else (u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i))"
  { fix i assume "i:I"
    { assume "e i = 0" hence "q i : S i" using `i:I` p_def q_def by auto }
    moreover
    { assume "e i ~= 0"
      hence "q i : S i" using mem_convex_alt[of "S i" "s i" "t i" "u * (c i)" "v * (d i)"]
         mult_nonneg_nonneg[of u "c i"] mult_nonneg_nonneg[of v "d i"]
         assms q_def e_def `i:I` `e i ~= 0` xc yc uv by auto
    } ultimately have "q i : S i" by auto
  } hence qs: "!i:I. q i : S i" by auto
  { fix i assume "i:I"
    { assume "e i = 0"
      have ge: "u * (c i) >= 0 & v * (d i) >= 0" using xc yc uv `i:I` by (simp add: mult_nonneg_nonneg)
      moreover hence "u * (c i) <= 0 & v * (d i) <= 0" using `e i = 0` e_def `i:I` by simp
      ultimately have "u * (c i) = 0 & v * (d i) = 0" by auto
      hence "(u * (c i))*\<^sub>R (s i)+(v * (d i))*\<^sub>R (t i) = (e i) *\<^sub>R (q i)"
         using `e i = 0` by auto
    }
    moreover
    { assume "e i ~= 0"
      hence "(u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i) = q i"
         using q_def by auto
      hence "e i *\<^sub>R ((u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i))
             = (e i) *\<^sub>R (q i)" by auto
      hence "(u * (c i))*\<^sub>R (s i)+(v * (d i))*\<^sub>R (t i) = (e i) *\<^sub>R (q i)"
         using `e i ~= 0` by (simp add: algebra_simps)
    } ultimately have
      "(u * (c i))*\<^sub>R (s i)+(v * (d i))*\<^sub>R (t i) = (e i) *\<^sub>R (q i)" by blast
  } hence *: "!i:I.
    (u * (c i))*\<^sub>R (s i)+(v * (d i))*\<^sub>R (t i) = (e i) *\<^sub>R (q i)" by auto
  have "u *\<^sub>R x + v *\<^sub>R y =
       setsum (%i. (u * (c i))*\<^sub>R (s i)+(v * (d i))*\<^sub>R (t i)) I"
          using xc yc by (simp add: algebra_simps scaleR_right.setsum setsum_addf)
  also have "...=setsum (%i. (e i) *\<^sub>R (q i)) I" using * by auto
  finally have "u *\<^sub>R x + v *\<^sub>R y = setsum (%i. (e i) *\<^sub>R (q i)) I" by auto
  hence "u *\<^sub>R x + v *\<^sub>R y : ?rhs" using ge0 sum1 qs by auto
} hence "convex ?rhs" unfolding convex_def by auto
from this show ?thesis using `?lhs >= ?rhs` *
   hull_minimal[of "Union (S ` I)" "?rhs" "convex"] by blast
qed

lemma convex_hull_union_two:
fixes S T :: "('m::euclidean_space) set"
assumes "convex S" "S ~= {}" "convex T" "T ~= {}"
shows "convex hull (S Un T) = {u *\<^sub>R s + v *\<^sub>R t |u v s t. u>=0 & v>=0 & u+v=1 & s:S & t:T}"
  (is "?lhs = ?rhs")
proof-
def I == "{(1::nat),2}"
def s == "(%i. (if i=(1::nat) then S else T))"
have "Union (s ` I) = S Un T" using s_def I_def by auto
hence "convex hull (Union (s ` I)) = convex hull (S Un T)" by auto
moreover have "convex hull Union (s ` I) =
    {SUM i:I. c i *\<^sub>R sa i |c sa. (ALL i:I. 0 <= c i) & setsum c I = 1 & (ALL i:I. sa i : s i)}"
    apply (subst convex_hull_finite_union[of I s]) using assms s_def I_def by auto
moreover have
  "{SUM i:I. c i *\<^sub>R sa i |c sa. (ALL i:I. 0 <= c i) & setsum c I = 1 & (ALL i:I. sa i : s i)} <=
  ?rhs"
  using s_def I_def by auto
ultimately have "?lhs<=?rhs" by auto
{ fix x assume "x : ?rhs"
  from this obtain u v s t
    where *: "x=u *\<^sub>R s + v *\<^sub>R t & u>=0 & v>=0 & u+v=1 & s:S & t:T" by auto
  hence "x : convex hull {s,t}" using convex_hull_2[of s t] by auto
  hence "x : convex hull (S Un T)" using * hull_mono[of "{s, t}" "S Un T"] by auto
} hence "?lhs >= ?rhs" by blast
from this show ?thesis using `?lhs<=?rhs` by auto
qed

subsection {* Convexity on direct sums *}

lemma closure_sum:
  fixes S T :: "('n::euclidean_space) set"
  shows "closure S + closure T \<subseteq> closure (S + T)"
proof-
  have "(closure S) + (closure T) = (\<lambda>(x,y). x + y) ` (closure S \<times> closure T)"
    by (simp add: set_plus_image)
  also have "... = (\<lambda>(x,y). x + y) ` closure (S \<times> T)"
    using closure_direct_sum by auto
  also have "... \<subseteq> closure (S + T)"
    using fst_snd_linear closure_linear_image[of "(\<lambda>(x,y). x + y)" "S \<times> T"]
    by (auto simp: set_plus_image)
  finally show ?thesis
    by auto
qed

lemma convex_oplus:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "convex T"
shows "convex (S + T)"
proof-
have "{x + y |x y. x : S & y : T} = {c. EX a:S. EX b:T. c = a + b}" by auto
thus ?thesis unfolding set_plus_def using convex_sums[of S T] assms by auto
qed

lemma convex_hull_sum:
fixes S T :: "('n::euclidean_space) set"
shows "convex hull (S + T) = (convex hull S) + (convex hull T)"
proof-
have "(convex hull S) + (convex hull T) =
      (%(x,y). x + y) ` ((convex hull S) <*> (convex hull T))"
   by (simp add: set_plus_image)
also have "... = (%(x,y). x + y) ` (convex hull (S <*> T))" using convex_hull_direct_sum by auto
also have "...= convex hull (S + T)" using fst_snd_linear linear_conv_bounded_linear
   convex_hull_linear_image[of "(%(x,y). x + y)" "S <*> T"] by (auto simp add: set_plus_image)
finally show ?thesis by auto
qed

lemma rel_interior_sum:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "convex T"
shows "rel_interior (S + T) = (rel_interior S) + (rel_interior T)"
proof-
have "(rel_interior S) + (rel_interior T) = (%(x,y). x + y) ` (rel_interior S <*> rel_interior T)"
   by (simp add: set_plus_image)
also have "... = (%(x,y). x + y) ` rel_interior (S <*> T)" using rel_interior_direct_sum assms by auto
also have "...= rel_interior (S + T)" using fst_snd_linear convex_direct_sum assms
   rel_interior_convex_linear_image[of "(%(x,y). x + y)" "S <*> T"] by (auto simp add: set_plus_image)
finally show ?thesis by auto
qed

lemma convex_sum_gen:
  fixes S :: "'a \<Rightarrow> 'n::euclidean_space set"
  assumes "\<And>i. i \<in> I \<Longrightarrow> (convex (S i))"
  shows "convex (setsum S I)"
proof cases
  assume "finite I" from this assms show ?thesis
    by induct (auto simp: convex_oplus)
qed auto

lemma convex_hull_sum_gen:
fixes S :: "'a => ('n::euclidean_space) set"
shows "convex hull (setsum S I) = setsum (%i. (convex hull (S i))) I"
apply (subst setsum_set_linear) using convex_hull_sum convex_hull_singleton by auto


lemma rel_interior_sum_gen:
fixes S :: "'a => ('n::euclidean_space) set"
assumes "!i:I. (convex (S i))"
shows "rel_interior (setsum S I) = setsum (%i. (rel_interior (S i))) I"
apply (subst setsum_set_cond_linear[of convex])
  using rel_interior_sum rel_interior_sing[of "0"] assms by (auto simp add: convex_oplus)

lemma convex_rel_open_direct_sum:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "rel_open S" "convex T" "rel_open T"
shows "convex (S <*> T) & rel_open (S <*> T)"
by (metis assms convex_direct_sum rel_interior_direct_sum rel_open_def)

lemma convex_rel_open_sum:
fixes S T :: "('n::euclidean_space) set"
assumes "convex S" "rel_open S" "convex T" "rel_open T"
shows "convex (S + T) & rel_open (S + T)"
by (metis assms convex_oplus rel_interior_sum rel_open_def)

lemma convex_hull_finite_union_cones:
assumes "finite I" "I ~= {}"
assumes "!i:I. (convex (S i) & cone (S i) & (S i) ~= {})"
shows "convex hull (Union (S ` I)) = setsum S I"
  (is "?lhs = ?rhs")
proof-
{ fix x assume "x : ?lhs"
  from this obtain c xs where x_def: "x=setsum (%i. c i *\<^sub>R xs i) I &
     (!i:I. c i >= 0) & (setsum c I = 1) & (!i:I. xs i : S i)"
     using convex_hull_finite_union[of I S] assms by auto
  def s == "(%i. c i *\<^sub>R xs i)"
  { fix i assume "i:I"
    hence "s i : S i" using s_def x_def assms mem_cone[of "S i" "xs i" "c i"] by auto
  } hence "!i:I. s i : S i" by auto
  moreover have "x = setsum s I" using x_def s_def by auto
  ultimately have "x : ?rhs" using set_setsum_alt[of I S] assms by auto
}
moreover
{ fix x assume "x : ?rhs"
  from this obtain s where x_def: "x=setsum s I & (!i:I. s i : S i)"
     using set_setsum_alt[of I S] assms by auto
  def xs == "(%i. of_nat(card I) *\<^sub>R s i)"
  hence "x=setsum (%i. ((1 :: real)/of_nat(card I)) *\<^sub>R xs i) I" using x_def assms by auto
  moreover have "!i:I. xs i : S i" using x_def xs_def assms by (simp add: cone_def)
  moreover have "(!i:I. (1 :: real)/of_nat(card I) >= 0)" by auto
  moreover have "setsum (%i. (1 :: real)/of_nat(card I)) I = 1" using assms by auto
  ultimately have "x : ?lhs" apply (subst convex_hull_finite_union[of I S])
    using assms apply blast
    using assms apply blast
    apply rule apply (rule_tac x="(%i. (1 :: real)/of_nat(card I))" in exI) by auto
} ultimately show ?thesis by auto
qed

lemma convex_hull_union_cones_two:
fixes S T :: "('m::euclidean_space) set"
assumes "convex S" "cone S" "S ~= {}"
assumes "convex T" "cone T" "T ~= {}"
shows "convex hull (S Un T) = S + T"
proof-
def I == "{(1::nat),2}"
def A == "(%i. (if i=(1::nat) then S else T))"
have "Union (A ` I) = S Un T" using A_def I_def by auto
hence "convex hull (Union (A ` I)) = convex hull (S Un T)" by auto
moreover have "convex hull Union (A ` I) = setsum A I"
    apply (subst convex_hull_finite_union_cones[of I A]) using assms A_def I_def by auto
moreover have
  "setsum A I = S + T" using A_def I_def
     unfolding set_plus_def apply auto unfolding set_plus_def by auto
ultimately show ?thesis by auto
qed

lemma rel_interior_convex_hull_union:
fixes S :: "'a => ('n::euclidean_space) set"
assumes "finite I"
assumes "!i:I. convex (S i) & (S i) ~= {}"
shows "rel_interior (convex hull (Union (S ` I))) =  {setsum (%i. c i *\<^sub>R s i) I
       |c s. (!i:I. c i > 0) & (setsum c I = 1) & (!i:I. s i : rel_interior(S i))}"
(is "?lhs=?rhs")
proof-
{ assume "I={}" hence ?thesis using convex_hull_empty rel_interior_empty by auto }
moreover
{ assume "I ~= {}"
  def C0 == "convex hull (Union (S ` I))"
  have "!i:I. C0 >= S i" unfolding C0_def using hull_subset[of "Union (S ` I)"] by auto
  def K0 == "cone hull ({(1 :: real)} <*> C0)"
  def K == "(%i. cone hull ({(1 :: real)} <*> (S i)))"
  have "!i:I. K i ~= {}" unfolding K_def using assms by (simp add: cone_hull_empty_iff[symmetric])
  { fix i assume "i:I"
    hence "convex (K i)" unfolding K_def apply (subst convex_cone_hull) apply (subst convex_direct_sum)
    using assms by auto
  }
  hence convK: "!i:I. convex (K i)" by auto
  { fix i assume "i:I"
    hence "K0 >= K i" unfolding K0_def K_def apply (subst hull_mono) using `!i:I. C0 >= S i` by auto
  }
  hence "K0 >= Union (K ` I)" by auto
  moreover have "convex K0" unfolding K0_def
     apply (subst convex_cone_hull) apply (subst convex_direct_sum)
     unfolding C0_def using convex_convex_hull by auto
  ultimately have geq: "K0 >= convex hull (Union (K ` I))" using hull_minimal[of _ "K0" "convex"] by blast
  have "!i:I. K i >= {(1 :: real)} <*> (S i)" using K_def by (simp add: hull_subset)
  hence "Union (K ` I) >= {(1 :: real)} <*> Union (S ` I)" by auto
  hence "convex hull Union (K ` I) >= convex hull ({(1 :: real)} <*> Union (S ` I))" by (simp add: hull_mono)
  hence "convex hull Union (K ` I) >= {(1 :: real)} <*> C0" unfolding C0_def
     using convex_hull_direct_sum[of "{(1 :: real)}" "Union (S ` I)"] convex_hull_singleton by auto
  moreover have "cone (convex hull(Union (K ` I)))" apply (subst cone_convex_hull)
     using cone_Union[of "K ` I"] apply auto unfolding K_def using cone_cone_hull by auto
  ultimately have "convex hull (Union (K ` I)) >= K0"
     unfolding K0_def using hull_minimal[of _ "convex hull (Union (K ` I))" "cone"] by blast
  hence "K0 = convex hull (Union (K ` I))" using geq by auto
  also have "...=setsum K I"
     apply (subst convex_hull_finite_union_cones[of I K])
     using assms apply blast
     using `I ~= {}` apply blast
     unfolding K_def apply rule
     apply (subst convex_cone_hull) apply (subst convex_direct_sum)
     using assms cone_cone_hull `!i:I. K i ~= {}` K_def by auto
  finally have "K0 = setsum K I" by auto
  hence *: "rel_interior K0 = setsum (%i. (rel_interior (K i))) I"
     using rel_interior_sum_gen[of I K] convK by auto
  { fix x assume "x : ?lhs"
    hence "((1::real),x) : rel_interior K0" using K0_def C0_def
       rel_interior_convex_cone_aux[of C0 "(1::real)" x] convex_convex_hull by auto
    from this obtain k where k_def: "((1::real),x) = setsum k I & (!i:I. k i : rel_interior (K i))"
      using `finite I` * set_setsum_alt[of I "(%i. rel_interior (K i))"] by auto
    { fix i assume "i:I"
      hence "(convex (S i)) & k i : rel_interior (cone hull {1} <*> S i)" using k_def K_def assms by auto
      hence "EX ci si. k i = (ci, ci *\<^sub>R si) & 0 < ci & si : rel_interior (S i)"
         using rel_interior_convex_cone[of "S i"] by auto
    }
    from this obtain c s where cs_def: "!i:I. (k i = (c i, c i *\<^sub>R s i) & 0 < c i
          & s i : rel_interior (S i))" by metis
    hence "x = (SUM i:I. c i *\<^sub>R s i) & setsum c I = 1" using k_def by (simp add: setsum_prod)
    hence "x : ?rhs" using k_def apply auto
       apply (rule_tac x="c" in exI) apply (rule_tac x="s" in exI) using cs_def by auto
  }
  moreover
  { fix x assume "x : ?rhs"
    from this obtain c s where cs_def: "x=setsum (%i. c i *\<^sub>R s i) I &
       (!i:I. c i > 0) & (setsum c I = 1) & (!i:I. s i : rel_interior(S i))" by auto
    def k == "(%i. (c i, c i *\<^sub>R s i))"
    { fix i assume "i:I"
      hence "k i : rel_interior (K i)"
         using k_def K_def assms cs_def rel_interior_convex_cone[of "S i"] by auto
    }
    hence "((1::real),x) : rel_interior K0"
       using K0_def * set_setsum_alt[of I "(%i. rel_interior (K i))"] assms k_def cs_def
       apply auto apply (rule_tac x="k" in exI) by (simp add: setsum_prod)
    hence "x : ?lhs" using K0_def C0_def
       rel_interior_convex_cone_aux[of C0 "(1::real)" x] by (auto simp add: convex_convex_hull)
  }
  ultimately have ?thesis by blast
} ultimately show ?thesis by blast
qed


lemma convex_le_Inf_differential:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_on I f"
  assumes "x \<in> interior I" "y \<in> I"
  shows "f y \<ge> f x + Inf ((\<lambda>t. (f x - f t) / (x - t)) ` ({x<..} \<inter> I)) * (y - x)"
    (is "_ \<ge> _ + Inf (?F x) * (y - x)")
proof (cases rule: linorder_cases)
  assume "x < y"
  moreover
  have "open (interior I)" by auto
  from openE[OF this `x \<in> interior I`] guess e . note e = this
  moreover def t \<equiv> "min (x + e / 2) ((x + y) / 2)"
  ultimately have "x < t" "t < y" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps split: split_min)
  with `x \<in> interior I` e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  have "open (interior I)" by auto
  from openE[OF this `x \<in> interior I`] guess e .
  moreover def K \<equiv> "x - e / 2"
  with `0 < e` have "K \<in> ball x e" "K < x" by (auto simp: dist_real_def)
  ultimately have "K \<in> I" "K < x" "x \<in> I"
    using interior_subset[of I] `x \<in> interior I` by auto

  have "Inf (?F x) \<le> (f x - f y) / (x - y)"
  proof (rule cInf_lower2)
    show "(f x - f t) / (x - t) \<in> ?F x"
      using `t \<in> I` `x < t` by auto
    show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
      using `convex_on I f` `x \<in> I` `y \<in> I` `x < t` `t < y` by (rule convex_on_diff)
  next
    fix y assume "y \<in> ?F x"
    with order_trans[OF convex_on_diff[OF `convex_on I f` `K \<in> I` _ `K < x` _]]
    show "(f K - f x) / (K - x) \<le> y" by auto
  qed
  then show ?thesis
    using `x < y` by (simp add: field_simps)
next
  assume "y < x"
  moreover
  have "open (interior I)" by auto
  from openE[OF this `x \<in> interior I`] guess e . note e = this
  moreover def t \<equiv> "x + e / 2"
  ultimately have "x < t" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps)
  with `x \<in> interior I` e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  have "(f x - f y) / (x - y) \<le> Inf (?F x)"
  proof (rule cInf_greatest)
    have "(f x - f y) / (x - y) = (f y - f x) / (y - x)"
      using `y < x` by (auto simp: field_simps)
    also
    fix z  assume "z \<in> ?F x"
    with order_trans[OF convex_on_diff[OF `convex_on I f` `y \<in> I` _ `y < x`]]
    have "(f y - f x) / (y - x) \<le> z" by auto
    finally show "(f x - f y) / (x - y) \<le> z" .
  next
    have "open (interior I)" by auto
    from openE[OF this `x \<in> interior I`] guess e . note e = this
    then have "x + e / 2 \<in> ball x e" by (auto simp: dist_real_def)
    with e interior_subset[of I] have "x + e / 2 \<in> {x<..} \<inter> I" by auto
    then show "?F x \<noteq> {}" by blast
  qed
  then show ?thesis
    using `y < x` by (simp add: field_simps)
qed simp

end
