(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
*)

header {* Kurzweil-Henstock Gauge Integration in many dimensions. *}

theory Integration
imports
  Derivative
  "~~/src/HOL/Library/Indicator_Function"
begin

lemma cSup_abs_le: (* TODO: is this really needed? *)
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. \<bar>x\<bar> \<le> a) \<Longrightarrow> \<bar>Sup S\<bar> \<le> a"
  by (auto simp add: abs_le_interval_iff intro: cSup_least) (metis cSup_upper2 bdd_aboveI)

lemma cInf_abs_ge: (* TODO: is this really needed? *)
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. \<bar>x\<bar> \<le> a) \<Longrightarrow> \<bar>Inf S\<bar> \<le> a"
  by (simp add: Inf_real_def) (insert cSup_abs_le [of "uminus ` S"], auto)

lemma cSup_asclose: (* TODO: is this really needed? *)
  fixes S :: "real set"
  assumes S: "S \<noteq> {}"
    and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e"
  shows "\<bar>Sup S - l\<bar> \<le> e"
proof -
  have th: "\<And>(x::real) l e. \<bar>x - l\<bar> \<le> e \<longleftrightarrow> l - e \<le> x \<and> x \<le> l + e"
    by arith
  have "bdd_above S"
    using b by (auto intro!: bdd_aboveI[of _ "l + e"])
  with S b show ?thesis
    unfolding th by (auto intro!: cSup_upper2 cSup_least)
qed

lemma cInf_asclose: (* TODO: is this really needed? *)
  fixes S :: "real set"
  assumes S: "S \<noteq> {}"
    and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e"
  shows "\<bar>Inf S - l\<bar> \<le> e"
proof -
  have "\<bar>- Sup (uminus ` S) - l\<bar> =  \<bar>Sup (uminus ` S) - (-l)\<bar>"
    by auto
  also have "\<dots> \<le> e"
    apply (rule cSup_asclose)
    using abs_minus_add_cancel b by (auto simp add: S)
  finally have "\<bar>- Sup (uminus ` S) - l\<bar> \<le> e" .
  then show ?thesis
    by (simp add: Inf_real_def)
qed

lemma cSup_finite_ge_iff:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<le> Sup S \<longleftrightarrow> (\<exists>x\<in>S. a \<le> x)"
  by (metis cSup_eq_Max Max_ge_iff)

lemma cSup_finite_le_iff:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<ge> Sup S \<longleftrightarrow> (\<forall>x\<in>S. a \<ge> x)"
  by (metis cSup_eq_Max Max_le_iff)

lemma cInf_finite_ge_iff:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. a \<le> x)"
  by (metis cInf_eq_Min Min_ge_iff)

lemma cInf_finite_le_iff:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<ge> Inf S \<longleftrightarrow> (\<exists>x\<in>S. a \<ge> x)"
  by (metis cInf_eq_Min Min_le_iff)

(*declare not_less[simp] not_le[simp]*)

lemmas scaleR_simps = scaleR_zero_left scaleR_minus_left scaleR_left_diff_distrib
  scaleR_zero_right scaleR_minus_right scaleR_right_diff_distrib scaleR_eq_0_iff
  scaleR_cancel_left scaleR_cancel_right scaleR_add_right scaleR_add_left real_vector_class.scaleR_one

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by (subst(asm) real_arch_inv)


subsection {* Sundries *}

lemma conjunctD2: assumes "a \<and> b" shows a b using assms by auto
lemma conjunctD3: assumes "a \<and> b \<and> c" shows a b c using assms by auto
lemma conjunctD4: assumes "a \<and> b \<and> c \<and> d" shows a b c d using assms by auto
lemma conjunctD5: assumes "a \<and> b \<and> c \<and> d \<and> e" shows a b c d e using assms by auto

declare norm_triangle_ineq4[intro]

lemma simple_image: "{f x |x . x \<in> s} = f ` s"
  by blast

lemma linear_simps:
  assumes "bounded_linear f"
  shows
    "f (a + b) = f a + f b"
    "f (a - b) = f a - f b"
    "f 0 = 0"
    "f (- a) = - f a"
    "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
proof -
  interpret f: bounded_linear f by fact
  show "f (a + b) = f a + f b" by (rule f.add)
  show "f (a - b) = f a - f b" by (rule f.diff)
  show "f 0 = 0" by (rule f.zero)
  show "f (- a) = - f a" by (rule f.minus)
  show "f (s *\<^sub>R v) = s *\<^sub>R (f v)" by (rule f.scaleR)
qed

lemma bounded_linearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>R x) = r *\<^sub>R f x"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  using assms by (rule bounded_linear_intro) (* FIXME: duplicate *)

lemma bounded_linear_component [intro]: "bounded_linear (\<lambda>x::'a::euclidean_space. x \<bullet> k)"
  by (rule bounded_linear_inner_left)

lemma transitive_stepwise_lt_eq:
  assumes "(\<And>x y z::nat. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)"
  shows "((\<forall>m. \<forall>n>m. R m n) \<longleftrightarrow> (\<forall>n. R n (Suc n)))"
  (is "?l = ?r")
proof safe
  assume ?r
  fix n m :: nat
  assume "m < n"
  then show "R m n"
  proof (induct n arbitrary: m)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    show ?case
    proof (cases "m < n")
      case True
      show ?thesis
        apply (rule assms[OF Suc(1)[OF True]])
        using `?r`
        apply auto
        done
    next
      case False
      then have "m = n"
        using Suc(2) by auto
      then show ?thesis
        using `?r` by auto
    qed
  qed
qed auto

lemma transitive_stepwise_gt:
  assumes "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" "\<And>n. R n (Suc n)"
  shows "\<forall>n>m. R m n"
proof -
  have "\<forall>m. \<forall>n>m. R m n"
    apply (subst transitive_stepwise_lt_eq)
    apply (rule assms)
    apply assumption
    apply assumption
    using assms(2) apply auto
    done
  then show ?thesis by auto
qed

lemma transitive_stepwise_le_eq:
  assumes "\<And>x. R x x" "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "(\<forall>m. \<forall>n\<ge>m. R m n) \<longleftrightarrow> (\<forall>n. R n (Suc n))"
  (is "?l = ?r")
proof safe
  assume ?r
  fix m n :: nat
  assume "m \<le> n"
  then show "R m n"
  proof (induct n arbitrary: m)
    case 0
    with assms show ?case by auto
  next
    case (Suc n)
    show ?case
    proof (cases "m \<le> n")
      case True
      show ?thesis
        apply (rule assms(2))
        apply (rule Suc(1)[OF True])
        using `?r` apply auto
        done
    next
      case False
      then have "m = Suc n"
        using Suc(2) by auto
      then show ?thesis
        using assms(1) by auto
    qed
  qed
qed auto

lemma transitive_stepwise_le:
  assumes "\<And>x. R x x" "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
    and "\<And>n. R n (Suc n)"
  shows "\<forall>n\<ge>m. R m n"
proof -
  have "\<forall>m. \<forall>n\<ge>m. R m n"
    apply (subst transitive_stepwise_le_eq)
    apply (rule assms)
    apply (rule assms,assumption,assumption)
    using assms(3)
    apply auto
    done
  then show ?thesis by auto
qed


subsection {* Some useful lemmas about intervals. *}

abbreviation One :: "'a::euclidean_space"
  where "One \<equiv> \<Sum>Basis"

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  using nonempty_Basis
  by (fastforce simp add: set_eq_iff mem_box)

lemma interior_subset_union_intervals:
  assumes "i = cbox a b"
    and "j = cbox c d"
    and "interior j \<noteq> {}"
    and "i \<subseteq> j \<union> s"
    and "interior i \<inter> interior j = {}"
  shows "interior i \<subseteq> interior s"
proof -
  have "box a b \<inter> cbox c d = {}"
     using inter_interval_mixed_eq_empty[of c d a b] and assms(3,5)
     unfolding assms(1,2) interior_cbox by auto
  moreover
  have "box a b \<subseteq> cbox c d \<union> s"
    apply (rule order_trans,rule box_subset_cbox)
    using assms(4) unfolding assms(1,2)
    apply auto
    done
  ultimately
  show ?thesis
    apply -
    apply (rule interior_maximal)
    defer
    apply (rule open_interior)
    unfolding assms(1,2) interior_cbox
    apply auto
    done
qed

lemma inter_interior_unions_intervals:
  fixes f::"('a::euclidean_space) set set"
  assumes "finite f"
    and "open s"
    and "\<forall>t\<in>f. \<exists>a b. t = cbox a b"
    and "\<forall>t\<in>f. s \<inter> (interior t) = {}"
  shows "s \<inter> interior (\<Union>f) = {}"
proof (rule ccontr, unfold ex_in_conv[symmetric])
  case goal1
  have lem1: "\<And>x e s U. ball x e \<subseteq> s \<inter> interior U \<longleftrightarrow> ball x e \<subseteq> s \<inter> U"
    apply rule
    defer
    apply (rule_tac Int_greatest)
    unfolding open_subset_interior[OF open_ball]
    using interior_subset
    apply auto
    done
  have lem2: "\<And>x s P. \<exists>x\<in>s. P x \<Longrightarrow> \<exists>x\<in>insert x s. P x" by auto
  have "\<And>f. finite f \<Longrightarrow> \<forall>t\<in>f. \<exists>a b. t = cbox a b \<Longrightarrow>
    \<exists>x. x \<in> s \<inter> interior (\<Union>f) \<Longrightarrow> \<exists>t\<in>f. \<exists>x. \<exists>e>0. ball x e \<subseteq> s \<inter> t"
  proof -
    case goal1
    then show ?case
    proof (induct rule: finite_induct)
      case empty
      obtain x where "x \<in> s \<inter> interior (\<Union>{})"
        using empty(2) ..
      then have False
        unfolding Union_empty interior_empty by auto
      then show ?case by auto
    next
      case (insert i f)
      obtain x where x: "x \<in> s \<inter> interior (\<Union>insert i f)"
        using insert(5) ..
      then obtain e where e: "0 < e \<and> ball x e \<subseteq> s \<inter> interior (\<Union>insert i f)"
        unfolding open_contains_ball_eq[OF open_Int[OF assms(2) open_interior], rule_format] ..
      obtain a where "\<exists>b. i = cbox a b"
        using insert(4)[rule_format,OF insertI1] ..
      then obtain b where ab: "i = cbox a b" ..
      show ?case
      proof (cases "x \<in> i")
        case False
        then have "x \<in> UNIV - cbox a b"
          unfolding ab by auto
        then obtain d where "0 < d \<and> ball x d \<subseteq> UNIV - cbox a b"
          unfolding open_contains_ball_eq[OF open_Diff[OF open_UNIV closed_cbox],rule_format] ..
        then have "0 < d" "ball x (min d e) \<subseteq> UNIV - i"
          unfolding ab ball_min_Int by auto
        then have "ball x (min d e) \<subseteq> s \<inter> interior (\<Union>f)"
          using e unfolding lem1 unfolding  ball_min_Int by auto
        then have "x \<in> s \<inter> interior (\<Union>f)" using `d>0` e by auto
        then have "\<exists>t\<in>f. \<exists>x e. 0 < e \<and> ball x e \<subseteq> s \<inter> t"
          apply -
          apply (rule insert(3))
          using insert(4)
          apply auto
          done
        then show ?thesis by auto
      next
        case True show ?thesis
        proof (cases "x\<in>box a b")
          case True
          then obtain d where "0 < d \<and> ball x d \<subseteq> box a b"
            unfolding open_contains_ball_eq[OF open_box,rule_format] ..
          then show ?thesis
            apply (rule_tac x=i in bexI, rule_tac x=x in exI, rule_tac x="min d e" in exI)
            unfolding ab
            using box_subset_cbox[of a b] and e
            apply fastforce+
            done
        next
          case False
          then obtain k where "x\<bullet>k \<le> a\<bullet>k \<or> x\<bullet>k \<ge> b\<bullet>k" and k: "k \<in> Basis"
            unfolding mem_box by (auto simp add: not_less)
          then have "x\<bullet>k = a\<bullet>k \<or> x\<bullet>k = b\<bullet>k"
            using True unfolding ab and mem_box
              apply (erule_tac x = k in ballE)
              apply auto
              done
          then have "\<exists>x. ball x (e/2) \<subseteq> s \<inter> (\<Union>f)"
          proof (rule disjE)
            let ?z = "x - (e/2) *\<^sub>R k"
            assume as: "x\<bullet>k = a\<bullet>k"
            have "ball ?z (e / 2) \<inter> i = {}"
              apply (rule ccontr)
              unfolding ex_in_conv[symmetric]
              apply (erule exE)
            proof -
              fix y
              assume "y \<in> ball ?z (e / 2) \<inter> i"
              then have "dist ?z y < e/2" and yi:"y\<in>i" by auto
              then have "\<bar>(?z - y) \<bullet> k\<bar> < e/2"
                using Basis_le_norm[OF k, of "?z - y"] unfolding dist_norm by auto
              then have "y\<bullet>k < a\<bullet>k"
                using e[THEN conjunct1] k
                by (auto simp add: field_simps abs_less_iff as inner_Basis inner_simps)
              then have "y \<notin> i"
                unfolding ab mem_box by (auto intro!: bexI[OF _ k])
              then show False using yi by auto
            qed
            moreover
            have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)"
              apply (rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]])
            proof
              fix y
              assume as: "y \<in> ball ?z (e/2)"
              have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y - (e / 2) *\<^sub>R k)"
                apply -
                apply (rule order_trans,rule norm_triangle_sub[of "x - y" "(e/2) *\<^sub>R k"])
                unfolding norm_scaleR norm_Basis[OF k]
                apply auto
                done
              also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2"
                apply (rule add_strict_left_mono)
                using as
                unfolding mem_ball dist_norm
                using e
                apply (auto simp add: field_simps)
                done
              finally show "y \<in> ball x e"
                unfolding mem_ball dist_norm using e by (auto simp add:field_simps)
            qed
            ultimately show ?thesis
              apply (rule_tac x="?z" in exI)
              unfolding Union_insert
              apply auto
              done
          next
            let ?z = "x + (e/2) *\<^sub>R k"
            assume as: "x\<bullet>k = b\<bullet>k"
            have "ball ?z (e / 2) \<inter> i = {}"
              apply (rule ccontr)
              unfolding ex_in_conv[symmetric]
              apply (erule exE)
            proof -
              fix y
              assume "y \<in> ball ?z (e / 2) \<inter> i"
              then have "dist ?z y < e/2" and yi: "y \<in> i"
                by auto
              then have "\<bar>(?z - y) \<bullet> k\<bar> < e/2"
                using Basis_le_norm[OF k, of "?z - y"]
                unfolding dist_norm by auto
              then have "y\<bullet>k > b\<bullet>k"
                using e[THEN conjunct1] k
                by (auto simp add:field_simps inner_simps inner_Basis as)
              then have "y \<notin> i"
                unfolding ab mem_box by (auto intro!: bexI[OF _ k])
              then show False using yi by auto
            qed
            moreover
            have "ball ?z (e/2) \<subseteq> s \<inter> (\<Union>insert i f)"
              apply (rule order_trans[OF _ e[THEN conjunct2, unfolded lem1]])
            proof
              fix y
              assume as: "y\<in> ball ?z (e/2)"
              have "norm (x - y) \<le> \<bar>e\<bar> / 2 + norm (x - y + (e / 2) *\<^sub>R k)"
                apply -
                apply (rule order_trans,rule norm_triangle_sub[of "x - y" "- (e/2) *\<^sub>R k"])
                unfolding norm_scaleR
                apply (auto simp: k)
                done
              also have "\<dots> < \<bar>e\<bar> / 2 + \<bar>e\<bar> / 2"
                apply (rule add_strict_left_mono)
                using as unfolding mem_ball dist_norm
                using e apply (auto simp add: field_simps)
                done
              finally show "y \<in> ball x e"
                unfolding mem_ball dist_norm using e by (auto simp add:field_simps)
            qed
            ultimately show ?thesis
              apply (rule_tac x="?z" in exI)
              unfolding Union_insert
              apply auto
              done
          qed
          then obtain x where "ball x (e / 2) \<subseteq> s \<inter> \<Union>f" ..
          then have "x \<in> s \<inter> interior (\<Union>f)"
            unfolding lem1[where U="\<Union>f", symmetric]
            using centre_in_ball e[THEN conjunct1] by auto
          then show ?thesis
            apply -
            apply (rule lem2, rule insert(3))
            using insert(4)
            apply auto
            done
        qed
      qed
    qed
  qed
  from this[OF assms(1,3) goal1]
  obtain t x e where "t \<in> f" "0 < e" "ball x e \<subseteq> s \<inter> t"
    by blast
  then have "x \<in> s" "x \<in> interior t"
    using open_subset_interior[OF open_ball, of x e t]
    by auto
  then show False
    using `t \<in> f` assms(4) by auto
qed

subsection {* Bounds on intervals where they exist. *}

definition interval_upperbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_upperbound s = (\<Sum>i\<in>Basis. (SUP x:s. x\<bullet>i) *\<^sub>R i)"

definition interval_lowerbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
   where "interval_lowerbound s = (\<Sum>i\<in>Basis. (INF x:s. x\<bullet>i) *\<^sub>R i)"

lemma interval_upperbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_upperbound (cbox a b) = (b::'a::euclidean_space)"
  unfolding interval_upperbound_def euclidean_representation_setsum cbox_def SUP_def
  by (safe intro!: cSup_eq) auto

lemma interval_lowerbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_lowerbound (cbox a b) = (a::'a::euclidean_space)"
  unfolding interval_lowerbound_def euclidean_representation_setsum cbox_def INF_def
  by (safe intro!: cInf_eq) auto

lemmas interval_bounds = interval_upperbound interval_lowerbound

lemma
  fixes X::"real set"
  shows interval_upperbound_real[simp]: "interval_upperbound X = Sup X"
    and interval_lowerbound_real[simp]: "interval_lowerbound X = Inf X"
  by (auto simp: interval_upperbound_def interval_lowerbound_def SUP_def INF_def)

lemma interval_bounds'[simp]:
  assumes "cbox a b \<noteq> {}"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
  using assms unfolding box_ne_empty by auto

subsection {* Content (length, area, volume...) of an interval. *}

definition "content (s::('a::euclidean_space) set) =
  (if s = {} then 0 else (\<Prod>i\<in>Basis. (interval_upperbound s)\<bullet>i - (interval_lowerbound s)\<bullet>i))"

lemma interval_not_empty: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> cbox a b \<noteq> {}"
  unfolding box_eq_empty unfolding not_ex not_less by auto

lemma content_cbox:
  fixes a :: "'a::euclidean_space"
  assumes "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
  shows "content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  using interval_not_empty[OF assms]
  unfolding content_def
  by (auto simp: )

lemma content_cbox':
  fixes a :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
  shows "content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  apply (rule content_cbox)
  using assms
  unfolding box_ne_empty
  apply assumption
  done

lemma content_real: "a \<le> b \<Longrightarrow> content {a..b} = b - a"
  by (auto simp: interval_upperbound_def interval_lowerbound_def SUP_def INF_def content_def)

lemma content_singleton[simp]: "content {a} = 0"
proof -
  have "content (cbox a a) = 0"
    by (subst content_cbox) (auto simp: ex_in_conv)
  then show ?thesis by (simp add: cbox_sing)
qed

lemma content_unit[intro]: "content(cbox 0 (One::'a::euclidean_space)) = 1"
 proof -
   have *: "\<forall>i\<in>Basis. (0::'a)\<bullet>i \<le> (One::'a)\<bullet>i"
    by auto
  have "0 \<in> cbox 0 (One::'a)"
    unfolding mem_box by auto
  then show ?thesis
     unfolding content_def interval_bounds[OF *] using setprod_1 by auto
 qed

lemma content_pos_le[intro]:
  fixes a::"'a::euclidean_space"
  shows "0 \<le> content (cbox a b)"
proof (cases "cbox a b = {}")
  case False
  then have *: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
    unfolding box_ne_empty .
  have "0 \<le> (\<Prod>i\<in>Basis. interval_upperbound (cbox a b) \<bullet> i - interval_lowerbound (cbox a b) \<bullet> i)"
    apply (rule setprod_nonneg)
    unfolding interval_bounds[OF *]
    using *
    apply auto
    done
  also have "\<dots> = content (cbox a b)" using False by (simp add: content_def)
  finally show ?thesis .
qed (simp add: content_def)

lemma content_pos_lt:
  fixes a :: "'a::euclidean_space"
  assumes "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
  shows "0 < content (cbox a b)"
  using assms
  by (auto simp: content_def box_eq_empty intro!: setprod_pos)

lemma content_eq_0:
  "content (cbox a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by (auto simp: content_def box_eq_empty intro!: setprod_pos bexI)

lemma cond_cases: "(P \<Longrightarrow> Q x) \<Longrightarrow> (\<not> P \<Longrightarrow> Q y) \<Longrightarrow> Q (if P then x else y)"
  by auto

lemma content_cbox_cases:
  "content (cbox a (b::'a::euclidean_space)) =
    (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then setprod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by (auto simp: not_le content_eq_0 intro: less_imp_le content_cbox)

lemma content_eq_0_interior: "content (cbox a b) = 0 \<longleftrightarrow> interior(cbox a b) = {}"
  unfolding content_eq_0 interior_cbox box_eq_empty
  by auto

lemma content_pos_lt_eq:
  "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  apply rule
  defer
  apply (rule content_pos_lt, assumption)
proof -
  assume "0 < content (cbox a b)"
  then have "content (cbox a b) \<noteq> 0" by auto
  then show "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"
    unfolding content_eq_0 not_ex not_le by fastforce
qed

lemma content_empty [simp]: "content {} = 0"
  unfolding content_def by auto

lemma content_subset:
  assumes "cbox a b \<subseteq> cbox c d"
  shows "content (cbox a b) \<le> content (cbox c d)"
proof (cases "cbox a b = {}")
  case True
  then show ?thesis
    using content_pos_le[of c d] by auto
next
  case False
  then have ab_ne: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
    unfolding box_ne_empty by auto
  then have ab_ab: "a\<in>cbox a b" "b\<in>cbox a b"
    unfolding mem_box by auto
  have "cbox c d \<noteq> {}" using assms False by auto
  then have cd_ne: "\<forall>i\<in>Basis. c \<bullet> i \<le> d \<bullet> i"
    using assms unfolding box_ne_empty by auto
  show ?thesis
    unfolding content_def
    unfolding interval_bounds[OF ab_ne] interval_bounds[OF cd_ne]
    unfolding if_not_P[OF False] if_not_P[OF `cbox c d \<noteq> {}`]
    apply (rule setprod_mono)
    apply rule
  proof
    fix i :: 'a
    assume i: "i \<in> Basis"
    show "0 \<le> b \<bullet> i - a \<bullet> i"
      using ab_ne[THEN bspec, OF i] i by auto
    show "b \<bullet> i - a \<bullet> i \<le> d \<bullet> i - c \<bullet> i"
      using assms[unfolded subset_eq mem_box,rule_format,OF ab_ab(2),of i]
      using assms[unfolded subset_eq mem_box,rule_format,OF ab_ab(1),of i]
      using i by auto
  qed
qed

lemma content_lt_nz: "0 < content (cbox a b) \<longleftrightarrow> content (cbox a b) \<noteq> 0"
  unfolding content_pos_lt_eq content_eq_0 unfolding not_ex not_le by fastforce


subsection {* The notion of a gauge --- simply an open set containing the point. *}

definition "gauge d \<longleftrightarrow> (\<forall>x. x \<in> d x \<and> open (d x))"

lemma gaugeI:
  assumes "\<And>x. x \<in> g x"
    and "\<And>x. open (g x)"
  shows "gauge g"
  using assms unfolding gauge_def by auto

lemma gaugeD[dest]:
  assumes "gauge d"
  shows "x \<in> d x"
    and "open (d x)"
  using assms unfolding gauge_def by auto

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
  unfolding gauge_def by auto

lemma gauge_ball[intro]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)"
  unfolding gauge_def by auto

lemma gauge_trivial[intro]: "gauge (\<lambda>x. ball x 1)"
  by (rule gauge_ball) auto

lemma gauge_inter[intro]: "gauge d1 \<Longrightarrow> gauge d2 \<Longrightarrow> gauge (\<lambda>x. d1 x \<inter> d2 x)"
  unfolding gauge_def by auto

lemma gauge_inters:
  assumes "finite s"
    and "\<forall>d\<in>s. gauge (f d)"
  shows "gauge (\<lambda>x. \<Inter> {f d x | d. d \<in> s})"
proof -
  have *: "\<And>x. {f d x |d. d \<in> s} = (\<lambda>d. f d x) ` s"
    by auto
  show ?thesis
    unfolding gauge_def unfolding *
    using assms unfolding Ball_def Inter_iff mem_Collect_eq gauge_def by auto
qed

lemma gauge_existence_lemma:
  "(\<forall>x. \<exists>d :: real. p x \<longrightarrow> 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. p x \<longrightarrow> q d x)"
  by (metis zero_less_one)


subsection {* Divisions. *}

definition division_of (infixl "division'_of" 40)
where
  "s division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>k\<in>s. k \<subseteq> i \<and> k \<noteq> {} \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>k1\<in>s. \<forall>k2\<in>s. k1 \<noteq> k2 \<longrightarrow> interior(k1) \<inter> interior(k2) = {}) \<and>
    (\<Union>s = i)"

lemma division_ofD[dest]:
  assumes "s division_of i"
  shows "finite s"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<noteq> {}"
    and "\<And>k. k \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>k1 k2. k1 \<in> s \<Longrightarrow> k2 \<in> s \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior(k1) \<inter> interior(k2) = {}"
    and "\<Union>s = i"
  using assms unfolding division_of_def by auto

lemma division_ofI:
  assumes "finite s"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<noteq> {}"
    and "\<And>k. k \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>k1 k2. k1 \<in> s \<Longrightarrow> k2 \<in> s \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
    and "\<Union>s = i"
  shows "s division_of i"
  using assms unfolding division_of_def by auto

lemma division_of_finite: "s division_of i \<Longrightarrow> finite s"
  unfolding division_of_def by auto

lemma division_of_self[intro]: "cbox a b \<noteq> {} \<Longrightarrow> {cbox a b} division_of (cbox a b)"
  unfolding division_of_def by auto

lemma division_of_trivial[simp]: "s division_of {} \<longleftrightarrow> s = {}"
  unfolding division_of_def by auto

lemma division_of_sing[simp]:
  "s division_of cbox a (a::'a::euclidean_space) \<longleftrightarrow> s = {cbox a a}"
  (is "?l = ?r")
proof
  assume ?r
  moreover
  {
    assume "s = {{a}}"
    moreover fix k assume "k\<in>s"
    ultimately have"\<exists>x y. k = cbox x y"
      apply (rule_tac x=a in exI)+
      unfolding cbox_sing
      apply auto
      done
  }
  ultimately show ?l
    unfolding division_of_def cbox_sing by auto
next
  assume ?l
  note * = conjunctD4[OF this[unfolded division_of_def cbox_sing]]
  {
    fix x
    assume x: "x \<in> s" have "x = {a}"
      using *(2)[rule_format,OF x] by auto
  }
  moreover have "s \<noteq> {}"
    using *(4) by auto
  ultimately show ?r
    unfolding cbox_sing by auto
qed

lemma elementary_empty: obtains p where "p division_of {}"
  unfolding division_of_trivial by auto

lemma elementary_interval: obtains p where "p division_of (cbox a b)"
  by (metis division_of_trivial division_of_self)

lemma division_contains: "s division_of i \<Longrightarrow> \<forall>x\<in>i. \<exists>k\<in>s. x \<in> k"
  unfolding division_of_def by auto

lemma forall_in_division:
  "d division_of i \<Longrightarrow> (\<forall>x\<in>d. P x) \<longleftrightarrow> (\<forall>a b. cbox a b \<in> d \<longrightarrow> P (cbox a b))"
  unfolding division_of_def by fastforce

lemma division_of_subset:
  assumes "p division_of (\<Union>p)"
    and "q \<subseteq> p"
  shows "q division_of (\<Union>q)"
proof (rule division_ofI)
  note * = division_ofD[OF assms(1)]
  show "finite q"
    apply (rule finite_subset)
    using *(1) assms(2)
    apply auto
    done
  {
    fix k
    assume "k \<in> q"
    then have kp: "k \<in> p"
      using assms(2) by auto
    show "k \<subseteq> \<Union>q"
      using `k \<in> q` by auto
    show "\<exists>a b. k = cbox a b"
      using *(4)[OF kp] by auto
    show "k \<noteq> {}"
      using *(3)[OF kp] by auto
  }
  fix k1 k2
  assume "k1 \<in> q" "k2 \<in> q" "k1 \<noteq> k2"
  then have **: "k1 \<in> p" "k2 \<in> p" "k1 \<noteq> k2"
    using assms(2) by auto
  show "interior k1 \<inter> interior k2 = {}"
    using *(5)[OF **] by auto
qed auto

lemma division_of_union_self[intro]: "p division_of s \<Longrightarrow> p division_of (\<Union>p)"
  unfolding division_of_def by auto

lemma division_of_content_0:
  assumes "content (cbox a b) = 0" "d division_of (cbox a b)"
  shows "\<forall>k\<in>d. content k = 0"
  unfolding forall_in_division[OF assms(2)]
  apply (rule,rule,rule)
  apply (drule division_ofD(2)[OF assms(2)])
  apply (drule content_subset) unfolding assms(1)
proof -
  case goal1
  then show ?case using content_pos_le[of a b] by auto
qed

lemma division_inter:
  fixes s1 s2 :: "'a::euclidean_space set"
  assumes "p1 division_of s1"
    and "p2 division_of s2"
  shows "{k1 \<inter> k2 | k1 k2 .k1 \<in> p1 \<and> k2 \<in> p2 \<and> k1 \<inter> k2 \<noteq> {}} division_of (s1 \<inter> s2)"
  (is "?A' division_of _")
proof -
  let ?A = "{s. s \<in>  (\<lambda>(k1,k2). k1 \<inter> k2) ` (p1 \<times> p2) \<and> s \<noteq> {}}"
  have *: "?A' = ?A" by auto
  show ?thesis
    unfolding *
  proof (rule division_ofI)
    have "?A \<subseteq> (\<lambda>(x, y). x \<inter> y) ` (p1 \<times> p2)"
      by auto
    moreover have "finite (p1 \<times> p2)"
      using assms unfolding division_of_def by auto
    ultimately show "finite ?A" by auto
    have *: "\<And>s. \<Union>{x\<in>s. x \<noteq> {}} = \<Union>s"
      by auto
    show "\<Union>?A = s1 \<inter> s2"
      apply (rule set_eqI)
      unfolding * and Union_image_eq UN_iff
      using division_ofD(6)[OF assms(1)] and division_ofD(6)[OF assms(2)]
      apply auto
      done
    {
      fix k
      assume "k \<in> ?A"
      then obtain k1 k2 where k: "k = k1 \<inter> k2" "k1 \<in> p1" "k2 \<in> p2" "k \<noteq> {}"
        by auto
      then show "k \<noteq> {}"
        by auto
      show "k \<subseteq> s1 \<inter> s2"
        using division_ofD(2)[OF assms(1) k(2)] and division_ofD(2)[OF assms(2) k(3)]
        unfolding k by auto
      obtain a1 b1 where k1: "k1 = cbox a1 b1"
        using division_ofD(4)[OF assms(1) k(2)] by blast
      obtain a2 b2 where k2: "k2 = cbox a2 b2"
        using division_ofD(4)[OF assms(2) k(3)] by blast
      show "\<exists>a b. k = cbox a b"
        unfolding k k1 k2 unfolding inter_interval by auto
    }
    fix k1 k2
    assume "k1 \<in> ?A"
    then obtain x1 y1 where k1: "k1 = x1 \<inter> y1" "x1 \<in> p1" "y1 \<in> p2" "k1 \<noteq> {}"
      by auto
    assume "k2 \<in> ?A"
    then obtain x2 y2 where k2: "k2 = x2 \<inter> y2" "x2 \<in> p1" "y2 \<in> p2" "k2 \<noteq> {}"
      by auto
    assume "k1 \<noteq> k2"
    then have th: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
      unfolding k1 k2 by auto
    have *: "interior x1 \<inter> interior x2 = {} \<or> interior y1 \<inter> interior y2 = {} \<Longrightarrow>
      interior (x1 \<inter> y1) \<subseteq> interior x1 \<Longrightarrow> interior (x1 \<inter> y1) \<subseteq> interior y1 \<Longrightarrow>
      interior (x2 \<inter> y2) \<subseteq> interior x2 \<Longrightarrow> interior (x2 \<inter> y2) \<subseteq> interior y2 \<Longrightarrow>
      interior (x1 \<inter> y1) \<inter> interior (x2 \<inter> y2) = {}" by auto
    show "interior k1 \<inter> interior k2 = {}"
      unfolding k1 k2
      apply (rule *)
      defer
      apply (rule_tac[1-4] interior_mono)
      using division_ofD(5)[OF assms(1) k1(2) k2(2)]
      using division_ofD(5)[OF assms(2) k1(3) k2(3)]
      using th
      apply auto
      done
  qed
qed

lemma division_inter_1:
  assumes "d division_of i"
    and "cbox a (b::'a::euclidean_space) \<subseteq> i"
  shows "{cbox a b \<inter> k | k. k \<in> d \<and> cbox a b \<inter> k \<noteq> {}} division_of (cbox a b)"
proof (cases "cbox a b = {}")
  case True
  show ?thesis
    unfolding True and division_of_trivial by auto
next
  case False
  have *: "cbox a b \<inter> i = cbox a b" using assms(2) by auto
  show ?thesis
    using division_inter[OF division_of_self[OF False] assms(1)]
    unfolding * by auto
qed

lemma elementary_inter:
  fixes s t :: "'a::euclidean_space set"
  assumes "p1 division_of s"
    and "p2 division_of t"
  shows "\<exists>p. p division_of (s \<inter> t)"
  apply rule
  apply (rule division_inter[OF assms])
  done

lemma elementary_inters:
  assumes "finite f"
    and "f \<noteq> {}"
    and "\<forall>s\<in>f. \<exists>p. p division_of (s::('a::euclidean_space) set)"
  shows "\<exists>p. p division_of (\<Inter> f)"
  using assms
proof (induct f rule: finite_induct)
  case (insert x f)
  show ?case
  proof (cases "f = {}")
    case True
    then show ?thesis
      unfolding True using insert by auto
  next
    case False
    obtain p where "p division_of \<Inter>f"
      using insert(3)[OF False insert(5)[unfolded ball_simps,THEN conjunct2]] ..
    moreover obtain px where "px division_of x"
      using insert(5)[rule_format,OF insertI1] ..
    ultimately show ?thesis
      apply -
      unfolding Inter_insert
      apply (rule elementary_inter)
      apply assumption
      apply assumption
      done
  qed
qed auto

lemma division_disjoint_union:
  assumes "p1 division_of s1"
    and "p2 division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) division_of (s1 \<union> s2)"
proof (rule division_ofI)
  note d1 = division_ofD[OF assms(1)]
  note d2 = division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)"
    using d1(1) d2(1) by auto
  show "\<Union>(p1 \<union> p2) = s1 \<union> s2"
    using d1(6) d2(6) by auto
  {
    fix k1 k2
    assume as: "k1 \<in> p1 \<union> p2" "k2 \<in> p1 \<union> p2" "k1 \<noteq> k2"
    moreover
    let ?g="interior k1 \<inter> interior k2 = {}"
    {
      assume as: "k1\<in>p1" "k2\<in>p2"
      have ?g
        using interior_mono[OF d1(2)[OF as(1)]] interior_mono[OF d2(2)[OF as(2)]]
        using assms(3) by blast
    }
    moreover
    {
      assume as: "k1\<in>p2" "k2\<in>p1"
      have ?g
        using interior_mono[OF d1(2)[OF as(2)]] interior_mono[OF d2(2)[OF as(1)]]
        using assms(3) by blast
    }
    ultimately show ?g
      using d1(5)[OF _ _ as(3)] and d2(5)[OF _ _ as(3)] by auto
  }
  fix k
  assume k: "k \<in> p1 \<union> p2"
  show "k \<subseteq> s1 \<union> s2"
    using k d1(2) d2(2) by auto
  show "k \<noteq> {}"
    using k d1(3) d2(3) by auto
  show "\<exists>a b. k = cbox a b"
    using k d1(4) d2(4) by auto
qed

lemma partial_division_extend_1:
  fixes a b c d :: "'a::euclidean_space"
  assumes incl: "cbox c d \<subseteq> cbox a b"
    and nonempty: "cbox c d \<noteq> {}"
  obtains p where "p division_of (cbox a b)" "cbox c d \<in> p"
proof
  let ?B = "\<lambda>f::'a\<Rightarrow>'a \<times> 'a.
    cbox (\<Sum>i\<in>Basis. (fst (f i) \<bullet> i) *\<^sub>R i) (\<Sum>i\<in>Basis. (snd (f i) \<bullet> i) *\<^sub>R i)"
  def p \<equiv> "?B ` (Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)})"

  show "cbox c d \<in> p"
    unfolding p_def
    by (auto simp add: box_eq_empty cbox_def intro!: image_eqI[where x="\<lambda>(i::'a)\<in>Basis. (c, d)"])
  {
    fix i :: 'a
    assume "i \<in> Basis"
    with incl nonempty have "a \<bullet> i \<le> c \<bullet> i" "c \<bullet> i \<le> d \<bullet> i" "d \<bullet> i \<le> b \<bullet> i"
      unfolding box_eq_empty subset_box by (auto simp: not_le)
  }
  note ord = this

  show "p division_of (cbox a b)"
  proof (rule division_ofI)
    show "finite p"
      unfolding p_def by (auto intro!: finite_PiE)
    {
      fix k
      assume "k \<in> p"
      then obtain f where f: "f \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}" and k: "k = ?B f"
        by (auto simp: p_def)
      then show "\<exists>a b. k = cbox a b"
        by auto
      have "k \<subseteq> cbox a b \<and> k \<noteq> {}"
      proof (simp add: k box_eq_empty subset_box not_less, safe)
        fix i :: 'a
        assume i: "i \<in> Basis"
        with f have "f i = (a, c) \<or> f i = (c, d) \<or> f i = (d, b)"
          by (auto simp: PiE_iff)
        with i ord[of i]
        show "a \<bullet> i \<le> fst (f i) \<bullet> i" "snd (f i) \<bullet> i \<le> b \<bullet> i" "fst (f i) \<bullet> i \<le> snd (f i) \<bullet> i"
          by auto
      qed
      then show "k \<noteq> {}" "k \<subseteq> cbox a b"
        by auto
      {
        fix l
        assume "l \<in> p"
        then obtain g where g: "g \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}" and l: "l = ?B g"
          by (auto simp: p_def)
        assume "l \<noteq> k"
        have "\<exists>i\<in>Basis. f i \<noteq> g i"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          with f g have "f = g"
            by (auto simp: PiE_iff extensional_def intro!: ext)
          with `l \<noteq> k` show False
            by (simp add: l k)
        qed
        then obtain i where *: "i \<in> Basis" "f i \<noteq> g i" ..
        then have "f i = (a, c) \<or> f i = (c, d) \<or> f i = (d, b)"
            "g i = (a, c) \<or> g i = (c, d) \<or> g i = (d, b)"
          using f g by (auto simp: PiE_iff)
        with * ord[of i] show "interior l \<inter> interior k = {}"
          by (auto simp add: l k interior_cbox disjoint_interval intro!: bexI[of _ i])
      }
      note `k \<subseteq> cbox a b`
    }
    moreover
    {
      fix x assume x: "x \<in> cbox a b"
      have "\<forall>i\<in>Basis. \<exists>l. x \<bullet> i \<in> {fst l \<bullet> i .. snd l \<bullet> i} \<and> l \<in> {(a, c), (c, d), (d, b)}"
      proof
        fix i :: 'a
        assume "i \<in> Basis"
        with x ord[of i]
        have "(a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> c \<bullet> i) \<or> (c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i) \<or>
            (d \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
          by (auto simp: cbox_def)
        then show "\<exists>l. x \<bullet> i \<in> {fst l \<bullet> i .. snd l \<bullet> i} \<and> l \<in> {(a, c), (c, d), (d, b)}"
          by auto
      qed
      then obtain f where
        f: "\<forall>i\<in>Basis. x \<bullet> i \<in> {fst (f i) \<bullet> i..snd (f i) \<bullet> i} \<and> f i \<in> {(a, c), (c, d), (d, b)}"
        unfolding bchoice_iff ..
      moreover from f have "restrict f Basis \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}"
        by auto
      moreover from f have "x \<in> ?B (restrict f Basis)"
        by (auto simp: mem_box)
      ultimately have "\<exists>k\<in>p. x \<in> k"
        unfolding p_def by blast
    }
    ultimately show "\<Union>p = cbox a b"
      by auto
  qed
qed

lemma partial_division_extend_interval:
  assumes "p division_of (\<Union>p)" "(\<Union>p) \<subseteq> cbox a b"
  obtains q where "p \<subseteq> q" "q division_of cbox a (b::'a::euclidean_space)"
proof (cases "p = {}")
  case True
  obtain q where "q division_of (cbox a b)"
    by (rule elementary_interval)
  then show ?thesis
    apply -
    apply (rule that[of q])
    unfolding True
    apply auto
    done
next
  case False
  note p = division_ofD[OF assms(1)]
  have *: "\<forall>k\<in>p. \<exists>q. q division_of cbox a b \<and> k \<in> q"
  proof
    case goal1
    obtain c d where k: "k = cbox c d"
      using p(4)[OF goal1] by blast
    have *: "cbox c d \<subseteq> cbox a b" "cbox c d \<noteq> {}"
      using p(2,3)[OF goal1, unfolded k] using assms(2)
      by (blast intro: order.trans)+
    obtain q where "q division_of cbox a b" "cbox c d \<in> q"
      by (rule partial_division_extend_1[OF *])
    then show ?case
      unfolding k by auto
  qed
  obtain q where q: "\<And>x. x \<in> p \<Longrightarrow> q x division_of cbox a b" "\<And>x. x \<in> p \<Longrightarrow> x \<in> q x"
    using bchoice[OF *] by blast
  have "\<And>x. x \<in> p \<Longrightarrow> \<exists>d. d division_of \<Union>(q x - {x})"
    apply rule
    apply (rule_tac p="q x" in division_of_subset)
  proof -
    fix x
    assume x: "x \<in> p"
    show "q x division_of \<Union>q x"
      apply -
      apply (rule division_ofI)
      using division_ofD[OF q(1)[OF x]]
      apply auto
      done
    show "q x - {x} \<subseteq> q x"
      by auto
  qed
  then have "\<exists>d. d division_of \<Inter> ((\<lambda>i. \<Union>(q i - {i})) ` p)"
    apply -
    apply (rule elementary_inters)
    apply (rule finite_imageI[OF p(1)])
    unfolding image_is_empty
    apply (rule False)
    apply auto
    done
  then obtain d where d: "d division_of \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p)" ..
  show ?thesis
    apply (rule that[of "d \<union> p"])
  proof -
    have *: "\<And>s f t. s \<noteq> {} \<Longrightarrow> \<forall>i\<in>s. f i \<union> i = t \<Longrightarrow> t = \<Inter>(f ` s) \<union> \<Union>s" by auto
    have *: "cbox a b = \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p) \<union> \<Union>p"
      apply (rule *[OF False])
    proof
      fix i
      assume i: "i \<in> p"
      show "\<Union>(q i - {i}) \<union> i = cbox a b"
        using division_ofD(6)[OF q(1)[OF i]] using q(2)[OF i] by auto
    qed
    show "d \<union> p division_of (cbox a b)"
      unfolding *
      apply (rule division_disjoint_union[OF d assms(1)])
      apply (rule inter_interior_unions_intervals)
      apply (rule p open_interior ballI)+
      apply assumption
    proof
      fix k
      assume k: "k \<in> p"
      have *: "\<And>u t s. u \<subseteq> s \<Longrightarrow> s \<inter> t = {} \<Longrightarrow> u \<inter> t = {}"
        by auto
      show "interior (\<Inter> ((\<lambda>i. \<Union>(q i - {i})) ` p)) \<inter> interior k = {}"
        apply (rule *[of _ "interior (\<Union>(q k - {k}))"])
        defer
        apply (subst Int_commute)
        apply (rule inter_interior_unions_intervals)
      proof -
        note qk=division_ofD[OF q(1)[OF k]]
        show "finite (q k - {k})" "open (interior k)" "\<forall>t\<in>q k - {k}. \<exists>a b. t = cbox a b"
          using qk by auto
        show "\<forall>t\<in>q k - {k}. interior k \<inter> interior t = {}"
          using qk(5) using q(2)[OF k] by auto
        have *: "\<And>x s. x \<in> s \<Longrightarrow> \<Inter>s \<subseteq> x"
          by auto
        show "interior (\<Inter> ((\<lambda>i. \<Union>(q i - {i})) ` p)) \<subseteq> interior (\<Union>(q k - {k}))"
          apply (rule interior_mono *)+
          using k
          apply auto
          done
      qed
    qed
  qed auto
qed

lemma elementary_bounded[dest]:
  fixes s :: "'a::euclidean_space set"
  shows "p division_of s \<Longrightarrow> bounded s"
  unfolding division_of_def by (metis bounded_Union bounded_cbox)

lemma elementary_subset_cbox:
  "p division_of s \<Longrightarrow> \<exists>a b. s \<subseteq> cbox a (b::'a::euclidean_space)"
  by (meson elementary_bounded bounded_subset_cbox)

lemma division_union_intervals_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
  obtains p where "(insert (cbox a b) p) division_of (cbox a b \<union> cbox c d)"
proof (cases "cbox c d = {}")
  case True
  show ?thesis
    apply (rule that[of "{}"])
    unfolding True
    using assms
    apply auto
    done
next
  case False
  show ?thesis
  proof (cases "cbox a b \<inter> cbox c d = {}")
    case True
    have *: "\<And>a b. {a, b} = {a} \<union> {b}" by auto
    show ?thesis
      apply (rule that[of "{cbox c d}"])
      unfolding *
      apply (rule division_disjoint_union)
      using `cbox c d \<noteq> {}` True assms
      using interior_subset
      apply auto
      done
  next
    case False
    obtain u v where uv: "cbox a b \<inter> cbox c d = cbox u v"
      unfolding inter_interval by auto
    have *: "cbox u v \<subseteq> cbox c d" using uv by auto
    obtain p where "p division_of cbox c d" "cbox u v \<in> p"
      by (rule partial_division_extend_1[OF * False[unfolded uv]])
    note p = this division_ofD[OF this(1)]
    have *: "cbox a b \<union> cbox c d = cbox a b \<union> \<Union>(p - {cbox u v})" "\<And>x s. insert x s = {x} \<union> s"
      using p(8) unfolding uv[symmetric] by auto
    show ?thesis
      apply (rule that[of "p - {cbox u v}"])
      unfolding *(1)
      apply (subst *(2))
      apply (rule division_disjoint_union)
      apply (rule, rule assms)
      apply (rule division_of_subset[of p])
      apply (rule division_of_union_self[OF p(1)])
      defer
      unfolding interior_inter[symmetric]
    proof -
      have *: "\<And>cd p uv ab. p \<subseteq> cd \<Longrightarrow> ab \<inter> cd = uv \<Longrightarrow> ab \<inter> p = uv \<inter> p" by auto
      have "interior (cbox a b \<inter> \<Union>(p - {cbox u v})) = interior(cbox u v \<inter> \<Union>(p - {cbox u v}))"
        apply (rule arg_cong[of _ _ interior])
        apply (rule *[OF _ uv])
        using p(8)
        apply auto
        done
      also have "\<dots> = {}"
        unfolding interior_inter
        apply (rule inter_interior_unions_intervals)
        using p(6) p(7)[OF p(2)] p(3)
        apply auto
        done
      finally show "interior (cbox a b \<inter> \<Union>(p - {cbox u v})) = {}" .
    qed auto
  qed
qed

lemma division_of_unions:
  assumes "finite f"
    and "\<And>p. p \<in> f \<Longrightarrow> p division_of (\<Union>p)"
    and "\<And>k1 k2. k1 \<in> \<Union>f \<Longrightarrow> k2 \<in> \<Union>f \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  shows "\<Union>f division_of \<Union>\<Union>f"
  apply (rule division_ofI)
  prefer 5
  apply (rule assms(3)|assumption)+
  apply (rule finite_Union assms(1))+
  prefer 3
  apply (erule UnionE)
  apply (rule_tac s=X in division_ofD(3)[OF assms(2)])
  using division_ofD[OF assms(2)]
  apply auto
  done

lemma elementary_union_interval:
  fixes a b :: "'a::euclidean_space"
  assumes "p division_of \<Union>p"
  obtains q where "q division_of (cbox a b \<union> \<Union>p)"
proof -
  note assm = division_ofD[OF assms]
  have lem1: "\<And>f s. \<Union>\<Union>(f ` s) = \<Union>((\<lambda>x. \<Union>(f x)) ` s)"
    by auto
  have lem2: "\<And>f s. f \<noteq> {} \<Longrightarrow> \<Union>{s \<union> t |t. t \<in> f} = s \<union> \<Union>f"
    by auto
  {
    presume "p = {} \<Longrightarrow> thesis"
      "cbox a b = {} \<Longrightarrow> thesis"
      "cbox a b \<noteq> {} \<Longrightarrow> interior (cbox a b) = {} \<Longrightarrow> thesis"
      "p \<noteq> {} \<Longrightarrow> interior (cbox a b)\<noteq>{} \<Longrightarrow> cbox a b \<noteq> {} \<Longrightarrow> thesis"
    then show thesis by auto
  next
    assume as: "p = {}"
    obtain p where "p division_of (cbox a b)"
      by (rule elementary_interval)
    then show thesis
      apply -
      apply (rule that[of p])
      unfolding as
      apply auto
      done
  next
    assume as: "cbox a b = {}"
    show thesis
      apply (rule that)
      unfolding as
      using assms
      apply auto
      done
  next
    assume as: "interior (cbox a b) = {}" "cbox a b \<noteq> {}"
    show thesis
      apply (rule that[of "insert (cbox a b) p"],rule division_ofI)
      unfolding finite_insert
      apply (rule assm(1)) unfolding Union_insert
      using assm(2-4) as
      apply -
      apply (fast dest: assm(5))+
      done
  next
    assume as: "p \<noteq> {}" "interior (cbox a b) \<noteq> {}" "cbox a b \<noteq> {}"
    have "\<forall>k\<in>p. \<exists>q. (insert (cbox a b) q) division_of (cbox a b \<union> k)"
    proof
      case goal1
      from assm(4)[OF this] obtain c d where "k = cbox c d" by blast
      then show ?case
        apply -
        apply (rule division_union_intervals_exists[OF as(3), of c d])
        apply auto
        done
    qed
    from bchoice[OF this] obtain q where "\<forall>x\<in>p. insert (cbox a b) (q x) division_of (cbox a b) \<union> x" ..
    note q = division_ofD[OF this[rule_format]]
    let ?D = "\<Union>{insert (cbox a b) (q k) | k. k \<in> p}"
    show thesis
      apply (rule that[of "?D"])
      apply (rule division_ofI)
    proof -
      have *: "{insert (cbox a b) (q k) |k. k \<in> p} = (\<lambda>k. insert (cbox a b) (q k)) ` p"
        by auto
      show "finite ?D"
        apply (rule finite_Union)
        unfolding *
        apply (rule finite_imageI)
        using assm(1) q(1)
        apply auto
        done
      show "\<Union>?D = cbox a b \<union> \<Union>p"
        unfolding * lem1
        unfolding lem2[OF as(1), of "cbox a b", symmetric]
        using q(6)
        by auto
      fix k
      assume k: "k \<in> ?D"
      then show "k \<subseteq> cbox a b \<union> \<Union>p"
        using q(2) by auto
      show "k \<noteq> {}"
        using q(3) k by auto
      show "\<exists>a b. k = cbox a b"
        using q(4) k by auto
      fix k'
      assume k': "k' \<in> ?D" "k \<noteq> k'"
      obtain x where x: "k \<in> insert (cbox a b) (q x)" "x\<in>p"
        using k by auto
      obtain x' where x': "k'\<in>insert (cbox a b) (q x')" "x'\<in>p"
        using k' by auto
      show "interior k \<inter> interior k' = {}"
      proof (cases "x = x'")
        case True
        show ?thesis
          apply(rule q(5))
          using x x' k'
          unfolding True
          apply auto
          done
      next
        case False
        {
          presume "k = cbox a b \<Longrightarrow> ?thesis"
            and "k' = cbox a b \<Longrightarrow> ?thesis"
            and "k \<noteq> cbox a b \<Longrightarrow> k' \<noteq> cbox a b \<Longrightarrow> ?thesis"
          then show ?thesis by auto
        next
          assume as': "k  = cbox a b"
          show ?thesis
            apply (rule q(5))
            using x' k'(2)
            unfolding as'
            apply auto
            done
        next
          assume as': "k' = cbox a b"
          show ?thesis
            apply (rule q(5))
            using x  k'(2)
            unfolding as'
            apply auto
            done
        }
        assume as': "k \<noteq> cbox a b" "k' \<noteq> cbox a b"
        obtain c d where k: "k = cbox c d"
          using q(4)[OF x(2,1)] by blast
        have "interior k \<inter> interior (cbox a b) = {}"
          apply (rule q(5))
          using x k'(2)
          using as'
          apply auto
          done
        then have "interior k \<subseteq> interior x"
          apply -
          apply (rule interior_subset_union_intervals[OF k _ as(2) q(2)[OF x(2,1)]])
          apply auto
          done
        moreover
        obtain c d where c_d: "k' = cbox c d"
          using q(4)[OF x'(2,1)] by blast
        have "interior k' \<inter> interior (cbox a b) = {}"
          apply (rule q(5))
          using x' k'(2)
          using as'
          apply auto
          done
        then have "interior k' \<subseteq> interior x'"
          apply -
          apply (rule interior_subset_union_intervals[OF c_d _ as(2) q(2)[OF x'(2,1)]])
          apply auto
          done
        ultimately show ?thesis
          using assm(5)[OF x(2) x'(2) False] by auto
      qed
    qed
  }
qed

lemma elementary_unions_intervals:
  assumes fin: "finite f"
    and "\<And>s. s \<in> f \<Longrightarrow> \<exists>a b. s = cbox a (b::'a::euclidean_space)"
  obtains p where "p division_of (\<Union>f)"
proof -
  have "\<exists>p. p division_of (\<Union>f)"
  proof (induct_tac f rule:finite_subset_induct)
    show "\<exists>p. p division_of \<Union>{}" using elementary_empty by auto
  next
    fix x F
    assume as: "finite F" "x \<notin> F" "\<exists>p. p division_of \<Union>F" "x\<in>f"
    from this(3) obtain p where p: "p division_of \<Union>F" ..
    from assms(2)[OF as(4)] obtain a b where x: "x = cbox a b" by blast
    have *: "\<Union>F = \<Union>p"
      using division_ofD[OF p] by auto
    show "\<exists>p. p division_of \<Union>insert x F"
      using elementary_union_interval[OF p[unfolded *], of a b]
      unfolding Union_insert x * by auto
  qed (insert assms, auto)
  then show ?thesis
    apply -
    apply (erule exE)
    apply (rule that)
    apply auto
    done
qed

lemma elementary_union:
  fixes s t :: "'a::euclidean_space set"
  assumes "ps division_of s"
    and "pt division_of t"
  obtains p where "p division_of (s \<union> t)"
proof -
  have "s \<union> t = \<Union>ps \<union> \<Union>pt"
    using assms unfolding division_of_def by auto
  then have *: "\<Union>(ps \<union> pt) = s \<union> t" by auto
  show ?thesis
    apply -
    apply (rule elementary_unions_intervals[of "ps \<union> pt"])
    unfolding *
    prefer 3
    apply (rule_tac p=p in that)
    using assms[unfolded division_of_def]
    apply auto
    done
qed

lemma partial_division_extend:
  fixes t :: "'a::euclidean_space set"
  assumes "p division_of s"
    and "q division_of t"
    and "s \<subseteq> t"
  obtains r where "p \<subseteq> r" and "r division_of t"
proof -
  note divp = division_ofD[OF assms(1)] and divq = division_ofD[OF assms(2)]
  obtain a b where ab: "t \<subseteq> cbox a b"
    using elementary_subset_cbox[OF assms(2)] by auto
  obtain r1 where "p \<subseteq> r1" "r1 division_of (cbox a b)"
    apply (rule partial_division_extend_interval)
    apply (rule assms(1)[unfolded divp(6)[symmetric]])
    apply (rule subset_trans)
    apply (rule ab assms[unfolded divp(6)[symmetric]])+
    apply assumption
    done
  note r1 = this division_ofD[OF this(2)]
  obtain p' where "p' division_of \<Union>(r1 - p)"
    apply (rule elementary_unions_intervals[of "r1 - p"])
    using r1(3,6)
    apply auto
    done
  then obtain r2 where r2: "r2 division_of (\<Union>(r1 - p)) \<inter> (\<Union>q)"
    apply -
    apply (drule elementary_inter[OF _ assms(2)[unfolded divq(6)[symmetric]]])
    apply auto
    done
  {
    fix x
    assume x: "x \<in> t" "x \<notin> s"
    then have "x\<in>\<Union>r1"
      unfolding r1 using ab by auto
    then obtain r where r: "r \<in> r1" "x \<in> r"
      unfolding Union_iff ..
    moreover
    have "r \<notin> p"
    proof
      assume "r \<in> p"
      then have "x \<in> s" using divp(2) r by auto
      then show False using x by auto
    qed
    ultimately have "x\<in>\<Union>(r1 - p)" by auto
  }
  then have *: "t = \<Union>p \<union> (\<Union>(r1 - p) \<inter> \<Union>q)"
    unfolding divp divq using assms(3) by auto
  show ?thesis
    apply (rule that[of "p \<union> r2"])
    unfolding *
    defer
    apply (rule division_disjoint_union)
    unfolding divp(6)
    apply(rule assms r2)+
  proof -
    have "interior s \<inter> interior (\<Union>(r1-p)) = {}"
    proof (rule inter_interior_unions_intervals)
      show "finite (r1 - p)" and "open (interior s)" and "\<forall>t\<in>r1-p. \<exists>a b. t = cbox a b"
        using r1 by auto
      have *: "\<And>s. (\<And>x. x \<in> s \<Longrightarrow> False) \<Longrightarrow> s = {}"
        by auto
      show "\<forall>t\<in>r1-p. interior s \<inter> interior t = {}"
      proof
        fix m x
        assume as: "m \<in> r1 - p"
        have "interior m \<inter> interior (\<Union>p) = {}"
        proof (rule inter_interior_unions_intervals)
          show "finite p" and "open (interior m)" and "\<forall>t\<in>p. \<exists>a b. t = cbox a b"
            using divp by auto
          show "\<forall>t\<in>p. interior m \<inter> interior t = {}"
            apply (rule, rule r1(7))
            using as
            using r1 
            apply auto
            done
        qed
        then show "interior s \<inter> interior m = {}"
          unfolding divp by auto
      qed
    qed
    then show "interior s \<inter> interior (\<Union>(r1-p) \<inter> (\<Union>q)) = {}"
      using interior_subset by auto
  qed auto
qed


subsection {* Tagged (partial) divisions. *}

definition tagged_partial_division_of (infixr "tagged'_partial'_division'_of" 40)
  where "s tagged_partial_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x k. (x, k) \<in> s \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>x1 k1 x2 k2. (x1, k1) \<in> s \<and> (x2, k2) \<in> s \<and> (x1, k1) \<noteq> (x2, k2) \<longrightarrow>
      interior k1 \<inter> interior k2 = {})"

lemma tagged_partial_division_ofD[dest]:
  assumes "s tagged_partial_division_of i"
  shows "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow>
      (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  using assms unfolding tagged_partial_division_of_def by blast+

definition tagged_division_of (infixr "tagged'_division'_of" 40)
  where "s tagged_division_of i \<longleftrightarrow> s tagged_partial_division_of i \<and> (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"

lemma tagged_division_of_finite: "s tagged_division_of i \<Longrightarrow> finite s"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_of:
  "s tagged_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x k. (x, k) \<in> s \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>x1 k1 x2 k2. (x1, k1) \<in> s \<and> (x2, k2) \<in> s \<and> (x1, k1) \<noteq> (x2, k2) \<longrightarrow>
      interior k1 \<inter> interior k2 = {}) \<and>
    (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_ofI:
  assumes "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow> (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow>
      interior k1 \<inter> interior k2 = {}"
    and "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  shows "s tagged_division_of i"
  unfolding tagged_division_of
  apply rule
  defer
  apply rule
  apply (rule allI impI conjI assms)+
  apply assumption
  apply rule
  apply (rule assms)
  apply assumption
  apply (rule assms)
  apply assumption
  using assms(1,5-)
  apply blast+
  done

lemma tagged_division_ofD[dest]:
  assumes "s tagged_division_of i"
  shows "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1, k1) \<in> s \<Longrightarrow> (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow>
      interior k1 \<inter> interior k2 = {}"
    and "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  using assms unfolding tagged_division_of by blast+

lemma division_of_tagged_division:
  assumes "s tagged_division_of i"
  shows "(snd ` s) division_of i"
proof (rule division_ofI)
  note assm = tagged_division_ofD[OF assms]
  show "\<Union>(snd ` s) = i" "finite (snd ` s)"
    using assm by auto
  fix k
  assume k: "k \<in> snd ` s"
  then obtain xk where xk: "(xk, k) \<in> s"
    by auto
  then show "k \<subseteq> i" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
    using assm by fastforce+
  fix k'
  assume k': "k' \<in> snd ` s" "k \<noteq> k'"
  from this(1) obtain xk' where xk': "(xk', k') \<in> s"
    by auto
  then show "interior k \<inter> interior k' = {}"
    apply -
    apply (rule assm(5))
    apply (rule xk xk')+
    using k'
    apply auto
    done
qed

lemma partial_division_of_tagged_division:
  assumes "s tagged_partial_division_of i"
  shows "(snd ` s) division_of \<Union>(snd ` s)"
proof (rule division_ofI)
  note assm = tagged_partial_division_ofD[OF assms]
  show "finite (snd ` s)" "\<Union>(snd ` s) = \<Union>(snd ` s)"
    using assm by auto
  fix k
  assume k: "k \<in> snd ` s"
  then obtain xk where xk: "(xk, k) \<in> s"
    by auto
  then show "k \<noteq> {}" "\<exists>a b. k = cbox a b" "k \<subseteq> \<Union>(snd ` s)"
    using assm by auto
  fix k'
  assume k': "k' \<in> snd ` s" "k \<noteq> k'"
  from this(1) obtain xk' where xk': "(xk', k') \<in> s"
    by auto
  then show "interior k \<inter> interior k' = {}"
    apply -
    apply (rule assm(5))
    apply(rule xk xk')+
    using k'
    apply auto
    done
qed

lemma tagged_partial_division_subset:
  assumes "s tagged_partial_division_of i"
    and "t \<subseteq> s"
  shows "t tagged_partial_division_of i"
  using assms
  unfolding tagged_partial_division_of_def
  using finite_subset[OF assms(2)]
  by blast

lemma setsum_over_tagged_division_lemma:
  fixes d :: "'m::euclidean_space set \<Rightarrow> 'a::real_normed_vector"
  assumes "p tagged_division_of i"
    and "\<And>u v. cbox u v \<noteq> {} \<Longrightarrow> content (cbox u v) = 0 \<Longrightarrow> d (cbox u v) = 0"
  shows "setsum (\<lambda>(x,k). d k) p = setsum d (snd ` p)"
proof -
  note assm = tagged_division_ofD[OF assms(1)]
  have *: "(\<lambda>(x,k). d k) = d \<circ> snd"
    unfolding o_def by (rule ext) auto
  show ?thesis
    unfolding *
    apply (subst eq_commute)
  proof (rule setsum_reindex_nonzero)
    show "finite p"
      using assm by auto
    fix x y
    assume as: "x\<in>p" "y\<in>p" "x\<noteq>y" "snd x = snd y"
    obtain a b where ab: "snd x = cbox a b"
      using assm(4)[of "fst x" "snd x"] as(1) by auto
    have "(fst x, snd y) \<in> p" "(fst x, snd y) \<noteq> y"
      unfolding as(4)[symmetric] using as(1-3) by auto
    then have "interior (snd x) \<inter> interior (snd y) = {}"
      apply -
      apply (rule assm(5)[of "fst x" _ "fst y"])
      using as
      apply auto
      done
    then have "content (cbox a b) = 0"
      unfolding as(4)[symmetric] ab content_eq_0_interior by auto
    then have "d (cbox a b) = 0"
      apply -
      apply (rule assms(2))
      using assm(2)[of "fst x" "snd x"] as(1)
      unfolding ab[symmetric]
      apply auto
      done
    then show "d (snd x) = 0"
      unfolding ab by auto
  qed
qed

lemma tag_in_interval: "p tagged_division_of i \<Longrightarrow> (x, k) \<in> p \<Longrightarrow> x \<in> i"
  by auto

lemma tagged_division_of_empty: "{} tagged_division_of {}"
  unfolding tagged_division_of by auto

lemma tagged_partial_division_of_trivial[simp]: "p tagged_partial_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_partial_division_of_def by auto

lemma tagged_division_of_trivial[simp]: "p tagged_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_division_of by auto

lemma tagged_division_of_self: "x \<in> cbox a b \<Longrightarrow> {(x,cbox a b)} tagged_division_of (cbox a b)"
  by (rule tagged_division_ofI) auto

lemma tagged_division_of_self_real: "x \<in> {a .. b::real} \<Longrightarrow> {(x,{a .. b})} tagged_division_of {a .. b}"
  unfolding box_real[symmetric]
  by (rule tagged_division_of_self)

lemma tagged_division_union:
  assumes "p1 tagged_division_of s1"
    and "p2 tagged_division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) tagged_division_of (s1 \<union> s2)"
proof (rule tagged_division_ofI)
  note p1 = tagged_division_ofD[OF assms(1)]
  note p2 = tagged_division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)"
    using p1(1) p2(1) by auto
  show "\<Union>{k. \<exists>x. (x, k) \<in> p1 \<union> p2} = s1 \<union> s2"
    using p1(6) p2(6) by blast
  fix x k
  assume xk: "(x, k) \<in> p1 \<union> p2"
  show "x \<in> k" "\<exists>a b. k = cbox a b"
    using xk p1(2,4) p2(2,4) by auto
  show "k \<subseteq> s1 \<union> s2"
    using xk p1(3) p2(3) by blast
  fix x' k'
  assume xk': "(x', k') \<in> p1 \<union> p2" "(x, k) \<noteq> (x', k')"
  have *: "\<And>a b. a \<subseteq> s1 \<Longrightarrow> b \<subseteq> s2 \<Longrightarrow> interior a \<inter> interior b = {}"
    using assms(3) interior_mono by blast
  show "interior k \<inter> interior k' = {}"
    apply (cases "(x, k) \<in> p1")
    apply (case_tac[!] "(x',k') \<in> p1")
    apply (rule p1(5))
    prefer 4
    apply (rule *)
    prefer 6
    apply (subst Int_commute)
    apply (rule *)
    prefer 8
    apply (rule p2(5))
    using p1(3) p2(3)
    using xk xk'
    apply auto
    done
qed

lemma tagged_division_unions:
  assumes "finite iset"
    and "\<forall>i\<in>iset. pfn i tagged_division_of i"
    and "\<forall>i1\<in>iset. \<forall>i2\<in>iset. i1 \<noteq> i2 \<longrightarrow> interior(i1) \<inter> interior(i2) = {}"
  shows "\<Union>(pfn ` iset) tagged_division_of (\<Union>iset)"
proof (rule tagged_division_ofI)
  note assm = tagged_division_ofD[OF assms(2)[rule_format]]
  show "finite (\<Union>(pfn ` iset))"
    apply (rule finite_Union)
    using assms
    apply auto
    done
  have "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` iset)} = \<Union>((\<lambda>i. \<Union>{k. \<exists>x. (x, k) \<in> pfn i}) ` iset)"
    by blast
  also have "\<dots> = \<Union>iset"
    using assm(6) by auto
  finally show "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` iset)} = \<Union>iset" .
  fix x k
  assume xk: "(x, k) \<in> \<Union>(pfn ` iset)"
  then obtain i where i: "i \<in> iset" "(x, k) \<in> pfn i"
    by auto
  show "x \<in> k" "\<exists>a b. k = cbox a b" "k \<subseteq> \<Union>iset"
    using assm(2-4)[OF i] using i(1) by auto
  fix x' k'
  assume xk': "(x', k') \<in> \<Union>(pfn ` iset)" "(x, k) \<noteq> (x', k')"
  then obtain i' where i': "i' \<in> iset" "(x', k') \<in> pfn i'"
    by auto
  have *: "\<And>a b. i \<noteq> i' \<Longrightarrow> a \<subseteq> i \<Longrightarrow> b \<subseteq> i' \<Longrightarrow> interior a \<inter> interior b = {}"
    using i(1) i'(1)
    using assms(3)[rule_format] interior_mono
    by blast
  show "interior k \<inter> interior k' = {}"
    apply (cases "i = i'")
    using assm(5)[OF i _ xk'(2)] i'(2)
    using assm(3)[OF i] assm(3)[OF i']
    defer
    apply -
    apply (rule *)
    apply auto
    done
qed

lemma tagged_partial_division_of_union_self:
  assumes "p tagged_partial_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
  apply (rule tagged_division_ofI)
  using tagged_partial_division_ofD[OF assms]
  apply auto
  done

lemma tagged_division_of_union_self:
  assumes "p tagged_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
  apply (rule tagged_division_ofI)
  using tagged_division_ofD[OF assms]
  apply auto
  done


subsection {* Fine-ness of a partition w.r.t. a gauge. *}

definition fine  (infixr "fine" 46)
  where "d fine s \<longleftrightarrow> (\<forall>(x,k) \<in> s. k \<subseteq> d x)"

lemma fineI:
  assumes "\<And>x k. (x, k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  shows "d fine s"
  using assms unfolding fine_def by auto

lemma fineD[dest]:
  assumes "d fine s"
  shows "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  using assms unfolding fine_def by auto

lemma fine_inter: "(\<lambda>x. d1 x \<inter> d2 x) fine p \<longleftrightarrow> d1 fine p \<and> d2 fine p"
  unfolding fine_def by auto

lemma fine_inters:
 "(\<lambda>x. \<Inter> {f d x | d.  d \<in> s}) fine p \<longleftrightarrow> (\<forall>d\<in>s. (f d) fine p)"
  unfolding fine_def by blast

lemma fine_union: "d fine p1 \<Longrightarrow> d fine p2 \<Longrightarrow> d fine (p1 \<union> p2)"
  unfolding fine_def by blast

lemma fine_unions: "(\<And>p. p \<in> ps \<Longrightarrow> d fine p) \<Longrightarrow> d fine (\<Union>ps)"
  unfolding fine_def by auto

lemma fine_subset: "p \<subseteq> q \<Longrightarrow> d fine q \<Longrightarrow> d fine p"
  unfolding fine_def by blast


subsection {* Gauge integral. Define on compact intervals first, then use a limit. *}

definition has_integral_compact_interval (infixr "has'_integral'_compact'_interval" 46)
  where "(f has_integral_compact_interval y) i \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of i \<and> d fine p \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - y) < e))"

definition has_integral ::
    "('n::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> 'n set \<Rightarrow> bool"
  (infixr "has'_integral" 46)
  where "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral_compact_interval y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral_compact_interval z) (cbox a b) \<and>
        norm (z - y) < e)))"

lemma has_integral:
  "(f has_integral y) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f x) p - y) < e))"
  unfolding has_integral_def has_integral_compact_interval_def
  by auto

lemma has_integral_real:
  "(f has_integral y) {a .. b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of {a .. b} \<and> d fine p \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f x) p - y) < e))"
  unfolding box_real[symmetric]
  by (rule has_integral)

lemma has_integralD[dest]:
  assumes "(f has_integral y) (cbox a b)"
    and "e > 0"
  obtains d where "gauge d"
    and "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d fine p \<Longrightarrow>
      norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f(x)) p - y) < e"
  using assms unfolding has_integral by auto

lemma has_integral_alt:
  "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)))"
  unfolding has_integral
  unfolding has_integral_compact_interval_def has_integral_def
  by auto

lemma has_integral_altD:
  assumes "(f has_integral y) i"
    and "\<not> (\<exists>a b. i = cbox a b)"
    and "e>0"
  obtains B where "B > 0"
    and "\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - y) < e)"
  using assms
  unfolding has_integral
  unfolding has_integral_compact_interval_def has_integral_def
  by auto

definition integrable_on (infixr "integrable'_on" 46)
  where "f integrable_on i \<longleftrightarrow> (\<exists>y. (f has_integral y) i)"

definition "integral i f = (SOME y. (f has_integral y) i)"

lemma integrable_integral[dest]: "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
  unfolding integrable_on_def integral_def by (rule someI_ex)

lemma has_integral_integrable[intro]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
  unfolding integrable_on_def by auto

lemma has_integral_integral: "f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
  by auto

lemma setsum_content_null:
  assumes "content (cbox a b) = 0"
    and "p tagged_division_of (cbox a b)"
  shows "setsum (\<lambda>(x,k). content k *\<^sub>R f x) p = (0::'a::real_normed_vector)"
proof (rule setsum_0', rule)
  fix y
  assume y: "y \<in> p"
  obtain x k where xk: "y = (x, k)"
    using surj_pair[of y] by blast
  note assm = tagged_division_ofD(3-4)[OF assms(2) y[unfolded xk]]
  from this(2) obtain c d where k: "k = cbox c d" by blast
  have "(\<lambda>(x, k). content k *\<^sub>R f x) y = content k *\<^sub>R f x"
    unfolding xk by auto
  also have "\<dots> = 0"
    using content_subset[OF assm(1)[unfolded k]] content_pos_le[of c d]
    unfolding assms(1) k
    by auto
  finally show "(\<lambda>(x, k). content k *\<^sub>R f x) y = 0" .
qed


subsection {* Some basic combining lemmas. *}

lemma tagged_division_unions_exists:
  assumes "finite iset"
    and "\<forall>i\<in>iset. \<exists>p. p tagged_division_of i \<and> d fine p"
    and "\<forall>i1\<in>iset. \<forall>i2\<in>iset. i1 \<noteq> i2 \<longrightarrow> interior i1 \<inter> interior i2 = {}"
    and "\<Union>iset = i"
   obtains p where "p tagged_division_of i" and "d fine p"
proof -
  obtain pfn where pfn:
    "\<And>x. x \<in> iset \<Longrightarrow> pfn x tagged_division_of x"
    "\<And>x. x \<in> iset \<Longrightarrow> d fine pfn x"
    using bchoice[OF assms(2)] by auto
  show thesis
    apply (rule_tac p="\<Union>(pfn ` iset)" in that)
    unfolding assms(4)[symmetric]
    apply (rule tagged_division_unions[OF assms(1) _ assms(3)])
    defer
    apply (rule fine_unions)
    using pfn
    apply auto
    done
qed


subsection {* The set we're concerned with must be closed. *}

lemma division_of_closed:
  fixes i :: "'n::euclidean_space set"
  shows "s division_of i \<Longrightarrow> closed i"
  unfolding division_of_def by fastforce

subsection {* General bisection principle for intervals; might be useful elsewhere. *}

lemma interval_bisection_step:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and "\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P (s \<union> t)"
    and "\<not> P (cbox a (b::'a))"
  obtains c d where "\<not> P (cbox c d)"
    and "\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
proof -
  have "cbox a b \<noteq> {}"
    using assms(1,3) by metis
  then have ab: "\<And>i. i\<in>Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
    by (force simp: mem_box)
  {
    fix f
    have "finite f \<Longrightarrow>
      \<forall>s\<in>f. P s \<Longrightarrow>
      \<forall>s\<in>f. \<exists>a b. s = cbox a b \<Longrightarrow>
      \<forall>s\<in>f.\<forall>t\<in>f. s \<noteq> t \<longrightarrow> interior s \<inter> interior t = {} \<Longrightarrow> P (\<Union>f)"
    proof (induct f rule: finite_induct)
      case empty
      show ?case
        using assms(1) by auto
    next
      case (insert x f)
      show ?case
        unfolding Union_insert
        apply (rule assms(2)[rule_format])
        apply rule
        defer
        apply rule
        defer
        apply (rule inter_interior_unions_intervals)
        using insert
        apply auto
        done
    qed
  } note * = this
  let ?A = "{cbox c d | c d::'a. \<forall>i\<in>Basis. (c\<bullet>i = a\<bullet>i) \<and> (d\<bullet>i = (a\<bullet>i + b\<bullet>i) / 2) \<or>
    (c\<bullet>i = (a\<bullet>i + b\<bullet>i) / 2) \<and> (d\<bullet>i = b\<bullet>i)}"
  let ?PP = "\<lambda>c d. \<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
  {
    presume "\<forall>c d. ?PP c d \<longrightarrow> P (cbox c d) \<Longrightarrow> False"
    then show thesis
      unfolding atomize_not not_all
      apply -
      apply (erule exE)+
      apply (rule_tac c=x and d=xa in that)
      apply auto
      done
  }
  assume as: "\<forall>c d. ?PP c d \<longrightarrow> P (cbox c d)"
  have "P (\<Union> ?A)"
    apply (rule *)
    apply (rule_tac[2-] ballI)
    apply (rule_tac[4] ballI)
    apply (rule_tac[4] impI)
  proof -
    let ?B = "(\<lambda>s. cbox (\<Sum>i\<in>Basis. (if i \<in> s then a\<bullet>i else (a\<bullet>i + b\<bullet>i) / 2) *\<^sub>R i::'a)
      (\<Sum>i\<in>Basis. (if i \<in> s then (a\<bullet>i + b\<bullet>i) / 2 else b\<bullet>i) *\<^sub>R i)) ` {s. s \<subseteq> Basis}"
    have "?A \<subseteq> ?B"
    proof
      case goal1
      then obtain c d where x: "x = cbox c d"
        "\<And>i. i \<in> Basis \<Longrightarrow>
          c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
          c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i" by blast
      have *: "\<And>a b c d. a = c \<Longrightarrow> b = d \<Longrightarrow> cbox a b = cbox c d"
        by auto
      show "x \<in> ?B"
        unfolding image_iff
        apply (rule_tac x="{i. i\<in>Basis \<and> c\<bullet>i = a\<bullet>i}" in bexI)
        unfolding x
        apply (rule *)
        apply (simp_all only: euclidean_eq_iff[where 'a='a] inner_setsum_left_Basis mem_Collect_eq simp_thms
          cong: ball_cong)
        apply safe
      proof -
        fix i :: 'a
        assume i: "i \<in> Basis"
        then show "c \<bullet> i = (if c \<bullet> i = a \<bullet> i then a \<bullet> i else (a \<bullet> i + b \<bullet> i) / 2)"
          and "d \<bullet> i = (if c \<bullet> i = a \<bullet> i then (a \<bullet> i + b \<bullet> i) / 2 else b \<bullet> i)"
          using x(2)[of i] ab[OF i] by (auto simp add:field_simps)
      qed
    qed
    then show "finite ?A"
      by (rule finite_subset) auto
    fix s
    assume "s \<in> ?A"
    then obtain c d where s:
      "s = cbox c d"
      "\<And>i. i \<in> Basis \<Longrightarrow>
         c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
         c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i"
      by blast
    show "P s"
      unfolding s
      apply (rule as[rule_format])
    proof -
      case goal1
      then show ?case
        using s(2)[of i] using ab[OF `i \<in> Basis`] by auto
    qed
    show "\<exists>a b. s = cbox a b"
      unfolding s by auto
    fix t
    assume "t \<in> ?A"
    then obtain e f where t:
      "t = cbox e f"
      "\<And>i. i \<in> Basis \<Longrightarrow>
        e \<bullet> i = a \<bullet> i \<and> f \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
        e \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> f \<bullet> i = b \<bullet> i"
      by blast
    assume "s \<noteq> t"
    then have "\<not> (c = e \<and> d = f)"
      unfolding s t by auto
    then obtain i where "c\<bullet>i \<noteq> e\<bullet>i \<or> d\<bullet>i \<noteq> f\<bullet>i" and i': "i \<in> Basis"
      unfolding euclidean_eq_iff[where 'a='a] by auto
    then have i: "c\<bullet>i \<noteq> e\<bullet>i" "d\<bullet>i \<noteq> f\<bullet>i"
      apply -
      apply(erule_tac[!] disjE)
    proof -
      assume "c\<bullet>i \<noteq> e\<bullet>i"
      then show "d\<bullet>i \<noteq> f\<bullet>i"
        using s(2)[OF i'] t(2)[OF i'] by fastforce
    next
      assume "d\<bullet>i \<noteq> f\<bullet>i"
      then show "c\<bullet>i \<noteq> e\<bullet>i"
        using s(2)[OF i'] t(2)[OF i'] by fastforce
    qed
    have *: "\<And>s t. (\<And>a. a \<in> s \<Longrightarrow> a \<in> t \<Longrightarrow> False) \<Longrightarrow> s \<inter> t = {}"
      by auto
    show "interior s \<inter> interior t = {}"
      unfolding s t interior_cbox
    proof (rule *)
      fix x
      assume "x \<in> box c d" "x \<in> box e f"
      then have x: "c\<bullet>i < d\<bullet>i" "e\<bullet>i < f\<bullet>i" "c\<bullet>i < f\<bullet>i" "e\<bullet>i < d\<bullet>i"
        unfolding mem_box using i'
        apply -
        apply (erule_tac[!] x=i in ballE)+
        apply auto
        done
      show False
        using s(2)[OF i']
        apply -
        apply (erule_tac disjE)
        apply (erule_tac[!] conjE)
      proof -
        assume as: "c \<bullet> i = a \<bullet> i" "d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2"
        show False
          using t(2)[OF i'] and i x unfolding as by (fastforce simp add:field_simps)
      next
        assume as: "c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2" "d \<bullet> i = b \<bullet> i"
        show False
          using t(2)[OF i'] and i x unfolding as by(fastforce simp add:field_simps)
      qed
    qed
  qed
  also have "\<Union> ?A = cbox a b"
  proof (rule set_eqI,rule)
    fix x
    assume "x \<in> \<Union>?A"
    then obtain c d where x:
      "x \<in> cbox c d"
      "\<And>i. i \<in> Basis \<Longrightarrow>
        c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
        c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i" by blast
    show "x\<in>cbox a b"
      unfolding mem_box
    proof safe
      fix i :: 'a
      assume i: "i \<in> Basis"
      then show "a \<bullet> i \<le> x \<bullet> i" "x \<bullet> i \<le> b \<bullet> i"
        using x(2)[OF i] x(1)[unfolded mem_box,THEN bspec, OF i] by auto
    qed
  next
    fix x
    assume x: "x \<in> cbox a b"
    have "\<forall>i\<in>Basis.
      \<exists>c d. (c = a\<bullet>i \<and> d = (a\<bullet>i + b\<bullet>i) / 2 \<or> c = (a\<bullet>i + b\<bullet>i) / 2 \<and> d = b\<bullet>i) \<and> c\<le>x\<bullet>i \<and> x\<bullet>i \<le> d"
      (is "\<forall>i\<in>Basis. \<exists>c d. ?P i c d")
      unfolding mem_box
    proof
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "?P i (a\<bullet>i) ((a \<bullet> i + b \<bullet> i) / 2) \<or> ?P i ((a \<bullet> i + b \<bullet> i) / 2) (b\<bullet>i)"
        using x[unfolded mem_box,THEN bspec, OF i] by auto
      then show "\<exists>c d. ?P i c d"
        by blast
    qed
    then show "x\<in>\<Union>?A"
      unfolding Union_iff Bex_def mem_Collect_eq choice_Basis_iff
      apply -
      apply (erule exE)+
      apply (rule_tac x="cbox xa xaa" in exI)
      unfolding mem_box
      apply auto
      done
  qed
  finally show False
    using assms by auto
qed

lemma interval_bisection:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))"
    and "\<not> P (cbox a (b::'a))"
  obtains x where "x \<in> cbox a b"
    and "\<forall>e>0. \<exists>c d. x \<in> cbox c d \<and> cbox c d \<subseteq> ball x e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
proof -
  have "\<forall>x. \<exists>y. \<not> P (cbox (fst x) (snd x)) \<longrightarrow> (\<not> P (cbox (fst y) (snd y)) \<and>
    (\<forall>i\<in>Basis. fst x\<bullet>i \<le> fst y\<bullet>i \<and> fst y\<bullet>i \<le> snd y\<bullet>i \<and> snd y\<bullet>i \<le> snd x\<bullet>i \<and>
       2 * (snd y\<bullet>i - fst y\<bullet>i) \<le> snd x\<bullet>i - fst x\<bullet>i))"
  proof
    case goal1
    then show ?case
    proof -
      presume "\<not> P (cbox (fst x) (snd x)) \<Longrightarrow> ?thesis"
      then show ?thesis by (cases "P (cbox (fst x) (snd x))") auto
    next
      assume as: "\<not> P (cbox (fst x) (snd x))"
      obtain c d where "\<not> P (cbox c d)"
        "\<forall>i\<in>Basis.
           fst x \<bullet> i \<le> c \<bullet> i \<and>
           c \<bullet> i \<le> d \<bullet> i \<and>
           d \<bullet> i \<le> snd x \<bullet> i \<and>
           2 * (d \<bullet> i - c \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i"
        by (rule interval_bisection_step[of P, OF assms(1-2) as])
      then show ?thesis
        apply -
        apply (rule_tac x="(c,d)" in exI)
        apply auto
        done
    qed
  qed
  then obtain f where f:
    "\<forall>x.
      \<not> P (cbox (fst x) (snd x)) \<longrightarrow>
      \<not> P (cbox (fst (f x)) (snd (f x))) \<and>
        (\<forall>i\<in>Basis.
            fst x \<bullet> i \<le> fst (f x) \<bullet> i \<and>
            fst (f x) \<bullet> i \<le> snd (f x) \<bullet> i \<and>
            snd (f x) \<bullet> i \<le> snd x \<bullet> i \<and>
            2 * (snd (f x) \<bullet> i - fst (f x) \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i)"
    apply -
    apply (drule choice)
    apply blast
    done
  def AB \<equiv> "\<lambda>n. (f ^^ n) (a,b)"
  def A \<equiv> "\<lambda>n. fst(AB n)"
  def B \<equiv> "\<lambda>n. snd(AB n)"
  note ab_def = A_def B_def AB_def
  have "A 0 = a" "B 0 = b" "\<And>n. \<not> P (cbox (A(Suc n)) (B(Suc n))) \<and>
    (\<forall>i\<in>Basis. A(n)\<bullet>i \<le> A(Suc n)\<bullet>i \<and> A(Suc n)\<bullet>i \<le> B(Suc n)\<bullet>i \<and> B(Suc n)\<bullet>i \<le> B(n)\<bullet>i \<and>
    2 * (B(Suc n)\<bullet>i - A(Suc n)\<bullet>i) \<le> B(n)\<bullet>i - A(n)\<bullet>i)" (is "\<And>n. ?P n")
  proof -
    show "A 0 = a" "B 0 = b"
      unfolding ab_def by auto
    case goal3
    note S = ab_def funpow.simps o_def id_apply
    show ?case
    proof (induct n)
      case 0
      then show ?case
        unfolding S
        apply (rule f[rule_format]) using assms(3)
        apply auto
        done
    next
      case (Suc n)
      show ?case
        unfolding S
        apply (rule f[rule_format])
        using Suc
        unfolding S
        apply auto
        done
    qed
  qed
  note AB = this(1-2) conjunctD2[OF this(3),rule_format]

  have interv: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. \<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e"
  proof -
    case goal1
    obtain n where n: "(\<Sum>i\<in>Basis. b \<bullet> i - a \<bullet> i) / e < 2 ^ n"
      using real_arch_pow2[of "(setsum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis) / e"] ..
    show ?case
      apply (rule_tac x=n in exI)
      apply rule
      apply rule
    proof -
      fix x y
      assume xy: "x\<in>cbox (A n) (B n)" "y\<in>cbox (A n) (B n)"
      have "dist x y \<le> setsum (\<lambda>i. abs((x - y)\<bullet>i)) Basis"
        unfolding dist_norm by(rule norm_le_l1)
      also have "\<dots> \<le> setsum (\<lambda>i. B n\<bullet>i - A n\<bullet>i) Basis"
      proof (rule setsum_mono)
        fix i :: 'a
        assume i: "i \<in> Basis"
        show "\<bar>(x - y) \<bullet> i\<bar> \<le> B n \<bullet> i - A n \<bullet> i"
          using xy[unfolded mem_box,THEN bspec, OF i]
          by (auto simp: inner_diff_left)
      qed
      also have "\<dots> \<le> setsum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis / 2^n"
        unfolding setsum_divide_distrib
      proof (rule setsum_mono)
        case goal1
        then show ?case
        proof (induct n)
          case 0
          then show ?case
            unfolding AB by auto
        next
          case (Suc n)
          have "B (Suc n) \<bullet> i - A (Suc n) \<bullet> i \<le> (B n \<bullet> i - A n \<bullet> i) / 2"
            using AB(4)[of i n] using goal1 by auto
          also have "\<dots> \<le> (b \<bullet> i - a \<bullet> i) / 2 ^ Suc n"
            using Suc by (auto simp add:field_simps)
          finally show ?case .
        qed
      qed
      also have "\<dots> < e"
        using n using goal1 by (auto simp add:field_simps)
      finally show "dist x y < e" .
    qed
  qed
  {
    fix n m :: nat
    assume "m \<le> n" then have "cbox (A n) (B n) \<subseteq> cbox (A m) (B m)"
    proof (induction rule: inc_induct)
      case (step i)
      show ?case
        using AB(4) by (intro order_trans[OF step.IH] subset_box_imp) auto
    qed simp
  } note ABsubset = this
  have "\<exists>a. \<forall>n. a\<in> cbox (A n) (B n)"
    by (rule decreasing_closed_nest[rule_format,OF closed_cbox _ ABsubset interv])
      (metis nat.exhaust AB(1-3) assms(1,3))
  then obtain x0 where x0: "\<And>n. x0 \<in> cbox (A n) (B n)"
    by blast
  show thesis
  proof (rule that[rule_format, of x0])
    show "x0\<in>cbox a b"
      using x0[of 0] unfolding AB .
    fix e :: real
    assume "e > 0"
    from interv[OF this] obtain n
      where n: "\<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e" ..
    show "\<exists>c d. x0 \<in> cbox c d \<and> cbox c d \<subseteq> ball x0 e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
      apply (rule_tac x="A n" in exI)
      apply (rule_tac x="B n" in exI)
      apply rule
      apply (rule x0)
      apply rule
      defer
      apply rule
    proof -
      show "\<not> P (cbox (A n) (B n))"
        apply (cases "0 < n")
        using AB(3)[of "n - 1"] assms(3) AB(1-2)
        apply auto
        done
      show "cbox (A n) (B n) \<subseteq> ball x0 e"
        using n using x0[of n] by auto
      show "cbox (A n) (B n) \<subseteq> cbox a b"
        unfolding AB(1-2)[symmetric] by (rule ABsubset) auto
    qed
  qed
qed


subsection {* Cousin's lemma. *}

lemma fine_division_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "gauge g"
  obtains p where "p tagged_division_of (cbox a b)" "g fine p"
proof -
  presume "\<not> (\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p) \<Longrightarrow> False"
  then obtain p where "p tagged_division_of (cbox a b)" "g fine p"
    by blast
  then show thesis ..
next
  assume as: "\<not> (\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p)"
  obtain x where x:
    "x \<in> (cbox a b)"
    "\<And>e. 0 < e \<Longrightarrow>
      \<exists>c d.
        x \<in> cbox c d \<and>
        cbox c d \<subseteq> ball x e \<and>
        cbox c d \<subseteq> (cbox a b) \<and>
        \<not> (\<exists>p. p tagged_division_of cbox c d \<and> g fine p)"
    apply (rule interval_bisection[of "\<lambda>s. \<exists>p. p tagged_division_of s \<and> g fine p",rule_format,OF _ _ as])
    apply (rule_tac x="{}" in exI)
    defer
    apply (erule conjE exE)+
  proof -
    show "{} tagged_division_of {} \<and> g fine {}"
      unfolding fine_def by auto
    fix s t p p'
    assume "p tagged_division_of s" "g fine p" "p' tagged_division_of t" "g fine p'"
      "interior s \<inter> interior t = {}"
    then show "\<exists>p. p tagged_division_of s \<union> t \<and> g fine p"
      apply -
      apply (rule_tac x="p \<union> p'" in exI)
      apply rule
      apply (rule tagged_division_union)
      prefer 4
      apply (rule fine_union)
      apply auto
      done
  qed blast
  obtain e where e: "e > 0" "ball x e \<subseteq> g x"
    using gaugeD[OF assms, of x] unfolding open_contains_ball by auto
  from x(2)[OF e(1)] obtain c d where c_d:
    "x \<in> cbox c d"
    "cbox c d \<subseteq> ball x e"
    "cbox c d \<subseteq> cbox a b"
    "\<not> (\<exists>p. p tagged_division_of cbox c d \<and> g fine p)"
    by blast
  have "g fine {(x, cbox c d)}"
    unfolding fine_def using e using c_d(2) by auto
  then show False
    using tagged_division_of_self[OF c_d(1)] using c_d by auto
qed

lemma fine_division_exists_real:
  fixes a b :: real
  assumes "gauge g"
  obtains p where "p tagged_division_of {a .. b}" "g fine p"
  by (metis assms box_real(2) fine_division_exists)

subsection {* Basic theorems about integrals. *}

lemma has_integral_unique:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i"
    and "(f has_integral k2) i"
  shows "k1 = k2"
proof (rule ccontr)
  let ?e = "norm (k1 - k2) / 2"
  assume as:"k1 \<noteq> k2"
  then have e: "?e > 0"
    by auto
  have lem: "\<And>f::'n \<Rightarrow> 'a.  \<And>a b k1 k2.
    (f has_integral k1) (cbox a b) \<Longrightarrow> (f has_integral k2) (cbox a b) \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> False"
  proof -
    case goal1
    let ?e = "norm (k1 - k2) / 2"
    from goal1(3) have e: "?e > 0" by auto
    obtain d1 where d1:
        "gauge d1"
        "\<And>p. p tagged_division_of cbox a b \<Longrightarrow>
          d1 fine p \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k1) < norm (k1 - k2) / 2"
      by (rule has_integralD[OF goal1(1) e]) blast
    obtain d2 where d2:
        "gauge d2"
        "\<And>p. p tagged_division_of cbox a b \<Longrightarrow>
          d2 fine p \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k2) < norm (k1 - k2) / 2"
      by (rule has_integralD[OF goal1(2) e]) blast
    obtain p where p:
        "p tagged_division_of cbox a b"
        "(\<lambda>x. d1 x \<inter> d2 x) fine p"
      by (rule fine_division_exists[OF gauge_inter[OF d1(1) d2(1)]])
    let ?c = "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
    have "norm (k1 - k2) \<le> norm (?c - k2) + norm (?c - k1)"
      using norm_triangle_ineq4[of "k1 - ?c" "k2 - ?c"]
      by (auto simp add:algebra_simps norm_minus_commute)
    also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
      apply (rule add_strict_mono)
      apply (rule_tac[!] d2(2) d1(2))
      using p unfolding fine_def
      apply auto
      done
    finally show False by auto
  qed
  {
    presume "\<not> (\<exists>a b. i = cbox a b) \<Longrightarrow> False"
    then show False
      apply -
      apply (cases "\<exists>a b. i = cbox a b")
      using assms
      apply (auto simp add:has_integral intro:lem[OF _ _ as])
      done
  }
  assume as: "\<not> (\<exists>a b. i = cbox a b)"
  obtain B1 where B1:
      "0 < B1"
      "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and>
          norm (z - k1) < norm (k1 - k2) / 2"
    by (rule has_integral_altD[OF assms(1) as,OF e]) blast
  obtain B2 where B2:
      "0 < B2"
      "\<And>a b. ball 0 B2 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and>
          norm (z - k2) < norm (k1 - k2) / 2"
    by (rule has_integral_altD[OF assms(2) as,OF e]) blast
  have "\<exists>a b::'n. ball 0 B1 \<union> ball 0 B2 \<subseteq> cbox a b"
    apply (rule bounded_subset_cbox)
    using bounded_Un bounded_ball
    apply auto
    done
  then obtain a b :: 'n where ab: "ball 0 B1 \<subseteq> cbox a b" "ball 0 B2 \<subseteq> cbox a b"
    by blast
  obtain w where w:
    "((\<lambda>x. if x \<in> i then f x else 0) has_integral w) (cbox a b)"
    "norm (w - k1) < norm (k1 - k2) / 2"
    using B1(2)[OF ab(1)] by blast
  obtain z where z:
    "((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b)"
    "norm (z - k2) < norm (k1 - k2) / 2"
    using B2(2)[OF ab(2)] by blast
  have "z = w"
    using lem[OF w(1) z(1)] by auto
  then have "norm (k1 - k2) \<le> norm (z - k2) + norm (w - k1)"
    using norm_triangle_ineq4 [of "k1 - w" "k2 - z"]
    by (auto simp add: norm_minus_commute)
  also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
    apply (rule add_strict_mono)
    apply (rule_tac[!] z(2) w(2))
    done
  finally show False by auto
qed

lemma integral_unique [intro]: "(f has_integral y) k \<Longrightarrow> integral k f = y"
  unfolding integral_def
  by (rule some_equality) (auto intro: has_integral_unique)

lemma has_integral_is_0:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<forall>x\<in>s. f x = 0"
  shows "(f has_integral 0) s"
proof -
  have lem: "\<And>a b. \<And>f::'n \<Rightarrow> 'a.
    (\<forall>x\<in>cbox a b. f(x) = 0) \<Longrightarrow> (f has_integral 0) (cbox a b)"
    unfolding has_integral
    apply rule
    apply rule
  proof -
    fix a b e
    fix f :: "'n \<Rightarrow> 'a"
    assume as: "\<forall>x\<in>cbox a b. f x = 0" "0 < (e::real)"
    show "\<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e)"
      apply (rule_tac x="\<lambda>x. ball x 1" in exI)
      apply rule
      apply (rule gaugeI)
      unfolding centre_in_ball
      defer
      apply (rule open_ball)
      apply rule
      apply rule
      apply (erule conjE)
    proof -
      case goal1
      have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) = 0"
      proof (rule setsum_0', rule)
        fix x
        assume x: "x \<in> p"
        have "f (fst x) = 0"
          using tagged_division_ofD(2-3)[OF goal1(1), of "fst x" "snd x"] using as x by auto
        then show "(\<lambda>(x, k). content k *\<^sub>R f x) x = 0"
          apply (subst surjective_pairing[of x])
          unfolding split_conv
          apply auto
          done
      qed
      then show ?case
        using as by auto
    qed auto
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    then show ?thesis
      apply -
      apply (cases "\<exists>a b. s = cbox a b")
      using assms
      apply (auto simp add:has_integral intro: lem)
      done
  }
  have *: "(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. 0)"
    apply (rule ext)
    using assms
    apply auto
    done
  assume "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
    apply (subst has_integral_alt)
    unfolding if_not_P *
    apply rule
    apply rule
    apply (rule_tac x=1 in exI)
    apply rule
    defer
    apply rule
    apply rule
    apply rule
  proof -
    fix e :: real
    fix a b
    assume "e > 0"
    then show "\<exists>z. ((\<lambda>x::'n. 0::'a) has_integral z) (cbox a b) \<and> norm (z - 0) < e"
      apply (rule_tac x=0 in exI)
      apply(rule,rule lem)
      apply auto
      done
  qed auto
qed

lemma has_integral_0[simp]: "((\<lambda>x::'n::euclidean_space. 0) has_integral 0) s"
  by (rule has_integral_is_0) auto

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) s \<longleftrightarrow> i = 0"
  using has_integral_unique[OF has_integral_0] by auto

lemma has_integral_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) s"
    and "bounded_linear h"
  shows "((h o f) has_integral ((h y))) s"
proof -
  interpret bounded_linear h
    using assms(2) .
  from pos_bounded obtain B where B: "0 < B" "\<And>x. norm (h x) \<le> norm x * B"
    by blast
  have lem: "\<And>(f :: 'n \<Rightarrow> 'a) y a b.
    (f has_integral y) (cbox a b) \<Longrightarrow> ((h o f) has_integral h y) (cbox a b)"
    apply (subst has_integral)
    apply rule
    apply rule
  proof -
    case goal1
    from pos_bounded
    obtain B where B: "0 < B" "\<And>x. norm (h x) \<le> norm x * B"
      by blast
    have *: "e / B > 0" using goal1(2) B by simp
    obtain g where g:
      "gauge g"
      "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> g fine p \<Longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - y) < e / B"
      by (rule has_integralD[OF goal1(1) *]) blast
    show ?case
      apply (rule_tac x=g in exI)
      apply rule
      apply (rule g(1))
      apply rule
      apply rule
      apply (erule conjE)
    proof -
      fix p
      assume as: "p tagged_division_of (cbox a b)" "g fine p"
      have *: "\<And>x k. h ((\<lambda>(x, k). content k *\<^sub>R f x) x) = (\<lambda>(x, k). h (content k *\<^sub>R f x)) x"
        by auto
      have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = setsum (h \<circ> (\<lambda>(x, k). content k *\<^sub>R f x)) p"
        unfolding o_def unfolding scaleR[symmetric] * by simp
      also have "\<dots> = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
        using setsum[of "\<lambda>(x,k). content k *\<^sub>R f x" p] using as by auto
      finally have *: "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) - h y) < e"
        unfolding * diff[symmetric]
        apply (rule le_less_trans[OF B(2)])
        using g(2)[OF as] B(1)
        apply (auto simp add: field_simps)
        done
    qed
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    then show ?thesis
      apply -
      apply (cases "\<exists>a b. s = cbox a b")
      using assms
      apply (auto simp add:has_integral intro!:lem)
      done
  }
  assume as: "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
    apply (subst has_integral_alt)
    unfolding if_not_P
    apply rule
    apply rule
  proof -
    fix e :: real
    assume e: "e > 0"
    have *: "0 < e/B" using e B(1) by simp
    obtain M where M:
      "M > 0"
      "\<And>a b. ball 0 M \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e / B"
      using has_integral_altD[OF assms(1) as *] by blast
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) has_integral z) (cbox a b) \<and> norm (z - h y) < e)"
      apply (rule_tac x=M in exI)
      apply rule
      apply (rule M(1))
      apply rule
      apply rule
      apply rule
    proof -
      case goal1
      obtain z where z:
        "((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b)"
        "norm (z - y) < e / B"
        using M(2)[OF goal1(1)] by blast
      have *: "(\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) = h \<circ> (\<lambda>x. if x \<in> s then f x else 0)"
        unfolding o_def
        apply (rule ext)
        using zero
        apply auto
        done
      show ?case
        apply (rule_tac x="h z" in exI)
        apply rule
        unfolding *
        apply (rule lem[OF z(1)])
        unfolding diff[symmetric]
        apply (rule le_less_trans[OF B(2)])
        using B(1) z(2)
        apply (auto simp add: field_simps)
        done
    qed
  qed
qed

lemma has_integral_cmul: "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) s"
  unfolding o_def[symmetric]
  apply (rule has_integral_linear,assumption)
  apply (rule bounded_linear_scaleR_right)
  done

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  from has_integral_cmul[OF assms[OF this], of c] show ?thesis
    unfolding real_scaleR_def .
qed

lemma has_integral_neg: "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral (-k)) s"
  apply (drule_tac c="-1" in has_integral_cmul)
  apply auto
  done

lemma has_integral_add:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k) s"
    and "(g has_integral l) s"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) s"
proof -
  have lem:"\<And>(f:: 'n \<Rightarrow> 'a) g a b k l.
    (f has_integral k) (cbox a b) \<Longrightarrow>
    (g has_integral l) (cbox a b) \<Longrightarrow>
    ((\<lambda>x. f x + g x) has_integral (k + l)) (cbox a b)"
  proof -
    case goal1
    show ?case
      unfolding has_integral
      apply rule
      apply rule
    proof -
      fix e :: real
      assume e: "e > 0"
      then have *: "e/2 > 0"
        by auto
      obtain d1 where d1:
        "gauge d1"
        "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d1 fine p \<Longrightarrow>
          norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k) < e / 2"
        using has_integralD[OF goal1(1) *] by blast
      obtain d2 where d2:
        "gauge d2"
        "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d2 fine p \<Longrightarrow>
          norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - l) < e / 2"
        using has_integralD[OF goal1(2) *] by blast
      show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e)"
        apply (rule_tac x="\<lambda>x. (d1 x) \<inter> (d2 x)" in exI)
        apply rule
        apply (rule gauge_inter[OF d1(1) d2(1)])
        apply (rule,rule,erule conjE)
      proof -
        fix p
        assume as: "p tagged_division_of (cbox a b)" "(\<lambda>x. d1 x \<inter> d2 x) fine p"
        have *: "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) =
          (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p. content k *\<^sub>R g x)"
          unfolding scaleR_right_distrib setsum_addf[of "\<lambda>(x,k). content k *\<^sub>R f x" "\<lambda>(x,k). content k *\<^sub>R g x" p,symmetric]
          by (rule setsum_cong2) auto
        have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) =
          norm (((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - l))"
          unfolding * by (auto simp add: algebra_simps)
        also
        let ?res = "\<dots>"
        from as have *: "d1 fine p" "d2 fine p"
          unfolding fine_inter by auto
        have "?res < e/2 + e/2"
          apply (rule le_less_trans[OF norm_triangle_ineq])
          apply (rule add_strict_mono)
          using d1(2)[OF as(1) *(1)] and d2(2)[OF as(1) *(2)]
          apply auto
          done
        finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e"
          by auto
      qed
    qed
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    then show ?thesis
      apply -
      apply (cases "\<exists>a b. s = cbox a b")
      using assms
      apply (auto simp add:has_integral intro!:lem)
      done
  }
  assume as: "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
    apply (subst has_integral_alt)
    unfolding if_not_P
    apply rule
    apply rule
  proof -
    case goal1
    then have *: "e/2 > 0"
      by auto
    from has_integral_altD[OF assms(1) as *]
    obtain B1 where B1:
        "0 < B1"
        "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
          \<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b) \<and> norm (z - k) < e / 2"
      by blast
    from has_integral_altD[OF assms(2) as *]
    obtain B2 where B2:
        "0 < B2"
        "\<And>a b. ball 0 B2 \<subseteq> (cbox a b) \<Longrightarrow>
          \<exists>z. ((\<lambda>x. if x \<in> s then g x else 0) has_integral z) (cbox a b) \<and> norm (z - l) < e / 2"
      by blast
    show ?case
      apply (rule_tac x="max B1 B2" in exI)
      apply rule
      apply (rule max.strict_coboundedI1)
      apply (rule B1)
      apply rule
      apply rule
      apply rule
    proof -
      fix a b
      assume "ball 0 (max B1 B2) \<subseteq> cbox a (b::'n)"
      then have *: "ball 0 B1 \<subseteq> cbox a (b::'n)" "ball 0 B2 \<subseteq> cbox a (b::'n)"
        by auto
      obtain w where w:
        "((\<lambda>x. if x \<in> s then f x else 0) has_integral w) (cbox a b)"
        "norm (w - k) < e / 2"
        using B1(2)[OF *(1)] by blast
      obtain z where z:
        "((\<lambda>x. if x \<in> s then g x else 0) has_integral z) (cbox a b)"
        "norm (z - l) < e / 2"
        using B2(2)[OF *(2)] by blast
      have *: "\<And>x. (if x \<in> s then f x + g x else 0) =
        (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0)"
        by auto
      show "\<exists>z. ((\<lambda>x. if x \<in> s then f x + g x else 0) has_integral z) (cbox a b) \<and> norm (z - (k + l)) < e"
        apply (rule_tac x="w + z" in exI)
        apply rule
        apply (rule lem[OF w(1) z(1), unfolded *[symmetric]])
        using norm_triangle_ineq[of "w - k" "z - l"] w(2) z(2)
        apply (auto simp add: field_simps)
        done
    qed
  qed
qed

lemma has_integral_sub:
  "(f has_integral k) s \<Longrightarrow> (g has_integral l) s \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_integral (k - l)) s"
  using has_integral_add[OF _ has_integral_neg, of f k s g l]
  unfolding algebra_simps
  by auto

lemma integral_0:
  "integral s (\<lambda>x::'n::euclidean_space. 0::'m::real_normed_vector) = 0"
  by (rule integral_unique has_integral_0)+

lemma integral_add: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow>
    integral s (\<lambda>x. f x + g x) = integral s f + integral s g"
  apply (rule integral_unique)
  apply (drule integrable_integral)+
  apply (rule has_integral_add)
  apply assumption+
  done

lemma integral_cmul: "f integrable_on s \<Longrightarrow> integral s (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral s f"
  apply (rule integral_unique)
  apply (drule integrable_integral)+
  apply (rule has_integral_cmul)
  apply assumption+
  done

lemma integral_neg: "f integrable_on s \<Longrightarrow> integral s (\<lambda>x. - f x) = - integral s f"
  apply (rule integral_unique)
  apply (drule integrable_integral)+
  apply (rule has_integral_neg)
  apply assumption+
  done

lemma integral_sub: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow>
    integral s (\<lambda>x. f x - g x) = integral s f - integral s g"
  apply (rule integral_unique)
  apply (drule integrable_integral)+
  apply (rule has_integral_sub)
  apply assumption+
  done

lemma integrable_0: "(\<lambda>x. 0) integrable_on s"
  unfolding integrable_on_def using has_integral_0 by auto

lemma integrable_add: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_add)

lemma integrable_cmul: "f integrable_on s \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_cmul)

lemma integrable_on_cmult_iff:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
  using integrable_cmul[of "\<lambda>x. c * f x" s "1 / c"] integrable_cmul[of f s c] `c \<noteq> 0`
  by auto

lemma integrable_neg: "f integrable_on s \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_neg)

lemma integrable_sub:
  "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_sub)

lemma integrable_linear:
  "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_linear)

lemma integral_linear:
  "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> integral s (h \<circ> f) = h (integral s f)"
  apply (rule has_integral_unique)
  defer
  unfolding has_integral_integral
  apply (drule (2) has_integral_linear)
  unfolding has_integral_integral[symmetric]
  apply (rule integrable_linear)
  apply assumption+
  done

lemma integral_component_eq[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x \<bullet> k) = integral s f \<bullet> k"
  unfolding integral_linear[OF assms(1) bounded_linear_component,unfolded o_def] ..

lemma has_integral_setsum:
  assumes "finite t"
    and "\<forall>a\<in>t. ((f a) has_integral (i a)) s"
  shows "((\<lambda>x. setsum (\<lambda>a. f a x) t) has_integral (setsum i t)) s"
  using assms(1) subset_refl[of t]
proof (induct rule: finite_subset_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  show ?case
    unfolding setsum_insert[OF insert(1,3)]
    apply (rule has_integral_add)
    using insert assms
    apply auto
    done
qed

lemma integral_setsum: "finite t \<Longrightarrow> \<forall>a\<in>t. (f a) integrable_on s \<Longrightarrow>
  integral s (\<lambda>x. setsum (\<lambda>a. f a x) t) = setsum (\<lambda>a. integral s (f a)) t"
  apply (rule integral_unique)
  apply (rule has_integral_setsum)
  using integrable_integral
  apply auto
  done

lemma integrable_setsum:
  "finite t \<Longrightarrow> \<forall>a \<in> t. (f a) integrable_on s \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) t) integrable_on s"
  unfolding integrable_on_def
  apply (drule bchoice)
  using has_integral_setsum[of t]
  apply auto
  done

lemma has_integral_eq:
  assumes "\<forall>x\<in>s. f x = g x"
    and "(f has_integral k) s"
  shows "(g has_integral k) s"
  using has_integral_sub[OF assms(2), of "\<lambda>x. f x - g x" 0]
  using has_integral_is_0[of s "\<lambda>x. f x - g x"]
  using assms(1)
  by auto

lemma integrable_eq: "\<forall>x\<in>s. f x = g x \<Longrightarrow> f integrable_on s \<Longrightarrow> g integrable_on s"
  unfolding integrable_on_def
  using has_integral_eq[of s f g]
  by auto

lemma has_integral_eq_eq: "\<forall>x\<in>s. f x = g x \<Longrightarrow> (f has_integral k) s \<longleftrightarrow> (g has_integral k) s"
  using has_integral_eq[of s f g] has_integral_eq[of s g f]
  by auto

lemma has_integral_null[dest]:
  assumes "content(cbox a b) = 0"
  shows "(f has_integral 0) (cbox a b)"
  unfolding has_integral
  apply rule
  apply rule
  apply (rule_tac x="\<lambda>x. ball x 1" in exI)
  apply rule
  defer
  apply rule
  apply rule
  apply (erule conjE)
proof -
  fix e :: real
  assume e: "e > 0"
  then show "gauge (\<lambda>x. ball x 1)"
    by auto
  fix p
  assume p: "p tagged_division_of (cbox a b)"
  have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) = 0"
    unfolding norm_eq_zero diff_0_right
    using setsum_content_null[OF assms(1) p, of f] .
  then show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
    using e by auto
qed

lemma has_integral_null_real[dest]:
  assumes "content {a .. b::real} = 0"
  shows "(f has_integral 0) {a .. b}"
  by (metis assms box_real(2) has_integral_null)

lemma has_integral_null_eq[simp]: "content (cbox a b) = 0 \<Longrightarrow> (f has_integral i) (cbox a b) \<longleftrightarrow> i = 0"
  apply rule
  apply (rule has_integral_unique)
  apply assumption
  apply (drule (1) has_integral_null)
  apply (drule has_integral_null)
  apply auto
  done

lemma integral_null[dest]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
  apply (rule integral_unique)
  apply (drule has_integral_null)
  apply assumption
  done

lemma integrable_on_null[dest]: "content (cbox a b) = 0 \<Longrightarrow> f integrable_on (cbox a b)"
  unfolding integrable_on_def
  apply (drule has_integral_null)
  apply auto
  done

lemma has_integral_empty[intro]: "(f has_integral 0) {}"
  unfolding empty_as_interval
  apply (rule has_integral_null)
  using content_empty
  unfolding empty_as_interval
  apply assumption
  done

lemma has_integral_empty_eq[simp]: "(f has_integral i) {} \<longleftrightarrow> i = 0"
  apply rule
  apply (rule has_integral_unique)
  apply assumption
  apply auto
  done

lemma integrable_on_empty[intro]: "f integrable_on {}"
  unfolding integrable_on_def by auto

lemma integral_empty[simp]: "integral {} f = 0"
  by (rule integral_unique) (rule has_integral_empty)

lemma has_integral_refl[intro]:
  fixes a :: "'a::euclidean_space"
  shows "(f has_integral 0) (cbox a a)"
    and "(f has_integral 0) {a}"
proof -
  have *: "{a} = cbox a a"
    apply (rule set_eqI)
    unfolding mem_box singleton_iff euclidean_eq_iff[where 'a='a]
    apply safe
    prefer 3
    apply (erule_tac x=b in ballE)
    apply (auto simp add: field_simps)
    done
  show "(f has_integral 0) (cbox a a)" "(f has_integral 0) {a}"
    unfolding *
    apply (rule_tac[!] has_integral_null)
    unfolding content_eq_0_interior
    unfolding interior_cbox
    using box_sing
    apply auto
    done
qed

lemma integrable_on_refl[intro]: "f integrable_on cbox a a"
  unfolding integrable_on_def by auto

lemma integral_refl: "integral (cbox a a) f = 0"
  by (rule integral_unique) auto


subsection {* Cauchy-type criterion for integrability. *}

(* XXXXXXX *)
lemma integrable_cauchy:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  shows "f integrable_on cbox a b \<longleftrightarrow>
    (\<forall>e>0.\<exists>d. gauge d \<and>
      (\<forall>p1 p2. p1 tagged_division_of (cbox a b) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b) \<and> d fine p2 \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 -
        setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) < e))"
  (is "?l = (\<forall>e>0. \<exists>d. ?P e d)")
proof
  assume ?l
  then guess y unfolding integrable_on_def has_integral .. note y=this
  show "\<forall>e>0. \<exists>d. ?P e d"
  proof (rule, rule)
    case goal1
    then have "e/2 > 0" by auto
    then guess d
      apply -
      apply (drule y[rule_format])
      apply (elim exE conjE)
      done
    note d=this[rule_format]
    show ?case
      apply (rule_tac x=d in exI)
      apply rule
      apply (rule d)
      apply rule
      apply rule
      apply rule
      apply (erule conjE)+
    proof -
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b)" "d fine p1"
        "p2 tagged_division_of (cbox a b)" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
        apply (rule dist_triangle_half_l[where y=y,unfolded dist_norm])
        using d(2)[OF conjI[OF as(1-2)]] d(2)[OF conjI[OF as(3-4)]] .
    qed
  qed
next
  assume "\<forall>e>0. \<exists>d. ?P e d"
  then have "\<forall>n::nat. \<exists>d. ?P (inverse(real (n + 1))) d"
    by auto
  from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format],rule_format]
  have "\<And>n. gauge (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}})"
    apply (rule gauge_inters)
    using d(1)
    apply auto
    done
  then have "\<forall>n. \<exists>p. p tagged_division_of (cbox a b) \<and> (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}}) fine p"
    apply -
  proof
    case goal1
    from this[of n]
    show ?case
      apply (drule_tac fine_division_exists)
      apply auto
      done
  qed
  from choice[OF this] guess p .. note p = conjunctD2[OF this[rule_format]]
  have dp: "\<And>i n. i\<le>n \<Longrightarrow> d i fine p n"
    using p(2) unfolding fine_inters by auto
  have "Cauchy (\<lambda>n. setsum (\<lambda>(x,k). content k *\<^sub>R (f x)) (p n))"
  proof (rule CauchyI)
    case goal1
    then guess N unfolding real_arch_inv[of e] .. note N=this
    show ?case
      apply (rule_tac x=N in exI)
    proof (rule, rule, rule, rule)
      fix m n
      assume mn: "N \<le> m" "N \<le> n"
      have *: "N = (N - 1) + 1" using N by auto
      show "norm ((\<Sum>(x, k)\<in>p m. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p n. content k *\<^sub>R f x)) < e"
        apply (rule less_trans[OF _ N[THEN conjunct2,THEN conjunct2]])
        apply(subst *)
        apply(rule d(2))
        using dp p(1)
        using mn
        apply auto
        done
    qed
  qed
  then guess y unfolding convergent_eq_cauchy[symmetric] .. note y=this[THEN LIMSEQ_D]
  show ?l
    unfolding integrable_on_def has_integral
    apply (rule_tac x=y in exI)
  proof (rule, rule)
    fix e :: real
    assume "e>0"
    then have *:"e/2 > 0" by auto
    then guess N1 unfolding real_arch_inv[of "e/2"] .. note N1=this
    then have N1': "N1 = N1 - 1 + 1"
      by auto
    guess N2 using y[OF *] .. note N2=this
    show "\<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - y) < e)"
      apply (rule_tac x="d (N1 + N2)" in exI)
      apply rule
      defer
    proof (rule, rule, erule conjE)
      show "gauge (d (N1 + N2))"
        using d by auto
      fix q
      assume as: "q tagged_division_of (cbox a b)" "d (N1 + N2) fine q"
      have *: "inverse (real (N1 + N2 + 1)) < e / 2"
        apply (rule less_trans)
        using N1
        apply auto
        done
      show "norm ((\<Sum>(x, k)\<in>q. content k *\<^sub>R f x) - y) < e"
        apply (rule norm_triangle_half_r)
        apply (rule less_trans[OF _ *])
        apply (subst N1', rule d(2)[of "p (N1+N2)"])
        defer
        using N2[rule_format,of "N1+N2"]
        using as dp[of "N1 - 1 + 1 + N2" "N1 + N2"]
        using p(1)[of "N1 + N2"]
        using N1
        apply auto
        done
    qed
  qed
qed


subsection {* Additivity of integral on abutting intervals. *}

lemma interval_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows
    "cbox a b \<inter> {x. x\<bullet>k \<le> c} = cbox a (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i) *\<^sub>R i)"
    "cbox a b \<inter> {x. x\<bullet>k \<ge> c} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i) *\<^sub>R i) b"
  apply (rule_tac[!] set_eqI)
  unfolding Int_iff mem_box mem_Collect_eq
  using assms
  apply auto
  done

lemma content_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "content (cbox a b) = content(cbox a b \<inter> {x. x\<bullet>k \<le> c}) + content(cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
proof cases
  note simps = interval_split[OF assms] content_cbox_cases
  have *: "Basis = insert k (Basis - {k})" "\<And>x. finite (Basis-{x})" "\<And>x. x\<notin>Basis-{x}"
    using assms by auto
  have *: "\<And>X Y Z. (\<Prod>i\<in>Basis. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>Basis-{k}. Z i (Y i))"
    "(\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i) = (\<Prod>i\<in>Basis-{k}. b\<bullet>i - a\<bullet>i) * (b\<bullet>k - a\<bullet>k)"
    apply (subst *(1))
    defer
    apply (subst *(1))
    unfolding setprod_insert[OF *(2-)]
    apply auto
    done
  assume as: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
  moreover
  have "\<And>x. min (b \<bullet> k) c = max (a \<bullet> k) c \<Longrightarrow>
    x * (b\<bullet>k - a\<bullet>k) = x * (max (a \<bullet> k) c - a \<bullet> k) + x * (b \<bullet> k - max (a \<bullet> k) c)"
    by  (auto simp add: field_simps)
  moreover
  have **: "(\<Prod>i\<in>Basis. ((\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) *\<^sub>R i) \<bullet> i - a \<bullet> i)) =
      (\<Prod>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) - a \<bullet> i)"
    "(\<Prod>i\<in>Basis. b \<bullet> i - ((\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i)) =
      (\<Prod>i\<in>Basis. b \<bullet> i - (if i = k then max (a \<bullet> k) c else a \<bullet> i))"
    by (auto intro!: setprod_cong)
  have "\<not> a \<bullet> k \<le> c \<Longrightarrow> \<not> c \<le> b \<bullet> k \<Longrightarrow> False"
    unfolding not_le
    using as[unfolded ,rule_format,of k] assms
    by auto
  ultimately show ?thesis
    using assms
    unfolding simps **
    unfolding *(1)[of "\<lambda>i x. b\<bullet>i - x"] *(1)[of "\<lambda>i x. x - a\<bullet>i"]
    unfolding *(2)
    by auto
next
  assume "\<not> (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  then have "cbox a b = {}"
    unfolding box_eq_empty by (auto simp: not_le)
  then show ?thesis
    by (auto simp: not_le)
qed

lemma division_split_left_inj:
  fixes type :: "'a::euclidean_space"
  assumes "d division_of i"
    and "k1 \<in> d"
    and "k2 \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x::'a. x\<bullet>k \<le> c} = k2 \<inter> {x. x\<bullet>k \<le> c}"
    and k: "k\<in>Basis"
  shows "content(k1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
proof -
  note d=division_ofD[OF assms(1)]
  have *: "\<And>(a::'a) b c. content (cbox a b \<inter> {x. x\<bullet>k \<le> c}) = 0 \<longleftrightarrow>
    interior(cbox a b \<inter> {x. x\<bullet>k \<le> c}) = {}"
    unfolding  interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] by (elim exE) note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] by (elim exE) note uv2=this
  have **: "\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}"
    by auto
  show ?thesis
    unfolding uv1 uv2 *
    apply (rule **[OF d(5)[OF assms(2-4)]])
    defer
    apply (subst assms(5)[unfolded uv1 uv2])
    unfolding uv1 uv2
    apply auto
    done
qed

lemma division_split_right_inj:
  fixes type :: "'a::euclidean_space"
  assumes "d division_of i"
    and "k1 \<in> d"
    and "k2 \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x::'a. x\<bullet>k \<ge> c} = k2 \<inter> {x. x\<bullet>k \<ge> c}"
    and k: "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
proof -
  note d=division_ofD[OF assms(1)]
  have *: "\<And>a b::'a. \<And>c. content(cbox a b \<inter> {x. x\<bullet>k \<ge> c}) = 0 \<longleftrightarrow>
    interior(cbox a b \<inter> {x. x\<bullet>k \<ge> c}) = {}"
    unfolding interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] by (elim exE) note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] by (elim exE) note uv2=this
  have **: "\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}"
    by auto
  show ?thesis
    unfolding uv1 uv2 *
    apply (rule **[OF d(5)[OF assms(2-4)]])
    defer
    apply (subst assms(5)[unfolded uv1 uv2])
    unfolding uv1 uv2
    apply auto
    done
qed

lemma tagged_division_split_left_inj:
  fixes x1 :: "'a::euclidean_space"
  assumes "d tagged_division_of i"
    and "(x1, k1) \<in> d"
    and "(x2, k2) \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x. x\<bullet>k \<le> c} = k2 \<inter> {x. x\<bullet>k \<le> c}"
    and k: "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
proof -
  have *: "\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c"
    unfolding image_iff
    apply (rule_tac x="(a,b)" in bexI)
    apply auto
    done
  show ?thesis
    apply (rule division_split_left_inj[OF division_of_tagged_division[OF assms(1)]])
    apply (rule_tac[1-2] *)
    using assms(2-)
    apply auto
    done
qed

lemma tagged_division_split_right_inj:
  fixes x1 :: "'a::euclidean_space"
  assumes "d tagged_division_of i"
    and "(x1, k1) \<in> d"
    and "(x2, k2) \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x. x\<bullet>k \<ge> c} = k2 \<inter> {x. x\<bullet>k \<ge> c}"
  and k: "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
proof -
  have *: "\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c"
    unfolding image_iff
    apply (rule_tac x="(a,b)" in bexI)
    apply auto
    done
  show ?thesis
    apply (rule division_split_right_inj[OF division_of_tagged_division[OF assms(1)]])
    apply (rule_tac[1-2] *)
    using assms(2-)
    apply auto
    done
qed

lemma division_split:
  fixes a :: "'a::euclidean_space"
  assumes "p division_of (cbox a b)"
    and k: "k\<in>Basis"
  shows "{l \<inter> {x. x\<bullet>k \<le> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} division_of(cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      (is "?p1 division_of ?I1")
    and "{l \<inter> {x. x\<bullet>k \<ge> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      (is "?p2 division_of ?I2")
proof (rule_tac[!] division_ofI)
  note p = division_ofD[OF assms(1)]
  show "finite ?p1" "finite ?p2"
    using p(1) by auto
  show "\<Union>?p1 = ?I1" "\<Union>?p2 = ?I2"
    unfolding p(6)[symmetric] by auto
  {
    fix k
    assume "k \<in> ?p1"
    then guess l unfolding mem_Collect_eq by (elim exE conjE) note l=this
    guess u v using p(4)[OF l(2)] by (elim exE) note uv=this
    show "k \<subseteq> ?I1" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
      unfolding l
      using p(2-3)[OF l(2)] l(3)
      unfolding uv
      apply -
      prefer 3
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix k'
    assume "k' \<in> ?p1"
    then guess l' unfolding mem_Collect_eq by (elim exE conjE) note l'=this
    assume "k \<noteq> k'"
    then show "interior k \<inter> interior k' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
  {
    fix k
    assume "k \<in> ?p2"
    then guess l unfolding mem_Collect_eq by (elim exE conjE) note l=this
    guess u v using p(4)[OF l(2)] by (elim exE) note uv=this
    show "k \<subseteq> ?I2" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
      unfolding l
      using p(2-3)[OF l(2)] l(3)
      unfolding uv
      apply -
      prefer 3
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix k'
    assume "k' \<in> ?p2"
    then guess l' unfolding mem_Collect_eq by (elim exE conjE) note l'=this
    assume "k \<noteq> k'"
    then show "interior k \<inter> interior k' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
qed

lemma has_integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
    and "(f has_integral j) (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(f has_integral (i + j)) (cbox a b)"
proof (unfold has_integral, rule, rule)
  case goal1
  then have e: "e/2 > 0"
    by auto
  guess d1 using has_integralD[OF assms(1)[unfolded interval_split[OF k]] e] .
  note d1=this[unfolded interval_split[symmetric,OF k]]
  guess d2 using has_integralD[OF assms(2)[unfolded interval_split[OF k]] e] .
  note d2=this[unfolded interval_split[symmetric,OF k]]
  let ?d = "\<lambda>x. if x\<bullet>k = c then (d1 x \<inter> d2 x) else ball x (abs(x\<bullet>k - c)) \<inter> d1 x \<inter> d2 x"
  show ?case
    apply (rule_tac x="?d" in exI)
    apply rule
    defer
    apply rule
    apply rule
    apply (elim conjE)
  proof -
    show "gauge ?d"
      using d1(1) d2(1) unfolding gauge_def by auto
    fix p
    assume "p tagged_division_of (cbox a b)" "?d fine p"
    note p = this tagged_division_ofD[OF this(1)]
    have lem0:
      "\<And>x kk. (x, kk) \<in> p \<Longrightarrow> kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {} \<Longrightarrow> x\<bullet>k \<le> c"
      "\<And>x kk. (x, kk) \<in> p \<Longrightarrow> kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {} \<Longrightarrow> x\<bullet>k \<ge> c"
    proof -
      fix x kk
      assume as: "(x, kk) \<in> p"
      {
        assume *: "kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}"
        show "x\<bullet>k \<le> c"
        proof (rule ccontr)
          assume **: "\<not> ?thesis"
          from this[unfolded not_le]
          have "kk \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
            using p(2)[unfolded fine_def, rule_format,OF as,unfolded split_conv] by auto
          with * have "\<exists>y. y \<in> ball x \<bar>x \<bullet> k - c\<bar> \<inter> {x. x \<bullet> k \<le> c}"
            by blast
          then guess y ..
          then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<le> c"
            apply -
            apply (rule le_less_trans)
            using Basis_le_norm[OF k, of "x - y"]
            apply (auto simp add: dist_norm inner_diff_left)
            done
          then show False
            using **[unfolded not_le] by (auto simp add: field_simps)
        qed
      next
        assume *: "kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}"
        show "x\<bullet>k \<ge> c"
        proof (rule ccontr)
          assume **: "\<not> ?thesis"
          from this[unfolded not_le] have "kk \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
            using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
          with * have "\<exists>y. y \<in> ball x \<bar>x \<bullet> k - c\<bar> \<inter> {x. x \<bullet> k \<ge> c}"
            by blast
          then guess y ..
          then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<ge> c"
            apply -
            apply (rule le_less_trans)
            using Basis_le_norm[OF k, of "x - y"]
            apply (auto simp add: dist_norm inner_diff_left)
            done
          then show False
            using **[unfolded not_le] by (auto simp add: field_simps)
        qed
      }
    qed

    have lem1: "\<And>f P Q. (\<forall>x k. (x, k) \<in> {(x, f k) | x k. P x k} \<longrightarrow> Q x k) \<longleftrightarrow>
      (\<forall>x k. P x k \<longrightarrow> Q x (f k))" by auto
    have lem2: "\<And>f s P f. finite s \<Longrightarrow> finite {(x,f k) | x k. (x,k) \<in> s \<and> P x k}"
    proof -
      case goal1
      then show ?case
        apply -
        apply (rule finite_subset[of _ "(\<lambda>(x,k). (x,f k)) ` s"])
        apply auto
        done
    qed
    have lem3: "\<And>g :: 'a set \<Rightarrow> 'a set. finite p \<Longrightarrow>
      setsum (\<lambda>(x, k). content k *\<^sub>R f x) {(x,g k) |x k. (x,k) \<in> p \<and> g k \<noteq> {}} =
      setsum (\<lambda>(x, k). content k *\<^sub>R f x) ((\<lambda>(x, k). (x, g k)) ` p)"
      apply (rule setsum_mono_zero_left)
      prefer 3
    proof
      fix g :: "'a set \<Rightarrow> 'a set"
      fix i :: "'a \<times> 'a set"
      assume "i \<in> (\<lambda>(x, k). (x, g k)) ` p - {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
      then obtain x k where xk:
        "i = (x, g k)"
        "(x, k) \<in> p"
        "(x, g k) \<notin> {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
        by auto
      have "content (g k) = 0"
        using xk using content_empty by auto
      then show "(\<lambda>(x, k). content k *\<^sub>R f x) i = 0"
        unfolding xk split_conv by auto
    qed auto
    have lem4: "\<And>g. (\<lambda>(x,l). content (g l) *\<^sub>R f x) = (\<lambda>(x,l). content l *\<^sub>R f x) \<circ> (\<lambda>(x,l). (x,g l))"
      by auto

    let ?M1 = "{(x, kk \<inter> {x. x\<bullet>k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
    have "norm ((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) < e/2"
      apply (rule d1(2),rule tagged_division_ofI)
      apply (rule lem2 p(3))+
      prefer 6
      apply (rule fineI)
    proof -
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M1} = cbox a b \<inter> {x. x\<bullet>k \<le> c}"
        unfolding p(8)[symmetric] by auto
      fix x l
      assume xl: "(x, l) \<in> ?M1"
      then guess x' l' unfolding mem_Collect_eq unfolding Pair_eq by (elim exE conjE) note xl'=this
      have "l' \<subseteq> d1 x'"
        apply (rule order_trans[OF fineD[OF p(2) xl'(3)]])
        apply auto
        done
      then show "l \<subseteq> d1 x"
        unfolding xl' by auto
      show "x \<in> l" "l \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c}"
        unfolding xl'
        using p(4-6)[OF xl'(3)] using xl'(4)
        using lem0(1)[OF xl'(3-4)] by auto
      show "\<exists>a b. l = cbox a b"
        unfolding xl'
        using p(6)[OF xl'(3)]
        by (fastforce simp add: interval_split[OF k,where c=c])
      fix y r
      let ?goal = "interior l \<inter> interior r = {}"
      assume yr: "(y, r) \<in> ?M1"
      then guess y' r' unfolding mem_Collect_eq unfolding Pair_eq by (elim exE conjE) note yr'=this
      assume as: "(x, l) \<noteq> (y, r)"
      show "interior l \<inter> interior r = {}"
      proof (cases "l' = r' \<longrightarrow> x' = y'")
        case False
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next
        case True
        then have "l' \<noteq> r'"
          using as unfolding xl' yr' by auto
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed
    qed
    moreover
    let ?M2 = "{(x,kk \<inter> {x. x\<bullet>k \<ge> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
    have "norm ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) < e/2"
      apply (rule d2(2),rule tagged_division_ofI)
      apply (rule lem2 p(3))+
      prefer 6
      apply (rule fineI)
    proof -
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M2} = cbox a b \<inter> {x. x\<bullet>k \<ge> c}"
        unfolding p(8)[symmetric] by auto
      fix x l
      assume xl: "(x, l) \<in> ?M2"
      then guess x' l' unfolding mem_Collect_eq unfolding Pair_eq by (elim exE conjE) note xl'=this
      have "l' \<subseteq> d2 x'"
        apply (rule order_trans[OF fineD[OF p(2) xl'(3)]])
        apply auto
        done
      then show "l \<subseteq> d2 x"
        unfolding xl' by auto
      show "x \<in> l" "l \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
        unfolding xl'
        using p(4-6)[OF xl'(3)]
        using xl'(4)
        using lem0(2)[OF xl'(3-4)]
        by auto
      show "\<exists>a b. l = cbox a b"
        unfolding xl'
        using p(6)[OF xl'(3)]
        by (fastforce simp add: interval_split[OF k, where c=c])
      fix y r
      let ?goal = "interior l \<inter> interior r = {}"
      assume yr: "(y, r) \<in> ?M2"
      then guess y' r' unfolding mem_Collect_eq unfolding Pair_eq by (elim exE conjE) note yr'=this
      assume as: "(x, l) \<noteq> (y, r)"
      show "interior l \<inter> interior r = {}"
      proof (cases "l' = r' \<longrightarrow> x' = y'")
        case False
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next
        case True
        then have "l' \<noteq> r'"
          using as unfolding xl' yr' by auto
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed
    qed
    ultimately
    have "norm (((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j)) < e/2 + e/2"
      apply -
      apply (rule norm_triangle_lt)
      apply auto
      done
    also {
      have *: "\<And>x y. x = (0::real) \<Longrightarrow> x *\<^sub>R (y::'b) = 0"
        using scaleR_zero_left by auto
      have "((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - (i + j)"
        by auto
      also have "\<dots> = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f x) +
        (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f x) - (i + j)"
        unfolding lem3[OF p(3)]
        apply (subst setsum_reindex_nonzero[OF p(3)])
        defer
        apply (subst setsum_reindex_nonzero[OF p(3)])
        defer
        unfolding lem4[symmetric]
        apply (rule refl)
        unfolding split_paired_all split_conv
        apply (rule_tac[!] *)
      proof -
        case goal1
        then show ?case
          apply -
          apply (rule tagged_division_split_left_inj [OF p(1), of a b aa ba])
          using k
          apply auto
          done
      next
        case goal2
        then show ?case
          apply -
          apply (rule tagged_division_split_right_inj[OF p(1), of a b aa ba])
          using k
          apply auto
          done
      qed
      also note setsum_addf[symmetric]
      also have *: "\<And>x. x \<in> p \<Longrightarrow>
        (\<lambda>(x,ka). content (ka \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f x) x +
          (\<lambda>(x,ka). content (ka \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f x) x =
        (\<lambda>(x,ka). content ka *\<^sub>R f x) x"
        unfolding split_paired_all split_conv
      proof -
        fix a b
        assume "(a, b) \<in> p"
        from p(6)[OF this] guess u v by (elim exE) note uv=this
        then show "content (b \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f a + content (b \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f a =
          content b *\<^sub>R f a"
          unfolding scaleR_left_distrib[symmetric]
          unfolding uv content_split[OF k,of u v c]
          by auto
      qed
      note setsum_cong2[OF this]
      finally have "(\<Sum>(x, k)\<in>{(x, kk \<inter> {x. x \<bullet> k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. content k *\<^sub>R f x) - i +
        ((\<Sum>(x, k)\<in>{(x, kk \<inter> {x. c \<le> x \<bullet> k}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f x) - (i + j)"
        by auto
    }
    finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (i + j)) < e"
      by auto
  qed
qed


subsection {* A sort of converse, integrability on subintervals. *}

lemma tagged_division_union_interval:
  fixes a :: "'a::euclidean_space"
  assumes "p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of (cbox a b)"
proof -
  have *: "cbox a b = (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<union> (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    by auto
  show ?thesis
    apply (subst *)
    apply (rule tagged_division_union[OF assms(1-2)])
    unfolding interval_split[OF k] interior_cbox
    using k
    apply (auto simp add: box_def elim!: ballE[where x=k])
    done
qed

lemma tagged_division_union_interval_real:
  fixes a :: real
  assumes "p1 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of {a .. b}"
  using assms
  unfolding box_real[symmetric]
  by (rule tagged_division_union_interval)

lemma has_integral_separate_sides:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "e > 0"
    and k: "k \<in> Basis"
  obtains d where "gauge d"
    "\<forall>p1 p2. p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) \<and> d fine p2 \<longrightarrow>
        norm ((setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 + setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e"
proof -
  guess d using has_integralD[OF assms(1-2)] . note d=this
  show ?thesis
    apply (rule that[of d])
    apply (rule d)
    apply rule
    apply rule
    apply rule
    apply (elim conjE)
  proof -
    fix p1 p2
    assume "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p1"
    note p1=tagged_division_ofD[OF this(1)] this
    assume "p2 tagged_division_of (cbox a b) \<inter> {x. c \<le> x \<bullet> k}" "d fine p2"
    note p2=tagged_division_ofD[OF this(1)] this
    note tagged_division_union_interval[OF p1(7) p2(7)] note p12 = tagged_division_ofD[OF this] this
    have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) =
      norm ((\<Sum>(x, k)\<in>p1 \<union> p2. content k *\<^sub>R f x) - i)"
      apply (subst setsum_Un_zero)
      apply (rule p1 p2)+
      apply rule
      unfolding split_paired_all split_conv
    proof -
      fix a b
      assume ab: "(a, b) \<in> p1 \<inter> p2"
      have "(a, b) \<in> p1"
        using ab by auto
      from p1(4)[OF this] guess u v by (elim exE) note uv = this
      have "b \<subseteq> {x. x\<bullet>k = c}"
        using ab p1(3)[of a b] p2(3)[of a b] by fastforce
      moreover
      have "interior {x::'a. x \<bullet> k = c} = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain x where x: "x \<in> interior {x::'a. x\<bullet>k = c}"
          by auto
        then guess e unfolding mem_interior .. note e=this
        have x: "x\<bullet>k = c"
          using x interior_subset by fastforce
        have *: "\<And>i. i \<in> Basis \<Longrightarrow> \<bar>(x - (x + (e / 2) *\<^sub>R k)) \<bullet> i\<bar> = (if i = k then e/2 else 0)"
          using e k by (auto simp: inner_simps inner_not_same_Basis)
        have "(\<Sum>i\<in>Basis. \<bar>(x - (x + (e / 2 ) *\<^sub>R k)) \<bullet> i\<bar>) =
          (\<Sum>i\<in>Basis. (if i = k then e / 2 else 0))"
          apply (rule setsum_cong2)
          apply (subst *)
          apply auto
          done
        also have "\<dots> < e"
          apply (subst setsum_delta)
          using e
          apply auto
          done
        finally have "x + (e/2) *\<^sub>R k \<in> ball x e"
          unfolding mem_ball dist_norm by(rule le_less_trans[OF norm_le_l1])
        then have "x + (e/2) *\<^sub>R k \<in> {x. x\<bullet>k = c}"
          using e by auto
        then show False
          unfolding mem_Collect_eq using e x k by (auto simp: inner_simps)
      qed
      ultimately have "content b = 0"
        unfolding uv content_eq_0_interior
        apply -
        apply (drule interior_mono)
        apply auto
        done
      then show "content b *\<^sub>R f a = 0"
        by auto
    qed auto
    also have "\<dots> < e"
      by (rule k d(2) p12 fine_union p1 p2)+
    finally show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) < e" .
  qed
qed

lemma integrable_split[intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes "f integrable_on cbox a b"
    and k: "k \<in> Basis"
  shows "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<le> c})" (is ?t1)
    and "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<ge> c})" (is ?t2)
proof -
  guess y using assms(1) unfolding integrable_on_def .. note y=this
  def b' \<equiv> "\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i)*\<^sub>R i::'a"
  def a' \<equiv> "\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i)*\<^sub>R i::'a"
  show ?t1 ?t2
    unfolding interval_split[OF k] integrable_cauchy
    unfolding interval_split[symmetric,OF k]
  proof (rule_tac[!] allI impI)+
    fix e :: real
    assume "e > 0"
    then have "e/2>0"
      by auto
    from has_integral_separate_sides[OF y this k,of c] guess d . note d=this[rule_format]
    let ?P = "\<lambda>A. \<exists>d. gauge d \<and> (\<forall>p1 p2. p1 tagged_division_of (cbox a b) \<inter> A \<and> d fine p1 \<and>
      p2 tagged_division_of (cbox a b) \<inter> A \<and> d fine p2 \<longrightarrow>
      norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e)"
    show "?P {x. x \<bullet> k \<le> c}"
      apply (rule_tac x=d in exI)
      apply rule
      apply (rule d)
      apply rule
      apply rule
      apply rule
    proof -
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c} \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof -
        guess p using fine_division_exists[OF d(1), of a' b] . note p=this
        show ?thesis
          using norm_triangle_half_l[OF d(2)[of p1 p] d(2)[of p2 p]]
          using as unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          using p using assms
          by (auto simp add: algebra_simps)
      qed
    qed
    show "?P {x. x \<bullet> k \<ge> c}"
      apply (rule_tac x=d in exI)
      apply rule
      apply (rule d)
      apply rule
      apply rule
      apply rule
    proof -
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c} \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c} \<and> d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof -
        guess p using fine_division_exists[OF d(1), of a b'] . note p=this
        show ?thesis
          using norm_triangle_half_l[OF d(2)[of p p1] d(2)[of p p2]]
          using as
          unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          using p
          using assms
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
qed


subsection {* Generalized notion of additivity. *}

definition "neutral opp = (SOME x. \<forall>y. opp x y = y \<and> opp y x = y)"

definition operative :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('b::euclidean_space) set \<Rightarrow> 'a) \<Rightarrow> bool"
  where "operative opp f \<longleftrightarrow>
    (\<forall>a b. content (cbox a b) = 0 \<longrightarrow> f (cbox a b) = neutral opp) \<and>
    (\<forall>a b c. \<forall>k\<in>Basis. f (cbox a b) = opp (f(cbox a b \<inter> {x. x\<bullet>k \<le> c})) (f (cbox a b \<inter> {x. x\<bullet>k \<ge> c})))"

lemma operativeD[dest]:
  fixes type :: "'a::euclidean_space"
  assumes "operative opp f"
  shows "\<And>a b::'a. content (cbox a b) = 0 \<Longrightarrow> f (cbox a b) = neutral opp"
    and "\<And>a b c k. k \<in> Basis \<Longrightarrow> f (cbox a b) =
      opp (f (cbox a b \<inter> {x. x\<bullet>k \<le> c})) (f (cbox a b \<inter> {x. x\<bullet>k \<ge> c}))"
  using assms unfolding operative_def by auto

lemma operative_trivial: "operative opp f \<Longrightarrow> content (cbox a b) = 0 \<Longrightarrow> f (cbox a b) = neutral opp"
  unfolding operative_def by auto

lemma property_empty_interval: "\<forall>a b. content (cbox a b) = 0 \<longrightarrow> P (cbox a b) \<Longrightarrow> P {}"
  using content_empty unfolding empty_as_interval by auto

lemma operative_empty: "operative opp f \<Longrightarrow> f {} = neutral opp"
  unfolding operative_def by (rule property_empty_interval) auto


subsection {* Using additivity of lifted function to encode definedness. *}

lemma forall_option: "(\<forall>x. P x) \<longleftrightarrow> P None \<and> (\<forall>x. P (Some x))"
  by (metis option.nchotomy)

lemma exists_option: "(\<exists>x. P x) \<longleftrightarrow> P None \<or> (\<exists>x. P (Some x))"
  by (metis option.nchotomy)

fun lifted where
  "lifted (opp :: 'a \<Rightarrow> 'a \<Rightarrow> 'b) (Some x) (Some y) = Some (opp x y)"
| "lifted opp None _ = (None::'b option)"
| "lifted opp _ None = None"

lemma lifted_simp_1[simp]: "lifted opp v None = None"
  by (induct v) auto

definition "monoidal opp \<longleftrightarrow>
  (\<forall>x y. opp x y = opp y x) \<and>
  (\<forall>x y z. opp x (opp y z) = opp (opp x y) z) \<and>
  (\<forall>x. opp (neutral opp) x = x)"

lemma monoidalI:
  assumes "\<And>x y. opp x y = opp y x"
    and "\<And>x y z. opp x (opp y z) = opp (opp x y) z"
    and "\<And>x. opp (neutral opp) x = x"
  shows "monoidal opp"
  unfolding monoidal_def using assms by fastforce

lemma monoidal_ac:
  assumes "monoidal opp"
  shows "opp (neutral opp) a = a"
    and "opp a (neutral opp) = a"
    and "opp a b = opp b a"
    and "opp (opp a b) c = opp a (opp b c)"
    and "opp a (opp b c) = opp b (opp a c)"
  using assms unfolding monoidal_def by metis+

lemma monoidal_simps[simp]:
  assumes "monoidal opp"
  shows "opp (neutral opp) a = a"
    and "opp a (neutral opp) = a"
  using monoidal_ac[OF assms] by auto

lemma neutral_lifted[cong]:
  assumes "monoidal opp"
  shows "neutral (lifted opp) = Some (neutral opp)"
  apply (subst neutral_def)
  apply (rule some_equality)
  apply rule
  apply (induct_tac y)
  prefer 3
proof -
  fix x
  assume "\<forall>y. lifted opp x y = y \<and> lifted opp y x = y"
  then show "x = Some (neutral opp)"
    apply (induct x)
    defer
    apply rule
    apply (subst neutral_def)
    apply (subst eq_commute)
    apply(rule some_equality)
    apply rule
    apply (erule_tac x="Some y" in allE)
    defer
    apply (rename_tac x)
    apply (erule_tac x="Some x" in allE)
    apply auto
    done
qed (auto simp add:monoidal_ac[OF assms])

lemma monoidal_lifted[intro]:
  assumes "monoidal opp"
  shows "monoidal (lifted opp)"
  unfolding monoidal_def forall_option neutral_lifted[OF assms]
  using monoidal_ac[OF assms]
  by auto

definition "support opp f s = {x. x\<in>s \<and> f x \<noteq> neutral opp}"
definition "fold' opp e s = (if finite s then Finite_Set.fold opp e s else e)"
definition "iterate opp s f = fold' (\<lambda>x a. opp (f x) a) (neutral opp) (support opp f s)"

lemma support_subset[intro]: "support opp f s \<subseteq> s"
  unfolding support_def by auto

lemma support_empty[simp]: "support opp f {} = {}"
  using support_subset[of opp f "{}"] by auto

lemma comp_fun_commute_monoidal[intro]:
  assumes "monoidal opp"
  shows "comp_fun_commute opp"
  unfolding comp_fun_commute_def
  using monoidal_ac[OF assms]
  by auto

lemma support_clauses:
  "\<And>f g s. support opp f {} = {}"
  "\<And>f g s. support opp f (insert x s) =
    (if f(x) = neutral opp then support opp f s else insert x (support opp f s))"
  "\<And>f g s. support opp f (s - {x}) = (support opp f s) - {x}"
  "\<And>f g s. support opp f (s \<union> t) = (support opp f s) \<union> (support opp f t)"
  "\<And>f g s. support opp f (s \<inter> t) = (support opp f s) \<inter> (support opp f t)"
  "\<And>f g s. support opp f (s - t) = (support opp f s) - (support opp f t)"
  "\<And>f g s. support opp g (f ` s) = f ` (support opp (g o f) s)"
  unfolding support_def by auto

lemma finite_support[intro]: "finite s \<Longrightarrow> finite (support opp f s)"
  unfolding support_def by auto

lemma iterate_empty[simp]: "iterate opp {} f = neutral opp"
  unfolding iterate_def fold'_def by auto

lemma iterate_insert[simp]:
  assumes "monoidal opp"
    and "finite s"
  shows "iterate opp (insert x s) f =
    (if x \<in> s then iterate opp s f else opp (f x) (iterate opp s f))"
proof (cases "x \<in> s")
  case True
  then have *: "insert x s = s"
    by auto
  show ?thesis unfolding iterate_def if_P[OF True] * by auto
next
  case False
  note x = this
  note * = comp_fun_commute.comp_comp_fun_commute [OF comp_fun_commute_monoidal[OF assms(1)]]
  show ?thesis
  proof (cases "f x = neutral opp")
    case True
    show ?thesis
      unfolding iterate_def if_not_P[OF x] support_clauses if_P[OF True]
      unfolding True monoidal_simps[OF assms(1)]
      by auto
  next
    case False
    show ?thesis
      unfolding iterate_def fold'_def  if_not_P[OF x] support_clauses if_not_P[OF False]
      apply (subst comp_fun_commute.fold_insert[OF * finite_support, simplified comp_def])
      using `finite s`
      unfolding support_def
      using False x
      apply auto
      done
  qed
qed

lemma iterate_some:
  assumes "monoidal opp"
    and "finite s"
  shows "iterate (lifted opp) s (\<lambda>x. Some(f x)) = Some (iterate opp s f)"
  using assms(2)
proof (induct s)
  case empty
  then show ?case
    using assms by auto
next
  case (insert x F)
  show ?case
    apply (subst iterate_insert)
    prefer 3
    apply (subst if_not_P)
    defer
    unfolding insert(3) lifted.simps
    apply rule
    using assms insert
    apply auto
    done
qed


subsection {* Two key instances of additivity. *}

lemma neutral_add[simp]: "neutral op + = (0::'a::comm_monoid_add)"
  unfolding neutral_def
  apply (rule some_equality)
  defer
  apply (erule_tac x=0 in allE)
  apply auto
  done

lemma operative_content[intro]: "operative (op +) content"
  unfolding operative_def neutral_add
  apply safe
  unfolding content_split[symmetric]
  apply rule
  done

lemma monoidal_monoid[intro]: "monoidal ((op +)::('a::comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a)"
  unfolding monoidal_def neutral_add
  by (auto simp add: algebra_simps)

lemma operative_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "operative (lifted(op +)) (\<lambda>i. if f integrable_on i then Some(integral i f) else None)"
  unfolding operative_def
  unfolding neutral_lifted[OF monoidal_monoid] neutral_add
  apply rule
  apply rule
  apply rule
  apply rule
  defer
  apply (rule allI ballI)+
proof -
  fix a b c
  fix k :: 'a
  assume k: "k \<in> Basis"
  show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) =
    lifted op + (if f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c} then Some (integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f) else None)
    (if f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k} then Some (integral (cbox a b \<inter> {x. c \<le> x \<bullet> k}) f) else None)"
  proof (cases "f integrable_on cbox a b")
    case True
    show ?thesis
      unfolding if_P[OF True]
      using k
      apply -
      unfolding if_P[OF integrable_split(1)[OF True]]
      unfolding if_P[OF integrable_split(2)[OF True]]
      unfolding lifted.simps option.inject
      apply (rule integral_unique)
      apply (rule has_integral_split[OF _ _ k])
      apply (rule_tac[!] integrable_integral integrable_split)+
      using True k
      apply auto
      done
  next
    case False
    have "\<not> (f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<or> \<not> ( f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k})"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "f integrable_on cbox a b"
        apply -
        unfolding integrable_on_def
        apply (rule_tac x="integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f + integral (cbox a b \<inter> {x. x \<bullet> k \<ge> c}) f" in exI)
        apply (rule has_integral_split[OF _ _ k])
        apply (rule_tac[!] integrable_integral)
        apply auto
        done
      then show False
        using False by auto
    qed
    then show ?thesis
      using False by auto
  qed
next
  fix a b :: 'a
  assume as: "content (cbox a b) = 0"
  then show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) = Some 0"
    unfolding if_P[OF integrable_on_null[OF as]]
    using has_integral_null_eq[OF as]
    by auto
qed


subsection {* Points of division of a partition. *}

definition "division_points (k::('a::euclidean_space) set) d =
   {(j,x). j \<in> Basis \<and> (interval_lowerbound k)\<bullet>j < x \<and> x < (interval_upperbound k)\<bullet>j \<and>
     (\<exists>i\<in>d. (interval_lowerbound i)\<bullet>j = x \<or> (interval_upperbound i)\<bullet>j = x)}"

lemma division_points_finite:
  fixes i :: "'a::euclidean_space set"
  assumes "d division_of i"
  shows "finite (division_points i d)"
proof -
  note assm = division_ofD[OF assms]
  let ?M = "\<lambda>j. {(j,x)|x. (interval_lowerbound i)\<bullet>j < x \<and> x < (interval_upperbound i)\<bullet>j \<and>
    (\<exists>i\<in>d. (interval_lowerbound i)\<bullet>j = x \<or> (interval_upperbound i)\<bullet>j = x)}"
  have *: "division_points i d = \<Union>(?M ` Basis)"
    unfolding division_points_def by auto
  show ?thesis
    unfolding * using assm by auto
qed

lemma division_points_subset:
  fixes a :: "'a::euclidean_space"
  assumes "d division_of (cbox a b)"
    and "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
    and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l . l \<in> d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subseteq>
      division_points (cbox a b) d" (is ?t1)
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l . l \<in> d \<and> ~(l \<inter> {x. x\<bullet>k \<ge> c} = {})} \<subseteq>
      division_points (cbox a b) d" (is ?t2)
proof -
  note assm = division_ofD[OF assms(1)]
  have *: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    "\<forall>i\<in>Basis. a\<bullet>i \<le> (\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else  b \<bullet> i) *\<^sub>R i) \<bullet> i"
    "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i \<le> b\<bullet>i"
    "min (b \<bullet> k) c = c" "max (a \<bullet> k) c = c"
    using assms using less_imp_le by auto
  show ?t1
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding *
    unfolding subset_eq
    apply rule
    unfolding mem_Collect_eq split_beta
    apply (erule bexE conjE)+
    apply (simp only: mem_Collect_eq inner_setsum_left_Basis simp_thms)
    apply (erule exE conjE)+
  proof
    fix i l x
    assume as:
      "a \<bullet> fst x < snd x" "snd x < (if fst x = k then c else b \<bullet> fst x)"
      "interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      "i = l \<inter> {x. x \<bullet> k \<le> c}" "l \<in> d" "l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
      and fstx: "fst x \<in> Basis"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *: "\<forall>i\<in>Basis. u \<bullet> i \<le> (\<Sum>i\<in>Basis. (if i = k then min (v \<bullet> k) c else v \<bullet> i) *\<^sub>R i) \<bullet> i"
      using as(6) unfolding l interval_split[OF k] box_ne_empty as .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using as(6) unfolding box_ne_empty[symmetric] by auto
    show "\<exists>i\<in>d. interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      apply (rule bexI[OF _ `l \<in> d`])
      using as(1-3,5) fstx
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] as
      apply (auto split: split_if_asm)
      done
    show "snd x < b \<bullet> fst x"
      using as(2) `c < b\<bullet>k` by (auto split: split_if_asm)
  qed
  show ?t2
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding *
    unfolding subset_eq
    apply rule
    unfolding mem_Collect_eq split_beta
    apply (erule bexE conjE)+
    apply (simp only: mem_Collect_eq inner_setsum_left_Basis simp_thms)
    apply (erule exE conjE)+
  proof
    fix i l x
    assume as:
      "(if fst x = k then c else a \<bullet> fst x) < snd x" "snd x < b \<bullet> fst x"
      "interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      "i = l \<inter> {x. c \<le> x \<bullet> k}" "l \<in> d" "l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}"
      and fstx: "fst x \<in> Basis"
    from assm(4)[OF this(5)] guess u v by (elim exE) note l=this
    have *: "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (u \<bullet> k) c else u \<bullet> i) *\<^sub>R i) \<bullet> i \<le> v \<bullet> i"
      using as(6) unfolding l interval_split[OF k] box_ne_empty as .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using as(6) unfolding box_ne_empty[symmetric] by auto
    show "\<exists>i\<in>d. interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      apply (rule bexI[OF _ `l \<in> d`])
      using as(1-3,5) fstx
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] as
      apply (auto split: split_if_asm)
      done
    show "a \<bullet> fst x < snd x"
      using as(1) `a\<bullet>k < c` by (auto split: split_if_asm)
   qed
qed

lemma division_points_psubset:
  fixes a :: "'a::euclidean_space"
  assumes "d division_of (cbox a b)"
    and "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
    and "l \<in> d"
     and "interval_lowerbound l\<bullet>k = c \<or> interval_upperbound l\<bullet>k = c"
    and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subset>
      division_points (cbox a b) d" (is "?D1 \<subset> ?D")
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} \<subset>
      division_points (cbox a b) d" (is "?D2 \<subset> ?D")
proof -
  have ab: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    using assms(2) by (auto intro!:less_imp_le)
  guess u v using division_ofD(4)[OF assms(1,5)] by (elim exE) note l=this
  have uv: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i" "\<forall>i\<in>Basis. a\<bullet>i \<le> u\<bullet>i \<and> v\<bullet>i \<le> b\<bullet>i"
    using division_ofD(2,2,3)[OF assms(1,5)] unfolding l box_ne_empty
    unfolding subset_eq
    apply -
    defer
    apply (erule_tac x=u in ballE)
    apply (erule_tac x=v in ballE)
    unfolding mem_box
    apply auto
    done
  have *: "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_upperbound l \<bullet> k}) \<bullet> k = interval_upperbound l \<bullet> k"
    "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_lowerbound l \<bullet> k}) \<bullet> k = interval_lowerbound l \<bullet> k"
    unfolding interval_split[OF k]
    apply (subst interval_bounds)
    prefer 3
    apply (subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)]
    using uv[rule_format,of k] ab k
    apply auto
    done
  have "\<exists>x. x \<in> ?D - ?D1"
    using assms(2-)
    apply -
    apply (erule disjE)
    apply (rule_tac x="(k,(interval_lowerbound l)\<bullet>k)" in exI)
    defer
    apply (rule_tac x="(k,(interval_upperbound l)\<bullet>k)" in exI)
    unfolding division_points_def
    unfolding interval_bounds[OF ab]
    apply (auto simp add:*)
    done
  then show "?D1 \<subset> ?D"
    apply -
    apply rule
    apply (rule division_points_subset[OF assms(1-4)])
    using k
    apply auto
    done

  have *: "interval_lowerbound (cbox a b \<inter> {x. x \<bullet> k \<ge> interval_lowerbound l \<bullet> k}) \<bullet> k = interval_lowerbound l \<bullet> k"
    "interval_lowerbound (cbox a b \<inter> {x. x \<bullet> k \<ge> interval_upperbound l \<bullet> k}) \<bullet> k = interval_upperbound l \<bullet> k"
    unfolding interval_split[OF k]
    apply (subst interval_bounds)
    prefer 3
    apply (subst interval_bounds)
    unfolding l interval_bounds[OF uv(1)]
    using uv[rule_format,of k] ab k
    apply auto
    done
  have "\<exists>x. x \<in> ?D - ?D2"
    using assms(2-)
    apply -
    apply (erule disjE)
    apply (rule_tac x="(k,(interval_lowerbound l)\<bullet>k)" in exI)
    defer
    apply (rule_tac x="(k,(interval_upperbound l)\<bullet>k)" in exI)
    unfolding division_points_def
    unfolding interval_bounds[OF ab]
    apply (auto simp add:*)
    done
  then show "?D2 \<subset> ?D"
    apply -
    apply rule
    apply (rule division_points_subset[OF assms(1-4) k])
    apply auto
    done
qed


subsection {* Preservation by divisions and tagged divisions. *}

lemma support_support[simp]:"support opp f (support opp f s) = support opp f s"
  unfolding support_def by auto

lemma iterate_support[simp]: "iterate opp (support opp f s) f = iterate opp s f"
  unfolding iterate_def support_support by auto

lemma iterate_expand_cases:
  "iterate opp s f = (if finite(support opp f s) then iterate opp (support opp f s) f else neutral opp)"
  apply cases
  apply (subst if_P, assumption)
  unfolding iterate_def support_support fold'_def
  apply auto
  done

lemma iterate_image:
  assumes "monoidal opp"
    and "inj_on f s"
  shows "iterate opp (f ` s) g = iterate opp s (g \<circ> f)"
proof -
  have *: "\<And>s. finite s \<Longrightarrow>  \<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<longrightarrow> x = y \<Longrightarrow>
    iterate opp (f ` s) g = iterate opp s (g \<circ> f)"
  proof -
    case goal1
    then show ?case
    proof (induct s)
      case empty
      then show ?case
        using assms(1) by auto
    next
      case (insert x s)
      show ?case
        unfolding iterate_insert[OF assms(1) insert(1)]
        unfolding if_not_P[OF insert(2)]
        apply (subst insert(3)[symmetric])
        unfolding image_insert
        defer
        apply (subst iterate_insert[OF assms(1)])
        apply (rule finite_imageI insert)+
        apply (subst if_not_P)
        unfolding image_iff o_def
        using insert(2,4)
        apply auto
        done
    qed
  qed
  show ?thesis
    apply (cases "finite (support opp g (f ` s))")
    apply (subst (1) iterate_support[symmetric],subst (2) iterate_support[symmetric])
    unfolding support_clauses
    apply (rule *)
    apply (rule finite_imageD,assumption)
    unfolding inj_on_def[symmetric]
    apply (rule subset_inj_on[OF assms(2) support_subset])+
    apply (subst iterate_expand_cases)
    unfolding support_clauses
    apply (simp only: if_False)
    apply (subst iterate_expand_cases)
    apply (subst if_not_P)
    apply auto
    done
qed


(* This lemma about iterations comes up in a few places. *)
lemma iterate_nonzero_image_lemma:
  assumes "monoidal opp"
    and "finite s" "g(a) = neutral opp"
    and "\<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<and> x \<noteq> y \<longrightarrow> g(f x) = neutral opp"
  shows "iterate opp {f x | x. x \<in> s \<and> f x \<noteq> a} g = iterate opp s (g \<circ> f)"
proof -
  have *: "{f x |x. x \<in> s \<and> f x \<noteq> a} = f ` {x. x \<in> s \<and> f x \<noteq> a}"
    by auto
  have **: "support opp (g \<circ> f) {x \<in> s. f x \<noteq> a} = support opp (g \<circ> f) s"
    unfolding support_def using assms(3) by auto
  show ?thesis
    unfolding *
    apply (subst iterate_support[symmetric])
    unfolding support_clauses
    apply (subst iterate_image[OF assms(1)])
    defer
    apply (subst(2) iterate_support[symmetric])
    apply (subst **)
    unfolding inj_on_def
    using assms(3,4)
    unfolding support_def
    apply auto
    done
qed

lemma iterate_eq_neutral:
  assumes "monoidal opp"
    and "\<forall>x \<in> s. f x = neutral opp"
  shows "iterate opp s f = neutral opp"
proof -
  have *: "support opp f s = {}"
    unfolding support_def using assms(2) by auto
  show ?thesis
    apply (subst iterate_support[symmetric])
    unfolding *
    using assms(1)
    apply auto
    done
qed

lemma iterate_op:
  assumes "monoidal opp"
    and "finite s"
  shows "iterate opp s (\<lambda>x. opp (f x) (g x)) = opp (iterate opp s f) (iterate opp s g)"
  using assms(2)
proof (induct s)
  case empty
  then show ?case
    unfolding iterate_insert[OF assms(1)] using assms(1) by auto
next
  case (insert x F)
  show ?case
    unfolding iterate_insert[OF assms(1) insert(1)] if_not_P[OF insert(2)] insert(3)
    by (simp add: monoidal_ac[OF assms(1)])
qed

lemma iterate_eq:
  assumes "monoidal opp"
    and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "iterate opp s f = iterate opp s g"
proof -
  have *: "support opp g s = support opp f s"
    unfolding support_def using assms(2) by auto
  show ?thesis
  proof (cases "finite (support opp f s)")
    case False
    then show ?thesis
      apply (subst iterate_expand_cases)
      apply (subst(2) iterate_expand_cases)
      unfolding *
      apply auto
      done
  next
    def su \<equiv> "support opp f s"
    case True note support_subset[of opp f s]
    then show ?thesis
      apply -
      apply (subst iterate_support[symmetric])
      apply (subst(2) iterate_support[symmetric])
      unfolding *
      using True
      unfolding su_def[symmetric]
    proof (induct su)
      case empty
      show ?case by auto
    next
      case (insert x s)
      show ?case
        unfolding iterate_insert[OF assms(1) insert(1)]
        unfolding if_not_P[OF insert(2)]
        apply (subst insert(3))
        defer
        apply (subst assms(2)[of x])
        using insert
        apply auto
        done
    qed
  qed
qed

lemma nonempty_witness:
  assumes "s \<noteq> {}"
  obtains x where "x \<in> s"
  using assms by auto

lemma operative_division:
  fixes f :: "'a::euclidean_space set \<Rightarrow> 'b"
  assumes "monoidal opp"
    and "operative opp f"
    and "d division_of (cbox a b)"
  shows "iterate opp d f = f (cbox a b)"
proof -
  def C \<equiv> "card (division_points (cbox a b) d)"
  then show ?thesis
    using assms
  proof (induct C arbitrary: a b d rule: full_nat_induct)
    case goal1
    { presume *: "content (cbox a b) \<noteq> 0 \<Longrightarrow> ?case"
      then show ?case
        apply -
        apply cases
        defer
        apply assumption
      proof -
        assume as: "content (cbox a b) = 0"
        show ?case
          unfolding operativeD(1)[OF assms(2) as]
          apply(rule iterate_eq_neutral[OF goal1(2)])
        proof
          fix x
          assume x: "x \<in> d"
          then guess u v
            apply (drule_tac division_ofD(4)[OF goal1(4)])
            apply (elim exE)
            done
          then show "f x = neutral opp"
            using division_of_content_0[OF as goal1(4)]
            using operativeD(1)[OF assms(2)] x
            by auto
        qed
      qed
    }
    assume "content (cbox a b) \<noteq> 0" note ab = this[unfolded content_lt_nz[symmetric] content_pos_lt_eq]
    then have ab': "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
      by (auto intro!: less_imp_le)
    show ?case
    proof (cases "division_points (cbox a b) d = {}")
      case True
      have d': "\<forall>i\<in>d. \<exists>u v. i = cbox u v \<and>
        (\<forall>j\<in>Basis. u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = a\<bullet>j \<or> u\<bullet>j = b\<bullet>j \<and> v\<bullet>j = b\<bullet>j \<or> u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = b\<bullet>j)"
        unfolding forall_in_division[OF goal1(4)]
        apply rule
        apply rule
        apply rule
        apply (rule_tac x=a in exI)
        apply (rule_tac x=b in exI)
        apply rule
        apply (rule refl)
      proof
        fix u v
        fix j :: 'a
        assume j: "j \<in> Basis"
        assume as: "cbox u v \<in> d"
        note division_ofD(3)[OF goal1(4) this]
        then have uv: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i" "u\<bullet>j \<le> v\<bullet>j"
          using j unfolding box_ne_empty by auto
        have *: "\<And>p r Q. \<not> j\<in>Basis \<or> p \<or> r \<or> (\<forall>x\<in>d. Q x) \<Longrightarrow> p \<or> r \<or> Q (cbox u v)"
          using as j by auto
        have "(j, u\<bullet>j) \<notin> division_points (cbox a b) d"
          "(j, v\<bullet>j) \<notin> division_points (cbox a b) d" using True by auto
        note this[unfolded de_Morgan_conj division_points_def mem_Collect_eq split_conv interval_bounds[OF ab'] bex_simps]
        note *[OF this(1)] *[OF this(2)] note this[unfolded interval_bounds[OF uv(1)]]
        moreover
        have "a\<bullet>j \<le> u\<bullet>j" "v\<bullet>j \<le> b\<bullet>j"
          using division_ofD(2,2,3)[OF goal1(4) as]
          unfolding subset_eq
          apply -
          apply (erule_tac x=u in ballE,erule_tac[3] x=v in ballE)
          unfolding box_ne_empty mem_box
          using j
          apply auto
          done
        ultimately show "u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = a\<bullet>j \<or> u\<bullet>j = b\<bullet>j \<and> v\<bullet>j = b\<bullet>j \<or> u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = b\<bullet>j"
          unfolding not_less de_Morgan_disj using ab[rule_format,of j] uv(2) j by auto
      qed
      have "(1/2) *\<^sub>R (a+b) \<in> cbox a b"
        unfolding mem_box using ab by(auto intro!: less_imp_le simp: inner_simps)
      note this[unfolded division_ofD(6)[OF goal1(4),symmetric] Union_iff]
      then guess i .. note i=this
      guess u v using d'[rule_format,OF i(1)] by (elim exE conjE) note uv=this
      have "cbox a b \<in> d"
      proof -
        { presume "i = cbox a b" then show ?thesis using i by auto }
        { presume "u = a" "v = b" then show "i = cbox a b" using uv by auto }
        show "u = a" "v = b"
          unfolding euclidean_eq_iff[where 'a='a]
        proof safe
          fix j :: 'a
          assume j: "j \<in> Basis"
          note i(2)[unfolded uv mem_box,rule_format,of j]
          then show "u \<bullet> j = a \<bullet> j" and "v \<bullet> j = b \<bullet> j"
            using uv(2)[rule_format,of j] j by (auto simp: inner_simps)
        qed
      qed
      then have *: "d = insert (cbox a b) (d - {cbox a b})"
        by auto
      have "iterate opp (d - {cbox a b}) f = neutral opp"
        apply (rule iterate_eq_neutral[OF goal1(2)])
      proof
        fix x
        assume x: "x \<in> d - {cbox a b}"
        then have "x\<in>d"
          by auto note d'[rule_format,OF this]
        then guess u v by (elim exE conjE) note uv=this
        have "u \<noteq> a \<or> v \<noteq> b"
          using x[unfolded uv] by auto
        then obtain j where "u\<bullet>j \<noteq> a\<bullet>j \<or> v\<bullet>j \<noteq> b\<bullet>j" and j: "j \<in> Basis"
          unfolding euclidean_eq_iff[where 'a='a] by auto
        then have "u\<bullet>j = v\<bullet>j"
          using uv(2)[rule_format,OF j] by auto
        then have "content (cbox u v) = 0"
          unfolding content_eq_0
          apply (rule_tac x=j in bexI)
          using j
          apply auto
          done
        then show "f x = neutral opp"
          unfolding uv(1) by (rule operativeD(1)[OF goal1(3)])
      qed
      then show "iterate opp d f = f (cbox a b)"
        apply -
        apply (subst *)
        apply (subst iterate_insert[OF goal1(2)])
        using goal1(2,4)
        apply auto
        done
    next
      case False
      then have "\<exists>x. x \<in> division_points (cbox a b) d"
        by auto
      then guess k c
        unfolding split_paired_Ex
        unfolding division_points_def mem_Collect_eq split_conv
        apply (elim exE conjE)
        done
      note this(2-4,1) note kc=this[unfolded interval_bounds[OF ab']]
      from this(3) guess j .. note j=this
      def d1 \<equiv> "{l \<inter> {x. x\<bullet>k \<le> c} | l. l \<in> d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
      def d2 \<equiv> "{l \<inter> {x. x\<bullet>k \<ge> c} | l. l \<in> d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
      def cb \<equiv> "(\<Sum>i\<in>Basis. (if i = k then c else b\<bullet>i) *\<^sub>R i)::'a"
      def ca \<equiv> "(\<Sum>i\<in>Basis. (if i = k then c else a\<bullet>i) *\<^sub>R i)::'a"
      note division_points_psubset[OF goal1(4) ab kc(1-2) j]
      note psubset_card_mono[OF _ this(1)] psubset_card_mono[OF _ this(2)]
      then have *: "(iterate opp d1 f) = f (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
        "(iterate opp d2 f) = f (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
        unfolding interval_split[OF kc(4)]
        apply (rule_tac[!] goal1(1)[rule_format])
        using division_split[OF goal1(4), where k=k and c=c]
        unfolding interval_split[OF kc(4)] d1_def[symmetric] d2_def[symmetric]
        unfolding goal1(2) Suc_le_mono
        using goal1(2-3)
        using division_points_finite[OF goal1(4)]
        using kc(4)
        apply auto
        done
      have "f (cbox a b) = opp (iterate opp d1 f) (iterate opp d2 f)" (is "_ = ?prev")
        unfolding *
        apply (rule operativeD(2))
        using goal1(3)
        using kc(4)
        apply auto
        done
      also have "iterate opp d1 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x\<bullet>k \<le> c}))"
        unfolding d1_def
        apply (rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval
        apply (rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[symmetric]
        apply (rule content_empty)
      proof (rule, rule, rule, erule conjE)
        fix l y
        assume as: "l \<in> d" "y \<in> d" "l \<inter> {x. x \<bullet> k \<le> c} = y \<inter> {x. x \<bullet> k \<le> c}" "l \<noteq> y"
        from division_ofD(4)[OF goal1(4) this(1)] guess u v by (elim exE) note l=this
        show "f (l \<inter> {x. x \<bullet> k \<le> c}) = neutral opp"
          unfolding l interval_split[OF kc(4)]
          apply (rule operativeD(1) goal1)+
          unfolding interval_split[symmetric,OF kc(4)]
          apply (rule division_split_left_inj)
          apply (rule goal1)
          unfolding l[symmetric]
          apply (rule as(1), rule as(2))
          apply (rule kc(4) as)+
          done
      qed
      also have "iterate opp d2 f = iterate opp d (\<lambda>l. f(l \<inter> {x. x\<bullet>k \<ge> c}))"
        unfolding d2_def
        apply (rule iterate_nonzero_image_lemma[unfolded o_def])
        unfolding empty_as_interval
        apply (rule goal1 division_of_finite operativeD[OF goal1(3)])+
        unfolding empty_as_interval[symmetric]
        apply (rule content_empty)
      proof (rule, rule, rule, erule conjE)
        fix l y
        assume as: "l \<in> d" "y \<in> d" "l \<inter> {x. c \<le> x \<bullet> k} = y \<inter> {x. c \<le> x \<bullet> k}" "l \<noteq> y"
        from division_ofD(4)[OF goal1(4) this(1)] guess u v by (elim exE) note l=this
        show "f (l \<inter> {x. x \<bullet> k \<ge> c}) = neutral opp"
        unfolding l interval_split[OF kc(4)]
          apply (rule operativeD(1) goal1)+
          unfolding interval_split[symmetric,OF kc(4)]
          apply (rule division_split_right_inj)
          apply (rule goal1)
          unfolding l[symmetric]
          apply (rule as(1))
          apply (rule as(2))
          apply (rule as kc(4))+
          done
      qed also have *: "\<forall>x\<in>d. f x = opp (f (x \<inter> {x. x \<bullet> k \<le> c})) (f (x \<inter> {x. c \<le> x \<bullet> k}))"
        unfolding forall_in_division[OF goal1(4)]
        apply (rule, rule, rule, rule operativeD(2))
        using goal1(3) kc
        by auto
      have "opp (iterate opp d (\<lambda>l. f (l \<inter> {x. x \<bullet> k \<le> c}))) (iterate opp d (\<lambda>l. f (l \<inter> {x. c \<le> x \<bullet> k}))) =
        iterate opp d f"
        apply (subst(3) iterate_eq[OF _ *[rule_format]])
        prefer 3
        apply (rule iterate_op[symmetric])
        using goal1
        apply auto
        done
      finally show ?thesis by auto
    qed
  qed
qed

lemma iterate_image_nonzero:
  assumes "monoidal opp"
    and "finite s"
    and "\<forall>x\<in>s. \<forall>y\<in>s. x \<noteq> y \<and> f x = f y \<longrightarrow> g (f x) = neutral opp"
  shows "iterate opp (f ` s) g = iterate opp s (g \<circ> f)"
  using assms
proof (induct rule: finite_subset_induct[OF assms(2) subset_refl])
  case goal1
  show ?case
    using assms(1) by auto
next
  case goal2
  have *: "\<And>x y. y = neutral opp \<Longrightarrow> x = opp y x"
    using assms(1) by auto
  show ?case
    unfolding image_insert
    apply (subst iterate_insert[OF assms(1)])
    apply (rule finite_imageI goal2)+
    apply (cases "f a \<in> f ` F")
    unfolding if_P if_not_P
    apply (subst goal2(4)[OF assms(1) goal2(1)])
    defer
    apply (subst iterate_insert[OF assms(1) goal2(1)])
    defer
    apply (subst iterate_insert[OF assms(1) goal2(1)])
    unfolding if_not_P[OF goal2(3)]
    defer unfolding image_iff
    defer
    apply (erule bexE)
    apply (rule *)
    unfolding o_def
    apply (rule_tac y=x in goal2(7)[rule_format])
    using goal2
    unfolding o_def
    apply auto
    done
qed

lemma operative_tagged_division:
  assumes "monoidal opp"
    and "operative opp f"
    and "d tagged_division_of (cbox a b)"
  shows "iterate opp d (\<lambda>(x,l). f l) = f (cbox a b)"
proof -
  have *: "(\<lambda>(x,l). f l) = f \<circ> snd"
    unfolding o_def by rule auto note assm = tagged_division_ofD[OF assms(3)]
  have "iterate opp d (\<lambda>(x,l). f l) = iterate opp (snd ` d) f"
    unfolding *
    apply (rule iterate_image_nonzero[symmetric,OF assms(1)])
    apply (rule tagged_division_of_finite assms)+
    unfolding Ball_def split_paired_All snd_conv
    apply (rule, rule, rule, rule, rule, rule, rule, erule conjE)
  proof -
    fix a b aa ba
    assume as: "(a, b) \<in> d" "(aa, ba) \<in> d" "(a, b) \<noteq> (aa, ba)" "b = ba"
    guess u v using assm(4)[OF as(1)] by (elim exE) note uv=this
    show "f b = neutral opp"
      unfolding uv
      apply (rule operativeD(1)[OF assms(2)])
      unfolding content_eq_0_interior
      using tagged_division_ofD(5)[OF assms(3) as(1-3)]
      unfolding as(4)[symmetric] uv
      apply auto
      done
  qed
  also have "\<dots> = f (cbox a b)"
    using operative_division[OF assms(1-2) division_of_tagged_division[OF assms(3)]] .
  finally show ?thesis .
qed


subsection {* Additivity of content. *}

lemma setsum_iterate:
  assumes "finite s"
  shows "setsum f s = iterate op + s f"
proof -
  have *: "setsum f s = setsum f (support op + f s)"
    apply (rule setsum_mono_zero_right)
    unfolding support_def neutral_add
    using assms
    apply auto
    done
  then show ?thesis unfolding * iterate_def fold'_def setsum.eq_fold
    unfolding neutral_add by (simp add: comp_def)
qed

lemma additive_content_division:
  assumes "d division_of (cbox a b)"
  shows "setsum content d = content (cbox a b)"
  unfolding operative_division[OF monoidal_monoid operative_content assms,symmetric]
  apply (subst setsum_iterate)
  using assms
  apply auto
  done

lemma additive_content_tagged_division:
  assumes "d tagged_division_of (cbox a b)"
  shows "setsum (\<lambda>(x,l). content l) d = content (cbox a b)"
  unfolding operative_tagged_division[OF monoidal_monoid operative_content assms,symmetric]
  apply (subst setsum_iterate)
  using assms
  apply auto
  done


subsection {* Finally, the integral of a constant *}

lemma has_integral_const[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>x. c) has_integral (content (cbox a b) *\<^sub>R c)) (cbox a b)"
  unfolding has_integral
  apply rule
  apply rule
  apply (rule_tac x="\<lambda>x. ball x 1" in exI)
  apply rule
  apply (rule gauge_trivial)
  apply rule
  apply rule
  apply (erule conjE)
  unfolding split_def
  apply (subst scaleR_left.setsum[symmetric, unfolded o_def])
  defer
  apply (subst additive_content_tagged_division[unfolded split_def])
  apply assumption
  apply auto
  done

lemma has_integral_const_real[intro]:
  fixes a b :: real
  shows "((\<lambda>x. c) has_integral (content {a .. b} *\<^sub>R c)) {a .. b}"
  by (metis box_real(2) has_integral_const)

lemma integral_const[simp]:
  fixes a b :: "'a::euclidean_space"
  shows "integral (cbox a b) (\<lambda>x. c) = content (cbox a b) *\<^sub>R c"
  by (rule integral_unique) (rule has_integral_const)

lemma integral_const_real[simp]:
  fixes a b :: real
  shows "integral {a .. b} (\<lambda>x. c) = content {a .. b} *\<^sub>R c"
  by (metis box_real(2) integral_const)


subsection {* Bounds on the norm of Riemann sums and the integral itself. *}

lemma dsum_bound:
  assumes "p division_of (cbox a b)"
    and "norm c \<le> e"
  shows "norm (setsum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content(cbox a b)"
  apply (rule order_trans)
  apply (rule norm_setsum)
  unfolding norm_scaleR setsum_left_distrib[symmetric]
  apply (rule order_trans[OF mult_left_mono])
  apply (rule assms)
  apply (rule setsum_abs_ge_zero)
  apply (subst mult_commute)
  apply (rule mult_left_mono)
  apply (rule order_trans[of _ "setsum content p"])
  apply (rule eq_refl)
  apply (rule setsum_cong2)
  apply (subst abs_of_nonneg)
  unfolding additive_content_division[OF assms(1)]
proof -
  from order_trans[OF norm_ge_zero[of c] assms(2)]
  show "0 \<le> e" .
  fix x assume "x \<in> p"
  from division_ofD(4)[OF assms(1) this] guess u v by (elim exE)
  then show "0 \<le> content x"
    using content_pos_le by auto
qed (insert assms, auto)

lemma rsum_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x) \<le> e"
  shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> e * content (cbox a b)"
proof (cases "cbox a b = {}")
  case True
  show ?thesis
    using assms(1) unfolding True tagged_division_of_trivial by auto
next
  case False
  show ?thesis
    apply (rule order_trans)
    apply (rule norm_setsum)
    unfolding split_def norm_scaleR
    apply (rule order_trans[OF setsum_mono])
    apply (rule mult_left_mono[OF _ abs_ge_zero, of _ e])
    defer
    unfolding setsum_left_distrib[symmetric]
    apply (subst mult_commute)
    apply (rule mult_left_mono)
    apply (rule order_trans[of _ "setsum (content \<circ> snd) p"])
    apply (rule eq_refl)
    apply (rule setsum_cong2)
    apply (subst o_def)
    apply (rule abs_of_nonneg)
  proof -
    show "setsum (content \<circ> snd) p \<le> content (cbox a b)"
      apply (rule eq_refl)
      unfolding additive_content_tagged_division[OF assms(1),symmetric] split_def
      apply auto
      done
    guess w using nonempty_witness[OF False] .
    then show "e \<ge> 0"
      apply -
      apply (rule order_trans)
      defer
      apply (rule assms(2)[rule_format])
      apply assumption
      apply auto
      done
    fix xk
    assume *: "xk \<in> p"
    guess x k using surj_pair[of xk] by (elim exE) note xk = this *[unfolded this]
    from tagged_division_ofD(4)[OF assms(1) xk(2)] guess u v by (elim exE) note uv=this
    show "0 \<le> content (snd xk)"
      unfolding xk snd_conv uv by(rule content_pos_le)
    show "norm (f (fst xk)) \<le> e"
      unfolding xk fst_conv using tagged_division_ofD(2,3)[OF assms(1) xk(2)] assms(2) by auto
  qed
qed

lemma rsum_diff_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e"
  shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - setsum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le>
    e * content (cbox a b)"
  apply (rule order_trans[OF _ rsum_bound[OF assms]])
  apply (rule eq_refl)
  apply (rule arg_cong[where f=norm])
  unfolding setsum_subtractf[symmetric]
  apply (rule setsum_cong2)
  unfolding scaleR_diff_right
  apply auto
  done

lemma has_integral_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
    and "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x) \<le> B"
  shows "norm i \<le> B * content (cbox a b)"
proof -
  let ?P = "content (cbox a b) > 0"
  {
    presume "?P \<Longrightarrow> ?thesis"
    then show ?thesis
    proof (cases ?P)
      case False
      then have *: "content (cbox a b) = 0"
        using content_lt_nz by auto
      then have **: "i = 0"
        using assms(2)
        apply (subst has_integral_null_eq[symmetric])
        apply auto
        done
      show ?thesis
        unfolding * ** using assms(1) by auto
    qed auto
  }
  assume ab: ?P
  { presume "\<not> ?thesis \<Longrightarrow> False" then show ?thesis by auto }
  assume "\<not> ?thesis"
  then have *: "norm i - B * content (cbox a b) > 0"
    by auto
  from assms(2)[unfolded has_integral,rule_format,OF *]
  guess d by (elim exE conjE) note d=this[rule_format]
  from fine_division_exists[OF this(1), of a b] guess p . note p=this
  have *: "\<And>s B. norm s \<le> B \<Longrightarrow> \<not> norm (s - i) < norm i - B"
  proof -
    case goal1
    then show ?case
      unfolding not_less
      using norm_triangle_sub[of i s]
      unfolding norm_minus_commute
      by auto
  qed
  show False
    using d(2)[OF conjI[OF p]] *[OF rsum_bound[OF p(1) assms(3)]] by auto
qed

lemma has_integral_bound_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
    and "(f has_integral i) {a .. b}"
    and "\<forall>x\<in>{a .. b}. norm (f x) \<le> B"
  shows "norm i \<le> B * content {a .. b}"
  by (metis assms(1) assms(2) assms(3) box_real(2) has_integral_bound)


subsection {* Similar theorems about relationship among components. *}

lemma rsum_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. (f x)\<bullet>i \<le> (g x)\<bullet>i"
  shows "(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p)\<bullet>i \<le> (setsum (\<lambda>(x,k). content k *\<^sub>R g x) p)\<bullet>i"
  unfolding inner_setsum_left
  apply (rule setsum_mono)
  apply safe
proof -
  fix a b
  assume ab: "(a, b) \<in> p"
  note assm = tagged_division_ofD(2-4)[OF assms(1) ab]
  from this(3) guess u v by (elim exE) note b=this
  show "(content b *\<^sub>R f a) \<bullet> i \<le> (content b *\<^sub>R g a) \<bullet> i"
    unfolding b
    unfolding inner_simps real_scaleR_def
    apply (rule mult_left_mono)
    defer
    apply (rule content_pos_le,rule assms(2)[rule_format])
    using assm
    apply auto
    done
qed

lemma has_integral_component_le:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
  assumes "(f has_integral i) s" "(g has_integral j) s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  have lem: "\<And>a b i j::'b. \<And>g f::'a \<Rightarrow> 'b. (f has_integral i) (cbox a b) \<Longrightarrow>
    (g has_integral j) (cbox a b) \<Longrightarrow> \<forall>x\<in>cbox a b. (f x)\<bullet>k \<le> (g x)\<bullet>k \<Longrightarrow> i\<bullet>k \<le> j\<bullet>k"
  proof (rule ccontr)
    case goal1
    then have *: "0 < (i\<bullet>k - j\<bullet>k) / 3"
      by auto
    guess d1 using goal1(1)[unfolded has_integral,rule_format,OF *] by (elim exE conjE) note d1=this[rule_format]
    guess d2 using goal1(2)[unfolded has_integral,rule_format,OF *] by (elim exE conjE) note d2=this[rule_format]
    guess p using fine_division_exists[OF gauge_inter[OF d1(1) d2(1)], of a b] unfolding fine_inter .
    note p = this(1) conjunctD2[OF this(2)]
    note le_less_trans[OF Basis_le_norm[OF k]]
    note this[OF d1(2)[OF conjI[OF p(1,2)]]] this[OF d2(2)[OF conjI[OF p(1,3)]]]
    then show False
      unfolding inner_simps
      using rsum_component_le[OF p(1) goal1(3)]
      by (simp add: abs_real_def split: split_if_asm)
  qed
  let ?P = "\<exists>a b. s = cbox a b"
  {
    presume "\<not> ?P \<Longrightarrow> ?thesis"
    then show ?thesis
    proof (cases ?P)
      case True
      then guess a b by (elim exE) note s=this
      show ?thesis
        apply (rule lem)
        using assms[unfolded s]
        apply auto
        done
    qed auto
  }
  assume as: "\<not> ?P"
  { presume "\<not> ?thesis \<Longrightarrow> False" then show ?thesis by auto }
  assume "\<not> i\<bullet>k \<le> j\<bullet>k"
  then have ij: "(i\<bullet>k - j\<bullet>k) / 3 > 0"
    by auto
  note has_integral_altD[OF _ as this]
  from this[OF assms(2)] this[OF assms(3)] guess B1 B2 . note B=this[rule_format]
  have "bounded (ball 0 B1 \<union> ball (0::'a) B2)"
    unfolding bounded_Un by(rule conjI bounded_ball)+
  from bounded_subset_cbox[OF this] guess a b by (elim exE)
  note ab = conjunctD2[OF this[unfolded Un_subset_iff]]
  guess w1 using B(2)[OF ab(1)] .. note w1=conjunctD2[OF this]
  guess w2 using B(4)[OF ab(2)] .. note w2=conjunctD2[OF this]
  have *: "\<And>w1 w2 j i::real .\<bar>w1 - i\<bar> < (i - j) / 3 \<Longrightarrow> \<bar>w2 - j\<bar> < (i - j) / 3 \<Longrightarrow> w1 \<le> w2 \<Longrightarrow> False"
    by (simp add: abs_real_def split: split_if_asm)
  note le_less_trans[OF Basis_le_norm[OF k]]
  note this[OF w1(2)] this[OF w2(2)]
  moreover
  have "w1\<bullet>k \<le> w2\<bullet>k"
    apply (rule lem[OF w1(1) w2(1)])
    using assms
    apply auto
    done
  ultimately show False
    unfolding inner_simps by(rule *)
qed

lemma integral_component_le:
  fixes g f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on s" "g integrable_on s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "(integral s f)\<bullet>k \<le> (integral s g)\<bullet>k"
  apply (rule has_integral_component_le)
  using integrable_integral assms
  apply auto
  done

lemma has_integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) s"
    and "\<forall>x\<in>s. 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(1) has_integral_0 assms(2)]
  using assms(3-)
  by auto

lemma integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on s" "\<forall>x\<in>s. 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> (integral s f)\<bullet>k"
  apply (rule has_integral_component_nonneg)
  using assms
  apply auto
  done

lemma has_integral_component_neg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> 0"
  shows "i\<bullet>k \<le> 0"
  using has_integral_component_le[OF assms(1,2) has_integral_0] assms(2-)
  by auto

lemma has_integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(3) has_integral_const assms(1),of "(\<Sum>i\<in>Basis. B *\<^sub>R i)::'b"] assms(2-)
  by (auto simp add: field_simps)

lemma has_integral_component_ubound:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "i\<bullet>k \<le> B * content (cbox a b)"
  using has_integral_component_le[OF assms(3,1) has_integral_const, of "\<Sum>i\<in>Basis. B *\<^sub>R i"] assms(2-)
  by (auto simp add: field_simps)

lemma integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> (integral(cbox a b) f)\<bullet>k"
  apply (rule has_integral_component_lbound)
  using assms
  unfolding has_integral_integral
  apply auto
  done

lemma integral_component_lbound_real:
  assumes "f integrable_on {a ::real .. b}"
    and "\<forall>x\<in>{a .. b}. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content {a .. b} \<le> (integral {a .. b} f)\<bullet>k"
  using assms
  by (metis box_real(2) integral_component_lbound)

lemma integral_component_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral (cbox a b) f)\<bullet>k \<le> B * content (cbox a b)"
  apply (rule has_integral_component_ubound)
  using assms
  unfolding has_integral_integral
  apply auto
  done

lemma integral_component_ubound_real:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a .. b}"
    and "\<forall>x\<in>{a .. b}. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral {a .. b} f)\<bullet>k \<le> B * content {a .. b}"
  using assms
  by (metis box_real(2) integral_component_ubound)

subsection {* Uniform limit of integrable functions is integrable. *}

lemma integrable_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "\<forall>e>0. \<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
  shows "f integrable_on cbox a b"
proof -
  {
    presume *: "content (cbox a b) > 0 \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      unfolding content_lt_nz integrable_on_def
      using has_integral_null
      apply auto
      done
  }
  assume as: "content (cbox a b) > 0"
  have *: "\<And>P. \<forall>e>(0::real). P e \<Longrightarrow> \<forall>n::nat. P (inverse (real n + 1))"
    by auto
  from choice[OF *[OF assms]] guess g .. note g=conjunctD2[OF this[rule_format],rule_format]
  from choice[OF allI[OF g(2)[unfolded integrable_on_def], of "\<lambda>x. x"]] guess i .. note i=this[rule_format]

  have "Cauchy i"
    unfolding Cauchy_def
  proof (rule, rule)
    fix e :: real
    assume "e>0"
    then have "e / 4 / content (cbox a b) > 0"
      using as by (auto simp add: field_simps)
    then guess M
      apply -
      apply (subst(asm) real_arch_inv)
      apply (elim exE conjE)
      done
    note M=this
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (i m) (i n) < e"
      apply (rule_tac x=M in exI,rule,rule,rule,rule)
    proof -
      case goal1
      have "e/4>0" using `e>0` by auto
      note * = i[unfolded has_integral,rule_format,OF this]
      from *[of m] guess gm by (elim conjE exE) note gm=this[rule_format]
      from *[of n] guess gn by (elim conjE exE) note gn=this[rule_format]
      from fine_division_exists[OF gauge_inter[OF gm(1) gn(1)], of a b] guess p . note p=this
      have lem2: "\<And>s1 s2 i1 i2. norm(s2 - s1) \<le> e/2 \<Longrightarrow> norm (s1 - i1) < e / 4 \<Longrightarrow>
        norm (s2 - i2) < e / 4 \<Longrightarrow> norm (i1 - i2) < e"
      proof -
        case goal1
        have "norm (i1 - i2) \<le> norm (i1 - s1) + norm (s1 - s2) + norm (s2 - i2)"
          using norm_triangle_ineq[of "i1 - s1" "s1 - i2"]
          using norm_triangle_ineq[of "s1 - s2" "s2 - i2"]
          by (auto simp add: algebra_simps)
        also have "\<dots> < e"
          using goal1
          unfolding norm_minus_commute
          by (auto simp add: algebra_simps)
        finally show ?case .
      qed
      show ?case
        unfolding dist_norm
        apply (rule lem2)
        defer
        apply (rule gm(2)[OF conjI[OF p(1)]],rule_tac[2] gn(2)[OF conjI[OF p(1)]])
        using conjunctD2[OF p(2)[unfolded fine_inter]]
        apply -
        apply assumption+
        apply (rule order_trans)
        apply (rule rsum_diff_bound[OF p(1), where e="2 / real M"])
      proof
        show "2 / real M * content (cbox a b) \<le> e / 2"
          unfolding divide_inverse
          using M as
          by (auto simp add: field_simps)
        fix x
        assume x: "x \<in> cbox a b"
        have "norm (f x - g n x) + norm (f x - g m x) \<le> inverse (real n + 1) + inverse (real m + 1)"
          using g(1)[OF x, of n] g(1)[OF x, of m] by auto
        also have "\<dots> \<le> inverse (real M) + inverse (real M)"
          apply (rule add_mono)
          apply (rule_tac[!] le_imp_inverse_le)
          using goal1 M
          apply auto
          done
        also have "\<dots> = 2 / real M"
          unfolding divide_inverse by auto
        finally show "norm (g n x - g m x) \<le> 2 / real M"
          using norm_triangle_le[of "g n x - f x" "f x - g m x" "2 / real M"]
          by (auto simp add: algebra_simps simp add: norm_minus_commute)
      qed
    qed
  qed
  from this[unfolded convergent_eq_cauchy[symmetric]] guess s .. note s=this

  show ?thesis
    unfolding integrable_on_def
    apply (rule_tac x=s in exI)
    unfolding has_integral
  proof (rule, rule)
    case goal1
    then have *: "e/3 > 0" by auto
    from LIMSEQ_D [OF s this] guess N1 .. note N1=this
    from goal1 as have "e / 3 / content (cbox a b) > 0"
      by (auto simp add: field_simps)
    from real_arch_invD[OF this] guess N2 by (elim exE conjE) note N2=this
    from i[of "N1 + N2",unfolded has_integral,rule_format,OF *] guess g' .. note g'=conjunctD2[OF this,rule_format]
    have lem: "\<And>sf sg i. norm (sf - sg) \<le> e / 3 \<Longrightarrow>
      norm(i - s) < e / 3 \<Longrightarrow> norm (sg - i) < e / 3 \<Longrightarrow> norm (sf - s) < e"
    proof -
      case goal1
      have "norm (sf - s) \<le> norm (sf - sg) + norm (sg - i) + norm (i - s)"
        using norm_triangle_ineq[of "sf - sg" "sg - s"]
        using norm_triangle_ineq[of "sg -  i" " i - s"]
        by (auto simp add: algebra_simps)
      also have "\<dots> < e"
        using goal1
        unfolding norm_minus_commute
        by (auto simp add: algebra_simps)
      finally show ?case .
    qed
    show ?case
      apply (rule_tac x=g' in exI)
      apply rule
      apply (rule g')
    proof (rule, rule)
      fix p
      assume p: "p tagged_division_of (cbox a b) \<and> g' fine p"
      note * = g'(2)[OF this]
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - s) < e"
        apply -
        apply (rule lem[OF _ _ *])
        apply (rule order_trans)
        apply (rule rsum_diff_bound[OF p[THEN conjunct1]])
        apply rule
        apply (rule g)
        apply assumption
      proof -
        have "content (cbox a b) < e / 3 * (real N2)"
          using N2 unfolding inverse_eq_divide using as by (auto simp add: field_simps)
        then have "content (cbox a b) < e / 3 * (real (N1 + N2) + 1)"
          apply -
          apply (rule less_le_trans,assumption)
          using `e>0`
          apply auto
          done
        then show "inverse (real (N1 + N2) + 1) * content (cbox a b) \<le> e / 3"
          unfolding inverse_eq_divide
          by (auto simp add: field_simps)
        show "norm (i (N1 + N2) - s) < e / 3"
          by (rule N1[rule_format]) auto
      qed
    qed
  qed
qed


subsection {* Negligible sets. *}

definition "negligible (s:: 'a::euclidean_space set) \<longleftrightarrow>
  (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) (cbox a b))"


subsection {* Negligibility of hyperplane. *}

lemma vsum_nonzero_image_lemma:
  assumes "finite s"
    and "g a = 0"
    and "\<forall>x\<in>s. \<forall>y\<in>s. f x = f y \<and> x \<noteq> y \<longrightarrow> g (f x) = 0"
  shows "setsum g {f x |x. x \<in> s \<and> f x \<noteq> a} = setsum (g o f) s"
  unfolding setsum_iterate[OF assms(1)]
  apply (subst setsum_iterate)
  defer
  apply (rule iterate_nonzero_image_lemma)
  apply (rule assms monoidal_monoid)+
  unfolding assms
  unfolding neutral_add
  using assms
  apply auto
  done

lemma interval_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "cbox a b \<inter> {x . abs(x\<bullet>k - c) \<le> (e::real)} =
    cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) (c - e) else a\<bullet>i) *\<^sub>R i)
     (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) (c + e) else b\<bullet>i) *\<^sub>R i)"
proof -
  have *: "\<And>x c e::real. abs(x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e"
    by auto
  have **: "\<And>s P Q. s \<inter> {x. P x \<and> Q x} = (s \<inter> {x. Q x}) \<inter> {x. P x}"
    by blast
  show ?thesis
    unfolding * ** interval_split[OF assms] by (rule refl)
qed

lemma division_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "p division_of (cbox a b)"
    and k: "k \<in> Basis"
  shows "{l \<inter> {x. abs(x\<bullet>k - c) \<le> e} |l. l \<in> p \<and> l \<inter> {x. abs(x\<bullet>k - c) \<le> e} \<noteq> {}} division_of (cbox a b \<inter> {x. abs(x\<bullet>k - c) \<le> e})"
proof -
  have *: "\<And>x c. abs (x - c) \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e"
    by auto
  have **: "\<And>p q p' q'. p division_of q \<Longrightarrow> p = p' \<Longrightarrow> q = q' \<Longrightarrow> p' division_of q'"
    by auto
  note division_split(1)[OF assms, where c="c+e",unfolded interval_split[OF k]]
  note division_split(2)[OF this, where c="c-e" and k=k,OF k]
  then show ?thesis
    apply (rule **)
    using k
    apply -
    unfolding interval_doublesplit
    unfolding *
    unfolding interval_split interval_doublesplit
    apply (rule set_eqI)
    unfolding mem_Collect_eq
    apply rule
    apply (erule conjE exE)+
    apply (rule_tac x=la in exI)
    defer
    apply (erule conjE exE)+
    apply (rule_tac x="l \<inter> {x. c + e \<ge> x \<bullet> k}" in exI)
    apply rule
    defer
    apply rule
    apply (rule_tac x=l in exI)
    apply blast+
    done
qed

lemma content_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "0 < e"
    and k: "k \<in> Basis"
  obtains d where "0 < d" and "content (cbox a b \<inter> {x. abs(x\<bullet>k - c) \<le> d}) < e"
proof (cases "content (cbox a b) = 0")
  case True
  show ?thesis
    apply (rule that[of 1])
    defer
    unfolding interval_doublesplit[OF k]
    apply (rule le_less_trans[OF content_subset])
    defer
    apply (subst True)
    unfolding interval_doublesplit[symmetric,OF k]
    using assms
    apply auto
    done
next
  case False
  def d \<equiv> "e / 3 / setprod (\<lambda>i. b\<bullet>i - a\<bullet>i) (Basis - {k})"
  note False[unfolded content_eq_0 not_ex not_le, rule_format]
  then have "\<And>x. x \<in> Basis \<Longrightarrow> b\<bullet>x > a\<bullet>x"
    by (auto simp add:not_le)
  then have prod0: "0 < setprod (\<lambda>i. b\<bullet>i - a\<bullet>i) (Basis - {k})"
    apply -
    apply (rule setprod_pos)
    apply (auto simp add: field_simps)
    done
  then have "d > 0"
    unfolding d_def
    using assms
    by (auto simp add:field_simps)
  then show ?thesis
  proof (rule that[of d])
    have *: "Basis = insert k (Basis - {k})"
      using k by auto
    have **: "cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {} \<Longrightarrow>
      (\<Prod>i\<in>Basis - {k}. interval_upperbound (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<bullet> i -
        interval_lowerbound (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<bullet> i) =
      (\<Prod>i\<in>Basis - {k}. b\<bullet>i - a\<bullet>i)"
      apply (rule setprod_cong)
      apply (rule refl)
      unfolding interval_doublesplit[OF k]
      apply (subst interval_bounds)
      defer
      apply (subst interval_bounds)
      unfolding box_eq_empty not_ex not_less
      apply auto
      done
    show "content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) < e"
      apply cases
      unfolding content_def
      apply (subst if_P)
      apply assumption
      apply (rule assms)
      unfolding if_not_P
      apply (subst *)
      apply (subst setprod_insert)
      unfolding **
      unfolding interval_doublesplit[OF k] box_eq_empty not_ex not_less
      prefer 3
      apply (subst interval_bounds)
      defer
      apply (subst interval_bounds)
      apply (simp_all only: k inner_setsum_left_Basis simp_thms if_P cong: bex_cong ball_cong)
    proof -
      have "(min (b \<bullet> k) (c + d) - max (a \<bullet> k) (c - d)) \<le> 2 * d"
        by auto
      also have "\<dots> < e / (\<Prod>i\<in>Basis - {k}. b \<bullet> i - a \<bullet> i)"
        unfolding d_def
        using assms prod0
        by (auto simp add: field_simps)
      finally show "(min (b \<bullet> k) (c + d) - max (a \<bullet> k) (c - d)) * (\<Prod>i\<in>Basis - {k}. b \<bullet> i - a \<bullet> i) < e"
        unfolding pos_less_divide_eq[OF prod0] .
    qed auto
  qed
qed

lemma negligible_standard_hyperplane[intro]:
  fixes k :: "'a::euclidean_space"
  assumes k: "k \<in> Basis"
  shows "negligible {x. x\<bullet>k = c}"
  unfolding negligible_def has_integral
  apply (rule, rule, rule, rule)
proof -
  case goal1
  from content_doublesplit[OF this k,of a b c] guess d . note d=this
  let ?i = "indicator {x::'a. x\<bullet>k = c} :: 'a\<Rightarrow>real"
  show ?case
    apply (rule_tac x="\<lambda>x. ball x d" in exI)
    apply rule
    apply (rule gauge_ball)
    apply (rule d)
  proof (rule, rule)
    fix p
    assume p: "p tagged_division_of (cbox a b) \<and> (\<lambda>x. ball x d) fine p"
    have *: "(\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) =
      (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. abs(x\<bullet>k - c) \<le> d}) *\<^sub>R ?i x)"
      apply (rule setsum_cong2)
      unfolding split_paired_all real_scaleR_def mult_cancel_right split_conv
      apply cases
      apply (rule disjI1)
      apply assumption
      apply (rule disjI2)
    proof -
      fix x l
      assume as: "(x, l) \<in> p" "?i x \<noteq> 0"
      then have xk: "x\<bullet>k = c"
        unfolding indicator_def
        apply -
        apply (rule ccontr)
        apply auto
        done
      show "content l = content (l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})"
        apply (rule arg_cong[where f=content])
        apply (rule set_eqI)
        apply rule
        apply rule
        unfolding mem_Collect_eq
      proof -
        fix y
        assume y: "y \<in> l"
        note p[THEN conjunct2,unfolded fine_def,rule_format,OF as(1),unfolded split_conv]
        note this[unfolded subset_eq mem_ball dist_norm,rule_format,OF y]
        note le_less_trans[OF Basis_le_norm[OF k] this]
        then show "\<bar>y \<bullet> k - c\<bar> \<le> d"
          unfolding inner_simps xk by auto
      qed auto
    qed
    note p'= tagged_division_ofD[OF p[THEN conjunct1]] and p''=division_of_tagged_division[OF p[THEN conjunct1]]
    show "norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) - 0) < e"
      unfolding diff_0_right *
      unfolding real_scaleR_def real_norm_def
      apply (subst abs_of_nonneg)
      apply (rule setsum_nonneg)
      apply rule
      unfolding split_paired_all split_conv
      apply (rule mult_nonneg_nonneg)
      apply (drule p'(4))
      apply (erule exE)+
      apply(rule_tac b=b in back_subst)
      prefer 2
      apply (subst(asm) eq_commute)
      apply assumption
      apply (subst interval_doublesplit[OF k])
      apply (rule content_pos_le)
      apply (rule indicator_pos_le)
    proof -
      have "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) \<le>
        (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}))"
        apply (rule setsum_mono)
        unfolding split_paired_all split_conv
        apply (rule mult_right_le_one_le)
        apply (drule p'(4))
        apply (auto simp add:interval_doublesplit[OF k])
        done
      also have "\<dots> < e"
        apply (subst setsum_over_tagged_division_lemma[OF p[THEN conjunct1]])
      proof -
        case goal1
        have "content (cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<le> content (cbox u v)"
          unfolding interval_doublesplit[OF k]
          apply (rule content_subset)
          unfolding interval_doublesplit[symmetric,OF k]
          apply auto
          done
        then show ?case
          unfolding goal1
          unfolding interval_doublesplit[OF k]
          by (blast intro: antisym)
      next
        have *: "setsum content {l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} |l. l \<in> snd ` p \<and> l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}} \<ge> 0"
          apply (rule setsum_nonneg)
          apply rule
          unfolding mem_Collect_eq image_iff
          apply (erule exE bexE conjE)+
          unfolding split_paired_all
        proof -
          fix x l a b
          assume as: "x = l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}" "(a, b) \<in> p" "l = snd (a, b)"
          guess u v using p'(4)[OF as(2)] by (elim exE) note * = this
          show "content x \<ge> 0"
            unfolding as snd_conv * interval_doublesplit[OF k]
            by (rule content_pos_le)
        qed
        have **: "norm (1::real) \<le> 1"
          by auto
        note division_doublesplit[OF p'' k,unfolded interval_doublesplit[OF k]]
        note dsum_bound[OF this **,unfolded interval_doublesplit[symmetric,OF k]]
        note this[unfolded real_scaleR_def real_norm_def mult_1_right mult_1, of c d]
        note le_less_trans[OF this d(2)]
        from this[unfolded abs_of_nonneg[OF *]]
        show "(\<Sum>ka\<in>snd ` p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) < e"
          apply (subst vsum_nonzero_image_lemma[of "snd ` p" content "{}", unfolded o_def,symmetric])
          apply (rule finite_imageI p' content_empty)+
          unfolding forall_in_division[OF p'']
        proof (rule,rule,rule,rule,rule,rule,rule,erule conjE)
          fix m n u v
          assume as:
            "cbox m n \<in> snd ` p" "cbox u v \<in> snd ` p"
            "cbox m n \<noteq> cbox u v"
            "cbox m n \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} = cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}"
          have "(cbox m n \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<inter> (cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<subseteq> cbox m n \<inter> cbox u v"
            by blast
          note interior_mono[OF this, unfolded division_ofD(5)[OF p'' as(1-3)] interior_inter[of "cbox m n"]]
          then have "interior (cbox m n \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = {}"
            unfolding as Int_absorb by auto
          then show "content (cbox m n \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = 0"
            unfolding interval_doublesplit[OF k] content_eq_0_interior[symmetric] .
        qed
      qed
      finally show "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) < e" .
    qed
  qed
qed


subsection {* A technical lemma about "refinement" of division. *}

lemma tagged_division_finer:
  fixes p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assumes "p tagged_division_of (cbox a b)"
    and "gauge d"
  obtains q where "q tagged_division_of (cbox a b)"
    and "d fine q"
    and "\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q"
proof -
  let ?P = "\<lambda>p. p tagged_partial_division_of (cbox a b) \<longrightarrow> gauge d \<longrightarrow>
    (\<exists>q. q tagged_division_of (\<Union>{k. \<exists>x. (x,k) \<in> p}) \<and> d fine q \<and>
      (\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q))"
  {
    have *: "finite p" "p tagged_partial_division_of (cbox a b)"
      using assms(1)
      unfolding tagged_division_of_def
      by auto
    presume "\<And>p. finite p \<Longrightarrow> ?P p"
    from this[rule_format,OF * assms(2)] guess q .. note q=this
    then show ?thesis
      apply -
      apply (rule that[of q])
      unfolding tagged_division_ofD[OF assms(1)]
      apply auto
      done
  }
  fix p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assume as: "finite p"
  show "?P p"
    apply rule
    apply rule
    using as
  proof (induct p)
    case empty
    show ?case
      apply (rule_tac x="{}" in exI)
      unfolding fine_def
      apply auto
      done
  next
    case (insert xk p)
    guess x k using surj_pair[of xk] by (elim exE) note xk=this
    note tagged_partial_division_subset[OF insert(4) subset_insertI]
    from insert(3)[OF this insert(5)] guess q1 .. note q1 = conjunctD3[OF this]
    have *: "\<Union>{l. \<exists>y. (y,l) \<in> insert xk p} = k \<union> \<Union>{l. \<exists>y. (y,l) \<in> p}"
      unfolding xk by auto
    note p = tagged_partial_division_ofD[OF insert(4)]
    from p(4)[unfolded xk, OF insertI1] guess u v by (elim exE) note uv=this

    have "finite {k. \<exists>x. (x, k) \<in> p}"
      apply (rule finite_subset[of _ "snd ` p"],rule)
      unfolding subset_eq image_iff mem_Collect_eq
      apply (erule exE)
      apply (rule_tac x="(xa,x)" in bexI)
      using p
      apply auto
      done
    then have int: "interior (cbox u v) \<inter> interior (\<Union>{k. \<exists>x. (x, k) \<in> p}) = {}"
      apply (rule inter_interior_unions_intervals)
      apply (rule open_interior)
      apply (rule_tac[!] ballI)
      unfolding mem_Collect_eq
      apply (erule_tac[!] exE)
      apply (drule p(4)[OF insertI2])
      apply assumption
      apply (rule p(5))
      unfolding uv xk
      apply (rule insertI1)
      apply (rule insertI2)
      apply assumption
      using insert(2)
      unfolding uv xk
      apply auto
      done
    show ?case
    proof (cases "cbox u v \<subseteq> d x")
      case True
      then show ?thesis
        apply (rule_tac x="{(x,cbox u v)} \<union> q1" in exI)
        apply rule
        unfolding * uv
        apply (rule tagged_division_union)
        apply (rule tagged_division_of_self)
        apply (rule p[unfolded xk uv] insertI1)+
        apply (rule q1)
        apply (rule int)
        apply rule
        apply (rule fine_union)
        apply (subst fine_def)
        defer
        apply (rule q1)
        unfolding Ball_def split_paired_All split_conv
        apply rule
        apply rule
        apply rule
        apply rule
        apply (erule insertE)
        defer
        apply (rule UnI2)
        apply (drule q1(3)[rule_format])
        unfolding xk uv
        apply auto
        done
    next
      case False
      from fine_division_exists[OF assms(2), of u v] guess q2 . note q2=this
      show ?thesis
        apply (rule_tac x="q2 \<union> q1" in exI)
        apply rule
        unfolding * uv
        apply (rule tagged_division_union q2 q1 int fine_union)+
        unfolding Ball_def split_paired_All split_conv
        apply rule
        apply (rule fine_union)
        apply (rule q1 q2)+
        apply rule
        apply rule
        apply rule
        apply rule
        apply (erule insertE)
        apply (rule UnI2)
        defer
        apply (drule q1(3)[rule_format])
        using False
        unfolding xk uv
        apply auto
        done
    qed
  qed
qed


subsection {* Hence the main theorem about negligible sets. *}

lemma finite_product_dependent:
  assumes "finite s"
    and "\<And>x. x \<in> s \<Longrightarrow> finite (t x)"
  shows "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}"
  using assms
proof induct
  case (insert x s)
  have *: "{(i, j) |i j. i \<in> insert x s \<and> j \<in> t i} =
    (\<lambda>y. (x,y)) ` (t x) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case
    unfolding *
    apply (rule finite_UnI)
    using insert
    apply auto
    done
qed auto

lemma sum_sum_product:
  assumes "finite s"
    and "\<forall>i\<in>s. finite (t i)"
  shows "setsum (\<lambda>i. setsum (x i) (t i)::real) s =
    setsum (\<lambda>(i,j). x i j) {(i,j) | i j. i \<in> s \<and> j \<in> t i}"
  using assms
proof induct
  case (insert a s)
  have *: "{(i, j) |i j. i \<in> insert a s \<and> j \<in> t i} =
    (\<lambda>y. (a,y)) ` (t a) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case
    unfolding *
    apply (subst setsum_Un_disjoint)
    unfolding setsum_insert[OF insert(1-2)]
    prefer 4
    apply (subst insert(3))
    unfolding add_right_cancel
  proof -
    show "setsum (x a) (t a) = (\<Sum>(xa, y)\<in> Pair a ` t a. x xa y)"
      apply (subst setsum_reindex)
      unfolding inj_on_def
      apply auto
      done
    show "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}"
      apply (rule finite_product_dependent)
      using insert
      apply auto
      done
  qed (insert insert, auto)
qed auto

lemma has_integral_negligible:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). f x = 0"
  shows "(f has_integral 0) t"
proof -
  presume P: "\<And>f::'b::euclidean_space \<Rightarrow> 'a.
    \<And>a b. \<forall>x. x \<notin> s \<longrightarrow> f x = 0 \<Longrightarrow> (f has_integral 0) (cbox a b)"
  let ?f = "(\<lambda>x. if x \<in> t then f x else 0)"
  show ?thesis
    apply (rule_tac f="?f" in has_integral_eq)
    apply rule
    unfolding if_P
    apply (rule refl)
    apply (subst has_integral_alt)
    apply cases
    apply (subst if_P, assumption)
    unfolding if_not_P
  proof -
    assume "\<exists>a b. t = cbox a b"
    then guess a b apply - by (erule exE)+ note t = this
    show "(?f has_integral 0) t"
      unfolding t
      apply (rule P)
      using assms(2)
      unfolding t
      apply auto
      done
  next
    show "\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> t then ?f x else 0) has_integral z) (cbox a b) \<and> norm (z - 0) < e)"
      apply safe
      apply (rule_tac x=1 in exI)
      apply rule
      apply (rule zero_less_one)
      apply safe
      apply (rule_tac x=0 in exI)
      apply rule
      apply (rule P)
      using assms(2)
      apply auto
      done
  qed
next
  fix f :: "'b \<Rightarrow> 'a"
  fix a b :: 'b
  assume assm: "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
  show "(f has_integral 0) (cbox a b)"
    unfolding has_integral
  proof safe
    case goal1
    then have "\<And>n. e / 2 / ((real n+1) * (2 ^ n)) > 0"
      apply -
      apply (rule divide_pos_pos)
      defer
      apply (rule mult_pos_pos)
      apply (auto simp add:field_simps)
      done
    note assms(1)[unfolded negligible_def has_integral,rule_format,OF this,of a b]
    note allI[OF this,of "\<lambda>x. x"]
    from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format]]
    show ?case
      apply (rule_tac x="\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x" in exI)
    proof safe
      show "gauge (\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x)"
        using d(1) unfolding gauge_def by auto
      fix p
      assume as: "p tagged_division_of (cbox a b)" "(\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x) fine p"
      let ?goal = "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
      {
        presume "p \<noteq> {} \<Longrightarrow> ?goal"
        then show ?goal
          apply (cases "p = {}")
          using goal1
          apply auto
          done
      }
      assume as': "p \<noteq> {}"
      from real_arch_simple[of "Sup((\<lambda>(x,k). norm(f x)) ` p)"] guess N ..
      then have N: "\<forall>x\<in>(\<lambda>(x, k). norm (f x)) ` p. x \<le> real N"
        apply (subst(asm) cSup_finite_le_iff)
        using as as'
        apply auto
        done
      have "\<forall>i. \<exists>q. q tagged_division_of (cbox a b) \<and> (d i) fine q \<and> (\<forall>(x, k)\<in>p. k \<subseteq> (d i) x \<longrightarrow> (x, k) \<in> q)"
        apply rule
        apply (rule tagged_division_finer[OF as(1) d(1)])
        apply auto
        done
      from choice[OF this] guess q .. note q=conjunctD3[OF this[rule_format]]
      have *: "\<And>i. (\<Sum>(x, k)\<in>q i. content k *\<^sub>R indicator s x) \<ge> (0::real)"
        apply (rule setsum_nonneg)
        apply safe
        unfolding real_scaleR_def
        apply (drule tagged_division_ofD(4)[OF q(1)])
        apply (auto intro: mult_nonneg_nonneg)
        done
      have **: "\<And>f g s t. finite s \<Longrightarrow> finite t \<Longrightarrow> (\<forall>(x,y) \<in> t. (0::real) \<le> g(x,y)) \<Longrightarrow>
        (\<forall>y\<in>s. \<exists>x. (x,y) \<in> t \<and> f(y) \<le> g(x,y)) \<Longrightarrow> setsum f s \<le> setsum g t"
      proof -
        case goal1
        then show ?case
          apply -
          apply (rule setsum_le_included[of s t g snd f])
          prefer 4
          apply safe
          apply (erule_tac x=x in ballE)
          apply (erule exE)
          apply (rule_tac x="(xa,x)" in bexI)
          apply auto  
          done
      qed
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) \<le> setsum (\<lambda>i. (real i + 1) *
        norm (setsum (\<lambda>(x,k). content k *\<^sub>R indicator s x :: real) (q i))) {..N+1}"
        unfolding real_norm_def setsum_right_distrib abs_of_nonneg[OF *] diff_0_right
        apply (rule order_trans)
        apply (rule norm_setsum)
        apply (subst sum_sum_product)
        prefer 3
      proof (rule **, safe)
        show "finite {(i, j) |i j. i \<in> {..N + 1} \<and> j \<in> q i}"
          apply (rule finite_product_dependent)
          using q
          apply auto
          done
        fix i a b
        assume as'': "(a, b) \<in> q i"
        show "0 \<le> (real i + 1) * (content b *\<^sub>R indicator s a)"
          unfolding real_scaleR_def
          using tagged_division_ofD(4)[OF q(1) as'']
          by (auto intro!: mult_nonneg_nonneg)
      next
        fix i :: nat
        show "finite (q i)"
          using q by auto
      next
        fix x k
        assume xk: "(x, k) \<in> p"
        def n \<equiv> "nat \<lfloor>norm (f x)\<rfloor>"
        have *: "norm (f x) \<in> (\<lambda>(x, k). norm (f x)) ` p"
          using xk by auto
        have nfx: "real n \<le> norm (f x)" "norm (f x) \<le> real n + 1"
          unfolding n_def by auto
        then have "n \<in> {0..N + 1}"
          using N[rule_format,OF *] by auto
        moreover
        note as(2)[unfolded fine_def,rule_format,OF xk,unfolded split_conv]
        note q(3)[rule_format,OF xk,unfolded split_conv,rule_format,OF this]
        note this[unfolded n_def[symmetric]]
        moreover
        have "norm (content k *\<^sub>R f x) \<le> (real n + 1) * (content k * indicator s x)"
        proof (cases "x \<in> s")
          case False
          then show ?thesis
            using assm by auto
        next
          case True
          have *: "content k \<ge> 0"
            using tagged_division_ofD(4)[OF as(1) xk] by auto
          moreover
          have "content k * norm (f x) \<le> content k * (real n + 1)"
            apply (rule mult_mono)
            using nfx *
            apply auto
            done
          ultimately
          show ?thesis
            unfolding abs_mult
            using nfx True
            by (auto simp add: field_simps)
        qed
        ultimately show "\<exists>y. (y, x, k) \<in> {(i, j) |i j. i \<in> {..N + 1} \<and> j \<in> q i} \<and> norm (content k *\<^sub>R f x) \<le>
          (real y + 1) * (content k *\<^sub>R indicator s x)"
          apply (rule_tac x=n in exI)
          apply safe
          apply (rule_tac x=n in exI)
          apply (rule_tac x="(x,k)" in exI)
          apply safe
          apply auto
          done
      qed (insert as, auto)
      also have "\<dots> \<le> setsum (\<lambda>i. e / 2 / 2 ^ i) {..N+1}"
        apply (rule setsum_mono)
      proof -
        case goal1
        then show ?case
          apply (subst mult_commute, subst pos_le_divide_eq[symmetric])
          using d(2)[rule_format,of "q i" i]
          using q[rule_format]
          apply (auto simp add: field_simps)
          done
      qed
      also have "\<dots> < e * inverse 2 * 2"
        unfolding divide_inverse setsum_right_distrib[symmetric]
        apply (rule mult_strict_left_mono)
        unfolding power_inverse lessThan_Suc_atMost[symmetric]
        apply (subst geometric_sum)
        using goal1
        apply auto
        done
      finally show "?goal" by auto
    qed
  qed
qed

lemma has_integral_spike:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s"
    and "(\<forall>x\<in>(t - s). g x = f x)"
    and "(f has_integral y) t"
  shows "(g has_integral y) t"
proof -
  {
    fix a b :: 'b
    fix f g :: "'b \<Rightarrow> 'a"
    fix y :: 'a
    assume as: "\<forall>x \<in> cbox a b - s. g x = f x" "(f has_integral y) (cbox a b)"
    have "((\<lambda>x. f x + (g x - f x)) has_integral (y + 0)) (cbox a b)"
      apply (rule has_integral_add[OF as(2)])
      apply (rule has_integral_negligible[OF assms(1)])
      using as
      apply auto
      done
    then have "(g has_integral y) (cbox a b)"
      by auto
  } note * = this
  show ?thesis
    apply (subst has_integral_alt)
    using assms(2-)
    apply -
    apply (rule cond_cases)
    apply safe
    apply (rule *)
    apply assumption+
    apply (subst(asm) has_integral_alt)
    unfolding if_not_P
    apply (erule_tac x=e in allE)
    apply safe
    apply (rule_tac x=B in exI)
    apply safe
    apply (erule_tac x=a in allE)
    apply (erule_tac x=b in allE)
    apply safe
    apply (rule_tac x=z in exI)
    apply safe
    apply (rule *[where fa2="\<lambda>x. if x\<in>t then f x else 0"])
    apply auto
    done
qed

lemma has_integral_spike_eq:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule
  apply (rule_tac[!] has_integral_spike[OF assms(1)])
  using assms(2)
  apply auto
  done

lemma integrable_spike:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
    and "f integrable_on t"
  shows "g integrable_on  t"
  using assms
  unfolding integrable_on_def
  apply -
  apply (erule exE)
  apply rule
  apply (rule has_integral_spike)
  apply fastforce+
  done

lemma integral_spike:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
  shows "integral t f = integral t g"
  unfolding integral_def
  using has_integral_spike_eq[OF assms]
  by auto


subsection {* Some other trivialities about negligible sets. *}

lemma negligible_subset[intro]:
  assumes "negligible s"
    and "t \<subseteq> s"
  shows "negligible t"
  unfolding negligible_def
proof safe
  case goal1
  show ?case
    using assms(1)[unfolded negligible_def,rule_format,of a b]
    apply -
    apply (rule has_integral_spike[OF assms(1)])
    defer
    apply assumption
    using assms(2)
    unfolding indicator_def
    apply auto
    done
qed

lemma negligible_diff[intro?]:
  assumes "negligible s"
  shows "negligible (s - t)"
  using assms by auto

lemma negligible_inter:
  assumes "negligible s \<or> negligible t"
  shows "negligible (s \<inter> t)"
  using assms by auto

lemma negligible_union:
  assumes "negligible s"
    and "negligible t"
  shows "negligible (s \<union> t)"
  unfolding negligible_def
proof safe
  case goal1
  note assm = assms[unfolded negligible_def,rule_format,of a b]
  then show ?case
    apply (subst has_integral_spike_eq[OF assms(2)])
    defer
    apply assumption
    unfolding indicator_def
    apply auto
    done
qed

lemma negligible_union_eq[simp]: "negligible (s \<union> t) \<longleftrightarrow> negligible s \<and> negligible t"
  using negligible_union by auto

lemma negligible_sing[intro]: "negligible {a::'a::euclidean_space}"
  using negligible_standard_hyperplane[OF SOME_Basis, of "a \<bullet> (SOME i. i \<in> Basis)"] by auto

lemma negligible_insert[simp]: "negligible (insert a s) \<longleftrightarrow> negligible s"
  apply (subst insert_is_Un)
  unfolding negligible_union_eq
  apply auto
  done

lemma negligible_empty[intro]: "negligible {}"
  by auto

lemma negligible_finite[intro]:
  assumes "finite s"
  shows "negligible s"
  using assms by (induct s) auto

lemma negligible_unions[intro]:
  assumes "finite s"
    and "\<forall>t\<in>s. negligible t"
  shows "negligible(\<Union>s)"
  using assms by induct auto

lemma negligible:
  "negligible s \<longleftrightarrow> (\<forall>t::('a::euclidean_space) set. ((indicator s::'a\<Rightarrow>real) has_integral 0) t)"
  apply safe
  defer
  apply (subst negligible_def)
proof -
  fix t :: "'a set"
  assume as: "negligible s"
  have *: "(\<lambda>x. if x \<in> s \<inter> t then 1 else 0) = (\<lambda>x. if x\<in>t then if x\<in>s then 1 else 0 else 0)"
    by auto
  show "((indicator s::'a\<Rightarrow>real) has_integral 0) t"
    apply (subst has_integral_alt)
    apply cases
    apply (subst if_P,assumption)
    unfolding if_not_P
    apply safe
    apply (rule as[unfolded negligible_def,rule_format])
    apply (rule_tac x=1 in exI)
    apply safe
    apply (rule zero_less_one)
    apply (rule_tac x=0 in exI)
    using negligible_subset[OF as,of "s \<inter> t"]
    unfolding negligible_def indicator_def [abs_def]
    unfolding *
    apply auto
    done
qed auto


subsection {* Finite case of the spike theorem is quite commonly needed. *}

lemma has_integral_spike_finite:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
    and "(f has_integral y) t"
  shows "(g has_integral y) t"
  apply (rule has_integral_spike)
  using assms
  apply auto
  done

lemma has_integral_spike_finite_eq:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule
  apply (rule_tac[!] has_integral_spike_finite)
  using assms
  apply auto
  done

lemma integrable_spike_finite:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
    and "f integrable_on t"
  shows "g integrable_on  t"
  using assms
  unfolding integrable_on_def
  apply safe
  apply (rule_tac x=y in exI)
  apply (rule has_integral_spike_finite)
  apply auto
  done


subsection {* In particular, the boundary of an interval is negligible. *}

lemma negligible_frontier_interval: "negligible(cbox (a::'a::euclidean_space) b - box a b)"
proof -
  let ?A = "\<Union>((\<lambda>k. {x. x\<bullet>k = a\<bullet>k} \<union> {x::'a. x\<bullet>k = b\<bullet>k}) ` Basis)"
  have "cbox a b - box a b \<subseteq> ?A"
    apply rule unfolding Diff_iff mem_box
    apply simp
    apply(erule conjE bexE)+
    apply(rule_tac x=i in bexI)
    apply auto
    done
  then show ?thesis
    apply -
    apply (rule negligible_subset[of ?A])
    apply (rule negligible_unions[OF finite_imageI])
    apply auto
    done
qed

lemma has_integral_spike_interior:
  assumes "\<forall>x\<in>box a b. g x = f x"
    and "(f has_integral y) (cbox a b)"
  shows "(g has_integral y) (cbox a b)"
  apply (rule has_integral_spike[OF negligible_frontier_interval _ assms(2)])
  using assms(1)
  apply auto
  done

lemma has_integral_spike_interior_eq:
  assumes "\<forall>x\<in>box a b. g x = f x"
  shows "(f has_integral y) (cbox a b) \<longleftrightarrow> (g has_integral y) (cbox a b)"
  apply rule
  apply (rule_tac[!] has_integral_spike_interior)
  using assms
  apply auto
  done

lemma integrable_spike_interior:
  assumes "\<forall>x\<in>box a b. g x = f x"
    and "f integrable_on cbox a b"
  shows "g integrable_on cbox a b"
  using assms
  unfolding integrable_on_def
  using has_integral_spike_interior[OF assms(1)]
  by auto


subsection {* Integrability of continuous functions. *}

lemma neutral_and[simp]: "neutral op \<and> = True"
  unfolding neutral_def by (rule some_equality) auto

lemma monoidal_and[intro]: "monoidal op \<and>"
  unfolding monoidal_def by auto

lemma iterate_and[simp]:
  assumes "finite s"
  shows "(iterate op \<and>) s p \<longleftrightarrow> (\<forall>x\<in>s. p x)"
  using assms
  apply induct
  unfolding iterate_insert[OF monoidal_and]
  apply auto
  done

lemma operative_division_and:
  assumes "operative op \<and> P"
    and "d division_of (cbox a b)"
  shows "(\<forall>i\<in>d. P i) \<longleftrightarrow> P (cbox a b)"
  using operative_division[OF monoidal_and assms] division_of_finite[OF assms(2)]
  by auto

lemma operative_approximable:
  fixes f::"'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative op \<and> (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)"
  unfolding operative_def neutral_and
proof safe
  fix a b :: 'b
  {
    assume "content (cbox a b) = 0"
    then show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
      apply (rule_tac x=f in exI)
      using assms
      apply (auto intro!:integrable_on_null)
      done
  }
  {
    fix c g
    fix k :: 'b
    assume as: "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
    assume k: "k \<in> Basis"
    show "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
      "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}"
      apply (rule_tac[!] x=g in exI)
      using as(1) integrable_split[OF as(2) k]
      apply auto
      done
  }
  fix c k g1 g2
  assume as: "\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g1 x) \<le> e" "g1 integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
    "\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g2 x) \<le> e" "g2 integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}"
  assume k: "k \<in> Basis"
  let ?g = "\<lambda>x. if x\<bullet>k = c then f x else if x\<bullet>k \<le> c then g1 x else g2 x"
  show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    apply (rule_tac x="?g" in exI)
  proof safe
    case goal1
    then show ?case
      apply -
      apply (cases "x\<bullet>k=c")
      apply (case_tac "x\<bullet>k < c")
      using as assms
      apply auto
      done
  next
    case goal2
    presume "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
      and "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
    then guess h1 h2 unfolding integrable_on_def by auto
    from has_integral_split[OF this k] show ?case
      unfolding integrable_on_def by auto
  next
    show "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}" "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
      apply(rule_tac[!] integrable_spike[OF negligible_standard_hyperplane[of k c]])
      using k as(2,4)
      apply auto
      done
  qed
qed

lemma approximable_on_division:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
    and "d division_of (cbox a b)"
    and "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
proof -
  note * = operative_division[OF monoidal_and operative_approximable[OF assms(1)] assms(2)]
  note this[unfolded iterate_and[OF division_of_finite[OF assms(2)]]]
  from assms(3)[unfolded this[of f]] guess g ..
  then show thesis
    apply -
    apply (rule that[of g])
    apply auto
    done
qed

lemma integrable_continuous:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
proof (rule integrable_uniform_limit, safe)
  fix e :: real
  assume e: "e > 0"
  from compact_uniformly_continuous[OF assms compact_cbox,unfolded uniformly_continuous_on_def,rule_format,OF e] guess d ..
  note d=conjunctD2[OF this,rule_format]
  from fine_division_exists[OF gauge_ball[OF d(1)], of a b] guess p . note p=this
  note p' = tagged_division_ofD[OF p(1)]
  have *: "\<forall>i\<in>snd ` p. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  proof (safe, unfold snd_conv)
    fix x l
    assume as: "(x, l) \<in> p"
    from p'(4)[OF this] guess a b by (elim exE) note l=this
    show "\<exists>g. (\<forall>x\<in>l. norm (f x - g x) \<le> e) \<and> g integrable_on l"
      apply (rule_tac x="\<lambda>y. f x" in exI)
    proof safe
      show "(\<lambda>y. f x) integrable_on l"
        unfolding integrable_on_def l
        apply rule
        apply (rule has_integral_const)
        done
      fix y
      assume y: "y \<in> l"
      note fineD[OF p(2) as,unfolded subset_eq,rule_format,OF this]
      note d(2)[OF _ _ this[unfolded mem_ball]]
      then show "norm (f y - f x) \<le> e"
        using y p'(2-3)[OF as] unfolding dist_norm l norm_minus_commute by fastforce
    qed
  qed
  from e have "e \<ge> 0"
    by auto
  from approximable_on_division[OF this division_of_tagged_division[OF p(1)] *] guess g .
  then show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    by auto
qed

lemma integrable_continuous_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
  shows "f integrable_on {a .. b}"
  by (metis assms box_real(2) integrable_continuous)


subsection {* Specialization of additivity to one dimension. *}

lemma
  shows real_inner_1_left: "inner 1 x = x"
  and real_inner_1_right: "inner x 1 = x"
  by simp_all

lemma content_real_eq_0: "content {a .. b::real} = 0 \<longleftrightarrow> a \<ge> b"
  by (metis atLeastatMost_empty_iff2 content_empty content_real diff_self eq_iff le_cases le_iff_diff_le_0)

lemma interval_real_split:
  "{a .. b::real} \<inter> {x. x \<le> c} = {a .. min b c}"
  "{a .. b} \<inter> {x. c \<le> x} = {max a c .. b}"
  apply (metis Int_atLeastAtMostL1 atMost_def)
  apply (metis Int_atLeastAtMostL2 atLeast_def)
  done

lemma operative_1_lt:
  assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a .. b::real} = neutral opp) \<and>
    (\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a .. c}) (f {c .. b}) = f {a .. b}))"
  apply (simp add: operative_def content_real_eq_0)
proof safe
  fix a b c :: real
  assume as:
    "\<forall>a b c. f {a..b} = opp (f ({a..b} \<inter> {x. x \<le> c})) (f ({a..b} \<inter> Collect (op \<le> c)))"
    "a < c"
    "c < b"
    from this(2-) have "cbox a b \<inter> {x. x \<le> c} = cbox a c" "cbox a b \<inter> {x. x \<ge> c} = cbox c b"
      by (auto simp: mem_box)
    then show "opp (f {a..c}) (f {c..b}) = f {a..b}"
      unfolding as(1)[rule_format,of a b "c"] by auto
next
  fix a b c :: real
  assume as: "\<forall>a b. b \<le> a \<longrightarrow> f {a..b} = neutral opp"
    "\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}"
  show " f {a..b} = opp (f ({a..b} \<inter> {x. x \<le> c})) (f ({a..b} \<inter> Collect (op \<le> c)))"
  proof (cases "c \<in> {a..b}")
    case False
    then have "c < a \<or> c > b" by auto
    then show ?thesis
    proof
      assume "c < a"
      then have *: "{a..b} \<inter> {x. x \<le> c} = {1..0}" "{a..b} \<inter> {x. c \<le> x} = {a..b}"
        by auto
      show ?thesis
        unfolding *
        apply (subst as(1)[rule_format,of 0 1])
        using assms
        apply auto
        done
    next
      assume "b < c"
      then have *: "{a..b} \<inter> {x. x \<le> c} = {a..b}" "{a..b} \<inter> {x. c \<le> x} = {1 .. 0}"
        by auto
      show ?thesis
        unfolding *
        apply (subst as(1)[rule_format,of 0 1])
        using assms
        apply auto
        done
    qed
  next
    case True
    then have *: "min (b) c = c" "max a c = c"
      by auto
    have **: "(1::real) \<in> Basis"
      by simp
    have ***: "\<And>P Q. (\<Sum>i\<in>Basis. (if i = 1 then P i else Q i) *\<^sub>R i) = (P 1::real)"
      by simp
    show ?thesis
      unfolding interval_real_split unfolding *
    proof (cases "c = a \<or> c = b")
      case False
      then show "f {a..b} = opp (f {a..c}) (f {c..b})"
        apply -
        apply (subst as(2)[rule_format])
        using True
        apply auto
        done
    next
      case True
      then show "f {a..b} = opp (f {a..c}) (f {c..b})"
      proof
        assume *: "c = a"
        then have "f {a .. c} = neutral opp"
          apply -
          apply (rule as(1)[rule_format])
          apply auto
          done
        then show ?thesis
          using assms unfolding * by auto
      next
        assume *: "c = b"
        then have "f {c .. b} = neutral opp"
          apply -
          apply (rule as(1)[rule_format])
          apply auto
          done
        then show ?thesis
          using assms unfolding * by auto
      qed
    qed
  qed
qed

lemma operative_1_le:
  assumes "monoidal opp"
  shows "operative opp f \<longleftrightarrow> ((\<forall>a b. b \<le> a \<longrightarrow> f {a .. b::real} = neutral opp) \<and>
    (\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f {a .. c}) (f {c .. b}) = f {a .. b}))"
  unfolding operative_1_lt[OF assms]
proof safe
  fix a b c :: real
  assume as:
    "\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}"
    "a < c"
    "c < b"
  show "opp (f {a..c}) (f {c..b}) = f {a..b}"
    apply (rule as(1)[rule_format])
    using as(2-)
    apply auto
    done
next
  fix a b c :: real
  assume "\<forall>a b. b \<le> a \<longrightarrow> f {a .. b} = neutral opp"
    and "\<forall>a b c. a < c \<and> c < b \<longrightarrow> opp (f {a..c}) (f {c..b}) = f {a..b}"
    and "a \<le> c"
    and "c \<le> b"
  note as = this[rule_format]
  show "opp (f {a..c}) (f {c..b}) = f {a..b}"
  proof (cases "c = a \<or> c = b")
    case False
    then show ?thesis
      apply -
      apply (subst as(2))
      using as(3-)
      apply auto
      done
  next
    case True
    then show ?thesis
    proof
      assume *: "c = a"
      then have "f {a .. c} = neutral opp"
        apply -
        apply (rule as(1)[rule_format])
        apply auto
        done
      then show ?thesis
        using assms unfolding * by auto
    next
      assume *: "c = b"
      then have "f {c .. b} = neutral opp"
        apply -
        apply (rule as(1)[rule_format])
        apply auto
        done
      then show ?thesis
        using assms unfolding * by auto
    qed
  qed
qed


subsection {* Special case of additivity we need for the FCT. *}

lemma additive_tagged_division_1:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f(Sup k) - f(Inf k)) p = f b - f a"
proof -
  let ?f = "(\<lambda>k::(real) set. if k = {} then 0 else f(interval_upperbound k) - f(interval_lowerbound k))"
  have ***: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
    using assms by auto
  have *: "operative op + ?f"
    unfolding operative_1_lt[OF monoidal_monoid] box_eq_empty
    by auto
  have **: "cbox a b \<noteq> {}"
    using assms(1) by auto
  note operative_tagged_division[OF monoidal_monoid * assms(2)[simplified box_real[symmetric]]]
  note * = this[unfolded if_not_P[OF **] interval_bounds[OF ***],symmetric]
  show ?thesis
    unfolding *
    apply (subst setsum_iterate[symmetric])
    defer
    apply (rule setsum_cong2)
    unfolding split_paired_all split_conv
    using assms(2)
    apply auto
    done
qed


subsection {* A useful lemma allowing us to factor out the content size. *}

lemma has_integral_factor_content:
  "(f has_integral i) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content (cbox a b)))"
proof (cases "content (cbox a b) = 0")
  case True
  show ?thesis
    unfolding has_integral_null_eq[OF True]
    apply safe
    apply (rule, rule, rule gauge_trivial, safe)
    unfolding setsum_content_null[OF True] True
    defer
    apply (erule_tac x=1 in allE)
    apply safe
    defer
    apply (rule fine_division_exists[of _ a b])
    apply assumption
    apply (erule_tac x=p in allE)
    unfolding setsum_content_null[OF True]
    apply auto
    done
next
  case False
  note F = this[unfolded content_lt_nz[symmetric]]
  let ?P = "\<lambda>e opp. \<exists>d. gauge d \<and>
    (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow> opp (norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i)) e)"
  show ?thesis
    apply (subst has_integral)
  proof safe
    fix e :: real
    assume e: "e > 0"
    {
      assume "\<forall>e>0. ?P e op <"
      then show "?P (e * content (cbox a b)) op \<le>"
        apply (erule_tac x="e * content (cbox a b)" in allE)
        apply (erule impE)
        defer
        apply (erule exE,rule_tac x=d in exI)
        using F e
        apply (auto simp add:field_simps)
        done
    }
    {
      assume "\<forall>e>0. ?P (e * content (cbox a b)) op \<le>"
      then show "?P e op <"
        apply (erule_tac x="e / 2 / content (cbox a b)" in allE)
        apply (erule impE)
        defer
        apply (erule exE,rule_tac x=d in exI)
        using F e
        apply (auto simp add: field_simps)
        done
    }
  qed
qed

lemma has_integral_factor_content_real:
  "(f has_integral i) {a .. b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a .. b}  \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a .. b} ))"
  unfolding box_real[symmetric]
  by (rule has_integral_factor_content)


subsection {* Fundamental theorem of calculus. *}

lemma interval_bounds_real:
  fixes q b :: real
  assumes "a \<le> b"
  shows "Sup {a..b} = b"
    and "Inf {a..b} = a"
  using assms by auto

lemma fundamental_theorem_of_calculus:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
    and "\<forall>x\<in>{a .. b}. (f has_vector_derivative f' x) (at x within {a .. b})"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  unfolding has_integral_factor_content box_real[symmetric]
proof safe
  fix e :: real
  assume e: "e > 0"
  note assm = assms(2)[unfolded has_vector_derivative_def has_derivative_within_alt]
  have *: "\<And>P Q. \<forall>x\<in>{a .. b}. P x \<and> (\<forall>e>0. \<exists>d>0. Q x e d) \<Longrightarrow> \<forall>x. \<exists>(d::real)>0. x\<in>{a .. b} \<longrightarrow> Q x e d"
    using e by blast
  note this[OF assm,unfolded gauge_existence_lemma]
  from choice[OF this,unfolded Ball_def[symmetric]] guess d ..
  note d=conjunctD2[OF this[rule_format],rule_format]
  show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b))"
    apply (rule_tac x="\<lambda>x. ball x (d x)" in exI)
    apply safe
    apply (rule gauge_ball_dependent)
    apply rule
    apply (rule d(1))
  proof -
    fix p
    assume as: "p tagged_division_of cbox a b" "(\<lambda>x. ball x (d x)) fine p"
    show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b)"
      unfolding content_real[OF assms(1), simplified box_real[symmetric]] additive_tagged_division_1[OF assms(1) as(1)[simplified box_real],of f,symmetric]
      unfolding additive_tagged_division_1[OF assms(1) as(1)[simplified box_real],of "\<lambda>x. x",symmetric]
      unfolding setsum_right_distrib
      defer
      unfolding setsum_subtractf[symmetric]
    proof (rule setsum_norm_le,safe)
      fix x k
      assume "(x, k) \<in> p"
      note xk = tagged_division_ofD(2-4)[OF as(1) this]
      from this(3) guess u v by (elim exE) note k=this
      have *: "u \<le> v"
        using xk unfolding k by auto
      have ball: "\<forall>xa\<in>k. xa \<in> ball x (d x)"
        using as(2)[unfolded fine_def,rule_format,OF `(x,k)\<in>p`,unfolded split_conv subset_eq] .
      have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) \<le>
        norm (f u - f x - (u - x) *\<^sub>R f' x) + norm (f v - f x - (v - x) *\<^sub>R f' x)"
        apply (rule order_trans[OF _ norm_triangle_ineq4])
        apply (rule eq_refl)
        apply (rule arg_cong[where f=norm])
        unfolding scaleR_diff_left
        apply (auto simp add:algebra_simps)
        done
      also have "\<dots> \<le> e * norm (u - x) + e * norm (v - x)"
        apply (rule add_mono)
        apply (rule d(2)[of "x" "u",unfolded o_def])
        prefer 4
        apply (rule d(2)[of "x" "v",unfolded o_def])
        using ball[rule_format,of u] ball[rule_format,of v]
        using xk(1-2)
        unfolding k subset_eq
        apply (auto simp add:dist_real_def)
        done
      also have "\<dots> \<le> e * (Sup k - Inf k)"
        unfolding k interval_bounds_real[OF *]
        using xk(1)
        unfolding k
        by (auto simp add: dist_real_def field_simps)
      finally show "norm (content k *\<^sub>R f' x - (f (Sup k) - f (Inf k))) \<le>
        e * (Sup k - Inf k)"
        unfolding box_real k interval_bounds_real[OF *] content_real[OF *]
          interval_upperbound_real interval_lowerbound_real
          .
    qed
  qed
qed


subsection {* Attempt a systematic general set of "offset" results for components. *}

lemma gauge_modify:
  assumes "(\<forall>s. open s \<longrightarrow> open {x. f(x) \<in> s})" "gauge d"
  shows "gauge (\<lambda>x. {y. f y \<in> d (f x)})"
  using assms
  unfolding gauge_def
  apply safe
  defer
  apply (erule_tac x="f x" in allE)
  apply (erule_tac x="d (f x)" in allE)
  apply auto
  done


subsection {* Only need trivial subintervals if the interval itself is trivial. *}

lemma division_of_nontrivial:
  fixes s :: "'a::euclidean_space set set"
  assumes "s division_of (cbox a b)"
    and "content (cbox a b) \<noteq> 0"
  shows "{k. k \<in> s \<and> content k \<noteq> 0} division_of (cbox a b)"
  using assms(1)
  apply -
proof (induct "card s" arbitrary: s rule: nat_less_induct)
  fix s::"'a set set"
  assume assm: "s division_of (cbox a b)"
    "\<forall>m<card s. \<forall>x. m = card x \<longrightarrow>
      x division_of (cbox a b) \<longrightarrow> {k \<in> x. content k \<noteq> 0} division_of (cbox a b)"
  note s = division_ofD[OF assm(1)]
  let ?thesis = "{k \<in> s. content k \<noteq> 0} division_of (cbox a b)"
  {
    presume *: "{k \<in> s. content k \<noteq> 0} \<noteq> s \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      defer
      apply (rule *)
      apply assumption
      using assm(1)
      apply auto
      done
  }
  assume noteq: "{k \<in> s. content k \<noteq> 0} \<noteq> s"
  then obtain k where k: "k \<in> s" "content k = 0"
    by auto
  from s(4)[OF k(1)] guess c d by (elim exE) note k=k this
  from k have "card s > 0"
    unfolding card_gt_0_iff using assm(1) by auto
  then have card: "card (s - {k}) < card s"
    using assm(1) k(1)
    apply (subst card_Diff_singleton_if)
    apply auto
    done
  have *: "closed (\<Union>(s - {k}))"
    apply (rule closed_Union)
    defer
    apply rule
    apply (drule DiffD1,drule s(4))
    using assm(1)
    apply auto
    done
  have "k \<subseteq> \<Union>(s - {k})"
    apply safe
    apply (rule *[unfolded closed_limpt,rule_format])
    unfolding islimpt_approachable
  proof safe
    fix x
    fix e :: real
    assume as: "x \<in> k" "e > 0"
    from k(2)[unfolded k content_eq_0] guess i ..
    then have i:"c\<bullet>i = d\<bullet>i" "i\<in>Basis"
      using s(3)[OF k(1),unfolded k] unfolding box_ne_empty by auto
    then have xi: "x\<bullet>i = d\<bullet>i"
      using as unfolding k mem_box by (metis antisym)
    def y \<equiv> "\<Sum>j\<in>Basis. (if j = i then if c\<bullet>i \<le> (a\<bullet>i + b\<bullet>i) / 2 then c\<bullet>i +
      min e (b\<bullet>i - c\<bullet>i) / 2 else c\<bullet>i - min e (c\<bullet>i - a\<bullet>i) / 2 else x\<bullet>j) *\<^sub>R j"
    show "\<exists>x'\<in>\<Union>(s - {k}). x' \<noteq> x \<and> dist x' x < e"
      apply (rule_tac x=y in bexI)
    proof
      have "d \<in> cbox c d"
        using s(3)[OF k(1)]
        unfolding k box_eq_empty mem_box
        by (fastforce simp add: not_less)
      then have "d \<in> cbox a b"
        using s(2)[OF k(1)]
        unfolding k
        by auto
      note di = this[unfolded mem_box,THEN bspec[where x=i]]
      then have xyi: "y\<bullet>i \<noteq> x\<bullet>i"
        unfolding y_def i xi
        using as(2) assms(2)[unfolded content_eq_0] i(2)
        by (auto elim!: ballE[of _ _ i])
      then show "y \<noteq> x"
        unfolding euclidean_eq_iff[where 'a='a] using i by auto
      have *: "Basis = insert i (Basis - {i})"
        using i by auto
      have "norm (y - x) < e + setsum (\<lambda>i. 0) Basis"
        apply (rule le_less_trans[OF norm_le_l1])
        apply (subst *)
        apply (subst setsum_insert)
        prefer 3
        apply (rule add_less_le_mono)
      proof -
        show "\<bar>(y - x) \<bullet> i\<bar> < e"
          using di as(2) y_def i xi by (auto simp: inner_simps)
        show "(\<Sum>i\<in>Basis - {i}. \<bar>(y - x) \<bullet> i\<bar>) \<le> (\<Sum>i\<in>Basis. 0)"
          unfolding y_def by (auto simp: inner_simps)
      qed auto
      then show "dist y x < e"
        unfolding dist_norm by auto
      have "y \<notin> k"
        unfolding k mem_box
        apply rule
        apply (erule_tac x=i in ballE)
        using xyi k i xi
        apply auto
        done
      moreover
      have "y \<in> \<Union>s"
        using set_rev_mp[OF as(1) s(2)[OF k(1)]] as(2) di i
        unfolding s mem_box y_def
        by (auto simp: field_simps elim!: ballE[of _ _ i])
      ultimately
      show "y \<in> \<Union>(s - {k})" by auto
    qed
  qed
  then have "\<Union>(s - {k}) = cbox a b"
    unfolding s(6)[symmetric] by auto
  then have  "{ka \<in> s - {k}. content ka \<noteq> 0} division_of (cbox a b)"
    apply -
    apply (rule assm(2)[rule_format,OF card refl])
    apply (rule division_ofI)
    defer
    apply (rule_tac[1-4] s)
    using assm(1)
    apply auto
    done
  moreover
  have "{ka \<in> s - {k}. content ka \<noteq> 0} = {k \<in> s. content k \<noteq> 0}"
    using k by auto
  ultimately show ?thesis by auto
qed


subsection {* Integrability on subintervals. *}

lemma operative_integrable:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  shows "operative op \<and> (\<lambda>i. f integrable_on i)"
  unfolding operative_def neutral_and
  apply safe
  apply (subst integrable_on_def)
  unfolding has_integral_null_eq
  apply (rule, rule refl)
  apply (rule, assumption, assumption)+
  unfolding integrable_on_def
  by (auto intro!: has_integral_split)

lemma integrable_subinterval:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "cbox c d \<subseteq> cbox a b"
  shows "f integrable_on cbox c d"
  apply (cases "cbox c d = {}")
  defer
  apply (rule partial_division_extend_1[OF assms(2)],assumption)
  using operative_division_and[OF operative_integrable,symmetric,of _ _ _ f] assms(1)
  apply auto
  done

lemma integrable_subinterval_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "{c .. d} \<subseteq> {a .. b}"
  shows "f integrable_on {c .. d}"
  by (metis assms(1) assms(2) box_real(2) integrable_subinterval)


subsection {* Combining adjacent intervals in 1 dimension. *}

lemma has_integral_combine:
  fixes a b c :: real
  assumes "a \<le> c"
    and "c \<le> b"
    and "(f has_integral i) {a .. c}"
    and "(f has_integral (j::'a::banach)) {c .. b}"
  shows "(f has_integral (i + j)) {a .. b}"
proof -
  note operative_integral[of f, unfolded operative_1_le[OF monoidal_lifted[OF monoidal_monoid]]]
  note conjunctD2[OF this,rule_format]
  note * = this(2)[OF conjI[OF assms(1-2)],unfolded if_P[OF assms(3)]]
  then have "f integrable_on cbox a b"
    apply -
    apply (rule ccontr)
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    using assms(3-)
    apply auto
    done
  with *
  show ?thesis
    apply -
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    unfolding lifted.simps
    using assms(3-)
    apply (auto simp add: integrable_on_def integral_unique)
    done
qed

lemma integral_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a .. b}"
  shows "integral {a .. c} f + integral {c .. b} f = integral {a .. b} f"
  apply (rule integral_unique[symmetric])
  apply (rule has_integral_combine[OF assms(1-2)])
  apply (metis assms(2) assms(3) atLeastatMost_subset_iff box_real(2) content_pos_le content_real_eq_0 integrable_integral integrable_subinterval le_add_same_cancel2 monoid_add_class.add.left_neutral)
  by (metis assms(1) assms(3) atLeastatMost_subset_iff box_real(2) content_pos_le content_real_eq_0 integrable_integral integrable_subinterval le_add_same_cancel1 monoid_add_class.add.right_neutral)

lemma integrable_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a .. c}"
    and "f integrable_on {c .. b}"
  shows "f integrable_on {a .. b}"
  using assms
  unfolding integrable_on_def
  by (fastforce intro!:has_integral_combine)


subsection {* Reduce integrability to "local" integrability. *}

lemma integrable_on_little_subintervals:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x\<in>cbox a b. \<exists>d>0. \<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v"
  shows "f integrable_on cbox a b"
proof -
  have "\<forall>x. \<exists>d. x\<in>cbox a b \<longrightarrow> d>0 \<and> (\<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v)"
    using assms by auto
  note this[unfolded gauge_existence_lemma]
  from choice[OF this] guess d .. note d=this[rule_format]
  guess p
    apply (rule fine_division_exists[OF gauge_ball_dependent,of d a b])
    using d
    by auto
  note p=this(1-2)
  note division_of_tagged_division[OF this(1)]
  note * = operative_division_and[OF operative_integrable,OF this,symmetric,of f]
  show ?thesis
    unfolding *
    apply safe
    unfolding snd_conv
  proof -
    fix x k
    assume "(x, k) \<in> p"
    note tagged_division_ofD(2-4)[OF p(1) this] fineD[OF p(2) this]
    then show "f integrable_on k"
      apply safe
      apply (rule d[THEN conjunct2,rule_format,of x])
      apply (auto intro: order.trans)
      done
  qed
qed


subsection {* Second FCT or existence of antiderivative. *}

lemma integrable_const[intro]: "(\<lambda>x. c) integrable_on cbox a b"
  unfolding integrable_on_def
  apply rule
  apply (rule has_integral_const)
  done

lemma integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
    and "x \<in> {a .. b}"
  shows "((\<lambda>u. integral {a .. u} f) has_vector_derivative f(x)) (at x within {a .. b})"
  unfolding has_vector_derivative_def has_derivative_within_alt
  apply safe
  apply (rule bounded_linear_scaleR_left)
proof -
  fix e :: real
  assume e: "e > 0"
  note compact_uniformly_continuous[OF assms(1) compact_Icc,unfolded uniformly_continuous_on_def]
  from this[rule_format,OF e] guess d by (elim conjE exE) note d=this[rule_format]
  let ?I = "\<lambda>a b. integral {a .. b} f"
  show "\<exists>d>0. \<forall>y\<in>{a .. b}. norm (y - x) < d \<longrightarrow>
    norm (?I a y - ?I a x - (y - x) *\<^sub>R f x) \<le> e * norm (y - x)"
  proof (rule, rule, rule d, safe)
    case goal1
    show ?case
    proof (cases "y < x")
      case False
      have "f integrable_on {a .. y}"
        apply (rule integrable_subinterval_real,rule integrable_continuous_real)
        apply (rule assms)
        unfolding not_less
        using assms(2) goal1
        apply auto
        done
      then have *: "?I a y - ?I a x = ?I x y"
        unfolding algebra_simps
        apply (subst eq_commute)
        apply (rule integral_combine)
        using False
        unfolding not_less
        using assms(2) goal1
        apply auto
        done
      have **: "norm (y - x) = content {x .. y}"
        using False by (auto simp: content_real)
      show ?thesis
        unfolding **
        apply (rule has_integral_bound_real[where f="(\<lambda>u. f u - f x)"])
        unfolding *
        defer
        apply (rule has_integral_sub)
        apply (rule integrable_integral)
        apply (rule integrable_subinterval_real)
        apply (rule integrable_continuous_real)
        apply (rule assms)+
      proof -
        show "{x .. y} \<subseteq> {a .. b}"
          using goal1 assms(2) by auto
        have *: "y - x = norm (y - x)"
          using False by auto
        show "((\<lambda>xa. f x) has_integral (y - x) *\<^sub>R f x) {x .. y}"
          apply (subst *)
          unfolding **
          by auto
        show "\<forall>xa\<in>{x .. y}. norm (f xa - f x) \<le> e"
          apply safe
          apply (rule less_imp_le)
          apply (rule d(2)[unfolded dist_norm])
          using assms(2)
          using goal1
          apply auto
          done
      qed (insert e, auto)
    next
      case True
      have "f integrable_on cbox a x"
        apply (rule integrable_subinterval,rule integrable_continuous)
        unfolding box_real
        apply (rule assms)+
        unfolding not_less
        using assms(2) goal1
        apply auto
        done
      then have *: "?I a x - ?I a y = ?I y x"
        unfolding algebra_simps
        apply (subst eq_commute)
        apply (rule integral_combine)
        using True using assms(2) goal1
        apply auto
        done
      have **: "norm (y - x) = content {y .. x}"
        apply (subst content_real)
        using True
        unfolding not_less
        apply auto
        done
      have ***: "\<And>fy fx c::'a. fx - fy - (y - x) *\<^sub>R c = -(fy - fx - (x - y) *\<^sub>R c)"
        unfolding scaleR_left.diff by auto
      show ?thesis
        apply (subst ***)
        unfolding norm_minus_cancel **
        apply (rule has_integral_bound_real[where f="(\<lambda>u. f u - f x)"])
        unfolding *
        unfolding o_def
        defer
        apply (rule has_integral_sub)
        apply (subst minus_minus[symmetric])
        unfolding minus_minus
        apply (rule integrable_integral)
        apply (rule integrable_subinterval_real,rule integrable_continuous_real)
        apply (rule assms)+
      proof -
        show "{y .. x} \<subseteq> {a .. b}"
          using goal1 assms(2) by auto
        have *: "x - y = norm (y - x)"
          using True by auto
        show "((\<lambda>xa. f x) has_integral (x - y) *\<^sub>R f x) {y .. x}"
          apply (subst *)
          unfolding **
          apply auto
          done
        show "\<forall>xa\<in>{y .. x}. norm (f xa - f x) \<le> e"
          apply safe
          apply (rule less_imp_le)
          apply (rule d(2)[unfolded dist_norm])
          using assms(2)
          using goal1
          apply auto
          done
      qed (insert e, auto)
    qed
  qed
qed

lemma antiderivative_continuous:
  fixes q b :: real
  assumes "continuous_on {a .. b} f"
  obtains g where "\<forall>x\<in>{a .. b}. (g has_vector_derivative (f x::_::banach)) (at x within {a .. b})"
  apply (rule that)
  apply rule
  using integral_has_vector_derivative[OF assms]
  apply auto
  done


subsection {* Combined fundamental theorem of calculus. *}

lemma antiderivative_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
  obtains g where "\<forall>u\<in>{a .. b}. \<forall>v \<in> {a .. b}. u \<le> v \<longrightarrow> (f has_integral (g v - g u)) {u .. v}"
proof -
  from antiderivative_continuous[OF assms] guess g . note g=this
  show ?thesis
    apply (rule that[of g])
  proof safe
    case goal1
    have "\<forall>x\<in>cbox u v. (g has_vector_derivative f x) (at x within cbox u v)"
      apply rule
      apply (rule has_vector_derivative_within_subset)
      apply (rule g[rule_format])
      using goal1(1-2)
      apply auto
      done
    then show ?case
      using fundamental_theorem_of_calculus[OF goal1(3),of "g" "f"] by auto
  qed
qed


subsection {* General "twiddling" for interval-to-interval function image. *}

lemma has_integral_twiddle:
  assumes "0 < r"
    and "\<forall>x. h(g x) = x"
    and "\<forall>x. g(h x) = x"
    and "\<forall>x. continuous (at x) g"
    and "\<forall>u v. \<exists>w z. g ` cbox u v = cbox w z"
    and "\<forall>u v. \<exists>w z. h ` cbox u v = cbox w z"
    and "\<forall>u v. content(g ` cbox u v) = r * content (cbox u v)"
    and "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(g x)) has_integral (1 / r) *\<^sub>R i) (h ` cbox a b)"
proof -
  {
    presume *: "cbox a b \<noteq> {} \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      defer
      apply (rule *)
      apply assumption
    proof -
      case goal1
      then show ?thesis
        unfolding goal1 assms(8)[unfolded goal1 has_integral_empty_eq] by auto qed
  }
  assume "cbox a b \<noteq> {}"
  from assms(6)[rule_format,of a b] guess w z by (elim exE) note wz=this
  have inj: "inj g" "inj h"
    unfolding inj_on_def
    apply safe
    apply(rule_tac[!] ccontr)
    using assms(2)
    apply(erule_tac x=x in allE)
    using assms(2)
    apply(erule_tac x=y in allE)
    defer
    using assms(3)
    apply (erule_tac x=x in allE)
    using assms(3)
    apply(erule_tac x=y in allE)
    apply auto
    done
  show ?thesis
    unfolding has_integral_def has_integral_compact_interval_def
    apply (subst if_P)
    apply rule
    apply rule
    apply (rule wz)
  proof safe
    fix e :: real
    assume e: "e > 0"
    with assms(1) have "e * r > 0" by simp
    from assms(8)[unfolded has_integral,rule_format,OF this] guess d by (elim exE conjE) note d=this[rule_format]
    def d' \<equiv> "\<lambda>x. {y. g y \<in> d (g x)}"
    have d': "\<And>x. d' x = {y. g y \<in> (d (g x))}"
      unfolding d'_def ..
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of h ` cbox a b \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e)"
    proof (rule_tac x=d' in exI, safe)
      show "gauge d'"
        using d(1)
        unfolding gauge_def d'
        using continuous_open_preimage_univ[OF assms(4)]
        by auto
      fix p
      assume as: "p tagged_division_of h ` cbox a b" "d' fine p"
      note p = tagged_division_ofD[OF as(1)]
      have "(\<lambda>(x, k). (g x, g ` k)) ` p tagged_division_of (cbox a b) \<and> d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
        unfolding tagged_division_of
      proof safe
        show "finite ((\<lambda>(x, k). (g x, g ` k)) ` p)"
          using as by auto
        show "d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
          using as(2) unfolding fine_def d' by auto
        fix x k
        assume xk[intro]: "(x, k) \<in> p"
        show "g x \<in> g ` k"
          using p(2)[OF xk] by auto
        show "\<exists>u v. g ` k = cbox u v"
          using p(4)[OF xk] using assms(5-6) by auto
        {
          fix y
          assume "y \<in> k"
          then show "g y \<in> cbox a b" "g y \<in> cbox a b"
            using p(3)[OF xk,unfolded subset_eq,rule_format,of "h (g y)"]
            using assms(2)[rule_format,of y]
            unfolding inj_image_mem_iff[OF inj(2)]
            by auto
        }
        fix x' k'
        assume xk': "(x', k') \<in> p"
        fix z
        assume "z \<in> interior (g ` k)" and "z \<in> interior (g ` k')"
        then have *: "interior (g ` k) \<inter> interior (g ` k') \<noteq> {}"
          by auto
        have same: "(x, k) = (x', k')"
          apply -
          apply (rule ccontr)
          apply (drule p(5)[OF xk xk'])
        proof -
          assume as: "interior k \<inter> interior k' = {}"
          from nonempty_witness[OF *] guess z .
          then have "z \<in> g ` (interior k \<inter> interior k')"
            using interior_image_subset[OF assms(4) inj(1)]
            unfolding image_Int[OF inj(1)]
            by auto
          then show False
            using as by blast
        qed
        then show "g x = g x'"
          by auto
        {
          fix z
          assume "z \<in> k"
          then show "g z \<in> g ` k'"
            using same by auto
        }
        {
          fix z
          assume "z \<in> k'"
          then show "g z \<in> g ` k"
            using same by auto
        }
      next
        fix x
        assume "x \<in> cbox a b"
        then have "h x \<in>  \<Union>{k. \<exists>x. (x, k) \<in> p}"
          using p(6) by auto
        then guess X unfolding Union_iff .. note X=this
        from this(1) guess y unfolding mem_Collect_eq ..
        then show "x \<in> \<Union>{k. \<exists>x. (x, k) \<in> (\<lambda>(x, k). (g x, g ` k)) ` p}"
          apply -
          apply (rule_tac X="g ` X" in UnionI)
          defer
          apply (rule_tac x="h x" in image_eqI)
          using X(2) assms(3)[rule_format,of x]
          apply auto
          done
      qed
        note ** = d(2)[OF this]
        have *: "inj_on (\<lambda>(x, k). (g x, g ` k)) p"
          using inj(1) unfolding inj_on_def by fastforce
        have "(\<Sum>(x, k)\<in>(\<lambda>(x, k). (g x, g ` k)) ` p. content k *\<^sub>R f x) - i = r *\<^sub>R (\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - i" (is "?l = _")
          unfolding algebra_simps add_left_cancel
          unfolding setsum_reindex[OF *]
          apply (subst scaleR_right.setsum)
          defer
          apply (rule setsum_cong2)
          unfolding o_def split_paired_all split_conv
          apply (drule p(4))
          apply safe
          unfolding assms(7)[rule_format]
          using p
          apply auto
          done
      also have "\<dots> = r *\<^sub>R ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i)" (is "_ = ?r")
        unfolding scaleR_diff_right scaleR_scaleR
        using assms(1)
        by auto
      finally have *: "?l = ?r" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e"
        using **
        unfolding *
        unfolding norm_scaleR
        using assms(1)
        by (auto simp add:field_simps)
    qed
  qed
qed


subsection {* Special case of a basic affine transformation. *}

lemma interval_image_affinity_interval:
  "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::'a::euclidean_space) + c) ` cbox a b = cbox u v"
  unfolding image_affinity_cbox
  by auto

lemma setprod_cong2:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "setprod f A = setprod g A"
  apply (rule setprod_cong)
  using assms
  apply auto
  done

lemma content_image_affinity_cbox:
  "content((\<lambda>x::'a::euclidean_space. m *\<^sub>R x + c) ` cbox a b) =
    abs m ^ DIM('a) * content (cbox a b)" (is "?l = ?r")
proof -
  {
    presume *: "cbox a b \<noteq> {} \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      unfolding not_not
      using content_empty
      apply auto
      done
  }
  assume as: "cbox a b \<noteq> {}"
  show ?thesis
  proof (cases "m \<ge> 0")
    case True
    with as have "cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c) \<noteq> {}"
      unfolding box_ne_empty
      apply (intro ballI)
      apply (erule_tac x=i in ballE)
      apply (auto simp: inner_simps intro!: mult_left_mono)
      done
    moreover from True have *: "\<And>i. (m *\<^sub>R b + c) \<bullet> i - (m *\<^sub>R a + c) \<bullet> i = m *\<^sub>R (b - a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis
      by (simp add: image_affinity_cbox True content_cbox'
        setprod_timesf setprod_constant inner_diff_left)
  next
    case False
    with as have "cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c) \<noteq> {}"
      unfolding box_ne_empty
      apply (intro ballI)
      apply (erule_tac x=i in ballE)
      apply (auto simp: inner_simps intro!: mult_left_mono)
      done
    moreover from False have *: "\<And>i. (m *\<^sub>R a + c) \<bullet> i - (m *\<^sub>R b + c) \<bullet> i = (-m) *\<^sub>R (b - a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis using False
      by (simp add: image_affinity_cbox content_cbox'
        setprod_timesf[symmetric] setprod_constant[symmetric] inner_diff_left)
  qed
qed

lemma has_integral_affinity:
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral ((1 / (abs(m) ^ DIM('a))) *\<^sub>R i)) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` cbox a b)"
  apply (rule has_integral_twiddle)
  apply safe
  apply (rule zero_less_power)
  unfolding euclidean_eq_iff[where 'a='a]
  unfolding scaleR_right_distrib inner_simps scaleR_scaleR
  defer
  apply (insert assms(2))
  apply (simp add: field_simps)
  apply (insert assms(2))
  apply (simp add: field_simps)
  apply (rule continuous_intros)+
  apply (rule interval_image_affinity_interval)+
  apply (rule content_image_affinity_cbox)
  using assms
  apply auto
  done

lemma integrable_affinity:
  assumes "f integrable_on cbox a b"
    and "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` cbox a b)"
  using assms
  unfolding integrable_on_def
  apply safe
  apply (drule has_integral_affinity)
  apply auto
  done


subsection {* Special case of stretching coordinate axes separately. *}

lemma image_stretch_interval:
  "(\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k)) *\<^sub>R k) ` cbox a (b::'a::euclidean_space) =
  (if (cbox a b) = {} then {} else
    cbox (\<Sum>k\<in>Basis. (min (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k::'a)
     (\<Sum>k\<in>Basis. (max (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k))"
proof cases
  assume *: "cbox a b \<noteq> {}"
  show ?thesis
    unfolding box_ne_empty if_not_P[OF *]
    apply (simp add: cbox_def image_Collect set_eq_iff euclidean_eq_iff[where 'a='a] ball_conj_distrib[symmetric])
    apply (subst choice_Basis_iff[symmetric])
  proof (intro allI ball_cong refl)
    fix x i :: 'a assume "i \<in> Basis"
    with * have a_le_b: "a \<bullet> i \<le> b \<bullet> i"
      unfolding box_ne_empty by auto
    show "(\<exists>xa. x \<bullet> i = m i * xa \<and> a \<bullet> i \<le> xa \<and> xa \<le> b \<bullet> i) \<longleftrightarrow>
        min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (m i * (a \<bullet> i)) (m i * (b \<bullet> i))"
    proof (cases "m i = 0")
      case True
      with a_le_b show ?thesis by auto
    next
      case False
      then have *: "\<And>a b. a = m i * b \<longleftrightarrow> b = a / m i"
        by (auto simp add: field_simps)
      from False have
          "min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (a \<bullet> i) else m i * (b \<bullet> i))"
          "max (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (b \<bullet> i) else m i * (a \<bullet> i))"
        using a_le_b by (auto simp: min_def max_def mult_le_cancel_left)
      with False show ?thesis using a_le_b
        unfolding * by (auto simp add: le_divide_eq divide_le_eq ac_simps)
    qed
  qed
qed simp

lemma interval_image_stretch_interval:
  "\<exists>u v. (\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k) ` cbox a (b::'a::euclidean_space) = cbox u (v::'a::euclidean_space)"
  unfolding image_stretch_interval by auto

lemma content_image_stretch_interval:
  "content ((\<lambda>x::'a::euclidean_space. (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)::'a) ` cbox a b) =
    abs (setprod m Basis) * content (cbox a b)"
proof (cases "cbox a b = {}")
  case True
  then show ?thesis
    unfolding content_def image_is_empty image_stretch_interval if_P[OF True] by auto
next
  case False
  then have "(\<lambda>x. (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) ` cbox a b \<noteq> {}"
    by auto
  then show ?thesis
    using False
    unfolding content_def image_stretch_interval
    apply -
    unfolding interval_bounds' if_not_P
    unfolding abs_setprod setprod_timesf[symmetric]
    apply (rule setprod_cong2)
    unfolding lessThan_iff
    apply (simp only: inner_setsum_left_Basis)
  proof -
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "(m i < 0 \<or> m i > 0) \<or> m i = 0"
      by auto
    then show "max (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) - min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) =
      \<bar>m i\<bar> * (b \<bullet> i - a \<bullet> i)"
      apply -
      apply (erule disjE)+
      unfolding min_def max_def
      using False[unfolded box_ne_empty,rule_format,of i] i
      apply (auto simp add:field_simps not_le mult_le_cancel_left_neg mult_le_cancel_left_pos)
      done
  qed
qed

lemma has_integral_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "((\<lambda>x. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) has_integral
    ((1/(abs(setprod m Basis))) *\<^sub>R i)) ((\<lambda>x. (\<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k)) ` cbox a b)"
  apply (rule has_integral_twiddle[where f=f])
  unfolding zero_less_abs_iff content_image_stretch_interval
  unfolding image_stretch_interval empty_as_interval euclidean_eq_iff[where 'a='a]
  using assms
proof -
  show "\<forall>y::'a. continuous (at y) (\<lambda>x. (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k))"
    apply rule
    apply (rule linear_continuous_at)
    unfolding linear_linear
    unfolding linear_iff inner_simps euclidean_eq_iff[where 'a='a]
    apply (auto simp add: field_simps)
    done
qed auto

lemma integrable_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "f integrable_on cbox a b"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "(\<lambda>x::'a. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) integrable_on
    ((\<lambda>x. \<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k) ` cbox a b)"
  using assms
  unfolding integrable_on_def
  apply -
  apply (erule exE)
  apply (drule has_integral_stretch)
  apply assumption
  apply auto
  done


subsection {* even more special cases. *}

lemma uminus_interval_vector[simp]:
  fixes a b :: "'a::euclidean_space"
  shows "uminus ` cbox a b = cbox (-b) (-a)"
  apply (rule set_eqI)
  apply rule
  defer
  unfolding image_iff
  apply (rule_tac x="-x" in bexI)
  apply (auto simp add:minus_le_iff le_minus_iff mem_box)
  done

lemma has_integral_reflect_lemma[intro]:
  assumes "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(-x)) has_integral i) (cbox (-b) (-a))"
  using has_integral_affinity[OF assms, of "-1" 0]
  by auto

lemma has_integral_reflect_lemma_real[intro]:
  assumes "(f has_integral i) {a .. b::real}"
  shows "((\<lambda>x. f(-x)) has_integral i) {-b .. -a}"
  using assms
  unfolding box_real[symmetric]
  by (rule has_integral_reflect_lemma)

lemma has_integral_reflect[simp]:
  "((\<lambda>x. f (-x)) has_integral i) (cbox (-b) (-a)) \<longleftrightarrow> (f has_integral i) (cbox a b)"
  apply rule
  apply (drule_tac[!] has_integral_reflect_lemma)
  apply auto
  done

lemma integrable_reflect[simp]: "(\<lambda>x. f(-x)) integrable_on cbox (-b) (-a) \<longleftrightarrow> f integrable_on cbox a b"
  unfolding integrable_on_def by auto

lemma integrable_reflect_real[simp]: "(\<lambda>x. f(-x)) integrable_on {-b .. -a} \<longleftrightarrow> f integrable_on {a .. b::real}"
  unfolding box_real[symmetric]
  by (rule integrable_reflect)

lemma integral_reflect[simp]: "integral (cbox (-b) (-a)) (\<lambda>x. f (-x)) = integral (cbox a b) f"
  unfolding integral_def by auto

lemma integral_reflect_real[simp]: "integral {-b .. -a} (\<lambda>x. f (-x)) = integral {a .. b::real} f"
  unfolding box_real[symmetric]
  by (rule integral_reflect)


subsection {* Stronger form of FCT; quite a tedious proof. *}

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)"
  by (meson zero_less_one)

lemma additive_tagged_division_1':
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f (Sup k) - f(Inf k)) p = f b - f a"
  using additive_tagged_division_1[OF _ assms(2), of f]
  using assms(1)
  by auto

lemma split_minus[simp]: "(\<lambda>(x, k). f x k) x - (\<lambda>(x, k). g x k) x = (\<lambda>(x, k). f x k - g x k) x"
  by (simp add: split_def)

lemma norm_triangle_le_sub: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
  apply (subst(asm)(2) norm_minus_cancel[symmetric])
  apply (drule norm_triangle_le)
  apply (auto simp add: algebra_simps)
  done

lemma fundamental_theorem_of_calculus_interior:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a <..< b}. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
proof -
  {
    presume *: "a < b \<Longrightarrow> ?thesis"
    show ?thesis
    proof (cases "a < b")
      case True
      then show ?thesis by (rule *)
    next
      case False
      then have "a = b"
        using assms(1) by auto
      then have *: "cbox a b = {b}" "f b - f a = 0"
        by (auto simp add:  order_antisym)
      show ?thesis
        unfolding *(2)
        unfolding content_eq_0
        using * `a = b`
        by (auto simp: ex_in_conv)
    qed
  }
  assume ab: "a < b"
  let ?P = "\<lambda>e. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a .. b} \<and> d fine p \<longrightarrow>
    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a .. b})"
  { presume "\<And>e. e > 0 \<Longrightarrow> ?P e" then show ?thesis unfolding has_integral_factor_content_real by auto }
  fix e :: real
  assume e: "e > 0"
  note assms(3)[unfolded has_vector_derivative_def has_derivative_at_alt ball_conj_distrib]
  note conjunctD2[OF this]
  note bounded=this(1) and this(2)
  from this(2) have "\<forall>x\<in>box a b. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
    norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> e/2 * norm (y - x)"
    apply -
    apply safe
    apply (erule_tac x=x in ballE)
    apply (erule_tac x="e/2" in allE)
    using e
    apply auto
    done
  note this[unfolded bgauge_existence_lemma]
  from choice[OF this] guess d ..
  note conjunctD2[OF this[rule_format]]
  note d = this[rule_format]
  have "bounded (f ` cbox a b)"
    apply (rule compact_imp_bounded compact_continuous_image)+
    using compact_cbox assms
    apply auto
    done
  from this[unfolded bounded_pos] guess B .. note B = this[rule_format]

  have "\<exists>da. 0 < da \<and> (\<forall>c. a \<le> c \<and> {a .. c} \<subseteq> {a .. b} \<and> {a .. c} \<subseteq> ball a da \<longrightarrow>
    norm (content {a .. c} *\<^sub>R f' a - (f c - f a)) \<le> (e * (b - a)) / 4)"
  proof -
    have "a \<in> {a .. b}"
      using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format]
    have "(e * (b - a)) / 8 > 0"
      using e ab by (auto simp add: field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm(l *\<^sub>R f' a) \<le> (e * (b - a)) / 8"
    proof (cases "f' a = 0")
      case True
      thus ?thesis using ab e by auto
    next
      case False
      then show ?thesis
        apply (rule_tac x="(e * (b - a)) / 8 / norm (f' a)" in exI)
        using ab e
        apply (auto simp add: field_simps)
        done
    qed
    then guess l .. note l = conjunctD2[OF this]
    show ?thesis
      apply (rule_tac x="min k l" in exI)
      apply safe
      unfolding min_less_iff_conj
      apply rule
      apply (rule l k)+
    proof -
      fix c
      assume as: "a \<le> c" "{a .. c} \<subseteq> {a .. b}" "{a .. c} \<subseteq> ball a (min k l)"
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_box]
      have "norm ((c - a) *\<^sub>R f' a - (f c - f a)) \<le> norm ((c - a) *\<^sub>R f' a) + norm (f c - f a)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> e * (b - a) / 8 + e * (b - a) / 8"
      proof (rule add_mono)
        case goal1
        have "\<bar>c - a\<bar> \<le> \<bar>l\<bar>"
          using as' by auto
        then show ?case
          apply -
          apply (rule order_trans[OF _ l(2)])
          unfolding norm_scaleR
          apply (rule mult_right_mono)
          apply auto
          done
      next
        case goal2
        show ?case
          apply (rule less_imp_le)
          apply (cases "a = c")
          defer
          apply (rule k(2)[unfolded dist_norm])
          using as' e ab
          apply (auto simp add: field_simps)
          done
      qed
      finally show "norm (content {a .. c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed
  qed
  then guess da .. note da=conjunctD2[OF this,rule_format]

  have "\<exists>db>0. \<forall>c\<le>b. {c .. b} \<subseteq> {a .. b} \<and> {c .. b} \<subseteq> ball b db \<longrightarrow>
    norm (content {c .. b} *\<^sub>R f' b - (f b - f c)) \<le> (e * (b - a)) / 4"
  proof -
    have "b \<in> {a .. b}"
      using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0"
      using e ab by (auto simp add: field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm (l *\<^sub>R f' b) \<le> (e * (b - a)) / 8"
    proof (cases "f' b = 0")
      case True
      thus ?thesis using ab e by auto
    next
      case False
      then show ?thesis
        apply (rule_tac x="(e * (b - a)) / 8 / norm (f' b)" in exI)
        using ab e
        apply (auto simp add: field_simps)
        done
    qed
    then guess l .. note l = conjunctD2[OF this]
    show ?thesis
      apply (rule_tac x="min k l" in exI)
      apply safe
      unfolding min_less_iff_conj
      apply rule
      apply (rule l k)+
    proof -
      fix c
      assume as: "c \<le> b" "{c..b} \<subseteq> {a..b}" "{c..b} \<subseteq> ball b (min k l)"
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_box]
      have "norm ((b - c) *\<^sub>R f' b - (f b - f c)) \<le> norm ((b - c) *\<^sub>R f' b) + norm (f b - f c)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> e * (b - a) / 8 + e * (b - a) / 8"
      proof (rule add_mono)
        case goal1
        have "\<bar>c - b\<bar> \<le> \<bar>l\<bar>"
          using as' by auto
        then show ?case
          apply -
          apply (rule order_trans[OF _ l(2)])
          unfolding norm_scaleR
          apply (rule mult_right_mono)
          apply auto
          done
      next
        case goal2
        show ?case
          apply (rule less_imp_le)
          apply (cases "b = c")
          defer
          apply (subst norm_minus_commute)
          apply (rule k(2)[unfolded dist_norm])
          using as' e ab
          apply (auto simp add: field_simps)
          done
      qed
      finally show "norm (content {c .. b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed
  qed
  then guess db .. note db=conjunctD2[OF this,rule_format]

  let ?d = "(\<lambda>x. ball x (if x=a then da else if x=b then db else d x))"
  show "?P e"
    apply (rule_tac x="?d" in exI)
  proof safe
    case goal1
    show ?case
      apply (rule gauge_ball_dependent)
      using ab db(1) da(1) d(1)
      apply auto
      done
  next
    case goal2
    note as=this
    let ?A = "{t. fst t \<in> {a, b}}"
    note p = tagged_division_ofD[OF goal2(1)]
    have pA: "p = (p \<inter> ?A) \<union> (p - ?A)" "finite (p \<inter> ?A)" "finite (p - ?A)" "(p \<inter> ?A) \<inter> (p - ?A) = {}"
      using goal2 by auto
    note * = additive_tagged_division_1'[OF assms(1) goal2(1), symmetric]
    have **: "\<And>n1 s1 n2 s2::real. n2 \<le> s2 / 2 \<Longrightarrow> n1 - s1 \<le> s2 / 2 \<Longrightarrow> n1 + n2 \<le> s1 + s2"
      by arith
    show ?case
      unfolding content_real[OF assms(1)] and *[of "\<lambda>x. x"] *[of f] setsum_subtractf[symmetric] split_minus
      unfolding setsum_right_distrib
      apply (subst(2) pA)
      apply (subst pA)
      unfolding setsum_Un_disjoint[OF pA(2-)]
    proof (rule norm_triangle_le, rule **)
      case goal1
      show ?case
        apply (rule order_trans)
        apply (rule setsum_norm_le)
        defer
        apply (subst setsum_divide_distrib)
        apply (rule order_refl)
        apply safe
        apply (unfold not_le o_def split_conv fst_conv)
      proof (rule ccontr)
        fix x k
        assume as: "(x, k) \<in> p"
          "e * (Sup k -  Inf k) / 2 <
            norm (content k *\<^sub>R f' x - (f (Sup k) - f (Inf k)))"
        from p(4)[OF this(1)] guess u v by (elim exE) note k=this
        then have "u \<le> v" and uv: "{u, v} \<subseteq> cbox u v"
          using p(2)[OF as(1)] by auto
        note result = as(2)[unfolded k box_real interval_bounds_real[OF this(1)] content_real[OF this(1)]]

        assume as': "x \<noteq> a" "x \<noteq> b"
        then have "x \<in> box a b"
          using p(2-3)[OF as(1)] by (auto simp: mem_box)
        note  * = d(2)[OF this]
        have "norm ((v - u) *\<^sub>R f' (x) - (f (v) - f (u))) =
          norm ((f (u) - f (x) - (u - x) *\<^sub>R f' (x)) - (f (v) - f (x) - (v - x) *\<^sub>R f' (x)))"
          apply (rule arg_cong[of _ _ norm])
          unfolding scaleR_left.diff
          apply auto
          done
        also have "\<dots> \<le> e / 2 * norm (u - x) + e / 2 * norm (v - x)"
          apply (rule norm_triangle_le_sub)
          apply (rule add_mono)
          apply (rule_tac[!] *)
          using fineD[OF goal2(2) as(1)] as'
          unfolding k subset_eq
          apply -
          apply (erule_tac x=u in ballE)
          apply (erule_tac[3] x=v in ballE)
          using uv
          apply (auto simp:dist_real_def)
          done
        also have "\<dots> \<le> e / 2 * norm (v - u)"
          using p(2)[OF as(1)]
          unfolding k
          by (auto simp add: field_simps)
        finally have "e * (v - u) / 2 < e * (v - u) / 2"
          apply -
          apply (rule less_le_trans[OF result])
          using uv
          apply auto
          done
        then show False by auto
      qed
    next
      have *: "\<And>x s1 s2::real. 0 \<le> s1 \<Longrightarrow> x \<le> (s1 + s2) / 2 \<Longrightarrow> x - s1 \<le> s2 / 2"
        by auto
      case goal2
      show ?case
        apply (rule *)
        apply (rule setsum_nonneg)
        apply rule
        apply (unfold split_paired_all split_conv)
        defer
        unfolding setsum_Un_disjoint[OF pA(2-),symmetric] pA(1)[symmetric]
        unfolding setsum_right_distrib[symmetric]
        thm additive_tagged_division_1
        apply (subst additive_tagged_division_1[OF _ as(1)])
        apply (rule assms)
      proof -
        fix x k
        assume "(x, k) \<in> p \<inter> {t. fst t \<in> {a, b}}"
        note xk=IntD1[OF this]
        from p(4)[OF this] guess u v by (elim exE) note uv=this
        with p(2)[OF xk] have "cbox u v \<noteq> {}"
          by auto
        then show "0 \<le> e * ((Sup k) - (Inf k))"
          unfolding uv using e by (auto simp add: field_simps)
      next
        have *: "\<And>s f t e. setsum f s = setsum f t \<Longrightarrow> norm (setsum f t) \<le> e \<Longrightarrow> norm (setsum f s) \<le> e"
          by auto
        show "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R f' x -
          (f ((Sup k)) - f ((Inf k)))) \<le> e * (b - a) / 2"
          apply (rule *[where t="p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0}"])
          apply (rule setsum_mono_zero_right[OF pA(2)])
          defer
          apply rule
          unfolding split_paired_all split_conv o_def
        proof -
          fix x k
          assume "(x, k) \<in> p \<inter> {t. fst t \<in> {a, b}} - p \<inter> {t. fst t \<in> {a, b} \<and> content (snd t) \<noteq> 0}"
          then have xk: "(x, k) \<in> p" "content k = 0"
            by auto
          from p(4)[OF xk(1)] guess u v by (elim exE) note uv=this
          have "k \<noteq> {}"
            using p(2)[OF xk(1)] by auto
          then have *: "u = v"
            using xk
            unfolding uv content_eq_0 box_eq_empty
            by auto
          then show "content k *\<^sub>R (f' (x)) - (f ((Sup k)) - f ((Inf k))) = 0"
            using xk unfolding uv by auto
        next
          have *: "p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0} =
            {t. t\<in>p \<and> fst t = a \<and> content(snd t) \<noteq> 0} \<union> {t. t\<in>p \<and> fst t = b \<and> content(snd t) \<noteq> 0}"
            by blast
          have **: "\<And>s f. \<And>e::real. (\<forall>x y. x \<in> s \<and> y \<in> s \<longrightarrow> x = y) \<Longrightarrow>
            (\<forall>x. x \<in> s \<longrightarrow> norm (f x) \<le> e) \<Longrightarrow> e > 0 \<Longrightarrow> norm (setsum f s) \<le> e"
          proof (case_tac "s = {}")
            case goal2
            then obtain x where "x \<in> s"
              by auto
            then have *: "s = {x}"
              using goal2(1) by auto
            then show ?case
              using `x \<in> s` goal2(2) by auto
          qed auto
          case goal2
          show ?case
            apply (subst *)
            apply (subst setsum_Un_disjoint)
            prefer 4
            apply (rule order_trans[of _ "e * (b - a)/4 + e * (b - a)/4"])
            apply (rule norm_triangle_le,rule add_mono)
            apply (rule_tac[1-2] **)
          proof -
            let ?B = "\<lambda>x. {t \<in> p. fst t = x \<and> content (snd t) \<noteq> 0}"
            have pa: "\<And>k. (a, k) \<in> p \<Longrightarrow> \<exists>v. k = cbox a v \<and> a \<le> v"
            proof -
              case goal1
              guess u v using p(4)[OF goal1] by (elim exE) note uv=this
              have *: "u \<le> v"
                using p(2)[OF goal1] unfolding uv by auto
              have u: "u = a"
              proof (rule ccontr)
                have "u \<in> cbox u v"
                  using p(2-3)[OF goal1(1)] unfolding uv by auto
                have "u \<ge> a"
                  using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto
                moreover assume "\<not> ?thesis"
                ultimately have "u > a" by auto
                then show False
                  using p(2)[OF goal1(1)] unfolding uv by (auto simp add:)
              qed
              then show ?case
                apply (rule_tac x=v in exI)
                unfolding uv
                using *
                apply auto
                done
            qed
            have pb: "\<And>k. (b, k) \<in> p \<Longrightarrow> \<exists>v. k = cbox v b \<and> b \<ge> v"
            proof -
              case goal1
              guess u v using p(4)[OF goal1] by (elim exE) note uv=this
              have *: "u \<le> v"
                using p(2)[OF goal1] unfolding uv by auto
              have u: "v =  b"
              proof (rule ccontr)
                have "u \<in> cbox u v"
                  using p(2-3)[OF goal1(1)] unfolding uv by auto
                have "v \<le> b"
                  using p(2-3)[OF goal1(1)] unfolding uv subset_eq by auto
                moreover assume "\<not> ?thesis"
                ultimately have "v < b" by auto
                then show False
                  using p(2)[OF goal1(1)] unfolding uv by (auto simp add:)
              qed
              then show ?case
                apply (rule_tac x=u in exI)
                unfolding uv
                using *
                apply auto
                done
            qed
            show "\<forall>x y. x \<in> ?B a \<and> y \<in> ?B a \<longrightarrow> x = y"
              apply (rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv
              apply safe
            proof -
              fix x k k'
              assume k: "(a, k) \<in> p" "(a, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pa[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pa[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = "min v v'"
              have "box a ?v \<subseteq> k \<inter> k'"
                unfolding v v' by (auto simp add: mem_box)
              note interior_mono[OF this,unfolded interior_inter]
              moreover have "(a + ?v)/2 \<in> box a ?v"
                using k(3-)
                unfolding v v' content_eq_0 not_le
                by (auto simp add: mem_box)
              ultimately have "(a + ?v)/2 \<in> interior k \<inter> interior k'"
                unfolding interior_open[OF open_box] by auto
              then have *: "k = k'"
                apply -
                apply (rule ccontr)
                using p(5)[OF k(1-2)]
                apply auto
                done
              { assume "x \<in> k" then show "x \<in> k'" unfolding * . }
              { assume "x \<in> k'" then show "x \<in> k" unfolding * . }
            qed
            show "\<forall>x y. x \<in> ?B b \<and> y \<in> ?B b \<longrightarrow> x = y"
              apply rule
              apply rule
              apply rule
              apply (unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv
              apply safe
            proof -
              fix x k k'
              assume k: "(b, k) \<in> p" "(b, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pb[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pb[OF k(2)] .. note v' = conjunctD2[OF this]
              let ?v = "max v v'"
              have "box ?v b \<subseteq> k \<inter> k'"
                unfolding v v' by (auto simp: mem_box)
                note interior_mono[OF this,unfolded interior_inter]
              moreover have " ((b + ?v)/2) \<in> box ?v b"
                using k(3-) unfolding v v' content_eq_0 not_le by (auto simp: mem_box)
              ultimately have " ((b + ?v)/2) \<in> interior k \<inter> interior k'"
                unfolding interior_open[OF open_box] by auto
              then have *: "k = k'"
                apply -
                apply (rule ccontr)
                using p(5)[OF k(1-2)]
                apply auto
                done
              { assume "x \<in> k" then show "x \<in> k'" unfolding * . }
              { assume "x \<in> k'" then show "x\<in>k" unfolding * . }
            qed

            let ?a = a and ?b = b (* a is something else while proofing the next theorem. *)
            show "\<forall>x. x \<in> ?B a \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' x - (f (Sup k) -
              f (Inf k))) x) \<le> e * (b - a) / 4"
              apply rule
              apply rule
              unfolding mem_Collect_eq
              unfolding split_paired_all fst_conv snd_conv
            proof safe
              case goal1
              guess v using pa[OF goal1(1)] .. note v = conjunctD2[OF this]
              have "?a \<in> {?a..v}"
                using v(2) by auto
              then have "v \<le> ?b"
                using p(3)[OF goal1(1)] unfolding subset_eq v by auto
              moreover have "{?a..v} \<subseteq> ball ?a da"
                using fineD[OF as(2) goal1(1)]
                apply -
                apply (subst(asm) if_P)
                apply (rule refl)
                unfolding subset_eq
                apply safe
                apply (erule_tac x=" x" in ballE)
                apply (auto simp add:subset_eq dist_real_def v)
                done
              ultimately show ?case
                unfolding v interval_bounds_real[OF v(2)] box_real
                apply -
                apply(rule da(2)[of "v"])
                using goal1 fineD[OF as(2) goal1(1)]
                unfolding v content_eq_0
                apply auto
                done
            qed
            show "\<forall>x. x \<in> ?B b \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' x -
              (f (Sup k) - f (Inf k))) x) \<le> e * (b - a) / 4"
              apply rule
              apply rule
              unfolding mem_Collect_eq
              unfolding split_paired_all fst_conv snd_conv
            proof safe
              case goal1 guess v using pb[OF goal1(1)] .. note v = conjunctD2[OF this]
              have "?b \<in> {v.. ?b}"
                using v(2) by auto
              then have "v \<ge> ?a" using p(3)[OF goal1(1)]
                unfolding subset_eq v by auto
              moreover have "{v..?b} \<subseteq> ball ?b db"
                using fineD[OF as(2) goal1(1)]
                apply -
                apply (subst(asm) if_P, rule refl)
                unfolding subset_eq
                apply safe
                apply (erule_tac x=" x" in ballE)
                using ab
                apply (auto simp add:subset_eq v dist_real_def)
                done
              ultimately show ?case
                unfolding v
                unfolding interval_bounds_real[OF v(2)] box_real
                apply -
                apply(rule db(2)[of "v"])
                using goal1 fineD[OF as(2) goal1(1)]
                unfolding v content_eq_0
                apply auto
                done
            qed
          qed (insert p(1) ab e, auto simp add: field_simps)
        qed auto
      qed
    qed
  qed
qed


subsection {* Stronger form with finite number of exceptional points. *}

lemma fundamental_theorem_of_calculus_interior_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    and "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a <..< b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  using assms
proof (induct "card s" arbitrary: s a b)
  case 0
  show ?case
    apply (rule fundamental_theorem_of_calculus_interior)
    using 0
    apply auto
    done
next
  case (Suc n)
  from this(2) guess c s'
    apply -
    apply (subst(asm) eq_commute)
    unfolding card_Suc_eq
    apply (subst(asm)(2) eq_commute)
    apply (elim exE conjE)
    done
  note cs = this[rule_format]
  show ?case
  proof (cases "c \<in> box a b")
    case False
    then show ?thesis
      apply -
      apply (rule Suc(1)[OF cs(3) _ Suc(4,5)])
      apply safe
      defer
      apply (rule Suc(6)[rule_format])
      using Suc(3)
      unfolding cs
      apply auto
      done
  next
    have *: "f b - f a = (f c - f a) + (f b - f c)"
      by auto
    case True
    then have "a \<le> c" "c \<le> b"
      by (auto simp: mem_box)
    then show ?thesis
      apply (subst *)
      apply (rule has_integral_combine)
      apply assumption+
      apply (rule_tac[!] Suc(1)[OF cs(3)])
      using Suc(3)
      unfolding cs
    proof -
      show "continuous_on {a .. c} f" "continuous_on {c .. b} f"
        apply (rule_tac[!] continuous_on_subset[OF Suc(5)])
        using True
        apply (auto simp: mem_box)
        done
      let ?P = "\<lambda>i j. \<forall>x\<in>{i <..< j} - s'. (f has_vector_derivative f' x) (at x)"
      show "?P a c" "?P c b"
        apply safe
        apply (rule_tac[!] Suc(6)[rule_format])
        using True
        unfolding cs
        apply (auto simp: mem_box)
        done
    qed auto
  qed
qed

lemma fundamental_theorem_of_calculus_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    and "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a .. b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  apply (rule fundamental_theorem_of_calculus_interior_strong[OF assms(1-3), of f'])
  using assms(4)
  apply (auto simp: mem_box)
  done

lemma indefinite_integral_continuous_left:
  fixes f:: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "a < c"
    and "c \<le> b"
    and "e > 0"
  obtains d where "d > 0"
    and "\<forall>t. c - d < t \<and> t \<le> c \<longrightarrow> norm (integral {a .. c} f - integral {a .. t} f) < e"
proof -
  have "\<exists>w>0. \<forall>t. c - w < t \<and> t < c \<longrightarrow> norm (f c) * norm(c - t) < e / 3"
  proof (cases "f c = 0")
    case False
    hence "0 < e / 3 / norm (f c)" using `e>0` by simp
    then show ?thesis
      apply -
      apply rule
      apply rule
      apply assumption
      apply safe
    proof -
      fix t
      assume as: "t < c" and "c - e / 3 / norm (f c) < t"
      then have "c - t < e / 3 / norm (f c)"
        by auto
      then have "norm (c - t) < e / 3 / norm (f c)"
        using as by auto
      then show "norm (f c) * norm (c - t) < e / 3"
        using False
        apply -
        apply (subst mult_commute)
        apply (subst pos_less_divide_eq[symmetric])
        apply auto
        done
    qed
  next
    case True
    show ?thesis
      apply (rule_tac x=1 in exI)
      unfolding True
      using `e > 0`
      apply auto
      done
  qed
  then guess w .. note w = conjunctD2[OF this,rule_format]

  have *: "e / 3 > 0"
    using assms by auto
  have "f integrable_on {a .. c}"
    apply (rule integrable_subinterval_real[OF assms(1)])
    using assms(2-3)
    apply auto
    done
  from integrable_integral[OF this,unfolded has_integral_real,rule_format,OF *] guess d1 ..
  note d1 = conjunctD2[OF this,rule_format]
  def d \<equiv> "\<lambda>x. ball x w \<inter> d1 x"
  have "gauge d"
    unfolding d_def using w(1) d1 by auto
  note this[unfolded gauge_def,rule_format,of c]
  note conjunctD2[OF this]
  from this(2)[unfolded open_contains_ball,rule_format,OF this(1)] guess k ..
  note k=conjunctD2[OF this]

  let ?d = "min k (c - a) / 2"
  show ?thesis
    apply (rule that[of ?d])
    apply safe
  proof -
    show "?d > 0"
      using k(1) using assms(2) by auto
    fix t
    assume as: "c - ?d < t" "t \<le> c"
    let ?thesis = "norm (integral ({a .. c}) f - integral ({a .. t}) f) < e"
    {
      presume *: "t < c \<Longrightarrow> ?thesis"
      show ?thesis
        apply (cases "t = c")
        defer
        apply (rule *)
        apply (subst less_le)
        using `e > 0` as(2)
        apply auto
        done
    }
    assume "t < c"

    have "f integrable_on {a .. t}"
      apply (rule integrable_subinterval_real[OF assms(1)])
      using assms(2-3) as(2)
      apply auto
      done
    from integrable_integral[OF this,unfolded has_integral_real,rule_format,OF *] guess d2 ..
    note d2 = conjunctD2[OF this,rule_format]
    def d3 \<equiv> "\<lambda>x. if x \<le> t then d1 x \<inter> d2 x else d1 x"
    have "gauge d3"
      using d2(1) d1(1) unfolding d3_def gauge_def by auto
    from fine_division_exists_real[OF this, of a t] guess p . note p=this
    note p'=tagged_division_ofD[OF this(1)]
    have pt: "\<forall>(x,k)\<in>p. x \<le> t"
    proof safe
      case goal1
      from p'(2,3)[OF this] show ?case
        by auto
    qed
    with p(2) have "d2 fine p"
      unfolding fine_def d3_def
      apply safe
      apply (erule_tac x="(a,b)" in ballE)+
      apply auto
      done
    note d2_fin = d2(2)[OF conjI[OF p(1) this]]

    have *: "{a .. c} \<inter> {x. x \<bullet> 1 \<le> t} = {a .. t}" "{a .. c} \<inter> {x. x \<bullet> 1 \<ge> t} = {t .. c}"
      using assms(2-3) as by (auto simp add: field_simps)
    have "p \<union> {(c, {t .. c})} tagged_division_of {a .. c} \<and> d1 fine p \<union> {(c, {t .. c})}"
      apply rule
      apply (rule tagged_division_union_interval_real[of _ _ _ 1 "t"])
      unfolding *
      apply (rule p)
      apply (rule tagged_division_of_self_real)
      unfolding fine_def
      apply safe
    proof -
      fix x k y
      assume "(x,k) \<in> p" and "y \<in> k"
      then show "y \<in> d1 x"
        using p(2) pt
        unfolding fine_def d3_def
        apply -
        apply (erule_tac x="(x,k)" in ballE)+
        apply auto
        done
    next
      fix x assume "x \<in> {t..c}"
      then have "dist c x < k"
        unfolding dist_real_def
        using as(1)
        by (auto simp add: field_simps)
      then show "x \<in> d1 c"
        using k(2)
        unfolding d_def
        by auto
    qed (insert as(2), auto) note d1_fin = d1(2)[OF this]

    have *: "integral {a .. c} f - integral {a .. t} f = -(((c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)) -
      integral {a .. c} f) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - integral {a .. t} f) + (c - t) *\<^sub>R f c"
      "e = (e/3 + e/3) + e/3"
      by auto
    have **: "(\<Sum>(x, k)\<in>p \<union> {(c, {t .. c})}. content k *\<^sub>R f x) =
      (c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
    proof -
      have **: "\<And>x F. F \<union> {x} = insert x F"
        by auto
      have "(c, cbox t c) \<notin> p"
      proof safe
        case goal1
        from p'(2-3)[OF this] have "c \<in> cbox a t"
          by auto
        then show False using `t < c`
          by auto
      qed
      then show ?thesis
        unfolding ** box_real
        apply -
        apply (subst setsum_insert)
        apply (rule p')
        unfolding split_conv
        defer
        apply (subst content_real)
        using as(2)
        apply auto
        done
    qed
    have ***: "c - w < t \<and> t < c"
    proof -
      have "c - k < t"
        using `k>0` as(1) by (auto simp add: field_simps)
      moreover have "k \<le> w"
        apply (rule ccontr)
        using k(2)
        unfolding subset_eq
        apply (erule_tac x="c + ((k + w)/2)" in ballE)
        unfolding d_def
        using `k > 0` `w > 0`
        apply (auto simp add: field_simps not_le not_less dist_real_def)
        done
      ultimately show ?thesis using `t < c`
        by (auto simp add: field_simps)
    qed
    show ?thesis
      unfolding *(1)
      apply (subst *(2))
      apply (rule norm_triangle_lt add_strict_mono)+
      unfolding norm_minus_cancel
      apply (rule d1_fin[unfolded **])
      apply (rule d2_fin)
      using w(2)[OF ***]
      unfolding norm_scaleR
      apply (auto simp add: field_simps)
      done
  qed
qed

lemma indefinite_integral_continuous_right:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "a \<le> c"
    and "c < b"
    and "e > 0"
  obtains d where "0 < d"
    and "\<forall>t. c \<le> t \<and> t < c + d \<longrightarrow> norm (integral {a .. c} f - integral {a .. t} f) < e"
proof -
  have *: "(\<lambda>x. f (- x)) integrable_on {-b .. -a}" "- b < - c" "- c \<le> - a"
    using assms by auto
  from indefinite_integral_continuous_left[OF * `e>0`] guess d . note d = this
  let ?d = "min d (b - c)"
  show ?thesis
    apply (rule that[of "?d"])
    apply safe
  proof -
    show "0 < ?d"
      using d(1) assms(3) by auto
    fix t :: real
    assume as: "c \<le> t" "t < c + ?d"
    have *: "integral {a .. c} f = integral {a .. b} f - integral {c .. b} f"
      "integral {a .. t} f = integral {a .. b} f - integral {t .. b} f"
      unfolding algebra_simps
      apply (rule_tac[!] integral_combine)
      using assms as
      apply auto
      done
    have "(- c) - d < (- t) \<and> - t \<le> - c"
      using as by auto note d(2)[rule_format,OF this]
    then show "norm (integral {a .. c} f - integral {a .. t} f) < e"
      unfolding *
      unfolding integral_reflect
      apply (subst norm_minus_commute)
      apply (auto simp add: algebra_simps)
      done
  qed
qed

lemma indefinite_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
  shows "continuous_on {a .. b} (\<lambda>x. integral {a .. x} f)"
proof (unfold continuous_on_iff, safe)
  fix x e :: real
  assume as: "x \<in> {a .. b}" "e > 0"
  let ?thesis = "\<exists>d>0. \<forall>x'\<in>{a .. b}. dist x' x < d \<longrightarrow> dist (integral {a .. x'} f) (integral {a .. x} f) < e"
  {
    presume *: "a < b \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
    proof -
      case goal1
      then have "cbox a b = {x}"
        using as(1)
        apply -
        apply (rule set_eqI)
        apply auto
        done
      then show ?case using `e > 0` by auto
    qed
  }
  assume "a < b"
  have "(x = a \<or> x = b) \<or> (a < x \<and> x < b)"
    using as(1) by auto
  then show ?thesis
    apply (elim disjE)
  proof -
    assume "x = a"
    have "a \<le> a" ..
    from indefinite_integral_continuous_right[OF assms(1) this `a<b` `e>0`] guess d . note d=this
    show ?thesis
      apply rule
      apply rule
      apply (rule d)
      apply safe
      apply (subst dist_commute)
      unfolding `x = a` dist_norm
      apply (rule d(2)[rule_format])
      apply auto
      done
  next
    assume "x = b"
    have "b \<le> b" ..
    from indefinite_integral_continuous_left[OF assms(1) `a<b` this `e>0`] guess d . note d=this
    show ?thesis
      apply rule
      apply rule
      apply (rule d)
      apply safe
      apply (subst dist_commute)
      unfolding `x = b` dist_norm
      apply (rule d(2)[rule_format])
      apply auto
      done
  next
    assume "a < x \<and> x < b"
    then have xl: "a < x" "x \<le> b" and xr: "a \<le> x" "x < b"
      by auto
    from indefinite_integral_continuous_left [OF assms(1) xl `e>0`] guess d1 . note d1=this
    from indefinite_integral_continuous_right[OF assms(1) xr `e>0`] guess d2 . note d2=this
    show ?thesis
      apply (rule_tac x="min d1 d2" in exI)
    proof safe
      show "0 < min d1 d2"
        using d1 d2 by auto
      fix y
      assume "y \<in> {a .. b}" and "dist y x < min d1 d2"
      then show "dist (integral {a .. y} f) (integral {a .. x} f) < e"
        apply (subst dist_commute)
        apply (cases "y < x")
        unfolding dist_norm
        apply (rule d1(2)[rule_format])
        defer
        apply (rule d2(2)[rule_format])
        unfolding not_less
        apply (auto simp add: field_simps)
        done
    qed
  qed
qed


subsection {* This doesn't directly involve integration, but that gives an easy proof. *}

lemma has_derivative_zero_unique_strong_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite k"
    and "continuous_on {a .. b} f"
    and "f a = y"
    and "\<forall>x\<in>({a .. b} - k). (f has_derivative (\<lambda>h. 0)) (at x within {a .. b})" "x \<in> {a .. b}"
  shows "f x = y"
proof -
  have ab: "a \<le> b"
    using assms by auto
  have *: "a \<le> x"
    using assms(5) by auto
  have "((\<lambda>x. 0\<Colon>'a) has_integral f x - f a) {a .. x}"
    apply (rule fundamental_theorem_of_calculus_interior_strong[OF assms(1) *])
    apply (rule continuous_on_subset[OF assms(2)])
    defer
    apply safe
    unfolding has_vector_derivative_def
    apply (subst has_derivative_within_open[symmetric])
    apply assumption
    apply (rule open_greaterThanLessThan)
    apply (rule has_derivative_within_subset[where s="{a .. b}"])
    using assms(4) assms(5)
    apply (auto simp: mem_box)
    done
  note this[unfolded *]
  note has_integral_unique[OF has_integral_0 this]
  then show ?thesis
    unfolding assms by auto
qed


subsection {* Generalize a bit to any convex set. *}

lemma has_derivative_zero_unique_strong_convex:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "convex s"
    and "finite k"
    and "continuous_on s f"
    and "c \<in> s"
    and "f c = y"
    and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x \<in> s"
  shows "f x = y"
proof -
  {
    presume *: "x \<noteq> c \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      unfolding assms(5)[symmetric]
      apply auto
      done
  }
  assume "x \<noteq> c"
  note conv = assms(1)[unfolded convex_alt,rule_format]
  have as1: "continuous_on {0 ..1} (f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x))"
    apply (rule continuous_intros)+
    apply (rule continuous_on_subset[OF assms(3)])
    apply safe
    apply (rule conv)
    using assms(4,7)
    apply auto
    done
  have *: "\<And>t xa. (1 - t) *\<^sub>R c + t *\<^sub>R x = (1 - xa) *\<^sub>R c + xa *\<^sub>R x \<Longrightarrow> t = xa"
  proof -
    case goal1
    then have "(t - xa) *\<^sub>R x = (t - xa) *\<^sub>R c"
      unfolding scaleR_simps by (auto simp add: algebra_simps)
    then show ?case
      using `x \<noteq> c` by auto
  qed
  have as2: "finite {t. ((1 - t) *\<^sub>R c + t *\<^sub>R x) \<in> k}"
    using assms(2)
    apply (rule finite_surj[where f="\<lambda>z. SOME t. (1-t) *\<^sub>R c + t *\<^sub>R x = z"])
    apply safe
    unfolding image_iff
    apply rule
    defer
    apply assumption
    apply (rule sym)
    apply (rule some_equality)
    defer
    apply (drule *)
    apply auto
    done
  have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x)) 1 = y"
    apply (rule has_derivative_zero_unique_strong_interval[OF as2 as1, of ])
    unfolding o_def
    using assms(5)
    defer
    apply -
    apply rule
  proof -
    fix t
    assume as: "t \<in> {0 .. 1} - {t. (1 - t) *\<^sub>R c + t *\<^sub>R x \<in> k}"
    have *: "c - t *\<^sub>R c + t *\<^sub>R x \<in> s - k"
      apply safe
      apply (rule conv[unfolded scaleR_simps])
      using `x \<in> s` `c \<in> s` as
      by (auto simp add: algebra_simps)
    have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x) has_derivative (\<lambda>x. 0) \<circ> (\<lambda>z. (0 - z *\<^sub>R c) + z *\<^sub>R x))
      (at t within {0 .. 1})"
      apply (intro derivative_eq_intros)
      apply simp_all
      apply (simp add: field_simps)
      unfolding scaleR_simps
      apply (rule has_derivative_within_subset,rule assms(6)[rule_format])
      apply (rule *)
      apply safe
      apply (rule conv[unfolded scaleR_simps])
      using `x \<in> s` `c \<in> s`
      apply auto
      done
    then show "((\<lambda>xa. f ((1 - xa) *\<^sub>R c + xa *\<^sub>R x)) has_derivative (\<lambda>h. 0)) (at t within {0 .. 1})"
      unfolding o_def .
  qed auto
  then show ?thesis
    by auto
qed


text {* Also to any open connected set with finite set of exceptions. Could
 generalize to locally convex set with limpt-free set of exceptions. *}

lemma has_derivative_zero_unique_strong_connected:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected s"
    and "open s"
    and "finite k"
    and "continuous_on s f"
    and "c \<in> s"
    and "f c = y"
    and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x\<in>s"
  shows "f x = y"
proof -
  have "{x \<in> s. f x \<in> {y}} = {} \<or> {x \<in> s. f x \<in> {y}} = s"
    apply (rule assms(1)[unfolded connected_clopen,rule_format])
    apply rule
    defer
    apply (rule continuous_closed_in_preimage[OF assms(4) closed_singleton])
    apply (rule open_openin_trans[OF assms(2)])
    unfolding open_contains_ball
  proof safe
    fix x
    assume "x \<in> s"
    from assms(2)[unfolded open_contains_ball,rule_format,OF this] guess e .. note e=conjunctD2[OF this]
    show "\<exists>e>0. ball x e \<subseteq> {xa \<in> s. f xa \<in> {f x}}"
      apply rule
      apply rule
      apply (rule e)
    proof safe
      fix y
      assume y: "y \<in> ball x e"
      then show "y \<in> s"
        using e by auto
      show "f y = f x"
        apply (rule has_derivative_zero_unique_strong_convex[OF convex_ball])
        apply (rule assms)
        apply (rule continuous_on_subset)
        apply (rule assms)
        apply (rule e)+
        apply (subst centre_in_ball)
        apply (rule e)
        apply rule
        apply safe
        apply (rule has_derivative_within_subset)
        apply (rule assms(7)[rule_format])
        using y e
        apply auto
        done
    qed
  qed
  then show ?thesis
    using `x \<in> s` `f c = y` `c \<in> s` by auto
qed

lemma has_derivative_zero_connected_constant:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected s"
      and "open s"
      and "finite k"
      and "continuous_on s f"
      and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    obtains c where "\<And>x. x \<in> s \<Longrightarrow> f(x) = c"
proof (cases "s = {}")
  case True
  then show ?thesis
by (metis empty_iff that)
next
  case False
  then obtain c where "c \<in> s"
    by (metis equals0I)
  then show ?thesis
    by (metis has_derivative_zero_unique_strong_connected assms that)
qed


subsection {* Integrating characteristic function of an interval *}

lemma has_integral_restrict_open_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> box c d then f x else 0) has_integral i) (cbox a b)"
proof -
  def g \<equiv> "\<lambda>x. if x \<in>box c d then f x else 0"
  {
    presume *: "cbox c d \<noteq> {} \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
    proof -
      case goal1
      then have *: "box c d = {}"
        by (metis bot.extremum_uniqueI box_subset_cbox)
      show ?thesis
        using assms(1)
        unfolding *
        using goal1
        by auto
    qed
  }
  assume "cbox c d \<noteq> {}"
  from partial_division_extend_1[OF assms(2) this] guess p . note p=this
  note mon = monoidal_lifted[OF monoidal_monoid]
  note operat = operative_division[OF this operative_integral p(1), symmetric]
  let ?P = "(if g integrable_on cbox a b then Some (integral (cbox a b) g) else None) = Some i"
  {
    presume "?P"
    then have "g integrable_on cbox a b \<and> integral (cbox a b) g = i"
      apply -
      apply cases
      apply (subst(asm) if_P)
      apply assumption
      apply auto
      done
    then show ?thesis
      using integrable_integral
      unfolding g_def
      by auto
  }

  note iterate_eq_neutral[OF mon,unfolded neutral_lifted[OF monoidal_monoid]]
  note * = this[unfolded neutral_add]
  have iterate:"iterate (lifted op +) (p - {cbox c d})
    (\<lambda>i. if g integrable_on i then Some (integral i g) else None) = Some 0"
  proof (rule *, rule)
    case goal1
    then have "x \<in> p"
      by auto
    note div = division_ofD(2-5)[OF p(1) this]
    from div(3) guess u v by (elim exE) note uv=this
    have "interior x \<inter> interior (cbox c d) = {}"
      using div(4)[OF p(2)] goal1 by auto
    then have "(g has_integral 0) x"
      unfolding uv
      apply -
      apply (rule has_integral_spike_interior[where f="\<lambda>x. 0"])
      unfolding g_def interior_cbox
      apply auto
      done
    then show ?case
      by auto
  qed

  have *: "p = insert (cbox c d) (p - {cbox c d})"
    using p by auto
  have **: "g integrable_on cbox c d"
    apply (rule integrable_spike_interior[where f=f])
    unfolding g_def
    defer
    apply (rule has_integral_integrable)
    using assms(1)
    apply auto
    done
  moreover
  have "integral (cbox c d) g = i"
    apply (rule has_integral_unique[OF _ assms(1)])
    apply (rule has_integral_spike_interior[where f=g])
    defer
    apply (rule integrable_integral[OF **])
    unfolding g_def
    apply auto
    done
  ultimately show ?P
    unfolding operat
    apply (subst *)
    apply (subst iterate_insert)
    apply rule+
    unfolding iterate
    defer
    apply (subst if_not_P)
    defer
    using p
    apply auto
    done
qed

lemma has_integral_restrict_closed_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b)"
proof -
  note has_integral_restrict_open_subinterval[OF assms]
  note * = has_integral_spike[OF negligible_frontier_interval _ this]
  show ?thesis
    apply (rule *[of c d])
    using box_subset_cbox[of c d]
    apply auto
    done
qed

lemma has_integral_restrict_closed_subintervals_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b) \<longleftrightarrow> (f has_integral i) (cbox c d)"
  (is "?l = ?r")
proof (cases "cbox c d = {}")
  case False
  let ?g = "\<lambda>x. if x \<in> cbox c d then f x else 0"
  show ?thesis
    apply rule
    defer
    apply (rule has_integral_restrict_closed_subinterval[OF _ assms])
    apply assumption
  proof -
    assume ?l
    then have "?g integrable_on cbox c d"
      apply -
      apply (rule integrable_subinterval[OF _ assms])
      apply auto
      done
    then have *: "f integrable_on cbox c d"
      apply -
      apply (rule integrable_eq)
      apply auto
      done
    then have "i = integral (cbox c d) f"
      apply -
      apply (rule has_integral_unique)
      apply (rule `?l`)
      apply (rule has_integral_restrict_closed_subinterval[OF _ assms])
      apply auto
      done
    then show ?r
      using * by auto
  qed
qed auto


text {* Hence we can apply the limit process uniformly to all integrals. *}

lemma has_integral':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> s then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - i) < e))"
  (is "?l \<longleftrightarrow> (\<forall>e>0. ?r e)")
proof -
  {
    presume *: "\<exists>a b. s = cbox a b \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      apply (subst has_integral_alt)
      apply auto
      done
  }
  assume "\<exists>a b. s = cbox a b"
  then guess a b by (elim exE) note s=this
  from bounded_cbox[of a b, unfolded bounded_pos] guess B ..
  note B = conjunctD2[OF this,rule_format] show ?thesis
    apply safe
  proof -
    fix e :: real
    assume ?l and "e > 0"
    show "?r e"
      apply (rule_tac x="B+1" in exI)
      apply safe
      defer
      apply (rule_tac x=i in exI)
    proof
      fix c d :: 'n
      assume as: "ball 0 (B+1) \<subseteq> cbox c d"
      then show "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) (cbox c d)"
        unfolding s
        apply -
        apply (rule has_integral_restrict_closed_subinterval)
        apply (rule `?l`[unfolded s])
        apply safe
        apply (drule B(2)[rule_format])
        unfolding subset_eq
        apply (erule_tac x=x in ballE)
        apply (auto simp add: dist_norm)
        done
    qed (insert B `e>0`, auto)
  next
    assume as: "\<forall>e>0. ?r e"
    from this[rule_format,OF zero_less_one] guess C .. note C=conjunctD2[OF this,rule_format]
    def c \<equiv> "(\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)::'n"
    def d \<equiv> "(\<Sum>i\<in>Basis. max B C *\<^sub>R i)::'n"
    have c_d: "cbox a b \<subseteq> cbox c d"
      apply safe
      apply (drule B(2))
      unfolding mem_box
    proof
      case goal1
      then show ?case
        using Basis_le_norm[OF `i\<in>Basis`, of x]
        unfolding c_def d_def
        by (auto simp add: field_simps setsum_negf)
    qed
    have "ball 0 C \<subseteq> cbox c d"
      apply safe
      unfolding mem_box mem_ball dist_norm
    proof
      case goal1
      then show ?case
        using Basis_le_norm[OF `i\<in>Basis`, of x]
        unfolding c_def d_def
        by (auto simp: setsum_negf)
    qed
    from C(2)[OF this] have "\<exists>y. (f has_integral y) (cbox a b)"
      unfolding has_integral_restrict_closed_subintervals_eq[OF c_d,symmetric]
      unfolding s
      by auto
    then guess y .. note y=this

    have "y = i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "0 < norm (y - i)"
        by auto
      from as[rule_format,OF this] guess C ..  note C=conjunctD2[OF this,rule_format]
      def c \<equiv> "(\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)::'n"
      def d \<equiv> "(\<Sum>i\<in>Basis. max B C *\<^sub>R i)::'n"
      have c_d: "cbox a b \<subseteq> cbox c d"
        apply safe
        apply (drule B(2))
        unfolding mem_box
      proof
        case goal1
        then show ?case
          using Basis_le_norm[of i x]
          unfolding c_def d_def
          by (auto simp add: field_simps setsum_negf)
      qed
      have "ball 0 C \<subseteq> cbox c d"
        apply safe
        unfolding mem_box mem_ball dist_norm
      proof
        case goal1
        then show ?case
          using Basis_le_norm[of i x]
          unfolding c_def d_def
          by (auto simp: setsum_negf)
      qed
      note C(2)[OF this] then guess z .. note z = conjunctD2[OF this, unfolded s]
      note this[unfolded has_integral_restrict_closed_subintervals_eq[OF c_d]]
      then have "z = y" and "norm (z - i) < norm (y - i)"
        apply -
        apply (rule has_integral_unique[OF _ y(1)])
        apply assumption
        apply assumption
        done
      then show False
        by auto
    qed
    then show ?l
      using y
      unfolding s
      by auto
  qed
qed

lemma has_integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "(g has_integral j) s"
    and "\<forall>x\<in>s. f x \<le> g x"
  shows "i \<le> j"
  using has_integral_component_le[OF _ assms(1-2), of 1]
  using assms(3)
  by auto

lemma integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. f x \<le> g x"
  shows "integral s f \<le> integral s g"
  by (rule has_integral_le[OF assms(1,2)[unfolded has_integral_integral] assms(3)])

lemma has_integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "\<forall>x\<in>s. 0 \<le> f x"
  shows "0 \<le> i"
  using has_integral_component_nonneg[of 1 f i s]
  unfolding o_def
  using assms
  by auto

lemma integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s"
    and "\<forall>x\<in>s. 0 \<le> f x"
  shows "0 \<le> integral s f"
  by (rule has_integral_nonneg[OF assms(1)[unfolded has_integral_integral] assms(2)])


text {* Hence a general restriction property. *}

lemma has_integral_restrict[simp]:
  assumes "s \<subseteq> t"
  shows "((\<lambda>x. if x \<in> s then f x else (0::'a::banach)) has_integral i) t \<longleftrightarrow> (f has_integral i) s"
proof -
  have *: "\<And>x. (if x \<in> t then if x \<in> s then f x else 0 else 0) =  (if x\<in>s then f x else 0)"
    using assms by auto
  show ?thesis
    apply (subst(2) has_integral')
    apply (subst has_integral')
    unfolding *
    apply rule
    done
qed

lemma has_integral_restrict_univ:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) UNIV \<longleftrightarrow> (f has_integral i) s"
  by auto

lemma has_integral_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
    and "s \<subseteq> t"
    and "(f has_integral i) s"
  shows "(f has_integral i) t"
proof -
  have "(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. if x \<in> t then f x else 0)"
    apply rule
    using assms(1-2)
    apply auto
    done
  then show ?thesis
    using assms(3)
    apply (subst has_integral_restrict_univ[symmetric])
    apply (subst(asm) has_integral_restrict_univ[symmetric])
    apply auto
    done
qed

lemma integrable_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
    and "s \<subseteq> t"
    and "f integrable_on s"
  shows "f integrable_on t"
  using assms
  unfolding integrable_on_def
  by (auto intro:has_integral_on_superset)

lemma integral_restrict_univ[intro]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<Longrightarrow> integral UNIV (\<lambda>x. if x \<in> s then f x else 0) = integral s f"
  apply (rule integral_unique)
  unfolding has_integral_restrict_univ
  apply auto
  done

lemma integrable_restrict_univ:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(\<lambda>x. if x \<in> s then f x else 0) integrable_on UNIV \<longleftrightarrow> f integrable_on s"
  unfolding integrable_on_def
  by auto

lemma negligible_on_intervals: "negligible s \<longleftrightarrow> (\<forall>a b. negligible(s \<inter> cbox a b))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?r
  show ?l
    unfolding negligible_def
  proof safe
    case goal1
    show ?case
      apply (rule has_integral_negligible[OF `?r`[rule_format,of a b]])
      unfolding indicator_def
      apply auto
      done
  qed
qed auto

lemma has_integral_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
  shows "(f has_integral y) s \<longleftrightarrow> (f has_integral y) t"
  unfolding has_integral_restrict_univ[symmetric,of f]
  apply (rule has_integral_spike_eq[OF assms])
  by (auto split: split_if_asm)

lemma has_integral_spike_set[dest]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
    and "(f has_integral y) s"
  shows "(f has_integral y) t"
  using assms has_integral_spike_set_eq
  by auto

lemma integrable_spike_set[dest]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
    and "f integrable_on s"
  shows "f integrable_on t"
  using assms(2)
  unfolding integrable_on_def
  unfolding has_integral_spike_set_eq[OF assms(1)] .

lemma integrable_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
  shows "f integrable_on s \<longleftrightarrow> f integrable_on t"
  apply rule
  apply (rule_tac[!] integrable_spike_set)
  using assms
  apply auto
  done

(*lemma integral_spike_set:
 "\<forall>f:real^M->real^N g s t.
        negligible(s DIFF t \<union> t DIFF s)
        \<longrightarrow> integral s f = integral t f"
qed  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

lemma has_integral_interior:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (interior s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

lemma has_integral_closure:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (closure s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;*)


subsection {* More lemmas that are useful later *}

lemma has_integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes k: "k \<in> Basis"
    and as: "s \<subseteq> t" "(f has_integral i) s" "(f has_integral j) t" "\<forall>x\<in>t. 0 \<le> f(x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  note has_integral_restrict_univ[symmetric, of f]
  note as(2-3)[unfolded this] note * = has_integral_component_le[OF k this]
  show ?thesis
    apply (rule *)
    using as(1,4)
    apply auto
    done
qed

lemma has_integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "(f has_integral i) s"
    and "(f has_integral j) t"
    and "\<forall>x\<in>t. 0 \<le> f x"
  shows "i \<le> j"
  using has_integral_subset_component_le[OF _ assms(1), of 1 f i j]
  using assms
  by auto

lemma integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "k \<in> Basis"
    and "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x \<bullet> k"
  shows "(integral s f)\<bullet>k \<le> (integral t f)\<bullet>k"
  apply (rule has_integral_subset_component_le)
  using assms
  apply auto
  done

lemma integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x"
  shows "integral s f \<le> integral t f"
  apply (rule has_integral_subset_le)
  using assms
  apply auto
  done

lemma has_integral_alt':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow> (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e)"
  (is "?l = ?r")
proof
  assume ?r
  show ?l
    apply (subst has_integral')
    apply safe
  proof -
    case goal1
    from `?r`[THEN conjunct2,rule_format,OF this] guess B .. note B=conjunctD2[OF this]
    show ?case
      apply rule
      apply rule
      apply (rule B)
      apply safe
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0)" in exI)
      apply (drule B(2)[rule_format])
      using integrable_integral[OF `?r`[THEN conjunct1,rule_format]]
      apply auto
      done
  qed
next
  assume ?l note as = this[unfolded has_integral'[of f],rule_format]
  let ?f = "\<lambda>x. if x \<in> s then f x else 0"
  show ?r
  proof safe
    fix a b :: 'n
    from as[OF zero_less_one] guess B .. note B=conjunctD2[OF this,rule_format]
    let ?a = "\<Sum>i\<in>Basis. min (a\<bullet>i) (-B) *\<^sub>R i::'n"
    let ?b = "\<Sum>i\<in>Basis. max (b\<bullet>i) B *\<^sub>R i::'n"
    show "?f integrable_on cbox a b"
    proof (rule integrable_subinterval[of _ ?a ?b])
      have "ball 0 B \<subseteq> cbox ?a ?b"
        apply safe
        unfolding mem_ball mem_box dist_norm
      proof
        case goal1
        then show ?case using Basis_le_norm[of i x]
          by (auto simp add:field_simps)
      qed
      from B(2)[OF this] guess z .. note conjunct1[OF this]
      then show "?f integrable_on cbox ?a ?b"
        unfolding integrable_on_def by auto
      show "cbox a b \<subseteq> cbox ?a ?b"
        apply safe
        unfolding mem_box
        apply rule
        apply (erule_tac x=i in ballE)
        apply auto
        done
    qed

    fix e :: real
    assume "e > 0"
    from as[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
      apply rule
      apply rule
      apply (rule B)
      apply safe
    proof -
      case goal1
      from B(2)[OF this] guess z .. note z=conjunctD2[OF this]
      from integral_unique[OF this(1)] show ?case
        using z(2) by auto
    qed
  qed
qed


subsection {* Continuity of the integral (for a 1-dimensional interval). *}

lemma integrable_alt:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<longleftrightarrow>
    (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
    norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) -
      integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e)"
  (is "?l = ?r")
proof
  assume ?l
  then guess y unfolding integrable_on_def .. note this[unfolded has_integral_alt'[of f]]
  note y=conjunctD2[OF this,rule_format]
  show ?r
    apply safe
    apply (rule y)
  proof -
    case goal1
    then have "e/2 > 0"
      by auto
    from y(2)[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show ?case
      apply rule
      apply rule
      apply (rule B)
      apply safe
    proof -
      case goal1
      show ?case
        apply (rule norm_triangle_half_l)
        using B(2)[OF goal1(1)] B(2)[OF goal1(2)]
        apply auto
        done
    qed
  qed
next
  assume ?r
  note as = conjunctD2[OF this,rule_format]
  let ?cube = "\<lambda>n. cbox (\<Sum>i\<in>Basis. - real n *\<^sub>R i::'n) (\<Sum>i\<in>Basis. real n *\<^sub>R i)"
  have "Cauchy (\<lambda>n. integral (?cube n) (\<lambda>x. if x \<in> s then f x else 0))"
  proof (unfold Cauchy_def, safe)
    case goal1
    from as(2)[OF this] guess B .. note B = conjunctD2[OF this,rule_format]
    from real_arch_simple[of B] guess N .. note N = this
    {
      fix n
      assume n: "n \<ge> N"
      have "ball 0 B \<subseteq> ?cube n"
        apply safe
        unfolding mem_ball mem_box dist_norm
      proof
        case goal1
        then show ?case
          using Basis_le_norm[of i x] `i\<in>Basis`
          using n N
          by (auto simp add: field_simps setsum_negf)
      qed
    }
    then show ?case
      apply -
      apply (rule_tac x=N in exI)
      apply safe
      unfolding dist_norm
      apply (rule B(2))
      apply auto
      done
  qed
  from this[unfolded convergent_eq_cauchy[symmetric]] guess i ..
  note i = this[THEN LIMSEQ_D]

  show ?l unfolding integrable_on_def has_integral_alt'[of f]
    apply (rule_tac x=i in exI)
    apply safe
    apply (rule as(1)[unfolded integrable_on_def])
  proof -
    case goal1
    then have *: "e/2 > 0" by auto
    from i[OF this] guess N .. note N =this[rule_format]
    from as(2)[OF *] guess B .. note B=conjunctD2[OF this,rule_format]
    let ?B = "max (real N) B"
    show ?case
      apply (rule_tac x="?B" in exI)
    proof safe
      show "0 < ?B"
        using B(1) by auto
      fix a b :: 'n
      assume ab: "ball 0 ?B \<subseteq> cbox a b"
      from real_arch_simple[of ?B] guess n .. note n=this
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
        apply (rule norm_triangle_half_l)
        apply (rule B(2))
        defer
        apply (subst norm_minus_commute)
        apply (rule N[of n])
      proof safe
        show "N \<le> n"
          using n by auto
        fix x :: 'n
        assume x: "x \<in> ball 0 B"
        then have "x \<in> ball 0 ?B"
          by auto
        then show "x \<in> cbox a b"
          using ab by blast
        show "x \<in> ?cube n"
          using x
          unfolding mem_box mem_ball dist_norm
          apply -
        proof
          case goal1
          then show ?case
            using Basis_le_norm[of i x] `i \<in> Basis`
            using n
            by (auto simp add: field_simps setsum_negf)
        qed
      qed
    qed
  qed
qed

lemma integrable_altD:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
  shows "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
    and "\<And>e. e > 0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e"
  using assms[unfolded integrable_alt[of f]] by auto

lemma integrable_on_subcbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "cbox a b \<subseteq> s"
  shows "f integrable_on cbox a b"
  apply (rule integrable_eq)
  defer
  apply (rule integrable_altD(1)[OF assms(1)])
  using assms(2)
  apply auto
  done


subsection {* A straddling criterion for integrability *}

lemma integrable_straddle_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g  h i j. (g has_integral i) (cbox a b) \<and> (h has_integral j) (cbox a b) \<and>
    norm (i - j) < e \<and> (\<forall>x\<in>cbox a b. (g x) \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on cbox a b"
proof (subst integrable_cauchy, safe)
  case goal1
  then have e: "e/3 > 0"
    by auto
  note assms[rule_format,OF this]
  then guess g h i j by (elim exE conjE) note obt = this
  from obt(1)[unfolded has_integral[of g], rule_format, OF e] guess d1 .. note d1=conjunctD2[OF this,rule_format]
  from obt(2)[unfolded has_integral[of h], rule_format, OF e] guess d2 .. note d2=conjunctD2[OF this,rule_format]
  show ?case
    apply (rule_tac x="\<lambda>x. d1 x \<inter> d2 x" in exI)
    apply (rule conjI gauge_inter d1 d2)+
    unfolding fine_inter
  proof safe
    have **: "\<And>i j g1 g2 h1 h2 f1 f2. g1 - h2 \<le> f1 - f2 \<Longrightarrow> f1 - f2 \<le> h1 - g2 \<Longrightarrow>
      abs (i - j) < e / 3 \<Longrightarrow> abs (g2 - i) < e / 3 \<Longrightarrow>  abs (g1 - i) < e / 3 \<Longrightarrow>
      abs (h2 - j) < e / 3 \<Longrightarrow> abs (h1 - j) < e / 3 \<Longrightarrow> abs (f1 - f2) < e"
    using `e > 0` by arith
    case goal1
    note tagged_division_ofD(2-4) note * = this[OF goal1(1)] this[OF goal1(4)]

    have "(\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R g x) \<ge> 0"
      and "0 \<le> (\<Sum>(x, k)\<in>p2. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)"
      and "(\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R g x) \<ge> 0"
      and "0 \<le> (\<Sum>(x, k)\<in>p1. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x)"
      unfolding setsum_subtractf[symmetric]
      apply -
      apply (rule_tac[!] setsum_nonneg)
      apply safe
      unfolding real_scaleR_def right_diff_distrib[symmetric]
      apply (rule_tac[!] mult_nonneg_nonneg)
    proof -
      fix a b
      assume ab: "(a, b) \<in> p1"
      show "0 \<le> content b"
        using *(3)[OF ab]
        apply safe
        apply (rule content_pos_le)
        done
      then show "0 \<le> content b" .
      show "0 \<le> f a - g a" "0 \<le> h a - f a"
        using *(1-2)[OF ab]
        using obt(4)[rule_format,of a]
        by auto
    next
      fix a b
      assume ab: "(a, b) \<in> p2"
      show "0 \<le> content b"
        using *(6)[OF ab]
        apply safe
        apply (rule content_pos_le)
        done
      then show "0 \<le> content b" .
      show "0 \<le> f a - g a" and "0 \<le> h a - f a"
        using *(4-5)[OF ab] using obt(4)[rule_format,of a] by auto
    qed
    then show ?case
      apply -
      unfolding real_norm_def
      apply (rule **)
      defer
      defer
      unfolding real_norm_def[symmetric]
      apply (rule obt(3))
      apply (rule d1(2)[OF conjI[OF goal1(4,5)]])
      apply (rule d1(2)[OF conjI[OF goal1(1,2)]])
      apply (rule d2(2)[OF conjI[OF goal1(4,6)]])
      apply (rule d2(2)[OF conjI[OF goal1(1,3)]])
      apply auto
      done
  qed
qed

lemma integrable_straddle:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g h i j. (g has_integral i) s \<and> (h has_integral j) s \<and>
    norm (i - j) < e \<and> (\<forall>x\<in>s. g x \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on s"
proof -
  have "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
  proof (rule integrable_straddle_interval, safe)
    case goal1
    then have *: "e/4 > 0"
      by auto
    from assms[rule_format,OF this] guess g h i j by (elim exE conjE) note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]]
    note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *]
    from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]]
    note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *]
    from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    def c \<equiv> "\<Sum>i\<in>Basis. min (a\<bullet>i) (- (max B1 B2)) *\<^sub>R i::'n"
    def d \<equiv> "\<Sum>i\<in>Basis. max (b\<bullet>i) (max B1 B2) *\<^sub>R i::'n"
    have *: "ball 0 B1 \<subseteq> cbox c d" "ball 0 B2 \<subseteq> cbox c d"
      apply safe
      unfolding mem_ball mem_box dist_norm
      apply (rule_tac[!] ballI)
    proof -
      case goal1
      then show ?case using Basis_le_norm[of i x]
        unfolding c_def d_def by auto
    next
      case goal2
      then show ?case using Basis_le_norm[of i x]
        unfolding c_def d_def by auto
    qed
    have **:" \<And>ch cg ag ah::real. norm (ah - ag) \<le> norm (ch - cg) \<Longrightarrow> norm (cg - i) < e / 4 \<Longrightarrow>
      norm (ch - j) < e / 4 \<Longrightarrow> norm (ag - ah) < e"
      using obt(3)
      unfolding real_norm_def
      by arith
    show ?case
      apply (rule_tac x="\<lambda>x. if x \<in> s then g x else 0" in exI)
      apply (rule_tac x="\<lambda>x. if x \<in> s then h x else 0" in exI)
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)" in exI)
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then h x else 0)" in exI)
      apply safe
      apply (rule_tac[1-2] integrable_integral,rule g)
      apply (rule h)
      apply (rule **[OF _ B1(2)[OF *(1)] B2(2)[OF *(2)]])
    proof -
      have *: "\<And>x f g. (if x \<in> s then f x else 0) - (if x \<in> s then g x else 0) =
        (if x \<in> s then f x - g x else (0::real))"
        by auto
      note ** = abs_of_nonneg[OF integral_nonneg[OF integrable_sub, OF h g]]
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then h x else 0) -
          integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)) \<le>
        norm (integral (cbox c d) (\<lambda>x. if x \<in> s then h x else 0) -
          integral (cbox c d) (\<lambda>x. if x \<in> s then g x else 0))"
        unfolding integral_sub[OF h g,symmetric] real_norm_def
        apply (subst **)
        defer
        apply (subst **)
        defer
        apply (rule has_integral_subset_le)
        defer
        apply (rule integrable_integral integrable_sub h g)+
      proof safe
        fix x
        assume "x \<in> cbox a b"
        then show "x \<in> cbox c d"
          unfolding mem_box c_def d_def
          apply -
          apply rule
          apply (erule_tac x=i in ballE)
          apply auto
          done
      qed (insert obt(4), auto)
    qed (insert obt(4), auto)
  qed
  note interv = this

  show ?thesis
    unfolding integrable_alt[of f]
    apply safe
    apply (rule interv)
  proof -
    case goal1
    then have *: "e/3 > 0"
      by auto
    from assms[rule_format,OF this] guess g h i j by (elim exE conjE) note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]]
    note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *]
    from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]]
    note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *]
    from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    show ?case
      apply (rule_tac x="max B1 B2" in exI)
      apply safe
      apply (rule max.strict_coboundedI1)
      apply (rule B1)
    proof -
      fix a b c d :: 'n
      assume as: "ball 0 (max B1 B2) \<subseteq> cbox a b" "ball 0 (max B1 B2) \<subseteq> cbox c d"
      have **: "ball 0 B1 \<subseteq> ball (0::'n) (max B1 B2)" "ball 0 B2 \<subseteq> ball (0::'n) (max B1 B2)"
        by auto
      have *: "\<And>ga gc ha hc fa fc::real.
        abs (ga - i) < e / 3 \<and> abs (gc - i) < e / 3 \<and> abs (ha - j) < e / 3 \<and>
        abs (hc - j) < e / 3 \<and> abs (i - j) < e / 3 \<and> ga \<le> fa \<and> fa \<le> ha \<and> gc \<le> fc \<and> fc \<le> hc \<Longrightarrow>
        abs (fa - fc) < e"
        by (simp add: abs_real_def split: split_if_asm)
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)
        (\<lambda>x. if x \<in> s then f x else 0)) < e"
        unfolding real_norm_def
        apply (rule *)
        apply safe
        unfolding real_norm_def[symmetric]
        apply (rule B1(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(1))
        apply (rule B1(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(2))
        apply (rule B2(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(1))
        apply (rule B2(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(2))
        apply (rule obt)
        apply (rule_tac[!] integral_le)
        using obt
        apply (auto intro!: h g interv)
        done
    qed
  qed
qed


subsection {* Adding integrals over several sets *}

lemma has_integral_union:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "(f has_integral i) s"
    and "(f has_integral j) t"
    and "negligible (s \<inter> t)"
  shows "(f has_integral (i + j)) (s \<union> t)"
proof -
  note * = has_integral_restrict_univ[symmetric, of f]
  show ?thesis
    unfolding *
    apply (rule has_integral_spike[OF assms(3)])
    defer
    apply (rule has_integral_add[OF assms(1-2)[unfolded *]])
    apply auto
    done
qed

lemma has_integral_unions:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "finite t"
    and "\<forall>s\<in>t. (f has_integral (i s)) s"
    and "\<forall>s\<in>t. \<forall>s'\<in>t. s \<noteq> s' \<longrightarrow> negligible (s \<inter> s')"
  shows "(f has_integral (setsum i t)) (\<Union>t)"
proof -
  note * = has_integral_restrict_univ[symmetric, of f]
  have **: "negligible (\<Union>((\<lambda>(a,b). a \<inter> b) ` {(a,b). a \<in> t \<and> b \<in> {y. y \<in> t \<and> a \<noteq> y}}))"
    apply (rule negligible_unions)
    apply (rule finite_imageI)
    apply (rule finite_subset[of _ "t \<times> t"])
    defer
    apply (rule finite_cartesian_product[OF assms(1,1)])
    using assms(3)
    apply auto
    done
  note assms(2)[unfolded *]
  note has_integral_setsum[OF assms(1) this]
  then show ?thesis unfolding * apply-apply(rule has_integral_spike[OF **]) defer apply assumption
  proof safe
    case goal1
    then show ?case
    proof (cases "x \<in> \<Union>t")
      case True
      then guess s unfolding Union_iff .. note s=this
      then have *: "\<forall>b\<in>t. x \<in> b \<longleftrightarrow> b = s"
        using goal1(3) by blast
      show ?thesis
        unfolding if_P[OF True]
        apply (rule trans)
        defer
        apply (rule setsum_cong2)
        apply (subst *)
        apply assumption
        apply (rule refl)
        unfolding setsum_delta[OF assms(1)]
        using s
        apply auto
        done
    qed auto
  qed
qed


text {* In particular adding integrals over a division, maybe not of an interval. *}

lemma has_integral_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>k\<in>d. (f has_integral (i k)) k"
  shows "(f has_integral (setsum i d)) s"
proof -
  note d = division_ofD[OF assms(1)]
  show ?thesis
    unfolding d(6)[symmetric]
    apply (rule has_integral_unions)
    apply (rule d assms)+
    apply rule
    apply rule
    apply rule
  proof -
    case goal1
    from d(4)[OF this(1)] d(4)[OF this(2)] guess a c b d by (elim exE) note obt=this
    from d(5)[OF goal1] show ?case
      unfolding obt interior_cbox
      apply -
      apply (rule negligible_subset[of "(cbox a b-box a b) \<union> (cbox c d-box c d)"])
      apply (rule negligible_union negligible_frontier_interval)+
      apply auto
      done
  qed
qed

lemma integral_combine_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>k\<in>d. f integrable_on k"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply (rule integral_unique)
  apply (rule has_integral_combine_division[OF assms(1)])
  using assms(2)
  unfolding has_integral_integral
  apply assumption
  done

lemma has_integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "d division_of k"
    and "k \<subseteq> s"
  shows "(f has_integral (setsum (\<lambda>i. integral i f) d)) k"
  apply (rule has_integral_combine_division[OF assms(2)])
  apply safe
  unfolding has_integral_integral[symmetric]
proof -
  case goal1
  from division_ofD(2,4)[OF assms(2) this]
  show ?case
    apply safe
    apply (rule integrable_on_subcbox)
    apply (rule assms)
    using assms(3)
    apply auto
    done
qed

lemma integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "d division_of s"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply (rule integral_unique)
  apply (rule has_integral_combine_division_topdown)
  using assms
  apply auto
  done

lemma integrable_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>i\<in>d. f integrable_on i"
  shows "f integrable_on s"
  using assms(2)
  unfolding integrable_on_def
  by (metis has_integral_combine_division[OF assms(1)])

lemma integrable_on_subdivision:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of i"
    and "f integrable_on s"
    and "i \<subseteq> s"
  shows "f integrable_on i"
  apply (rule integrable_combine_division assms)+
proof safe
  case goal1
  note division_ofD(2,4)[OF assms(1) this]
  then show ?case
    apply safe
    apply (rule integrable_on_subcbox[OF assms(2)])
    using assms(3)
    apply auto
    done
qed


subsection {* Also tagged divisions *}

lemma has_integral_combine_tagged_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of s"
    and "\<forall>(x,k) \<in> p. (f has_integral (i k)) k"
  shows "(f has_integral (setsum (\<lambda>(x,k). i k) p)) s"
proof -
  have *: "(f has_integral (setsum (\<lambda>k. integral k f) (snd ` p))) s"
    apply (rule has_integral_combine_division)
    apply (rule division_of_tagged_division[OF assms(1)])
    using assms(2)
    unfolding has_integral_integral[symmetric]
    apply safe
    apply auto
    done
  then show ?thesis
    apply -
    apply (rule subst[where P="\<lambda>i. (f has_integral i) s"])
    defer
    apply assumption
    apply (rule trans[of _ "setsum (\<lambda>(x,k). integral k f) p"])
    apply (subst eq_commute)
    apply (rule setsum_over_tagged_division_lemma[OF assms(1)])
    apply (rule integral_null)
    apply assumption
    apply (rule setsum_cong2)
    using assms(2)
    apply auto
    done
qed

lemma integral_combine_tagged_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>(x,k)\<in>p. f integrable_on k"
  shows "integral (cbox a b) f = setsum (\<lambda>(x,k). integral k f) p"
  apply (rule integral_unique)
  apply (rule has_integral_combine_tagged_division[OF assms(1)])
  using assms(2)
  apply auto
  done

lemma has_integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "(f has_integral (setsum (\<lambda>(x,k). integral k f) p)) (cbox a b)"
  apply (rule has_integral_combine_tagged_division[OF assms(2)])
proof safe
  case goal1
  note tagged_division_ofD(3-4)[OF assms(2) this]
  then show ?case
    using integrable_subinterval[OF assms(1)] by blast
qed

lemma integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "integral (cbox a b) f = setsum (\<lambda>(x,k). integral k f) p"
  apply (rule integral_unique)
  apply (rule has_integral_combine_tagged_division_topdown)
  using assms
  apply auto
  done


subsection {* Henstock's lemma *}

lemma henstock_lemma_part1:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and "(\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - integral(cbox a b) f) < e)"
    and p: "p tagged_partial_division_of (cbox a b)" "d fine p"
  shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x - integral k f) p) \<le> e"
  (is "?x \<le> e")
proof -
  { presume "\<And>k. 0<k \<Longrightarrow> ?x \<le> e + k" then show ?thesis by (blast intro: field_le_epsilon) }
  fix k :: real
  assume k: "k > 0"
  note p' = tagged_partial_division_ofD[OF p(1)]
  have "\<Union>(snd ` p) \<subseteq> cbox a b"
    using p'(3) by fastforce
  note partial_division_of_tagged_division[OF p(1)] this
  from partial_division_extend_interval[OF this] guess q . note q=this and q' = division_ofD[OF this(2)]
  def r \<equiv> "q - snd ` p"
  have "snd ` p \<inter> r = {}"
    unfolding r_def by auto
  have r: "finite r"
    using q' unfolding r_def by auto

  have "\<forall>i\<in>r. \<exists>p. p tagged_division_of i \<and> d fine p \<and>
    norm (setsum (\<lambda>(x,j). content j *\<^sub>R f x) p - integral i f) < k / (real (card r) + 1)"
  proof safe
    case goal1
    then have i: "i \<in> q"
      unfolding r_def by auto
    from q'(4)[OF this] guess u v by (elim exE) note uv=this
    have *: "k / (real (card r) + 1) > 0" using k by simp
    have "f integrable_on cbox u v"
      apply (rule integrable_subinterval[OF assms(1)])
      using q'(2)[OF i]
      unfolding uv
      apply auto
      done
    note integrable_integral[OF this, unfolded has_integral[of f]]
    from this[rule_format,OF *] guess dd .. note dd=conjunctD2[OF this,rule_format]
    note gauge_inter[OF `gauge d` dd(1)]
    from fine_division_exists[OF this,of u v] guess qq .
    then show ?case
      apply (rule_tac x=qq in exI)
      using dd(2)[of qq]
      unfolding fine_inter uv
      apply auto
      done
  qed
  from bchoice[OF this] guess qq .. note qq=this[rule_format]

  let ?p = "p \<union> \<Union>(qq ` r)"
  have "norm ((\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) - integral (cbox a b) f) < e"
    apply (rule assms(4)[rule_format])
  proof
    show "d fine ?p"
      apply (rule fine_union)
      apply (rule p)
      apply (rule fine_unions)
      using qq
      apply auto
      done
    note * = tagged_partial_division_of_union_self[OF p(1)]
    have "p \<union> \<Union>(qq ` r) tagged_division_of \<Union>(snd ` p) \<union> \<Union>r"
    proof (rule tagged_division_union[OF * tagged_division_unions])
      show "finite r"
        by fact
      case goal2
      then show ?case
        using qq by auto
    next
      case goal3
      then show ?case
        apply rule
        apply rule
        apply rule
        apply(rule q'(5))
        unfolding r_def
        apply auto
        done
    next
      case goal4
      then show ?case
        apply (rule inter_interior_unions_intervals)
        apply fact
        apply rule
        apply rule
        apply (rule q')
        defer
        apply rule
        apply (subst Int_commute)
        apply (rule inter_interior_unions_intervals)
        apply (rule finite_imageI)
        apply (rule p')
        apply rule
        defer
        apply rule
        apply (rule q')
        using q(1) p'
        unfolding r_def
        apply auto
        done
    qed
    moreover have "\<Union>(snd ` p) \<union> \<Union>r = cbox a b" and "{qq i |i. i \<in> r} = qq ` r"
      unfolding Union_Un_distrib[symmetric] r_def
      using q
      by auto
    ultimately show "?p tagged_division_of (cbox a b)"
      by fastforce
  qed

  then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>\<Union>(qq ` r). content k *\<^sub>R f x) -
    integral (cbox a b) f) < e"
    apply (subst setsum_Un_zero[symmetric])
    apply (rule p')
    prefer 3
    apply assumption
    apply rule
    apply (rule finite_imageI)
    apply (rule r)
    apply safe
    apply (drule qq)
  proof -
    fix x l k
    assume as: "(x, l) \<in> p" "(x, l) \<in> qq k" "k \<in> r"
    note qq[OF this(3)]
    note tagged_division_ofD(3,4)[OF conjunct1[OF this] as(2)]
    from this(2) guess u v by (elim exE) note uv=this
    have "l\<in>snd ` p" unfolding image_iff apply(rule_tac x="(x,l)" in bexI) using as by auto
    then have "l \<in> q" "k \<in> q" "l \<noteq> k"
      using as(1,3) q(1) unfolding r_def by auto
    note q'(5)[OF this]
    then have "interior l = {}"
      using interior_mono[OF `l \<subseteq> k`] by blast
    then show "content l *\<^sub>R f x = 0"
      unfolding uv content_eq_0_interior[symmetric] by auto
  qed auto

  then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x))
    (qq ` r) - integral (cbox a b) f) < e"
    apply (subst (asm) setsum_UNION_zero)
    prefer 4
    apply assumption
    apply (rule finite_imageI)
    apply fact
    unfolding split_paired_all split_conv image_iff
    defer
    apply (erule bexE)+
  proof -
    fix x m k l T1 T2
    assume "(x, m) \<in> T1" "(x, m) \<in> T2" "T1 \<noteq> T2" "k \<in> r" "l \<in> r" "T1 = qq k" "T2 = qq l"
    note as = this(1-5)[unfolded this(6-)]
    note kl = tagged_division_ofD(3,4)[OF qq[THEN conjunct1]]
    from this(2)[OF as(4,1)] guess u v by (elim exE) note uv=this
    have *: "interior (k \<inter> l) = {}"
      unfolding interior_inter
      apply (rule q')
      using as
      unfolding r_def
      apply auto
      done
    have "interior m = {}"
      unfolding subset_empty[symmetric]
      unfolding *[symmetric]
      apply (rule interior_mono)
      using kl(1)[OF as(4,1)] kl(1)[OF as(5,2)]
      apply auto
      done
    then show "content m *\<^sub>R f x = 0"
      unfolding uv content_eq_0_interior[symmetric]
      by auto
  qed (insert qq, auto)

  then have **: "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x) \<circ> qq) r -
    integral (cbox a b) f) < e"
    apply (subst (asm) setsum_reindex_nonzero)
    apply fact
    apply (rule setsum_0')
    apply rule
    unfolding split_paired_all split_conv
    defer
    apply assumption
  proof -
    fix k l x m
    assume as: "k \<in> r" "l \<in> r" "k \<noteq> l" "qq k = qq l" "(x, m) \<in> qq k"
    note tagged_division_ofD(6)[OF qq[THEN conjunct1]]
    from this[OF as(1)] this[OF as(2)] show "content m *\<^sub>R f x = 0"
      using as(3) unfolding as by auto
  qed

  have *: "\<And>ir ip i cr cp. norm ((cp + cr) - i) < e \<Longrightarrow> norm(cr - ir) < k \<Longrightarrow>
    ip + ir = i \<Longrightarrow> norm (cp - ip) \<le> e + k"
  proof -
    case goal1
    then show ?case
      using norm_triangle_le[of "cp + cr - i" "- (cr - ir)"]
      unfolding goal1(3)[symmetric] norm_minus_cancel
      by (auto simp add: algebra_simps)
  qed

  have "?x =  norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p. integral k f))"
    unfolding split_def setsum_subtractf ..
  also have "\<dots> \<le> e + k"
    apply (rule *[OF **, where ir="setsum (\<lambda>k. integral k f) r"])
  proof -
    case goal2
    have *: "(\<Sum>(x, k)\<in>p. integral k f) = (\<Sum>k\<in>snd ` p. integral k f)"
      apply (subst setsum_reindex_nonzero)
      apply fact
      unfolding split_paired_all snd_conv split_def o_def
    proof -
      fix x l y m
      assume as: "(x, l) \<in> p" "(y, m) \<in> p" "(x, l) \<noteq> (y, m)" "l = m"
      from p'(4)[OF as(1)] guess u v by (elim exE) note uv=this
      show "integral l f = 0"
        unfolding uv
        apply (rule integral_unique)
        apply (rule has_integral_null)
        unfolding content_eq_0_interior
        using p'(5)[OF as(1-3)]
        unfolding uv as(4)[symmetric]
        apply auto
        done
    qed auto
    show ?case
      unfolding integral_combine_division_topdown[OF assms(1) q(2)] * r_def
      apply (rule setsum_Un_disjoint'[symmetric])
      using q(1) q'(1) p'(1)
      apply auto
      done
  next
    case goal1
    have *: "k * real (card r) / (1 + real (card r)) < k"
      using k by (auto simp add: field_simps)
    show ?case
      apply (rule le_less_trans[of _ "setsum (\<lambda>x. k / (real (card r) + 1)) r"])
      unfolding setsum_subtractf[symmetric]
      apply (rule setsum_norm_le)
      apply rule
      apply (drule qq)
      defer
      unfolding divide_inverse setsum_left_distrib[symmetric]
      unfolding divide_inverse[symmetric]
      using *
      apply (auto simp add: field_simps real_eq_of_nat)
      done
  qed
  finally show "?x \<le> e + k" .
qed

lemma henstock_lemma_part2:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and "\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - integral (cbox a b) f) < e"
    and "p tagged_partial_division_of (cbox a b)"
    and "d fine p"
  shows "setsum (\<lambda>(x,k). norm (content k *\<^sub>R f x - integral k f)) p \<le> 2 * real (DIM('n)) * e"
  unfolding split_def
  apply (rule setsum_norm_allsubsets_bound)
  defer
  apply (rule henstock_lemma_part1[unfolded split_def,OF assms(1-3)])
  apply safe
  apply (rule assms[rule_format,unfolded split_def])
  defer
  apply (rule tagged_partial_division_subset)
  apply (rule assms)
  apply assumption
  apply (rule fine_subset)
  apply assumption
  apply (rule assms)
  using assms(5)
  apply auto
  done

lemma henstock_lemma:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "e > 0"
  obtains d where "gauge d"
    and "\<forall>p. p tagged_partial_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      setsum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p < e"
proof -
  have *: "e / (2 * (real DIM('n) + 1)) > 0" using assms(2) by simp
  from integrable_integral[OF assms(1),unfolded has_integral[of f],rule_format,OF this]
  guess d .. note d = conjunctD2[OF this]
  show thesis
    apply (rule that)
    apply (rule d)
  proof safe
    case goal1
    note * = henstock_lemma_part2[OF assms(1) * d this]
    show ?case
      apply (rule le_less_trans[OF *])
      using `e > 0`
      apply (auto simp add: field_simps)
      done
  qed
qed


subsection {* Geometric progression *}

text {* FIXME: Should one or more of these theorems be moved to @{file
"~~/src/HOL/Set_Interval.thy"}, alongside @{text geometric_sum}? *}

lemma sum_gp_basic:
  fixes x :: "'a::ring_1"
  shows "(1 - x) * setsum (\<lambda>i. x^i) {0 .. n} = (1 - x^(Suc n))"
proof -
  def y \<equiv> "1 - x"
  have "y * (\<Sum>i=0..n. (1 - y) ^ i) = 1 - (1 - y) ^ Suc n"
    by (induct n) (simp_all add: algebra_simps)
  then show ?thesis
    unfolding y_def by simp
qed

lemma sum_gp_multiplied:
  assumes mn: "m \<le> n"
  shows "((1::'a::{field}) - x) * setsum (op ^ x) {m..n} = x^m - x^ Suc n"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{0..(n - m)}"
  from mn have mn': "n - m \<ge> 0"
    by arith
  let ?f = "op + m"
  have i: "inj_on ?f ?S"
    unfolding inj_on_def by auto
  have f: "?f ` ?S = {m..n}"
    using mn
    apply (auto simp add: image_iff Bex_def)
    apply presburger
    done
  have th: "op ^ x o op + m = (\<lambda>i. x^m * x^i)"
    by (rule ext) (simp add: power_add power_mult)
  from setsum_reindex[OF i, of "op ^ x", unfolded f th setsum_right_distrib[symmetric]]
  have "?lhs = x^m * ((1 - x) * setsum (op ^ x) {0..n - m})"
    by simp
  then show ?thesis
    unfolding sum_gp_basic
    using mn
    by (simp add: field_simps power_add[symmetric])
qed

lemma sum_gp:
  "setsum (op ^ (x::'a::{field})) {m .. n} =
    (if n < m then 0
     else if x = 1 then of_nat ((n + 1) - m)
     else (x^ m - x^ (Suc n)) / (1 - x))"
proof -
  {
    assume nm: "n < m"
    then have ?thesis by simp
  }
  moreover
  {
    assume "\<not> n < m"
    then have nm: "m \<le> n"
      by arith
    {
      assume x: "x = 1"
      then have ?thesis
        by simp
    }
    moreover
    {
      assume x: "x \<noteq> 1"
      then have nz: "1 - x \<noteq> 0"
        by simp
      from sum_gp_multiplied[OF nm, of x] nz have ?thesis
        by (simp add: field_simps)
    }
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed

lemma sum_gp_offset:
  "setsum (op ^ (x::'a::{field})) {m .. m+n} =
    (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  unfolding sum_gp[of x m "m + n"] power_Suc
  by (simp add: field_simps power_add)


subsection {* Monotone convergence (bounded interval first) *}

lemma monotone_convergence_interval:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on cbox a b"
    and "\<forall>k. \<forall>x\<in>cbox a b.(f k x) \<le> f (Suc k) x"
    and "\<forall>x\<in>cbox a b. ((\<lambda>k. f k x) ---> g x) sequentially"
    and "bounded {integral (cbox a b) (f k) | k . k \<in> UNIV}"
  shows "g integrable_on cbox a b \<and> ((\<lambda>k. integral (cbox a b) (f k)) ---> integral (cbox a b) g) sequentially"
proof (cases "content (cbox a b) = 0")
  case True
  show ?thesis
    using integrable_on_null[OF True]
    unfolding integral_null[OF True]
    using tendsto_const
    by auto
next
  case False
  have fg: "\<forall>x\<in>cbox a b. \<forall> k. (f k x) \<bullet> 1 \<le> (g x) \<bullet> 1"
  proof safe
    case goal1
    note assms(3)[rule_format,OF this]
    note * = Lim_component_ge[OF this trivial_limit_sequentially]
    show ?case
      apply (rule *)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply -
      apply (rule transitive_stepwise_le)
      using assms(2)[rule_format,OF goal1]
      apply auto
      done
  qed
  have "\<exists>i. ((\<lambda>k. integral (cbox a b) (f k)) ---> i) sequentially"
    apply (rule bounded_increasing_convergent)
    defer
    apply rule
    apply (rule integral_le)
    apply safe
    apply (rule assms(1-2)[rule_format])+
    using assms(4)
    apply auto
    done
  then guess i .. note i=this
  have i': "\<And>k. (integral(cbox a b) (f k)) \<le> i\<bullet>1"
    apply (rule Lim_component_ge)
    apply (rule i)
    apply (rule trivial_limit_sequentially)
    unfolding eventually_sequentially
    apply (rule_tac x=k in exI)
    apply (rule transitive_stepwise_le)
    prefer 3
    unfolding inner_simps real_inner_1_right
    apply (rule integral_le)
    apply (rule assms(1-2)[rule_format])+
    using assms(2)
    apply auto
    done

  have "(g has_integral i) (cbox a b)"
    unfolding has_integral
  proof safe
    case goal1
    note e=this
    then have "\<forall>k. (\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f k x) - integral (cbox a b) (f k)) < e / 2 ^ (k + 2)))"
      apply -
      apply rule
      apply (rule assms(1)[unfolded has_integral_integral has_integral,rule_format])
      apply auto
      done
    from choice[OF this] guess c .. note c=conjunctD2[OF this[rule_format],rule_format]

    have "\<exists>r. \<forall>k\<ge>r. 0 \<le> i\<bullet>1 - (integral (cbox a b) (f k)) \<and> i\<bullet>1 - (integral (cbox a b) (f k)) < e / 4"
    proof -
      case goal1
      have "e/4 > 0"
        using e by auto
      from LIMSEQ_D [OF i this] guess r ..
      then show ?case
        apply (rule_tac x=r in exI)
        apply rule
        apply (erule_tac x=k in allE)
      proof -
        case goal1
        then show ?case
          using i'[of k] by auto
      qed
    qed
    then guess r .. note r=conjunctD2[OF this[rule_format]]

    have "\<forall>x\<in>cbox a b. \<exists>n\<ge>r. \<forall>k\<ge>n. 0 \<le> (g x)\<bullet>1 - (f k x)\<bullet>1 \<and>
      (g x)\<bullet>1 - (f k x)\<bullet>1 < e / (4 * content(cbox a b))"
    proof
      case goal1
      have "e / (4 * content (cbox a b)) > 0"
        using `e>0` False content_pos_le[of a b] by auto
      from assms(3)[rule_format, OF goal1, THEN LIMSEQ_D, OF this]
      guess n .. note n=this
      then show ?case
        apply (rule_tac x="n + r" in exI)
        apply safe
        apply (erule_tac[2-3] x=k in allE)
        unfolding dist_real_def
        using fg[rule_format,OF goal1]
        apply (auto simp add: field_simps)
        done
    qed
    from bchoice[OF this] guess m .. note m=conjunctD2[OF this[rule_format],rule_format]
    def d \<equiv> "\<lambda>x. c (m x) x"

    show ?case
      apply (rule_tac x=d in exI)
    proof safe
      show "gauge d"
        using c(1) unfolding gauge_def d_def by auto
    next
      fix p
      assume p: "p tagged_division_of (cbox a b)" "d fine p"
      note p'=tagged_division_ofD[OF p(1)]
      have "\<exists>a. \<forall>x\<in>p. m (fst x) \<le> a"
        by (metis finite_imageI finite_nat_set_iff_bounded_le p'(1) rev_image_eqI)
      then guess s .. note s=this
      have *: "\<forall>a b c d. norm(a - b) \<le> e / 4 \<and> norm(b - c) < e / 2 \<and>
        norm (c - d) < e / 4 \<longrightarrow> norm (a - d) < e"
      proof safe
        case goal1
        then show ?case
          using norm_triangle_lt[of "a - b" "b - c" "3* e/4"]
            norm_triangle_lt[of "a - b + (b - c)" "c - d" e]
          unfolding norm_minus_cancel
          by (auto simp add: algebra_simps)
      qed
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - i) < e"
        apply (rule *[rule_format,where
          b="\<Sum>(x, k)\<in>p. content k *\<^sub>R f (m x) x" and c="\<Sum>(x, k)\<in>p. integral k (f (m x))"])
      proof safe
        case goal1
        show ?case
          apply (rule order_trans[of _ "\<Sum>(x, k)\<in>p. content k * (e / (4 * content (cbox a b)))"])
          unfolding setsum_subtractf[symmetric]
          apply (rule order_trans)
          apply (rule norm_setsum)
          apply (rule setsum_mono)
          unfolding split_paired_all split_conv
          unfolding split_def setsum_left_distrib[symmetric] scaleR_diff_right[symmetric]
          unfolding additive_content_tagged_division[OF p(1), unfolded split_def]
        proof -
          fix x k
          assume xk: "(x, k) \<in> p"
          then have x: "x \<in> cbox a b"
            using p'(2-3)[OF xk] by auto
          from p'(4)[OF xk] guess u v by (elim exE) note uv=this
          show "norm (content k *\<^sub>R (g x - f (m x) x)) \<le> content k * (e / (4 * content (cbox a b)))"
            unfolding norm_scaleR uv
            unfolding abs_of_nonneg[OF content_pos_le]
            apply (rule mult_left_mono)
            using m(2)[OF x,of "m x"]
            apply auto
            done
        qed (insert False, auto)

      next
        case goal2
        show ?case
          apply (rule le_less_trans[of _ "norm (\<Sum>j = 0..s.
            \<Sum>(x, k)\<in>{xk\<in>p. m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x)))"])
          apply (subst setsum_group)
          apply fact
          apply (rule finite_atLeastAtMost)
          defer
          apply (subst split_def)+
          unfolding setsum_subtractf
          apply rule
        proof -
          show "norm (\<Sum>j = 0..s. \<Sum>(x, k)\<in>{xk \<in> p.
            m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x))) < e / 2"
            apply (rule le_less_trans[of _ "setsum (\<lambda>i. e / 2^(i+2)) {0..s}"])
            apply (rule setsum_norm_le)
          proof
            show "(\<Sum>i = 0..s. e / 2 ^ (i + 2)) < e / 2"
              unfolding power_add divide_inverse inverse_mult_distrib
              unfolding setsum_right_distrib[symmetric] setsum_left_distrib[symmetric]
              unfolding power_inverse sum_gp
              apply(rule mult_strict_left_mono[OF _ e])
              unfolding power2_eq_square
              apply auto
              done
            fix t
            assume "t \<in> {0..s}"
            show "norm (\<Sum>(x, k)\<in>{xk \<in> p. m (fst xk) = t}. content k *\<^sub>R f (m x) x -
              integral k (f (m x))) \<le> e / 2 ^ (t + 2)"
              apply (rule order_trans
                [of _ "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f t x - integral k (f t)) {xk \<in> p. m (fst xk) = t})"])
              apply (rule eq_refl)
              apply (rule arg_cong[where f=norm])
              apply (rule setsum_cong2)
              defer
              apply (rule henstock_lemma_part1)
              apply (rule assms(1)[rule_format])
              apply (simp add: e)
              apply safe
              apply (rule c)+
              apply rule
              apply assumption+
              apply (rule tagged_partial_division_subset[of p])
              apply (rule p(1)[unfolded tagged_division_of_def,THEN conjunct1])
              defer
              unfolding fine_def
              apply safe
              apply (drule p(2)[unfolded fine_def,rule_format])
              unfolding d_def
              apply auto
              done
          qed
        qed (insert s, auto)
      next
        case goal3
        note comb = integral_combine_tagged_division_topdown[OF assms(1)[rule_format] p(1)]
        have *: "\<And>sr sx ss ks kr::real. kr = sr \<longrightarrow> ks = ss \<longrightarrow>
          ks \<le> i \<and> sr \<le> sx \<and> sx \<le> ss \<and> 0 \<le> i\<bullet>1 - kr\<bullet>1 \<and> i\<bullet>1 - kr\<bullet>1 < e/4 \<longrightarrow> abs (sx - i) < e/4"
          by auto
        show ?case
          unfolding real_norm_def
          apply (rule *[rule_format])
          apply safe
          apply (rule comb[of r])
          apply (rule comb[of s])
          apply (rule i'[unfolded real_inner_1_right])
          apply (rule_tac[1-2] setsum_mono)
          unfolding split_paired_all split_conv
          apply (rule_tac[1-2] integral_le[OF ])
        proof safe
          show "0 \<le> i\<bullet>1 - (integral (cbox a b) (f r))\<bullet>1"
            using r(1) by auto
          show "i\<bullet>1 - (integral (cbox a b) (f r))\<bullet>1 < e / 4"
            using r(2) by auto
          fix x k
          assume xk: "(x, k) \<in> p"
          from p'(4)[OF this] guess u v by (elim exE) note uv=this
          show "f r integrable_on k"
            and "f s integrable_on k"
            and "f (m x) integrable_on k"
            and "f (m x) integrable_on k"
            unfolding uv
            apply (rule_tac[!] integrable_on_subcbox[OF assms(1)[rule_format]])
            using p'(3)[OF xk]
            unfolding uv
            apply auto
            done
          fix y
          assume "y \<in> k"
          then have "y \<in> cbox a b"
            using p'(3)[OF xk] by auto
          then have *: "\<And>m. \<forall>n\<ge>m. f m y \<le> f n y"
            apply -
            apply (rule transitive_stepwise_le)
            using assms(2)
            apply auto
            done
          show "f r y \<le> f (m x) y" and "f (m x) y \<le> f s y"
            apply (rule_tac[!] *[rule_format])
            using s[rule_format,OF xk] m(1)[of x] p'(2-3)[OF xk]
            apply auto
            done
        qed
      qed
    qed
  qed note * = this

  have "integral (cbox a b) g = i"
    by (rule integral_unique) (rule *)
  then show ?thesis
    using i * by auto
qed

lemma monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"
    and "\<forall>k. \<forall>x\<in>s. (f k x) \<le> (f (Suc k) x)"
    and "\<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially"
    and "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof -
  have lem: "\<And>f::nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real.
    \<And>g s. \<forall>k.\<forall>x\<in>s. 0 \<le> f k x \<Longrightarrow> \<forall>k. (f k) integrable_on s \<Longrightarrow>
      \<forall>k. \<forall>x\<in>s. f k x \<le> f (Suc k) x \<Longrightarrow> \<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially \<Longrightarrow>
    bounded {integral s (f k)| k. True} \<Longrightarrow>
    g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
  proof -
    case goal1
    note assms=this[rule_format]
    have "\<forall>x\<in>s. \<forall>k. (f k x)\<bullet>1 \<le> (g x)\<bullet>1"
      apply safe
      apply (rule Lim_component_ge)
      apply (rule goal1(4)[rule_format])
      apply assumption
      apply (rule trivial_limit_sequentially)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply (rule transitive_stepwise_le)
      using goal1(3)
      apply auto
      done
    note fg=this[rule_format]

    have "\<exists>i. ((\<lambda>k. integral s (f k)) ---> i) sequentially"
      apply (rule bounded_increasing_convergent)
      apply (rule goal1(5))
      apply rule
      apply (rule integral_le)
      apply (rule goal1(2)[rule_format])+
      using goal1(3)
      apply auto
      done
    then guess i .. note i=this
    have "\<And>k. \<forall>x\<in>s. \<forall>n\<ge>k. f k x \<le> f n x"
      apply rule
      apply (rule transitive_stepwise_le)
      using goal1(3)
      apply auto
      done
    then have i': "\<forall>k. (integral s (f k))\<bullet>1 \<le> i\<bullet>1"
      apply -
      apply rule
      apply (rule Lim_component_ge)
      apply (rule i)
      apply (rule trivial_limit_sequentially)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply safe
      apply (rule integral_component_le)
      apply simp
      apply (rule goal1(2)[rule_format])+
      apply auto
      done

    note int = assms(2)[unfolded integrable_alt[of _ s],THEN conjunct1,rule_format]
    have ifif: "\<And>k t. (\<lambda>x. if x \<in> t then if x \<in> s then f k x else 0 else 0) =
      (\<lambda>x. if x \<in> t \<inter> s then f k x else 0)"
      by (rule ext) auto
    have int': "\<And>k a b. f k integrable_on cbox a b \<inter> s"
      apply (subst integrable_restrict_univ[symmetric])
      apply (subst ifif[symmetric])
      apply (subst integrable_restrict_univ)
      apply (rule int)
      done
    have "\<And>a b. (\<lambda>x. if x \<in> s then g x else 0) integrable_on cbox a b \<and>
      ((\<lambda>k. integral (cbox a b) (\<lambda>x. if x \<in> s then f k x else 0)) --->
      integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)) sequentially"
    proof (rule monotone_convergence_interval, safe)
      case goal1
      show ?case by (rule int)
    next
      case goal2
      then show ?case
        apply (cases "x \<in> s")
        using assms(3)
        apply auto
        done
    next
      case goal3
      then show ?case
        apply (cases "x \<in> s")
        using assms(4)
        apply auto
        done
    next
      case goal4
      note * = integral_nonneg
      have "\<And>k. norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f k x else 0)) \<le> norm (integral s (f k))"
        unfolding real_norm_def
        apply (subst abs_of_nonneg)
        apply (rule *[OF int])
        apply safe
        apply (case_tac "x \<in> s")
        apply (drule assms(1))
        prefer 3
        apply (subst abs_of_nonneg)
        apply (rule *[OF assms(2) goal1(1)[THEN spec]])
        apply (subst integral_restrict_univ[symmetric,OF int])
        unfolding ifif
        unfolding integral_restrict_univ[OF int']
        apply (rule integral_subset_le[OF _ int' assms(2)])
        using assms(1)
        apply auto
        done
      then show ?case
        using assms(5)
        unfolding bounded_iff
        apply safe
        apply (rule_tac x=aa in exI)
        apply safe
        apply (erule_tac x="integral s (f k)" in ballE)
        apply (rule order_trans)
        apply assumption
        apply auto
        done
    qed
    note g = conjunctD2[OF this]

    have "(g has_integral i) s"
      unfolding has_integral_alt'
      apply safe
      apply (rule g(1))
    proof -
      case goal1
      then have "e/4>0"
        by auto
      from LIMSEQ_D [OF i this] guess N .. note N=this
      note assms(2)[of N,unfolded has_integral_integral has_integral_alt'[of "f N"]]
      from this[THEN conjunct2,rule_format,OF `e/4>0`] guess B .. note B=conjunctD2[OF this]
      show ?case
        apply rule
        apply rule
        apply (rule B)
        apply safe
      proof -
        fix a b :: 'n
        assume ab: "ball 0 B \<subseteq> cbox a b"
        from `e > 0` have "e/2 > 0"
          by auto
        from LIMSEQ_D [OF g(2)[of a b] this] guess M .. note M=this
        have **: "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f N x else 0) - i) < e/2"
          apply (rule norm_triangle_half_l)
          using B(2)[rule_format,OF ab] N[rule_format,of N]
          apply -
          defer
          apply (subst norm_minus_commute)
          apply auto
          done
        have *: "\<And>f1 f2 g. abs (f1 - i) < e / 2 \<longrightarrow> abs (f2 - g) < e / 2 \<longrightarrow>
          f1 \<le> f2 \<longrightarrow> f2 \<le> i \<longrightarrow> abs (g - i) < e"
          unfolding real_inner_1_right by arith
        show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0) - i) < e"
          unfolding real_norm_def
          apply (rule *[rule_format])
          apply (rule **[unfolded real_norm_def])
          apply (rule M[rule_format,of "M + N",unfolded real_norm_def])
          apply (rule le_add1)
          apply (rule integral_le[OF int int])
          defer
          apply (rule order_trans[OF _ i'[rule_format,of "M + N",unfolded real_inner_1_right]])
        proof safe
          case goal2
          have "\<And>m. x \<in> s \<Longrightarrow> \<forall>n\<ge>m. (f m x)\<bullet>1 \<le> (f n x)\<bullet>1"
            apply (rule transitive_stepwise_le)
            using assms(3)
            apply auto
            done
          then show ?case
            by auto
        next
          case goal1
          show ?case
            apply (subst integral_restrict_univ[symmetric,OF int])
            unfolding ifif integral_restrict_univ[OF int']
            apply (rule integral_subset_le[OF _ int'])
            using assms
            apply auto
            done
        qed
      qed
    qed
    then show ?case
      apply safe
      defer
      apply (drule integral_unique)
      using i
      apply auto
      done
  qed

  have sub: "\<And>k. integral s (\<lambda>x. f k x - f 0 x) = integral s (f k) - integral s (f 0)"
    apply (subst integral_sub)
    apply (rule assms(1)[rule_format])+
    apply rule
    done
  have "\<And>x m. x \<in> s \<Longrightarrow> \<forall>n\<ge>m. f m x \<le> f n x"
    apply (rule transitive_stepwise_le)
    using assms(2)
    apply auto
    done
  note * = this[rule_format]
  have "(\<lambda>x. g x - f 0 x) integrable_on s \<and> ((\<lambda>k. integral s (\<lambda>x. f (Suc k) x - f 0 x)) --->
    integral s (\<lambda>x. g x - f 0 x)) sequentially"
    apply (rule lem)
    apply safe
  proof -
    case goal1
    then show ?case
      using *[of x 0 "Suc k"] by auto
  next
    case goal2
    then show ?case
      apply (rule integrable_sub)
      using assms(1)
      apply auto
      done
  next
    case goal3
    then show ?case
      using *[of x "Suc k" "Suc (Suc k)"] by auto
  next
    case goal4
    then show ?case
      apply -
      apply (rule tendsto_diff)
      using LIMSEQ_ignore_initial_segment[OF assms(3)[rule_format],of x 1]
      apply auto
      done
  next
    case goal5
    then show ?case
      using assms(4)
      unfolding bounded_iff
      apply safe
      apply (rule_tac x="a + norm (integral s (\<lambda>x. f 0 x))" in exI)
      apply safe
      apply (erule_tac x="integral s (\<lambda>x. f (Suc k) x)" in ballE)
      unfolding sub
      apply (rule order_trans[OF norm_triangle_ineq4])
      apply auto
      done
  qed
  note conjunctD2[OF this]
  note tendsto_add[OF this(2) tendsto_const[of "integral s (f 0)"]]
    integrable_add[OF this(1) assms(1)[rule_format,of 0]]
  then show ?thesis
    unfolding sub
    apply -
    apply rule
    defer
    apply (subst(asm) integral_sub)
    using assms(1)
    apply auto
    apply (rule LIMSEQ_imp_Suc)
    apply assumption
    done
qed

lemma monotone_convergence_decreasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"
    and "\<forall>k. \<forall>x\<in>s. f (Suc k) x \<le> f k x"
    and "\<forall>x\<in>s. ((\<lambda>k. f k x) ---> g x) sequentially"
    and "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof -
  note assm = assms[rule_format]
  have *: "{integral s (\<lambda>x. - f k x) |k. True} = op *\<^sub>R -1 ` {integral s (f k)| k. True}"
    apply safe
    unfolding image_iff
    apply (rule_tac x="integral s (f k)" in bexI)
    prefer 3
    apply (rule_tac x=k in exI)
    unfolding integral_neg[OF assm(1)]
    apply auto
    done
  have "(\<lambda>x. - g x) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. - f k x)) ---> integral s (\<lambda>x. - g x)) sequentially"
    apply (rule monotone_convergence_increasing)
    apply safe
    apply (rule integrable_neg)
    apply (rule assm)
    defer
    apply (rule tendsto_minus)
    apply (rule assm)
    apply assumption
    unfolding *
    apply (rule bounded_scaling)
    using assm
    apply auto
    done
  note * = conjunctD2[OF this]
  show ?thesis
    apply rule
    using integrable_neg[OF *(1)]
    defer
    using tendsto_minus[OF *(2)]
    unfolding integral_neg[OF assm(1)]
    unfolding integral_neg[OF *(1),symmetric]
    apply auto
    done
qed


subsection {* Absolute integrability (this is the same as Lebesgue integrability) *}

definition absolutely_integrable_on (infixr "absolutely'_integrable'_on" 46)
  where "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and> (\<lambda>x. (norm(f x))) integrable_on s"

lemma absolutely_integrable_onI[intro?]:
  "f integrable_on s \<Longrightarrow>
    (\<lambda>x. (norm(f x))) integrable_on s \<Longrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_onD[dest]:
  assumes "f absolutely_integrable_on s"
  shows "f integrable_on s"
    and "(\<lambda>x. norm (f x)) integrable_on s"
  using assms
  unfolding absolutely_integrable_on_def
  by auto

(*lemma absolutely_integrable_on_trans[simp]:
  fixes f::"'n::euclidean_space \<Rightarrow> real"
  shows "(vec1 o f) absolutely_integrable_on s \<longleftrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def o_def by auto*)

lemma integral_norm_bound_integral:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. norm (f x) \<le> g x"
  shows "norm (integral s f) \<le> integral s g"
proof -
  have *: "\<And>x y. (\<forall>e::real. 0 < e \<longrightarrow> x < y + e) \<longrightarrow> x \<le> y"
    apply safe
    apply (rule ccontr)
    apply (erule_tac x="x - y" in allE)
    apply auto
    done
  have "\<And>e sg dsa dia ig.
    norm sg \<le> dsa \<longrightarrow> abs (dsa - dia) < e / 2 \<longrightarrow> norm (sg - ig) < e / 2 \<longrightarrow> norm ig < dia + e"
  proof safe
    case goal1
    show ?case
      apply (rule le_less_trans[OF norm_triangle_sub[of ig sg]])
      apply (subst real_sum_of_halves[of e,symmetric])
      unfolding add_assoc[symmetric]
      apply (rule add_le_less_mono)
      defer
      apply (subst norm_minus_commute)
      apply (rule goal1)
      apply (rule order_trans[OF goal1(1)])
      using goal1(2)
      apply arith
      done
  qed
  note norm=this[rule_format]
  have lem: "\<And>f::'n \<Rightarrow> 'a. \<And>g a b. f integrable_on cbox a b \<Longrightarrow> g integrable_on cbox a b \<Longrightarrow>
    \<forall>x\<in>cbox a b. norm (f x) \<le> g x \<Longrightarrow> norm (integral(cbox a b) f) \<le> integral (cbox a b) g"
  proof (rule *[rule_format])
    case goal1
    then have *: "e/2 > 0"
      by auto
    from integrable_integral[OF goal1(1),unfolded has_integral[of f],rule_format,OF *]
    guess d1 .. note d1 = conjunctD2[OF this,rule_format]
    from integrable_integral[OF goal1(2),unfolded has_integral[of g],rule_format,OF *]
    guess d2 .. note d2 = conjunctD2[OF this,rule_format]
    note gauge_inter[OF d1(1) d2(1)]
    from fine_division_exists[OF this, of a b] guess p . note p=this
    show ?case
      apply (rule norm)
      defer
      apply (rule d2(2)[OF conjI[OF p(1)],unfolded real_norm_def])
      defer
      apply (rule d1(2)[OF conjI[OF p(1)]])
      defer
      apply (rule setsum_norm_le)
    proof safe
      fix x k
      assume "(x, k) \<in> p"
      note as = tagged_division_ofD(2-4)[OF p(1) this]
      from this(3) guess u v by (elim exE) note uv=this
      show "norm (content k *\<^sub>R f x) \<le> content k *\<^sub>R g x"
        unfolding uv norm_scaleR
        unfolding abs_of_nonneg[OF content_pos_le] real_scaleR_def
        apply (rule mult_left_mono)
        using goal1(3) as
        apply auto
        done
    qed (insert p[unfolded fine_inter], auto)
  qed

  { presume "\<And>e. 0 < e \<Longrightarrow> norm (integral s f) < integral s g + e"
    then show ?thesis by (rule *[rule_format]) auto }
  fix e :: real
  assume "e > 0"
  then have e: "e/2 > 0"
    by auto
  note assms(1)[unfolded integrable_alt[of f]] note f=this[THEN conjunct1,rule_format]
  note assms(2)[unfolded integrable_alt[of g]] note g=this[THEN conjunct1,rule_format]
  from integrable_integral[OF assms(1),unfolded has_integral'[of f],rule_format,OF e]
  guess B1 .. note B1=conjunctD2[OF this[rule_format],rule_format]
  from integrable_integral[OF assms(2),unfolded has_integral'[of g],rule_format,OF e]
  guess B2 .. note B2=conjunctD2[OF this[rule_format],rule_format]
  from bounded_subset_cbox[OF bounded_ball, of "0::'n" "max B1 B2"]
  guess a b by (elim exE) note ab=this[unfolded ball_max_Un]

  have "ball 0 B1 \<subseteq> cbox a b"
    using ab by auto
  from B1(2)[OF this] guess z .. note z=conjunctD2[OF this]
  have "ball 0 B2 \<subseteq> cbox a b"
    using ab by auto
  from B2(2)[OF this] guess w .. note w=conjunctD2[OF this]

  show "norm (integral s f) < integral s g + e"
    apply (rule norm)
    apply (rule lem[OF f g, of a b])
    unfolding integral_unique[OF z(1)] integral_unique[OF w(1)]
    defer
    apply (rule w(2)[unfolded real_norm_def])
    apply (rule z(2))
    apply safe
    apply (case_tac "x \<in> s")
    unfolding if_P
    apply (rule assms(3)[rule_format])
    apply auto
    done
qed

lemma integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. norm(f x) \<le> (g x)\<bullet>k"
  shows "norm (integral s f) \<le> (integral s g)\<bullet>k"
proof -
  have "norm (integral s f) \<le> integral s ((\<lambda>x. x \<bullet> k) \<circ> g)"
    apply (rule integral_norm_bound_integral[OF assms(1)])
    apply (rule integrable_linear[OF assms(2)])
    apply rule
    unfolding o_def
    apply (rule assms)
    done
  then show ?thesis
    unfolding o_def integral_component_eq[OF assms(2)] .
qed

lemma has_integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) s"
    and "(g has_integral j) s"
    and "\<forall>x\<in>s. norm (f x) \<le> (g x)\<bullet>k"
  shows "norm i \<le> j\<bullet>k"
  using integral_norm_bound_integral_component[of f s g k]
  unfolding integral_unique[OF assms(1)] integral_unique[OF assms(2)]
  using assms
  by auto

lemma absolutely_integrable_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on s"
  shows "norm (integral s f) \<le> integral s (\<lambda>x. norm (f x))"
  apply (rule integral_norm_bound_integral)
  using assms
  apply auto
  done

lemma absolutely_integrable_0[intro]:
  "(\<lambda>x. 0) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_cmul[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  using integrable_cmul[of f s c]
  using integrable_cmul[of "\<lambda>x. norm (f x)" s "abs c"]
  by auto

lemma absolutely_integrable_neg[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. -f(x)) absolutely_integrable_on s"
  apply (drule absolutely_integrable_cmul[where c="-1"])
  apply auto
  done

lemma absolutely_integrable_norm[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. norm (f x)) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_abs[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. abs(f x::real)) absolutely_integrable_on s"
  apply (drule absolutely_integrable_norm)
  unfolding real_norm_def
  apply assumption
  done

lemma absolutely_integrable_on_subinterval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f absolutely_integrable_on s \<Longrightarrow>
    cbox a b \<subseteq> s \<Longrightarrow> f absolutely_integrable_on cbox a b"
  unfolding absolutely_integrable_on_def
  by (metis integrable_on_subcbox)

lemma absolutely_integrable_bounded_variation:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on UNIV"
  obtains B where "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  apply (rule that[of "integral UNIV (\<lambda>x. norm (f x))"])
proof safe
  case goal1
  note d = division_ofD[OF this(2)]
  have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. integral i (\<lambda>x. norm (f x)))"
    apply (rule setsum_mono,rule absolutely_integrable_le)
    apply (drule d(4))
    apply safe
    apply (rule absolutely_integrable_on_subinterval[OF assms])
    apply auto
    done
  also have "\<dots> \<le> integral (\<Union>d) (\<lambda>x. norm (f x))"
    apply (subst integral_combine_division_topdown[OF _ goal1(2)])
    using integrable_on_subdivision[OF goal1(2)]
    using assms
    apply auto
    done
  also have "\<dots> \<le> integral UNIV (\<lambda>x. norm (f x))"
    apply (rule integral_subset_le)
    using integrable_on_subdivision[OF goal1(2)]
    using assms
    apply auto
    done
  finally show ?case .
qed

lemma helplemma:
  assumes "setsum (\<lambda>x. norm (f x - g x)) s < e"
    and "finite s"
  shows "abs (setsum (\<lambda>x. norm(f x)) s - setsum (\<lambda>x. norm(g x)) s) < e"
  unfolding setsum_subtractf[symmetric]
  apply (rule le_less_trans[OF setsum_abs])
  apply (rule le_less_trans[OF _ assms(1)])
  apply (rule setsum_mono)
  apply (rule norm_triangle_ineq3)
  done

lemma bounded_variation_absolutely_integrable_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on cbox a b"
    and *: "\<forall>d. d division_of (cbox a b) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
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
    apply rule
    apply (rule assms)
    apply rule
    apply (subst has_integral[of _ ?S])
  proof safe
    case goal1
    then have "?S - e / 2 < ?S" by simp
    then obtain d where d: "d division_of (cbox a b)" "?S - e / 2 < (\<Sum>k\<in>d. norm (integral k f))"
      unfolding less_cSUP_iff[OF D] by auto
    note d' = division_ofD[OF this(1)]

    have "\<forall>x. \<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
    proof
      case goal1
      have "\<exists>da>0. \<forall>xa\<in>\<Union>{i \<in> d. x \<notin> i}. da \<le> dist x xa"
        apply (rule separate_point_closed)
        apply (rule closed_Union)
        apply (rule finite_subset[OF _ d'(1)])
        apply safe
        apply (drule d'(4))
        apply auto
        done
      then show ?case
        apply safe
        apply (rule_tac x=da in exI)
        apply safe
        apply (erule_tac x=xa in ballE)
        apply auto
        done
    qed
    from choice[OF this] guess k .. note k=conjunctD2[OF this[rule_format],rule_format]

    have "e/2 > 0"
      using goal1 by auto
    from henstock_lemma[OF assms(1) this] guess g . note g=this[rule_format]
    let ?g = "\<lambda>x. g x \<inter> ball x (k x)"
    show ?case
      apply (rule_tac x="?g" in exI)
      apply safe
    proof -
      show "gauge ?g"
        using g(1)
        unfolding gauge_def
        using k(1)
        by auto
      fix p
      assume "p tagged_division_of (cbox a b)" and "?g fine p"
      note p = this(1) conjunctD2[OF this(2)[unfolded fine_inter]]
      note p' = tagged_division_ofD[OF p(1)]
      def p' \<equiv> "{(x,k) | x k. \<exists>i l. x \<in> i \<and> i \<in> d \<and> (x,l) \<in> p \<and> k = i \<inter> l}"
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
          unfolding inter_interval
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
            defer
            unfolding mem_Collect_eq
            apply (rule_tac x=x in exI)+
            apply (rule_tac x="i\<inter>l" in exI)
            apply safe
            apply (rule_tac x=i in exI)
            apply (rule_tac x=l in exI)
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
        apply (rule helplemma)
        using p''
        apply auto
        done

      have p'alt: "p' = {(x,(i \<inter> l)) | x i l. (x,l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}}"
      proof safe
        case goal2
        have "x \<in> i"
          using fineD[OF p(3) goal2(1)] k(2)[OF goal2(2), of x] goal2(4-)
          by auto
        then have "(x, i \<inter> l) \<in> p'"
          unfolding p'_def
          apply safe
          apply (rule_tac x=x in exI)
          apply (rule_tac x="i \<inter> l" in exI)
          apply safe
          using goal2
          apply auto
          done
        then show ?case
          using goal2(3) by auto
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
        apply (subst setsum_over_tagged_division_lemma[OF p'',of "\<lambda>k. norm (integral k f)"])
        unfolding norm_eq_zero
        apply (rule integral_null)
        apply assumption
        apply rule
        done
      note snd_p = division_ofD[OF division_of_tagged_division[OF p(1)]]

      have *: "\<And>sni sni' sf sf'. abs (sf' - sni') < e / 2 \<longrightarrow> ?S - e / 2 < sni \<and> sni' \<le> ?S \<and>
        sni \<le> sni' \<and> sf' = sf \<longrightarrow> abs (sf - ?S) < e"
        by arith
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format,OF **])
        apply safe
        apply(rule d(2))
      proof -
        case goal1 show ?case
          by (auto simp: sum_p' division_of_tagged_division[OF p''] D intro!: cSUP_upper)
      next
        case goal2
        have *: "{k \<inter> l | k l. k \<in> d \<and> l \<in> snd ` p} =
          (\<lambda>(k,l). k \<inter> l) ` {(k,l)|k l. k \<in> d \<and> l \<in> snd ` p}"
          by auto
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. \<Sum>l\<in>snd ` p. norm (integral (i \<inter> l) f))"
        proof (rule setsum_mono)
          case goal1
          note k=this
          from d'(4)[OF this] guess u v by (elim exE) note uv=this
          def d' \<equiv> "{cbox u v \<inter> l |l. l \<in> snd ` p \<and>  cbox u v \<inter> l \<noteq> {}}"
          note uvab = d'(2)[OF k[unfolded uv]]
          have "d' division_of cbox u v"
            apply (subst d'_def)
            apply (rule division_inter_1)
            apply (rule division_of_tagged_division[OF p(1)])
            apply (rule uvab)
            done
          then have "norm (integral k f) \<le> setsum (\<lambda>k. norm (integral k f)) d'"
            unfolding uv
            apply (subst integral_combine_division_topdown[of _ _ d'])
            apply (rule integrable_on_subcbox[OF assms(1) uvab])
            apply assumption
            apply (rule setsum_norm_le)
            apply auto
            done
          also have "\<dots> = (\<Sum>k\<in>{k \<inter> l |l. l \<in> snd ` p}. norm (integral k f))"
            apply (rule setsum_mono_zero_left)
            apply (subst simple_image)
            apply (rule finite_imageI)+
            apply fact
            unfolding d'_def uv
            apply blast
          proof
            case goal1
            then have "i \<in> {cbox u v \<inter> l |l. l \<in> snd ` p}"
              by auto
            from this[unfolded mem_Collect_eq] guess l .. note l=this
            then have "cbox u v \<inter> l = {}"
              using goal1 by auto
            then show ?case
              using l by auto
          qed
          also have "\<dots> = (\<Sum>l\<in>snd ` p. norm (integral (k \<inter> l) f))"
            unfolding simple_image
            apply (rule setsum_reindex_nonzero[unfolded o_def])
            apply (rule finite_imageI)
            apply (rule p')
          proof -
            case goal1
            have "interior (k \<inter> l) \<subseteq> interior (l \<inter> y)"
              apply (subst(2) interior_inter)
              apply (rule Int_greatest)
              defer
              apply (subst goal1(4))
              apply auto
              done
            then have *: "interior (k \<inter> l) = {}"
              using snd_p(5)[OF goal1(1-3)] by auto
            from d'(4)[OF k] snd_p(4)[OF goal1(1)] guess u1 v1 u2 v2 by (elim exE) note uv=this
            show ?case
              using *
              unfolding uv inter_interval content_eq_0_interior[symmetric]
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
        also have "\<dots> = (\<Sum>x\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (split op \<inter> x) f))"
          unfolding split_def ..
        also have "\<dots> = (\<Sum>k\<in>{i \<inter> l |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral k f))"
          unfolding *
          apply (rule setsum_reindex_nonzero[symmetric,unfolded o_def])
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
            unfolding uv inter_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed
        also have "\<dots> = (\<Sum>(x, k)\<in>p'. norm (integral k f))"
          unfolding sum_p'
          apply (rule setsum_mono_zero_right)
          apply (subst *)
          apply (rule finite_imageI[OF finite_product_dependent])
          apply fact
          apply (rule finite_imageI[OF p'(1)])
          apply safe
        proof -
          case goal2
          have "ia \<inter> b = {}"
            using goal2
            unfolding p'alt image_iff Bex_def not_ex
            apply (erule_tac x="(a, ia \<inter> b)" in allE)
            apply auto
            done
          then show ?case
            by auto
        next
          case goal1
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
        case goal3
        let ?S = "{(x, i \<inter> l) |x i l. (x, l) \<in> p \<and> i \<in> d}"
        have Sigma_alt: "\<And>s t. s \<times> t = {(i, j) |i j. i \<in> s \<and> j \<in> t}"
          by auto
        have *: "?S = (\<lambda>(xl,i). (fst xl, snd xl \<inter> i)) ` (p \<times> d)" (*{(xl,i)|xl i. xl\<in>p \<and> i\<in>d}"**)
          apply safe
          unfolding image_iff
          apply (rule_tac x="((x,l),i)" in bexI)
          apply auto
          done
        note pdfin = finite_cartesian_product[OF p'(1) d'(1)]
        have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x, k)\<in>?S. \<bar>content k\<bar> * norm (f x))"
          unfolding norm_scaleR
          apply (rule setsum_mono_zero_left)
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
          apply (subst setsum_reindex_nonzero)
          apply fact
          unfolding split_paired_all
          unfolding o_def split_def snd_conv fst_conv mem_Sigma_iff Pair_eq
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
            unfolding uv inter_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed safe
        also have "\<dots> = (\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x))"
          unfolding Sigma_alt
          apply (subst sum_sum_product[symmetric])
          apply (rule p')
          apply rule
          apply (rule d')
          apply (rule setsum_cong2)
          unfolding split_paired_all split_conv
        proof -
          fix x l
          assume as: "(x, l) \<in> p"
          note xl = p'(2-4)[OF this]
          from this(3) guess u v by (elim exE) note uv=this
          have "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar>) = (\<Sum>k\<in>d. content (k \<inter> cbox u v))"
            apply (rule setsum_cong2)
            apply (drule d'(4))
            apply safe
            apply (subst Int_commute)
            unfolding inter_interval uv
            apply (subst abs_of_nonneg)
            apply auto
            done
          also have "\<dots> = setsum content {k \<inter> cbox u v| k. k \<in> d}"
            unfolding simple_image
            apply (rule setsum_reindex_nonzero[unfolded o_def,symmetric])
            apply (rule d')
          proof -
            case goal1
            from d'(4)[OF this(1)] d'(4)[OF this(2)]
            guess u1 v1 u2 v2 by (elim exE) note uv=this
            have "{} = interior ((k \<inter> y) \<inter> cbox u v)"
              apply (subst interior_inter)
              using d'(5)[OF goal1(1-3)]
              apply auto
              done
            also have "\<dots> = interior (y \<inter> (k \<inter> cbox u v))"
              by auto
            also have "\<dots> = interior (k \<inter> cbox u v)"
              unfolding goal1(4) by auto
            finally show ?case
              unfolding uv inter_interval content_eq_0_interior ..
          qed
          also have "\<dots> = setsum content {cbox u v \<inter> k |k. k \<in> d \<and> cbox u v \<inter> k \<noteq> {}}"
            apply (rule setsum_mono_zero_right)
            unfolding simple_image
            apply (rule finite_imageI)
            apply (rule d')
            apply blast
            apply safe
            apply (rule_tac x=k in exI)
          proof -
            case goal1
            from d'(4)[OF this(1)] guess a b by (elim exE) note ab=this
            have "interior (k \<inter> cbox u v) \<noteq> {}"
              using goal1(2)
              unfolding ab inter_interval content_eq_0_interior
              by auto
            then show ?case
              using goal1(1)
              using interior_subset[of "k \<inter> cbox u v"]
              by auto
          qed
          finally show "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar> * norm (f x)) = content l *\<^sub>R norm (f x)"
            unfolding setsum_left_distrib[symmetric] real_scaleR_def
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
    and "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm (integral k f)) d \<le> B"
  shows "f absolutely_integrable_on UNIV"
proof (rule absolutely_integrable_onI, fact, rule)
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
  show "((\<lambda>x. norm (f x)) has_integral ?S) UNIV"
    apply (subst has_integral_alt')
    apply safe
  proof -
    case goal1
    show ?case
      using f_int[of a b] by auto
  next
    case goal2
    have "\<exists>y\<in>setsum (\<lambda>k. norm (integral k f)) ` {d. d division_of \<Union>d}. \<not> y \<le> ?S - e"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "?S \<le> ?S - e"
        by (intro cSUP_least[OF D(1)]) auto
      then show False
        using goal2 by auto
    qed
    then obtain K where *: "\<exists>x\<in>{d. d division_of \<Union>d}. K = (\<Sum>k\<in>x. norm (integral k f))"
      "SUPREMUM {d. d division_of \<Union>d} (setsum (\<lambda>k. norm (integral k f))) - e < K"
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
      have *: "\<forall>s s1. ?S - e < s1 \<and> s1 \<le> s \<and> s < ?S + e \<longrightarrow> abs (s - ?S) < e"
        by arith
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format])
        apply safe
        apply (rule d(2))
      proof -
        case goal1
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> setsum (\<lambda>k. integral k (\<lambda>x. norm (f x))) d"
          apply (rule setsum_mono)
          apply (rule absolutely_integrable_le)
          apply (drule d'(4))
          apply safe
          apply (rule f_int)
          done
        also have "\<dots> = integral (\<Union>d) (\<lambda>x. norm (f x))"
          apply (rule integral_combine_division_bottomup[symmetric])
          apply (rule d)
          unfolding forall_in_division[OF d(1)]
          using f_int
          apply auto
          done
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)"
        proof -
          case goal1
          have "\<Union>d \<subseteq> cbox a b"
            apply rule
            apply (drule K(2)[rule_format])
            apply (rule ab[unfolded subset_eq,rule_format])
            apply (auto simp add: dist_norm)
            done
          then show ?case
            apply -
            apply (subst if_P)
            apply rule
            apply (rule integral_subset_le)
            defer
            apply (rule integrable_on_subdivision[of _ _ _ "cbox a b"])
            apply (rule d)
            using f_int[of a b]
            apply auto
            done
        qed
        finally show ?case .
      next
        note f = absolutely_integrable_onD[OF f_int[of a b]]
        note * = this(2)[unfolded has_integral_integral has_integral[of "\<lambda>x. norm (f x)"],rule_format]
        have "e/2>0"
          using `e > 0` by auto
        from * [OF this] obtain d1 where
          d1: "gauge d1" "\<forall>p. p tagged_division_of (cbox a b) \<and> d1 fine p \<longrightarrow>
            norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm (f x))) < e / 2"
          by auto
        from henstock_lemma [OF f(1) `e/2>0`] obtain d2 where
          d2: "gauge d2" "\<forall>p. p tagged_partial_division_of (cbox a b) \<and> d2 fine p \<longrightarrow>
            (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x - integral k f)) < e / 2"
          by blast
        obtain p where
          p: "p tagged_division_of (cbox a b)" "d1 fine p" "d2 fine p"
          by (rule fine_division_exists [OF gauge_inter [OF d1(1) d2(1)], of a b])
            (auto simp add: fine_inter)
        have *: "\<And>sf sf' si di. sf' = sf \<longrightarrow> si \<le> ?S \<longrightarrow> abs (sf - si) < e / 2 \<longrightarrow>
          abs (sf' - di) < e / 2 \<longrightarrow> di < ?S + e"
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
          show "abs ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm(f x))) < e / 2"
            using d1(2)[rule_format,OF conjI[OF p(1,2)]]
            by (simp only: real_norm_def)
          show "(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) = (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x))"
            apply (rule setsum_cong2)
            unfolding split_paired_all split_conv
            apply (drule tagged_division_ofD(4)[OF p(1)])
            unfolding norm_scaleR
            apply (subst abs_of_nonneg)
            apply auto
            done
          show "(\<Sum>(x, k)\<in>p. norm (integral k f)) \<le> ?S"
            using partial_division_of_tagged_division[of p "cbox a b"] p(1)
            apply (subst setsum_over_tagged_division_lemma[OF p(1)])
            apply (simp add: integral_null)
            apply (intro cSUP_upper2[OF D(2), of "snd ` p"])
            apply (auto simp: tagged_partial_division_of_def)
            done
        qed
      qed
    qed (insert K, auto)
  qed
qed

lemma absolutely_integrable_restrict_univ:
  "(\<lambda>x. if x \<in> s then f x else (0::'a::banach)) absolutely_integrable_on UNIV \<longleftrightarrow>
    f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def if_distrib norm_zero integrable_restrict_univ ..

lemma absolutely_integrable_add[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. f x + g x) absolutely_integrable_on s"
proof -
  let ?P = "\<And>f g::'n \<Rightarrow> 'm. f absolutely_integrable_on UNIV \<Longrightarrow>
    g absolutely_integrable_on UNIV \<Longrightarrow> (\<lambda>x. f x + g x) absolutely_integrable_on UNIV"
  {
    presume as: "PROP ?P"
    note a = absolutely_integrable_restrict_univ[symmetric]
    have *: "\<And>x. (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0) =
      (if x \<in> s then f x + g x else 0)" by auto
    show ?thesis
      apply (subst a)
      using as[OF assms[unfolded a[of f] a[of g]]]
      apply (simp only: *)
      done
  }
  fix f g :: "'n \<Rightarrow> 'm"
  assume assms: "f absolutely_integrable_on UNIV" "g absolutely_integrable_on UNIV"
  note absolutely_integrable_bounded_variation
  from this[OF assms(1)] this[OF assms(2)] guess B1 B2 . note B=this[rule_format]
  show "(\<lambda>x. f x + g x) absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[of _ "B1+B2"])
    apply (rule integrable_add)
    prefer 3
  proof safe
    case goal1
    have "\<And>k. k \<in> d \<Longrightarrow> f integrable_on k \<and> g integrable_on k"
      apply (drule division_ofD(4)[OF goal1])
      apply safe
      apply (rule_tac[!] integrable_on_subcbox[of _ UNIV])
      using assms
      apply auto
      done
    then have "(\<Sum>k\<in>d. norm (integral k (\<lambda>x. f x + g x))) \<le>
      (\<Sum>k\<in>d. norm (integral k f)) + (\<Sum>k\<in>d. norm (integral k g))"
      apply -
      unfolding setsum_addf[symmetric]
      apply (rule setsum_mono)
      apply (subst integral_add)
      prefer 3
      apply (rule norm_triangle_ineq)
      apply auto
      done
    also have "\<dots> \<le> B1 + B2"
      using B(1)[OF goal1] B(2)[OF goal1] by auto
    finally show ?case .
  qed (insert assms, auto)
qed

lemma absolutely_integrable_sub[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. f x - g x) absolutely_integrable_on s"
  using absolutely_integrable_add[OF assms(1) absolutely_integrable_neg[OF assms(2)]]
  by (simp add: algebra_simps)

lemma absolutely_integrable_linear:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and h :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "bounded_linear h"
  shows "(h \<circ> f) absolutely_integrable_on s"
proof -
  {
    presume as: "\<And>f::'m \<Rightarrow> 'n. \<And>h::'n \<Rightarrow> 'p. f absolutely_integrable_on UNIV \<Longrightarrow>
      bounded_linear h \<Longrightarrow> (h \<circ> f) absolutely_integrable_on UNIV"
    note a = absolutely_integrable_restrict_univ[symmetric]
    show ?thesis
      apply (subst a)
      using as[OF assms[unfolded a[of f] a[of g]]]
      apply (simp only: o_def if_distrib linear_simps[OF assms(2)])
      done
  }
  fix f :: "'m \<Rightarrow> 'n"
  fix h :: "'n \<Rightarrow> 'p"
  assume assms: "f absolutely_integrable_on UNIV" "bounded_linear h"
  from absolutely_integrable_bounded_variation[OF assms(1)] guess B . note B=this
  from bounded_linear.pos_bounded[OF assms(2)] guess b .. note b=conjunctD2[OF this]
  show "(h \<circ> f) absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[of _ "B * b"])
    apply (rule integrable_linear[OF _ assms(2)])
  proof safe
    case goal2
    have "(\<Sum>k\<in>d. norm (integral k (h \<circ> f))) \<le> setsum (\<lambda>k. norm(integral k f)) d * b"
      unfolding setsum_left_distrib
      apply (rule setsum_mono)
    proof -
      case goal1
      from division_ofD(4)[OF goal2 this]
      guess u v by (elim exE) note uv=this
      have *: "f integrable_on k"
        unfolding uv
        apply (rule integrable_on_subcbox[of _ UNIV])
        using assms
        apply auto
        done
      note this[unfolded has_integral_integral]
      note has_integral_linear[OF this assms(2)] integrable_linear[OF * assms(2)]
      note * = has_integral_unique[OF this(2)[unfolded has_integral_integral] this(1)]
      show ?case
        unfolding * using b by auto
    qed
    also have "\<dots> \<le> B * b"
      apply (rule mult_right_mono)
      using B goal2 b
      apply auto
      done
    finally show ?case .
  qed (insert assms, auto)
qed

lemma absolutely_integrable_setsum:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "finite t"
    and "\<And>a. a \<in> t \<Longrightarrow> (f a) absolutely_integrable_on s"
  shows "(\<lambda>x. setsum (\<lambda>a. f a x) t) absolutely_integrable_on s"
  using assms(1,2)
  apply induct
  defer
  apply (subst setsum.insert)
  apply assumption+
  apply rule
  apply auto
  done

lemma bounded_linear_setsum:
  fixes f :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> bounded_linear (f i)"
  shows "bounded_linear (\<lambda>x. \<Sum>i\<in>I. f i x)"
proof (cases "finite I")
  case True
  from this f show ?thesis
    by (induct I) (auto intro!: bounded_linear_add bounded_linear_zero)
next
  case False
  then show ?thesis by (simp add: bounded_linear_zero)
qed

lemma absolutely_integrable_vector_abs:
  fixes f :: "'a::euclidean_space => 'b::euclidean_space"
    and T :: "'c::euclidean_space \<Rightarrow> 'b"
  assumes f: "f absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. abs(f x\<bullet>T i) *\<^sub>R i)) absolutely_integrable_on s"
  (is "?Tf absolutely_integrable_on s")
proof -
  have if_distrib: "\<And>P A B x. (if P then A else B) *\<^sub>R x = (if P then A *\<^sub>R x else B *\<^sub>R x)"
    by simp
  have *: "\<And>x. ?Tf x = (\<Sum>i\<in>Basis.
    ((\<lambda>y. (\<Sum>j\<in>Basis. (if j = i then y else 0) *\<^sub>R j)) o
     (\<lambda>x. (norm (\<Sum>j\<in>Basis. (if j = i then f x\<bullet>T i else 0) *\<^sub>R j)))) x)"
    by (simp add: comp_def if_distrib setsum_cases)
  show ?thesis
    unfolding *
    apply (rule absolutely_integrable_setsum[OF finite_Basis])
    apply (rule absolutely_integrable_linear)
    apply (rule absolutely_integrable_norm)
    apply (rule absolutely_integrable_linear[OF f, unfolded o_def])
    apply (auto simp: linear_linear euclidean_eq_iff[where 'a='c] inner_simps intro!: linearI)
    done
qed

lemma absolutely_integrable_max:
  fixes f g :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. max (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)::'n) absolutely_integrable_on s"
proof -
  have *:"\<And>x. (1 / 2) *\<^sub>R (((\<Sum>i\<in>Basis. \<bar>(f x - g x) \<bullet> i\<bar> *\<^sub>R i)::'n) + (f x + g x)) =
      (\<Sum>i\<in>Basis. max (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)"
    unfolding euclidean_eq_iff[where 'a='n] by (auto simp: inner_simps)
  note absolutely_integrable_sub[OF assms] absolutely_integrable_add[OF assms]
  note absolutely_integrable_vector_abs[OF this(1), where T="\<lambda>x. x"] this(2)
  note absolutely_integrable_add[OF this]
  note absolutely_integrable_cmul[OF this, of "1/2"]
  then show ?thesis unfolding * .
qed

lemma absolutely_integrable_min:
  fixes f g::"'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. min (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)::'n) absolutely_integrable_on s"
proof -
  have *:"\<And>x. (1 / 2) *\<^sub>R ((f x + g x) - (\<Sum>i\<in>Basis. \<bar>(f x - g x) \<bullet> i\<bar> *\<^sub>R i::'n)) =
      (\<Sum>i\<in>Basis. min (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)"
    unfolding euclidean_eq_iff[where 'a='n] by (auto simp: inner_simps)

  note absolutely_integrable_add[OF assms] absolutely_integrable_sub[OF assms]
  note this(1) absolutely_integrable_vector_abs[OF this(2), where T="\<lambda>x. x"]
  note absolutely_integrable_sub[OF this]
  note absolutely_integrable_cmul[OF this,of "1/2"]
  then show ?thesis unfolding * .
qed

lemma absolutely_integrable_abs_eq:
  fixes f::"'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and>
    (\<lambda>x. (\<Sum>i\<in>Basis. abs(f x\<bullet>i) *\<^sub>R i)::'m) integrable_on s"
  (is "?l = ?r")
proof
  assume ?l
  then show ?r
    apply -
    apply rule
    defer
    apply (drule absolutely_integrable_vector_abs)
    apply auto
    done
next
  assume ?r
  {
    presume lem: "\<And>f::'n \<Rightarrow> 'm. f integrable_on UNIV \<Longrightarrow>
      (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) integrable_on UNIV \<Longrightarrow>
        f absolutely_integrable_on UNIV"
    have *: "\<And>x. (\<Sum>i\<in>Basis. \<bar>(if x \<in> s then f x else 0) \<bullet> i\<bar> *\<^sub>R i) =
      (if x \<in> s then (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) else (0::'m))"
      unfolding euclidean_eq_iff[where 'a='m]
      by auto
    show ?l
      apply (subst absolutely_integrable_restrict_univ[symmetric])
      apply (rule lem)
      unfolding integrable_restrict_univ *
      using `?r`
      apply auto
      done
  }
  fix f :: "'n \<Rightarrow> 'm"
  assume assms: "f integrable_on UNIV" "(\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) integrable_on UNIV"
  let ?B = "\<Sum>i\<in>Basis. integral UNIV (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) \<bullet> i"
  show "f absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[OF assms(1), where B="?B"])
    apply safe
  proof -
    case goal1
    note d=this and d'=division_ofD[OF this]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le>
      (\<Sum>k\<in>d. setsum (op \<bullet> (integral k (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m))) Basis)"
      apply (rule setsum_mono)
      apply (rule order_trans[OF norm_le_l1])
      apply (rule setsum_mono)
      unfolding lessThan_iff
    proof -
      fix k
      fix i :: 'm
      assume "k \<in> d" and i: "i \<in> Basis"
      from d'(4)[OF this(1)] guess a b by (elim exE) note ab=this
      show "\<bar>integral k f \<bullet> i\<bar> \<le> integral k (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) \<bullet> i"
        apply (rule abs_leI)
        unfolding inner_minus_left[symmetric]
        defer
        apply (subst integral_neg[symmetric])
        defer
        apply (rule_tac[1-2] integral_component_le[OF i])
        apply (rule integrable_neg)
        using integrable_on_subcbox[OF assms(1),of a b]
          integrable_on_subcbox[OF assms(2),of a b] i
        unfolding ab
        apply auto
        done
    qed
    also have "\<dots> \<le> setsum (op \<bullet> (integral UNIV (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m))) Basis"
      apply (subst setsum_commute)
      apply (rule setsum_mono)
    proof -
      case goal1
      have *: "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) integrable_on \<Union>d"
        using integrable_on_subdivision[OF d assms(2)] by auto
      have "(\<Sum>i\<in>d. integral i (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j) =
        integral (\<Union>d) (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j"
        unfolding inner_setsum_left[symmetric] integral_combine_division_topdown[OF * d] ..
      also have "\<dots> \<le> integral UNIV (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j"
        apply (rule integral_subset_component_le)
        using assms * `j \<in> Basis`
        apply auto
        done
      finally show ?case .
    qed
    finally show ?case .
  qed
qed

lemma nonnegative_absolutely_integrable:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<forall>x\<in>s. \<forall>i\<in>Basis. 0 \<le> f x \<bullet> i"
    and "f integrable_on s"
  shows "f absolutely_integrable_on s"
  unfolding absolutely_integrable_abs_eq
  apply rule
  apply (rule assms)
  apply (rule integrable_eq[of _ f])
  using assms
  apply (auto simp: euclidean_eq_iff[where 'a='m])
  done

lemma absolutely_integrable_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<forall>x\<in>s. norm (f x) \<le> g x"
    and "f integrable_on s"
    and "g integrable_on s"
  shows "f absolutely_integrable_on s"
proof -
  {
    presume *: "\<And>f::'n \<Rightarrow> 'm. \<And>g. \<forall>x. norm (f x) \<le> g x \<Longrightarrow> f integrable_on UNIV \<Longrightarrow>
      g integrable_on UNIV \<Longrightarrow> f absolutely_integrable_on UNIV"
    show ?thesis
      apply (subst absolutely_integrable_restrict_univ[symmetric])
      apply (rule *[of _ "\<lambda>x. if x\<in>s then g x else 0"])
      using assms
      unfolding integrable_restrict_univ
      apply auto
      done
  }
  fix g
  fix f :: "'n \<Rightarrow> 'm"
  assume assms: "\<forall>x. norm (f x) \<le> g x" "f integrable_on UNIV" "g integrable_on UNIV"
  show "f absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[OF assms(2),where B="integral UNIV g"])
  proof safe
    case goal1
    note d=this and d'=division_ofD[OF this]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>k\<in>d. integral k g)"
      apply (rule setsum_mono)
      apply (rule integral_norm_bound_integral)
      apply (drule_tac[!] d'(4))
      apply safe
      apply (rule_tac[1-2] integrable_on_subcbox)
      using assms
      apply auto
      done
    also have "\<dots> = integral (\<Union>d) g"
      apply (rule integral_combine_division_bottomup[symmetric])
      apply (rule d)
      apply safe
      apply (drule d'(4))
      apply safe
      apply (rule integrable_on_subcbox[OF assms(3)])
      apply auto
      done
    also have "\<dots> \<le> integral UNIV g"
      apply (rule integral_subset_le)
      defer
      apply (rule integrable_on_subdivision[OF d,of _ UNIV])
      prefer 4
      apply rule
      apply (rule_tac y="norm (f x)" in order_trans)
      using assms
      apply auto
      done
    finally show ?case .
  qed
qed

lemma absolutely_integrable_integrable_bound_real:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>x\<in>s. norm (f x) \<le> g x"
    and "f integrable_on s"
    and "g integrable_on s"
  shows "f absolutely_integrable_on s"
  apply (rule absolutely_integrable_integrable_bound[where g=g])
  using assms
  unfolding o_def
  apply auto
  done

lemma absolutely_integrable_absolutely_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
    and g :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  assumes "\<forall>x\<in>s. norm (f x) \<le> norm (g x)"
    and "f integrable_on s"
    and "g absolutely_integrable_on s"
  shows "f absolutely_integrable_on s"
  apply (rule absolutely_integrable_integrable_bound[of s f "\<lambda>x. norm (g x)"])
  using assms
  apply auto
  done

lemma absolutely_integrable_inf_real:
  assumes "finite k"
    and "k \<noteq> {}"
    and "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Inf ((fs x) ` k))) absolutely_integrable_on s"
  using assms
proof induct
  case (insert a k)
  let ?P = "(\<lambda>x.
    if fs x ` k = {} then fs x a
    else min (fs x a) (Inf (fs x ` k))) absolutely_integrable_on s"
  show ?case
    unfolding image_insert
    apply (subst Inf_insert_finite)
    apply (rule finite_imageI[OF insert(1)])
  proof (cases "k = {}")
    case True
    then show ?P
      apply (subst if_P)
      defer
      apply (rule insert(5)[rule_format])
      apply auto
      done
  next
    case False
    then show ?P
      apply (subst if_not_P)
      defer
      apply (rule absolutely_integrable_min[where 'n=real, unfolded Basis_real_def, simplified])
      defer
      apply(rule insert(3)[OF False])
      using insert(5)
      apply auto
      done
  qed
next
  case empty
  then show ?case by auto
qed

lemma absolutely_integrable_sup_real:
  assumes "finite k"
    and "k \<noteq> {}"
    and "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Sup ((fs x) ` k))) absolutely_integrable_on s"
  using assms
proof induct
  case (insert a k)
  let ?P = "(\<lambda>x.
    if fs x ` k = {} then fs x a
    else max (fs x a) (Sup (fs x ` k))) absolutely_integrable_on s"
  show ?case
    unfolding image_insert
    apply (subst Sup_insert_finite)
    apply (rule finite_imageI[OF insert(1)])
  proof (cases "k = {}")
    case True
    then show ?P
      apply (subst if_P)
      defer
      apply (rule insert(5)[rule_format])
      apply auto
      done
  next
    case False
    then show ?P
      apply (subst if_not_P)
      defer
      apply (rule absolutely_integrable_max[where 'n=real, unfolded Basis_real_def, simplified])
      defer
      apply (rule insert(3)[OF False])
      using insert(5)
      apply auto
      done
  qed
qed auto


subsection {* Dominated convergence *}

lemma dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>k. (f k) integrable_on s" "h integrable_on s"
    and "\<And>k. \<forall>x \<in> s. norm (f k x) \<le> h x"
    and "\<forall>x \<in> s. ((\<lambda>k. f k x) ---> g x) sequentially"
  shows "g integrable_on s"
    and "((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
proof -
  have bdd_below[simp]: "\<And>x P. x \<in> s \<Longrightarrow> bdd_below {f n x |n. P n}"
  proof (safe intro!: bdd_belowI)
    fix n x show "x \<in> s \<Longrightarrow> - h x \<le> f n x"
      using assms(3)[rule_format, of x n] by simp
  qed
  have bdd_above[simp]: "\<And>x P. x \<in> s \<Longrightarrow> bdd_above {f n x |n. P n}"
  proof (safe intro!: bdd_aboveI)
    fix n x show "x \<in> s \<Longrightarrow> f n x \<le> h x"
      using assms(3)[rule_format, of x n] by simp
  qed

  have "\<And>m. (\<lambda>x. Inf {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) --->
    integral s (\<lambda>x. Inf {f j x |j. m \<le> j}))sequentially"
  proof (rule monotone_convergence_decreasing, safe)
    fix m :: nat
    show "bounded {integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        unfolding simple_image
        apply (rule absolutely_integrable_onD)
        apply (rule absolutely_integrable_inf_real)
        prefer 5
        unfolding real_norm_def
        apply rule
        apply (rule cInf_abs_ge)
        prefer 5
        apply rule
        apply (rule_tac g = h in absolutely_integrable_integrable_bound_real)
        using assms
        unfolding real_norm_def
        apply auto
        done
    qed
    fix k :: nat
    show "(\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding simple_image
      apply (rule absolutely_integrable_onD)
      apply (rule absolutely_integrable_inf_real)
      prefer 3
      using absolutely_integrable_integrable_bound_real[OF assms(3,1,2)]
      apply auto
      done
    fix x
    assume x: "x \<in> s"
    show "Inf {f j x |j. j \<in> {m..m + Suc k}} \<le> Inf {f j x |j. j \<in> {m..m + k}}"
      by (rule cInf_superset_mono) auto
    let ?S = "{f j x| j. m \<le> j}"
    show "((\<lambda>k. Inf {f j x |j. j \<in> {m..m + k}}) ---> Inf ?S) sequentially"
    proof (rule LIMSEQ_I)
      case goal1
      note r = this

      have "\<exists>y\<in>?S. y < Inf ?S + r"
        by (subst cInf_less_iff[symmetric]) (auto simp: `x\<in>s` r)
      then obtain N where N: "f N x < Inf ?S + r" "m \<le> N"
        by blast

      show ?case
        apply (rule_tac x=N in exI)
      proof safe
        case goal1
        have *: "\<And>y ix. y < Inf ?S + r \<longrightarrow> Inf ?S \<le> ix \<longrightarrow> ix \<le> y \<longrightarrow> abs(ix - Inf ?S) < r"
          by arith
        show ?case
          unfolding real_norm_def
            apply (rule *[rule_format, OF N(1)])
            apply (rule cInf_superset_mono, auto simp: `x\<in>s`) []
            apply (rule cInf_lower)
            using N goal1
            apply auto []
            apply simp
            done
      qed
    qed
  qed
  note dec1 = conjunctD2[OF this]

  have "\<And>m. (\<lambda>x. Sup {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) --->
    integral s (\<lambda>x. Sup {f j x |j. m \<le> j})) sequentially"
  proof (rule monotone_convergence_increasing,safe)
    fix m :: nat
    show "bounded {integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply (rule integral_norm_bound_integral) unfolding simple_image
        apply (rule absolutely_integrable_onD)
        apply(rule absolutely_integrable_sup_real)
        prefer 5 unfolding real_norm_def
        apply rule
        apply (rule cSup_abs_le)
        prefer 5
        apply rule
        apply (rule_tac g=h in absolutely_integrable_integrable_bound_real)
        using assms
        unfolding real_norm_def
        apply auto
        done
    qed
    fix k :: nat
    show "(\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding simple_image
      apply (rule absolutely_integrable_onD)
      apply (rule absolutely_integrable_sup_real)
      prefer 3
      using absolutely_integrable_integrable_bound_real[OF assms(3,1,2)]
      apply auto
      done
    fix x
    assume x: "x\<in>s"
    show "Sup {f j x |j. j \<in> {m..m + Suc k}} \<ge> Sup {f j x |j. j \<in> {m..m + k}}"
      by (rule cSup_subset_mono) auto
    let ?S = "{f j x| j. m \<le> j}"
    show "((\<lambda>k. Sup {f j x |j. j \<in> {m..m + k}}) ---> Sup ?S) sequentially"
    proof (rule LIMSEQ_I)
      case goal1 note r=this
      have "\<exists>y\<in>?S. Sup ?S - r < y"
        by (subst less_cSup_iff[symmetric]) (auto simp: r `x\<in>s`)
      then obtain N where N: "Sup ?S - r < f N x" "m \<le> N"
        by blast

      show ?case
        apply (rule_tac x=N in exI)
      proof safe
        case goal1
        have *: "\<And>y ix. Sup ?S - r < y \<longrightarrow> ix \<le> Sup ?S \<longrightarrow> y \<le> ix \<longrightarrow> abs(ix - Sup ?S) < r"
          by arith
        show ?case
          apply simp
          apply (rule *[rule_format, OF N(1)])
          apply (rule cSup_subset_mono, auto simp: `x\<in>s`) []
          apply (subst cSup_upper)
          using N goal1
          apply auto
          done
      qed
    qed
  qed
  note inc1 = conjunctD2[OF this]

  have "g integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) ---> integral s g) sequentially"
    apply (rule monotone_convergence_increasing,safe)
    apply fact
  proof -
    show "bounded {integral s (\<lambda>x. Inf {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        apply fact+
        unfolding real_norm_def
        apply rule
        apply (rule cInf_abs_ge)
        using assms(3)
        apply auto
        done
    qed
    fix k :: nat and x
    assume x: "x \<in> s"

    have *: "\<And>x y::real. x \<ge> - y \<Longrightarrow> - x \<le> y" by auto
    show "Inf {f j x |j. k \<le> j} \<le> Inf {f j x |j. Suc k \<le> j}"
      by (intro cInf_superset_mono) (auto simp: `x\<in>s`)

    show "(\<lambda>k::nat. Inf {f j x |j. k \<le> j}) ----> g x"
    proof (rule LIMSEQ_I)
      case goal1
      then have "0<r/2"
        by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N = this
      show ?case
        apply (rule_tac x=N in exI,safe)
        unfolding real_norm_def
        apply (rule le_less_trans[of _ "r/2"])
        apply (rule cInf_asclose)
        apply safe
        defer
        apply (rule less_imp_le)
        using N goal1
        apply auto
        done
    qed
  qed
  note inc2 = conjunctD2[OF this]

  have "g integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) ---> integral s g) sequentially"
    apply (rule monotone_convergence_decreasing,safe)
    apply fact
  proof -
    show "bounded {integral s (\<lambda>x. Sup {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        apply fact+
        unfolding real_norm_def
        apply rule
        apply (rule cSup_abs_le)
        using assms(3)
        apply auto
        done
    qed
    fix k :: nat
    fix x
    assume x: "x \<in> s"

    show "Sup {f j x |j. k \<le> j} \<ge> Sup {f j x |j. Suc k \<le> j}"
      by (rule cSup_subset_mono) (auto simp: `x\<in>s`)
    show "((\<lambda>k. Sup {f j x |j. k \<le> j}) ---> g x) sequentially"
    proof (rule LIMSEQ_I)
      case goal1
      then have "0<r/2"
        by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N=this
      show ?case
        apply (rule_tac x=N in exI,safe)
        unfolding real_norm_def
        apply (rule le_less_trans[of _ "r/2"])
        apply (rule cSup_asclose)
        apply safe
        defer
        apply (rule less_imp_le)
        using N goal1
        apply auto
        done
    qed
  qed
  note dec2 = conjunctD2[OF this]

  show "g integrable_on s" by fact
  show "((\<lambda>k. integral s (f k)) ---> integral s g) sequentially"
  proof (rule LIMSEQ_I)
    case goal1
    from LIMSEQ_D [OF inc2(2) goal1] guess N1 .. note N1=this[unfolded real_norm_def]
    from LIMSEQ_D [OF dec2(2) goal1] guess N2 .. note N2=this[unfolded real_norm_def]
    show ?case
    proof (rule_tac x="N1+N2" in exI, safe)
      fix n
      assume n: "n \<ge> N1 + N2"
      have *: "\<And>i0 i i1 g. \<bar>i0 - g\<bar> < r \<longrightarrow> \<bar>i1 - g\<bar> < r \<longrightarrow> i0 \<le> i \<longrightarrow> i \<le> i1 \<longrightarrow> \<bar>i - g\<bar> < r"
        by arith
      show "norm (integral s (f n) - integral s g) < r"
        unfolding real_norm_def
      proof (rule *[rule_format,OF N1[rule_format] N2[rule_format], of n n])
        show "integral s (\<lambda>x. Inf {f j x |j. n \<le> j}) \<le> integral s (f n)"
          by (rule integral_le[OF dec1(1) assms(1)]) (auto intro!: cInf_lower)
        show "integral s (f n) \<le> integral s (\<lambda>x. Sup {f j x |j. n \<le> j})"
          by (rule integral_le[OF assms(1) inc1(1)]) (auto intro!: cSup_upper)
      qed (insert n, auto)
    qed
  qed
qed

end
