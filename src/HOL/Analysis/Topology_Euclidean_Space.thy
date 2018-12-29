(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Topology in Euclidean Space\<close>

theory Topology_Euclidean_Space
  imports
    Elementary_Normed_Spaces
    Linear_Algebra
    Norm_Arith
begin

lemma euclidean_dist_l2:
  fixes x y :: "'a :: euclidean_space"
  shows "dist x y = L2_set (\<lambda>i. dist (x \<bullet> i) (y \<bullet> i)) Basis"
  unfolding dist_norm norm_eq_sqrt_inner L2_set_def
  by (subst euclidean_inner) (simp add: power2_eq_square inner_diff_left)

lemma norm_nth_le: "norm (x \<bullet> i) \<le> norm x" if "i \<in> Basis"
proof -
  have "(x \<bullet> i)\<^sup>2 = (\<Sum>i\<in>{i}. (x \<bullet> i)\<^sup>2)"
    by simp
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. (x \<bullet> i)\<^sup>2)"
    by (intro sum_mono2) (auto simp: that)
  finally show ?thesis
    unfolding norm_conv_dist euclidean_dist_l2[of x] L2_set_def
    by (auto intro!: real_le_rsqrt)
qed


subsection \<open>Boxes\<close>

abbreviation One :: "'a::euclidean_space"
  where "One \<equiv> \<Sum>Basis"

lemma One_non_0: assumes "One = (0::'a::euclidean_space)" shows False
proof -
  have "dependent (Basis :: 'a set)"
    apply (simp add: dependent_finite)
    apply (rule_tac x="\<lambda>i. 1" in exI)
    using SOME_Basis apply (auto simp: assms)
    done
  with independent_Basis show False by force
qed

corollary One_neq_0[iff]: "One \<noteq> 0"
  by (metis One_non_0)

corollary Zero_neq_One[iff]: "0 \<noteq> One"
  by (metis One_non_0)

definition%important (in euclidean_space) eucl_less (infix "<e" 50)
  where "eucl_less a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i)"

definition%important box_eucl_less: "box a b = {x. a <e x \<and> x <e b}"
definition%important "cbox a b = {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i}"

lemma box_def: "box a b = {x. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
  and in_box_eucl_less: "x \<in> box a b \<longleftrightarrow> a <e x \<and> x <e b"
  and mem_box: "x \<in> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i)"
    "x \<in> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
  by (auto simp: box_eucl_less eucl_less_def cbox_def)

lemma cbox_Pair_eq: "cbox (a, c) (b, d) = cbox a b \<times> cbox c d"
  by (force simp: cbox_def Basis_prod_def)

lemma cbox_Pair_iff [iff]: "(x, y) \<in> cbox (a, c) (b, d) \<longleftrightarrow> x \<in> cbox a b \<and> y \<in> cbox c d"
  by (force simp: cbox_Pair_eq)

lemma cbox_Complex_eq: "cbox (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (cbox a b \<times> cbox c d)"
  apply (auto simp: cbox_def Basis_complex_def)
  apply (rule_tac x = "(Re x, Im x)" in image_eqI)
  using complex_eq by auto

lemma cbox_Pair_eq_0: "cbox (a, c) (b, d) = {} \<longleftrightarrow> cbox a b = {} \<or> cbox c d = {}"
  by (force simp: cbox_Pair_eq)

lemma swap_cbox_Pair [simp]: "prod.swap ` cbox (c, a) (d, b) = cbox (a,c) (b,d)"
  by auto

lemma mem_box_real[simp]:
  "(x::real) \<in> box a b \<longleftrightarrow> a < x \<and> x < b"
  "(x::real) \<in> cbox a b \<longleftrightarrow> a \<le> x \<and> x \<le> b"
  by (auto simp: mem_box)

lemma box_real[simp]:
  fixes a b:: real
  shows "box a b = {a <..< b}" "cbox a b = {a .. b}"
  by auto

lemma box_Int_box:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<inter> box c d =
    box (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box by auto

lemma rational_boxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> box a b \<and> box a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by (auto simp: DIM_positive)
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>xa. a xa \<in> \<rat> \<and> a xa < x \<bullet> xa \<and> x \<bullet> xa - a xa < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>xa. b xa \<in> \<rat> \<and> x \<bullet> xa < b xa \<and> b xa - x \<bullet> xa < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> box ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding L2_set_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i < y\<bullet>i \<and> y\<bullet>i < b i"
        using * i by (auto simp: box_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  qed (insert a b, auto simp: box_def)
qed

lemma open_UNION_box:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. box (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. box (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab:
      "x \<in> box a b"
      "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
      "\<forall>i\<in>Basis. b \<bullet> i \<in> \<rat>"
      "box a b \<subseteq> ball x e"
      using rational_boxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_box:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = box a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. box (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_box [OF assms] by metis
  qed auto
qed

lemma rational_cboxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> cbox a b \<and> cbox a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by auto
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>u. a u \<in> \<rat> \<and> a u < x \<bullet> u \<and> x \<bullet> u - a u < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>u. b u \<in> \<rat> \<and> x \<bullet> u < b u \<and> b u - x \<bullet> u < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> cbox ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding L2_set_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i \<le> y\<bullet>i \<and> y\<bullet>i \<le> b i"
        using * i by (auto simp: cbox_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  next
    show "x \<in> cbox (\<Sum>i\<in>Basis. a i *\<^sub>R i) (\<Sum>i\<in>Basis. b i *\<^sub>R i)"
      using a b less_imp_le by (auto simp: cbox_def)
  qed (use a b cbox_def in auto)
qed

lemma open_UNION_cbox:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. cbox (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. cbox (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab: "x \<in> cbox a b" "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
                                  "\<forall>i \<in> Basis. b \<bullet> i \<in> \<rat>" "cbox a b \<subseteq> ball x e"
      using rational_cboxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_cbox:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. cbox (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_cbox [OF assms] by metis
  qed auto
qed

lemma box_eq_empty:
  fixes a :: "'a::euclidean_space"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i < a\<bullet>i))" (is ?th2)
proof -
  {
    fix i x
    assume i: "i\<in>Basis" and as:"b\<bullet>i \<le> a\<bullet>i" and x:"x\<in>box a b"
    then have "a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i"
      unfolding mem_box by (auto simp: box_def)
    then have "a\<bullet>i < b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as: "\<forall>i\<in>Basis. \<not> (b\<bullet>i \<le> a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "a\<bullet>i < b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i < ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i < b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "box a b \<noteq> {}"
      using mem_box(1)[of "?x" a b] by auto
  }
  ultimately show ?th1 by blast

  {
    fix i x
    assume i: "i \<in> Basis" and as:"b\<bullet>i < a\<bullet>i" and x:"x\<in>cbox a b"
    then have "a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
      unfolding mem_box by auto
    then have "a\<bullet>i \<le> b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as:"\<forall>i\<in>Basis. \<not> (b\<bullet>i < a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i:"i \<in> Basis"
      have "a\<bullet>i \<le> b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i \<le> ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i \<le> b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "cbox a b \<noteq> {}"
      using mem_box(2)[of "?x" a b] by auto
  }
  ultimately show ?th2 by blast
qed

lemma box_ne_empty:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i)"
  and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  unfolding box_eq_empty[of a b] by fastforce+

lemma
  fixes a :: "'a::euclidean_space"
  shows cbox_sing [simp]: "cbox a a = {a}"
    and box_sing [simp]: "box a a = {}"
  unfolding set_eq_iff mem_box eq_iff [symmetric]
  by (auto intro!: euclidean_eqI[where 'a='a])
     (metis all_not_in_conv nonempty_Basis)

lemma subset_box_imp:
  fixes a :: "'a::euclidean_space"
  shows "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> cbox a b"
     and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box
  by (best intro: order_trans less_le_trans le_less_trans less_imp_le)+

lemma box_subset_cbox:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<subseteq> cbox a b"
  unfolding subset_eq [unfolded Ball_def] mem_box
  by (fast intro: less_imp_le)

lemma subset_box:
  fixes a :: "'a::euclidean_space"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th4)
proof -
  let ?lesscd = "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
  let ?lerhs = "\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
  show ?th1 ?th2
    by (fastforce simp: mem_box)+
  have acdb: "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
    if i: "i \<in> Basis" and box: "box c d \<subseteq> cbox a b" and cd: "\<And>i. i \<in> Basis \<Longrightarrow> c\<bullet>i < d\<bullet>i" for i
  proof -
    have "box c d \<noteq> {}"
      using that
      unfolding box_eq_empty by force
    { let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((min (a\<bullet>j) (d\<bullet>j))+c\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume *: "a\<bullet>i > c\<bullet>i"
      then have "c \<bullet> j < ?x \<bullet> j \<and> ?x \<bullet> j < d \<bullet> j" if "j \<in> Basis" for j
        using cd that by (fastforce simp add: i *)
      then have "?x \<in> box c d"
        unfolding mem_box by auto
      moreover have "?x \<notin> cbox a b"
        using i cd * by (force simp: mem_box)
      ultimately have False using box by auto
    }
    then have "a\<bullet>i \<le> c\<bullet>i" by force
    moreover
    { let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((max (b\<bullet>j) (c\<bullet>j))+d\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume *: "b\<bullet>i < d\<bullet>i"
      then have "d \<bullet> j > ?x \<bullet> j \<and> ?x \<bullet> j > c \<bullet> j" if "j \<in> Basis" for j
        using cd that by (fastforce simp add: i *)
      then have "?x \<in> box c d"
        unfolding mem_box by auto
      moreover have "?x \<notin> cbox a b"
        using i cd * by (force simp: mem_box)
      ultimately have False using box by auto
    }
    then have "b\<bullet>i \<ge> d\<bullet>i" by (rule ccontr) auto
    ultimately show ?thesis by auto
  qed
  show ?th3
    using acdb by (fastforce simp add: mem_box)
  have acdb': "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
    if "i \<in> Basis" "box c d \<subseteq> box a b" "\<And>i. i \<in> Basis \<Longrightarrow> c\<bullet>i < d\<bullet>i" for i
      using box_subset_cbox[of a b] that acdb by auto
  show ?th4
    using acdb' by (fastforce simp add: mem_box)
qed

lemma eq_cbox: "cbox a b = cbox c d \<longleftrightarrow> cbox a b = {} \<and> cbox c d = {} \<or> a = c \<and> b = d"
      (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "cbox a b \<subseteq> cbox c d" "cbox c d \<subseteq> cbox a b"
    by auto
  then show ?rhs
    by (force simp: subset_box box_eq_empty intro: antisym euclidean_eqI)
next
  assume ?rhs
  then show ?lhs
    by force
qed

lemma eq_cbox_box [simp]: "cbox a b = box c d \<longleftrightarrow> cbox a b = {} \<and> box c d = {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then have "cbox a b \<subseteq> box c d" "box c d \<subseteq> cbox a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using L box_ne_empty box_sing apply (fastforce simp add:)
    done
qed force

lemma eq_box_cbox [simp]: "box a b = cbox c d \<longleftrightarrow> box a b = {} \<and> cbox c d = {}"
  by (metis eq_cbox_box)

lemma eq_box: "box a b = box c d \<longleftrightarrow> box a b = {} \<and> box c d = {} \<or> a = c \<and> b = d"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then have "box a b \<subseteq> box c d" "box c d \<subseteq> box a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using box_ne_empty(2) L
    apply auto
     apply (meson euclidean_eqI less_eq_real_def not_less)+
    done
qed force

lemma subset_box_complex:
   "cbox a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "cbox a b \<subseteq> box c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a > Re c \<and> Im a > Im c \<and> Re b < Re d \<and> Im b < Im d"
   "box a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "box a b \<subseteq> box c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
  by (subst subset_box; force simp: Basis_complex_def)+

lemma Int_interval:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d =
    cbox (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box
  by auto

lemma disjoint_interval:
  fixes a::"'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i < c\<bullet>i \<or> d\<bullet>i < a\<bullet>i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th4)
proof -
  let ?z = "(\<Sum>i\<in>Basis. (((max (a\<bullet>i) (c\<bullet>i)) + (min (b\<bullet>i) (d\<bullet>i))) / 2) *\<^sub>R i)::'a"
  have **: "\<And>P Q. (\<And>i :: 'a. i \<in> Basis \<Longrightarrow> Q ?z i \<Longrightarrow> P i) \<Longrightarrow>
      (\<And>i x :: 'a. i \<in> Basis \<Longrightarrow> P i \<Longrightarrow> Q x i) \<Longrightarrow> (\<forall>x. \<exists>i\<in>Basis. Q x i) \<longleftrightarrow> (\<exists>i\<in>Basis. P i)"
    by blast
  note * = set_eq_iff Int_iff empty_iff mem_box ball_conj_distrib[symmetric] eq_False ball_simps(10)
  show ?th1 unfolding * by (intro **) auto
  show ?th2 unfolding * by (intro **) auto
  show ?th3 unfolding * by (intro **) auto
  show ?th4 unfolding * by (intro **) auto
qed

lemma UN_box_eq_UNIV: "(\<Union>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One)) = UNIV"
proof -
  have "\<bar>x \<bullet> b\<bar> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
    if [simp]: "b \<in> Basis" for x b :: 'a
  proof -
    have "\<bar>x \<bullet> b\<bar> \<le> real_of_int \<lceil>\<bar>x \<bullet> b\<bar>\<rceil>"
      by (rule le_of_int_ceiling)
    also have "\<dots> \<le> real_of_int \<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil>"
      by (auto intro!: ceiling_mono)
    also have "\<dots> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
      by simp
    finally show ?thesis .
  qed
  then have "\<exists>n::nat. \<forall>b\<in>Basis. \<bar>x \<bullet> b\<bar> < real n" for x :: 'a
    by (metis order.strict_trans reals_Archimedean2)
  moreover have "\<And>x b::'a. \<And>n::nat.  \<bar>x \<bullet> b\<bar> < real n \<longleftrightarrow> - real n < x \<bullet> b \<and> x \<bullet> b < real n"
    by auto
  ultimately show ?thesis
    by (auto simp: box_def inner_sum_left inner_Basis sum.If_cases)
qed


subsection \<open>General Intervals\<close>

definition%important "is_interval (s::('a::euclidean_space) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i\<in>Basis. ((a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i) \<or> (b\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> a\<bullet>i))) \<longrightarrow> x \<in> s)"

lemma is_interval_1:
  "is_interval (s::real set) \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> s)"
  unfolding is_interval_def by auto

lemma is_interval_inter: "is_interval X \<Longrightarrow> is_interval Y \<Longrightarrow> is_interval (X \<inter> Y)"
  unfolding is_interval_def
  by blast

lemma is_interval_cbox [simp]: "is_interval (cbox a (b::'a::euclidean_space))" (is ?th1)
  and is_interval_box [simp]: "is_interval (box a b)" (is ?th2)
  unfolding is_interval_def mem_box Ball_def atLeastAtMost_iff
  by (meson order_trans le_less_trans less_le_trans less_trans)+

lemma is_interval_empty [iff]: "is_interval {}"
  unfolding is_interval_def  by simp

lemma is_interval_univ [iff]: "is_interval UNIV"
  unfolding is_interval_def  by simp

lemma mem_is_intervalI:
  assumes "is_interval s"
    and "a \<in> s" "b \<in> s"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i \<or> b \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i"
  shows "x \<in> s"
  by (rule assms(1)[simplified is_interval_def, rule_format, OF assms(2,3,4)])

lemma interval_subst:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
    and "x \<in> S" "y j \<in> S"
    and "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. (if i = j then y i \<bullet> i else x \<bullet> i) *\<^sub>R i) \<in> S"
  by (rule mem_is_intervalI[OF assms(1,2)]) (auto simp: assms)

lemma mem_box_componentwiseI:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> ((\<lambda>x. x \<bullet> i) ` S)"
  shows "x \<in> S"
proof -
  from assms have "\<forall>i \<in> Basis. \<exists>s \<in> S. x \<bullet> i = s \<bullet> i"
    by auto
  with finite_Basis obtain s and bs::"'a list"
    where s: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i = s i \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> s i \<in> S"
      and bs: "set bs = Basis" "distinct bs"
    by (metis finite_distinct_list)
  from nonempty_Basis s obtain j where j: "j \<in> Basis" "s j \<in> S"
    by blast
  define y where
    "y = rec_list (s j) (\<lambda>j _ Y. (\<Sum>i\<in>Basis. (if i = j then s i \<bullet> i else Y \<bullet> i) *\<^sub>R i))"
  have "x = (\<Sum>i\<in>Basis. (if i \<in> set bs then s i \<bullet> i else s j \<bullet> i) *\<^sub>R i)"
    using bs by (auto simp: s(1)[symmetric] euclidean_representation)
  also have [symmetric]: "y bs = \<dots>"
    using bs(2) bs(1)[THEN equalityD1]
    by (induct bs) (auto simp: y_def euclidean_representation intro!: euclidean_eqI[where 'a='a])
  also have "y bs \<in> S"
    using bs(1)[THEN equalityD1]
    apply (induct bs)
     apply (auto simp: y_def j)
    apply (rule interval_subst[OF assms(1)])
      apply (auto simp: s)
    done
  finally show ?thesis .
qed

lemma cbox01_nonempty [simp]: "cbox 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left sum_nonneg)

lemma box01_nonempty [simp]: "box 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left)

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  using nonempty_Basis box01_nonempty box_eq_empty(1) box_ne_empty(1) by blast

lemma interval_subset_is_interval:
  assumes "is_interval S"
  shows "cbox a b \<subseteq> S \<longleftrightarrow> cbox a b = {} \<or> a \<in> S \<and> b \<in> S" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs  using box_ne_empty(1) mem_box(2) by fastforce
next
  assume ?rhs
  have "cbox a b \<subseteq> S" if "a \<in> S" "b \<in> S"
    using assms unfolding is_interval_def
    apply (clarsimp simp add: mem_box)
    using that by blast
  with \<open>?rhs\<close> show ?lhs
    by blast
qed

lemma is_real_interval_union:
  "is_interval (X \<union> Y)"
  if X: "is_interval X" and Y: "is_interval Y" and I: "(X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> X \<inter> Y \<noteq> {})"
  for X Y::"real set"
proof -
  consider "X \<noteq> {}" "Y \<noteq> {}" | "X = {}" | "Y = {}" by blast
  then show ?thesis
  proof cases
    case 1
    then obtain r where "r \<in> X \<or> X \<inter> Y = {}" "r \<in> Y \<or> X \<inter> Y = {}"
      by blast
    then show ?thesis
      using I 1 X Y unfolding is_interval_1
      by (metis (full_types) Un_iff le_cases)
  qed (use that in auto)
qed

lemma is_interval_translationI:
  assumes "is_interval X"
  shows "is_interval ((+) x ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (x + b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + d) \<bullet> i \<or>
       (x + d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + b) \<bullet> i"
  hence "e - x \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "e - x"])
      (auto simp: algebra_simps)
  thus "e \<in> (+) x ` X" by force
qed

lemma is_interval_uminusI:
  assumes "is_interval X"
  shows "is_interval (uminus ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (- b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- d) \<bullet> i \<or>
       (- d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- b) \<bullet> i"
  hence "- e \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "- e"])
      (auto simp: algebra_simps)
  thus "e \<in> uminus ` X" by force
qed

lemma is_interval_uminus[simp]: "is_interval (uminus ` x) = is_interval x"
  using is_interval_uminusI[of x] is_interval_uminusI[of "uminus ` x"]
  by (auto simp: image_image)

lemma is_interval_neg_translationI:
  assumes "is_interval X"
  shows "is_interval ((-) x ` X)"
proof -
  have "(-) x ` X = (+) x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots>"
    by (metis is_interval_uminusI is_interval_translationI assms)
  finally show ?thesis .
qed

lemma is_interval_translation[simp]:
  "is_interval ((+) x ` X) = is_interval X"
  using is_interval_neg_translationI[of "(+) x ` X" x]
  by (auto intro!: is_interval_translationI simp: image_image)

lemma is_interval_minus_translation[simp]:
  shows "is_interval ((-) x ` X) = is_interval X"
proof -
  have "(-) x ` X = (+) x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots> = is_interval X"
    by simp
  finally show ?thesis .
qed

lemma is_interval_minus_translation'[simp]:
  shows "is_interval ((\<lambda>x. x - c) ` X) = is_interval X"
  using is_interval_translation[of "-c" X]
  by (metis image_cong uminus_add_conv_diff)

lemma compact_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a. \<exists> r.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially)"
  by (rule compact_lemma_general[where unproj="\<lambda>e. \<Sum>i\<in>Basis. e i *\<^sub>R i"])
     (auto intro!: assms bounded_linear_inner_left bounded_linear_image
       simp: euclidean_representation)

instance%important euclidean_space \<subseteq> heine_borel
proof%unimportant
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "bounded (range f)"
  then obtain l::'a and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially"
    using compact_lemma [OF f] by blast
  {
    fix e::real
    assume "e > 0"
    hence "e / real_of_nat DIM('a) > 0" by (simp add: DIM_positive)
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))) sequentially"
      by simp
    moreover
    {
      fix n
      assume n: "\<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i))"
        apply (subst euclidean_dist_l2)
        using zero_le_dist
        apply (rule L2_set_le_sum)
        done
      also have "\<dots> < (\<Sum>i\<in>(Basis::'a set). e / (real_of_nat DIM('a)))"
        apply (rule sum_strict_mono)
        using n
        apply auto
        done
      finally have "dist (f (r n)) l < e"
        by auto
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  then have *: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    by auto
qed

instance euclidean_space \<subseteq> banach ..


subsubsection%unimportant \<open>Structural rules for pointwise continuity\<close>

lemma continuous_infnorm[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. infnorm (f x))"
  unfolding continuous_def by (rule tendsto_infnorm)

lemma continuous_inner[continuous_intros]:
  assumes "continuous F f"
    and "continuous F g"
  shows "continuous F (\<lambda>x. inner (f x) (g x))"
  using assms unfolding continuous_def by (rule tendsto_inner)


subsubsection%unimportant \<open>Structural rules for setwise continuity\<close>

lemma continuous_on_infnorm[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. infnorm (f x))"
  unfolding continuous_on by (fast intro: tendsto_infnorm)

lemma continuous_on_inner[continuous_intros]:
  fixes g :: "'a::topological_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on s f"
    and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. inner (f x) (g x))"
  using bounded_bilinear_inner assms
  by (rule bounded_bilinear.continuous_on)

subsection%unimportant \<open>Intervals\<close>

text \<open>Openness of halfspaces.\<close>

lemma open_halfspace_lt: "open {x. inner a x < b}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_gt: "open {x. inner a x > b}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_component_lt: "open {x::'a::euclidean_space. x\<bullet>i < a}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_component_gt: "open {x::'a::euclidean_space. x\<bullet>i > a}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

text \<open>This gives a simple derivation of limit component bounds.\<close>

lemma open_box[intro]: "open (box a b)"
proof -
  have "open (\<Inter>i\<in>Basis. ((\<bullet>) i) -` {a \<bullet> i <..< b \<bullet> i})"
    by (auto intro!: continuous_open_vimage continuous_inner continuous_ident continuous_const)
  also have "(\<Inter>i\<in>Basis. ((\<bullet>) i) -` {a \<bullet> i <..< b \<bullet> i}) = box a b"
    by (auto simp: box_def inner_commute)
  finally show ?thesis .
qed

instance euclidean_space \<subseteq> second_countable_topology
proof
  define a where "a f = (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have a: "\<And>f. (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i) = a f"
    by simp
  define b where "b f = (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have b: "\<And>f. (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i) = b f"
    by simp
  define B where "B = (\<lambda>f. box (a f) (b f)) ` (Basis \<rightarrow>\<^sub>E (\<rat> \<times> \<rat>))"

  have "Ball B open" by (simp add: B_def open_box)
  moreover have "(\<forall>A. open A \<longrightarrow> (\<exists>B'\<subseteq>B. \<Union>B' = A))"
  proof safe
    fix A::"'a set"
    assume "open A"
    show "\<exists>B'\<subseteq>B. \<Union>B' = A"
      apply (rule exI[of _ "{b\<in>B. b \<subseteq> A}"])
      apply (subst (3) open_UNION_box[OF \<open>open A\<close>])
      apply (auto simp: a b B_def)
      done
  qed
  ultimately
  have "topological_basis B"
    unfolding topological_basis_def by blast
  moreover
  have "countable B"
    unfolding B_def
    by (intro countable_image countable_PiE finite_Basis countable_SIGMA countable_rat)
  ultimately show "\<exists>B::'a set set. countable B \<and> open = generate_topology B"
    by (blast intro: topological_basis_imp_subbasis)
qed

instance euclidean_space \<subseteq> polish_space ..

lemma closed_cbox[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "closed (cbox a b)"
proof -
  have "closed (\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i})"
    by (intro closed_INT ballI continuous_closed_vimage allI
      linear_continuous_at closed_real_atLeastAtMost finite_Basis bounded_linear_inner_left)
  also have "(\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i}) = cbox a b"
    by (auto simp: cbox_def)
  finally show "closed (cbox a b)" .
qed

lemma interior_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "interior (cbox a b) = box a b" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L"
    using box_subset_cbox open_box
    by (rule interior_maximal)
  {
    fix x
    assume "x \<in> interior (cbox a b)"
    then obtain s where s: "open s" "x \<in> s" "s \<subseteq> cbox a b" ..
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> cbox a b"
      unfolding open_dist and subset_eq by auto
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "dist (x - (e / 2) *\<^sub>R i) x < e"
        and "dist (x + (e / 2) *\<^sub>R i) x < e"
        unfolding dist_norm
        apply auto
        unfolding norm_minus_cancel
        using norm_Basis[OF i] \<open>e>0\<close>
        apply auto
        done
      then have "a \<bullet> i \<le> (x - (e / 2) *\<^sub>R i) \<bullet> i" and "(x + (e / 2) *\<^sub>R i) \<bullet> i \<le> b \<bullet> i"
        using e[THEN spec[where x="x - (e/2) *\<^sub>R i"]]
          and e[THEN spec[where x="x + (e/2) *\<^sub>R i"]]
        unfolding mem_box
        using i
        by blast+
      then have "a \<bullet> i < x \<bullet> i" and "x \<bullet> i < b \<bullet> i"
        using \<open>e>0\<close> i
        by (auto simp: inner_diff_left inner_Basis inner_add_left)
    }
    then have "x \<in> box a b"
      unfolding mem_box by auto
  }
  then show "?L \<subseteq> ?R" ..
qed

lemma bounded_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b)"
proof -
  let ?b = "\<Sum>i\<in>Basis. \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
  {
    fix x :: "'a"
    assume "\<And>i. i\<in>Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
    then have "(\<Sum>i\<in>Basis. \<bar>x \<bullet> i\<bar>) \<le> ?b"
      by (force simp: intro!: sum_mono)
    then have "norm x \<le> ?b"
      using norm_le_l1[of x] by auto
  }
  then show ?thesis
    unfolding cbox_def bounded_iff by force
qed

lemma bounded_box [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (box a b)"
  using bounded_cbox[of a b] box_subset_cbox[of a b] bounded_subset[of "cbox a b" "box a b"]
  by simp

lemma not_interval_UNIV [simp]:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> UNIV" "box a b \<noteq> UNIV"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma not_interval_UNIV2 [simp]:
  fixes a :: "'a::euclidean_space"
  shows "UNIV \<noteq> cbox a b" "UNIV \<noteq> box a b"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma compact_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "compact (cbox a b)"
  using bounded_closed_imp_seq_compact[of "cbox a b"] using bounded_cbox[of a b]
  by (auto simp: compact_eq_seq_compact_metric)

lemma box_midpoint:
  fixes a :: "'a::euclidean_space"
  assumes "box a b \<noteq> {}"
  shows "((1/2) *\<^sub>R (a + b)) \<in> box a b"
proof -
  have "a \<bullet> i < ((1 / 2) *\<^sub>R (a + b)) \<bullet> i \<and> ((1 / 2) *\<^sub>R (a + b)) \<bullet> i < b \<bullet> i" if "i \<in> Basis" for i
    using assms that by (auto simp: inner_add_left box_ne_empty)
  then show ?thesis unfolding mem_box by auto
qed

lemma open_cbox_convex:
  fixes x :: "'a::euclidean_space"
  assumes x: "x \<in> box a b"
    and y: "y \<in> cbox a b"
    and e: "0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "a \<bullet> i = e * (a \<bullet> i) + (1 - e) * (a \<bullet> i)"
      unfolding left_diff_distrib by simp
    also have "\<dots> < e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
    proof (rule add_less_le_mono)
      show "e * (a \<bullet> i) < e * (x \<bullet> i)"
        using \<open>0 < e\<close> i mem_box(1) x by auto
      show "(1 - e) * (a \<bullet> i) \<le> (1 - e) * (y \<bullet> i)"
        by (meson diff_ge_0_iff_ge \<open>e \<le> 1\<close> i mem_box(2) mult_left_mono y)
    qed
    finally have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i"
      unfolding inner_simps by auto
    moreover
    {
      have "b \<bullet> i = e * (b\<bullet>i) + (1 - e) * (b\<bullet>i)"
        unfolding left_diff_distrib by simp
      also have "\<dots> > e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
      proof (rule add_less_le_mono)
        show "e * (x \<bullet> i) < e * (b \<bullet> i)"
          using \<open>0 < e\<close> i mem_box(1) x by auto
        show "(1 - e) * (y \<bullet> i) \<le> (1 - e) * (b \<bullet> i)"
          by (meson diff_ge_0_iff_ge \<open>e \<le> 1\<close> i mem_box(2) mult_left_mono y)
      qed
      finally have "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
        unfolding inner_simps by auto
    }
    ultimately have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i \<and> (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
      by auto
  }
  then show ?thesis
    unfolding mem_box by auto
qed

lemma closure_cbox [simp]: "closure (cbox a b) = cbox a b"
  by (simp add: closed_cbox)

lemma closure_box [simp]:
  fixes a :: "'a::euclidean_space"
   assumes "box a b \<noteq> {}"
  shows "closure (box a b) = cbox a b"
proof -
  have ab: "a <e b"
    using assms by (simp add: eucl_less_def box_ne_empty)
  let ?c = "(1 / 2) *\<^sub>R (a + b)"
  {
    fix x
    assume as:"x \<in> cbox a b"
    define f where [abs_def]: "f n = x + (inverse (real n + 1)) *\<^sub>R (?c - x)" for n
    {
      fix n
      assume fn: "f n <e b \<longrightarrow> a <e f n \<longrightarrow> f n = x" and xc: "x \<noteq> ?c"
      have *: "0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1"
        unfolding inverse_le_1_iff by auto
      have "(inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b)) + (1 - inverse (real n + 1)) *\<^sub>R x =
        x + (inverse (real n + 1)) *\<^sub>R (((1 / 2) *\<^sub>R (a + b)) - x)"
        by (auto simp: algebra_simps)
      then have "f n <e b" and "a <e f n"
        using open_cbox_convex[OF box_midpoint[OF assms] as *]
        unfolding f_def by (auto simp: box_def eucl_less_def)
      then have False
        using fn unfolding f_def using xc by auto
    }
    moreover
    {
      assume "\<not> (f \<longlongrightarrow> x) sequentially"
      {
        fix e :: real
        assume "e > 0"
        then obtain N :: nat where N: "inverse (real (N + 1)) < e"
          using reals_Archimedean by auto
        have "inverse (real n + 1) < e" if "N \<le> n" for n
          by (auto intro!: that le_less_trans [OF _ N])
        then have "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto
      }
      then have "((\<lambda>n. inverse (real n + 1)) \<longlongrightarrow> 0) sequentially"
        unfolding lim_sequentially by(auto simp: dist_norm)
      then have "(f \<longlongrightarrow> x) sequentially"
        unfolding f_def
        using tendsto_add[OF tendsto_const, of "\<lambda>n::nat. (inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x)" 0 sequentially x]
        using tendsto_scaleR [OF _ tendsto_const, of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *\<^sub>R (a + b) - x)"]
        by auto
    }
    ultimately have "x \<in> closure (box a b)"
      using as box_midpoint[OF assms]
      unfolding closure_def islimpt_sequential
      by (cases "x=?c") (auto simp: in_box_eucl_less)
  }
  then show ?thesis
    using closure_minimal[OF box_subset_cbox, of a b] by blast
qed

lemma bounded_subset_box_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> box (-a) a"
proof -
  obtain b where "b>0" and b: "\<forall>x\<in>S. norm x \<le> b"
    using assms[unfolded bounded_pos] by auto
  define a :: 'a where "a = (\<Sum>i\<in>Basis. (b + 1) *\<^sub>R i)"
  have "(-a)\<bullet>i < x\<bullet>i" and "x\<bullet>i < a\<bullet>i" if "x \<in> S" and i: "i \<in> Basis" for x i
    using b Basis_le_norm[OF i, of x] that by (auto simp: a_def)
  then have "S \<subseteq> box (-a) a"
    by (auto simp: simp add: box_def)
  then show ?thesis ..
qed

lemma bounded_subset_cbox_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> cbox (-a) a"
proof -
  obtain a where "S \<subseteq> box (-a) a"
    using bounded_subset_box_symmetric[OF assms] by auto
  then show ?thesis
    by (meson box_subset_cbox dual_order.trans that)
qed

lemma frontier_cbox:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (cbox a b) = cbox a b - box a b"
  unfolding frontier_def unfolding interior_cbox and closure_closed[OF closed_cbox] ..

lemma frontier_box:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (box a b) = (if box a b = {} then {} else cbox a b - box a b)"
proof (cases "box a b = {}")
  case True
  then show ?thesis
    using frontier_empty by auto
next
  case False
  then show ?thesis
    unfolding frontier_def and closure_box[OF False] and interior_open[OF open_box]
    by auto
qed

lemma Int_interval_mixed_eq_empty:
  fixes a :: "'a::euclidean_space"
   assumes "box c d \<noteq> {}"
  shows "box a b \<inter> cbox c d = {} \<longleftrightarrow> box a b \<inter> box c d = {}"
  unfolding closure_box[OF assms, symmetric]
  unfolding open_Int_closure_eq_empty[OF open_box] ..

lemma eucl_less_eq_halfspaces:
  fixes a :: "'a::euclidean_space"
  shows "{x. x <e a} = (\<Inter>i\<in>Basis. {x. x \<bullet> i < a \<bullet> i})"
        "{x. a <e x} = (\<Inter>i\<in>Basis. {x. a \<bullet> i < x \<bullet> i})"
  by (auto simp: eucl_less_def)

lemma open_Collect_eucl_less[simp, intro]:
  fixes a :: "'a::euclidean_space"
  shows "open {x. x <e a}" "open {x. a <e x}"
  by (auto simp: eucl_less_eq_halfspaces open_halfspace_component_lt open_halfspace_component_gt)

no_notation
  eucl_less (infix "<e" 50)

end
