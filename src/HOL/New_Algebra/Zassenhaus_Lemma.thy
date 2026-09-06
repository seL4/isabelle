(*
  The Zassenhaus (butterfly) lemma, developed directly over New-Algebra's
  set-based group and quotient infrastructure.
*)

theory Zassenhaus_Lemma
  imports Group_Theory
begin

section \<open>The Zassenhaus Lemma\<close>

text \<open>
  Suppose that @{term H1} is normal in @{term H}, and @{term K1} is normal in
  @{term K}.  The two wings of the butterfly are obtained by multiplying each
  normal subgroup by @{term "H \<inter> K"}; their denominators use the smaller
  intersections @{term "H \<inter> K1"} and @{term "K \<inter> H1"}.

  A locale records this symmetric configuration once.  In particular, no
  ambient record updates or HOL-Algebra structures occur in the statement.
\<close>
locale zassenhaus =
  G: Group G "(\<cdot>)" \<one> +
  H: subgroup_of_group H G "(\<cdot>)" \<one> +
  K: subgroup_of_group K G "(\<cdot>)" \<one> +
  H1: normal_subgroup H1 H "(\<cdot>)" \<one> +
  K1: normal_subgroup K1 K "(\<cdot>)" \<one>
  for G H K H1 K1 and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

interpretation HK_sub: Subgroup "H \<inter> K" G "(\<cdot>)" \<one>
  by (rule G.subgroup_intersection[OF H.Subgroup_axioms K.Subgroup_axioms])

interpretation HK1_sub: Subgroup "H \<inter> K1" H "(\<cdot>)" \<one>
proof -
  have K1_G: "Subgroup K1 G (\<cdot>) \<one>"
    by (rule subgroup_transitive[OF K1.Subgroup_axioms K.Subgroup_axioms])
  have I_G: "Subgroup (H \<inter> K1) G (\<cdot>) \<one>"
    by (rule G.subgroup_intersection[OF H.Subgroup_axioms K1_G])
  show "Subgroup (H \<inter> K1) H (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF I_G H.Subgroup_axioms])
    show "H \<inter> K1 \<subseteq> H" by blast
  qed
qed

interpretation KH1_sub: Subgroup "K \<inter> H1" K "(\<cdot>)" \<one>
proof -
  have H1_G: "Subgroup H1 G (\<cdot>) \<one>"
    by (rule subgroup_transitive[OF H1.Subgroup_axioms H.Subgroup_axioms])
  have I_G: "Subgroup (K \<inter> H1) G (\<cdot>) \<one>"
    by (rule G.subgroup_intersection[OF K.Subgroup_axioms H1_G])
  show "Subgroup (K \<inter> H1) K (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF I_G K.Subgroup_axioms])
    show "K \<inter> H1 \<subseteq> K" by blast
  qed
qed

interpretation HK1_normal: normal_subgroup "H \<inter> K1" "H \<inter> K" "(\<cdot>)" \<one>
proof -
  have I_sub: "Subgroup (H \<inter> K) K (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF HK_sub.Subgroup_axioms K.Subgroup_axioms])
    show "H \<inter> K \<subseteq> K" by blast
  qed
  have C_K: "Subgroup (H \<inter> K1) K (\<cdot>) \<one>"
  proof -
    have "Subgroup ((H \<inter> K) \<inter> K1) K (\<cdot>) \<one>"
      by (rule K.sub.subgroup_intersection[OF I_sub K1.Subgroup_axioms])
    moreover have "(H \<inter> K) \<inter> K1 = H \<inter> K1"
      using K1.sub by blast
    ultimately show ?thesis by simp
  qed
  have C_sub: "Subgroup (H \<inter> K1) (H \<inter> K) (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF C_K I_sub])
    show "H \<inter> K1 \<subseteq> H \<inter> K" using K1.sub by blast
  qed
  interpret C: Subgroup "H \<inter> K1" "H \<inter> K" "(\<cdot>)" \<one> by fact
  interpret I: Subgroup "H \<inter> K" K "(\<cdot>)" \<one> by fact
  have I_H_sub: "Subgroup (H \<inter> K) H (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF HK_sub.Subgroup_axioms H.Subgroup_axioms])
    show "H \<inter> K \<subseteq> H" by blast
  qed
  interpret I_H: Subgroup "H \<inter> K" H "(\<cdot>)" \<one> by fact
  show "normal_subgroup (H \<inter> K1) (H \<inter> K) (\<cdot>) \<one>"
  proof
    fix g c
    assume g: "g \<in> H \<inter> K" and c: "c \<in> H \<inter> K1"
    have inv_K: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = K.sub.inverse g"
      by (rule I.subgroup_inverse_equality[symmetric]) (rule g)
    have inv_H: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = H.sub.inverse g"
      by (rule I_H.subgroup_inverse_equality[symmetric]) (rule g)
    have g_H: "g \<in> H" and c_H: "c \<in> H" and g_K: "g \<in> K" and c_K1: "c \<in> K1"
      using g c by blast+
    have inv_g_H: "H.sub.inverse g \<in> H"
      by (rule H.sub.invertible_inverse_closed[OF H.sub.invertible[OF g_H] g_H])
    have in_H: "H.sub.inverse g \<cdot> c \<cdot> g \<in> H"
      by (rule H.sub.composition_closed[OF H.sub.composition_closed[OF inv_g_H c_H] g_H])
    have in_K1: "K.sub.inverse g \<cdot> c \<cdot> g \<in> K1"
      by (rule K1.normal[OF g_K c_K1])
    show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> H \<inter> K1"
    proof
      show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> H"
        using in_H by (simp only: inv_H)
      show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> K1"
        using in_K1 by (simp only: inv_K)
    qed
  qed
qed

interpretation KH1_normal: normal_subgroup "K \<inter> H1" "H \<inter> K" "(\<cdot>)" \<one>
proof -
  have I_sub: "Subgroup (H \<inter> K) H (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF HK_sub.Subgroup_axioms H.Subgroup_axioms])
    show "H \<inter> K \<subseteq> H" by blast
  qed
  have C_H: "Subgroup (K \<inter> H1) H (\<cdot>) \<one>"
  proof -
    have "Subgroup ((H \<inter> K) \<inter> H1) H (\<cdot>) \<one>"
      by (rule H.sub.subgroup_intersection[OF I_sub H1.Subgroup_axioms])
    moreover have "(H \<inter> K) \<inter> H1 = K \<inter> H1"
      using H1.sub by blast
    ultimately show ?thesis by simp
  qed
  have C_sub: "Subgroup (K \<inter> H1) (H \<inter> K) (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF C_H I_sub])
    show "K \<inter> H1 \<subseteq> H \<inter> K" using H1.sub by blast
  qed
  interpret C: Subgroup "K \<inter> H1" "H \<inter> K" "(\<cdot>)" \<one> by fact
  interpret I: Subgroup "H \<inter> K" H "(\<cdot>)" \<one> by fact
  have I_K_sub: "Subgroup (H \<inter> K) K (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF HK_sub.Subgroup_axioms K.Subgroup_axioms])
    show "H \<inter> K \<subseteq> K" by blast
  qed
  interpret I_K: Subgroup "H \<inter> K" K "(\<cdot>)" \<one> by fact
  show "normal_subgroup (K \<inter> H1) (H \<inter> K) (\<cdot>) \<one>"
  proof
    fix g c
    assume g: "g \<in> H \<inter> K" and c: "c \<in> K \<inter> H1"
    have inv_H: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = H.sub.inverse g"
      by (rule I.subgroup_inverse_equality[symmetric]) (rule g)
    have inv_K: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = K.sub.inverse g"
      by (rule I_K.subgroup_inverse_equality[symmetric]) (rule g)
    have g_K: "g \<in> K" and c_K: "c \<in> K" and g_H: "g \<in> H" and c_H1: "c \<in> H1"
      using g c by blast+
    have inv_g_K: "K.sub.inverse g \<in> K"
      by (rule K.sub.invertible_inverse_closed[OF K.sub.invertible[OF g_K] g_K])
    have in_K: "K.sub.inverse g \<cdot> c \<cdot> g \<in> K"
      by (rule K.sub.composition_closed[OF K.sub.composition_closed[OF inv_g_K c_K] g_K])
    have in_H1: "H.sub.inverse g \<cdot> c \<cdot> g \<in> H1"
      by (rule H1.normal[OF g_H c_H1])
    show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> K \<inter> H1"
    proof
      show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> K"
        using in_K by (simp only: inv_K)
      show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> H1"
        using in_H1 by (simp only: inv_H)
    qed
  qed
qed

interpretation middle_H: Subgroup "H \<inter> K" H "(\<cdot>)" \<one>
  by (rule subgroup_restrict[OF HK_sub.Subgroup_axioms H.Subgroup_axioms]) blast

interpretation middle_K: Subgroup "H \<inter> K" K "(\<cdot>)" \<one>
  by (rule subgroup_restrict[OF HK_sub.Subgroup_axioms K.Subgroup_axioms]) blast

interpretation middle_H_group: subgroup_of_group "H \<inter> K" H "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF middle_H.Subgroup_axioms H.sub.Group_axioms])

interpretation middle_K_group: subgroup_of_group "H \<inter> K" K "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF middle_K.Subgroup_axioms K.sub.Group_axioms])

interpretation HK1_group: subgroup_of_group "H \<inter> K1" H "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF HK1_sub.Subgroup_axioms H.sub.Group_axioms])

interpretation KH1_group: subgroup_of_group "K \<inter> H1" K "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF KH1_sub.Subgroup_axioms K.sub.Group_axioms])

text \<open>The four subgroup products making up the two wings.\<close>
definition left_top where
  "left_top = (case_prod (\<cdot>)) ` ((H \<inter> K) \<times> H1)"

definition left_bottom where
  "left_bottom = (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> H1)"

definition right_top where
  "right_top = (case_prod (\<cdot>)) ` ((H \<inter> K) \<times> K1)"

definition right_bottom where
  "right_bottom = (case_prod (\<cdot>)) ` ((K \<inter> H1) \<times> K1)"

interpretation left_top_product:
  normal_subgroup_product H1 "H \<inter> K" H "(\<cdot>)" \<one>
  ..

interpretation left_bottom_product:
  normal_subgroup_product H1 "H \<inter> K1" H "(\<cdot>)" \<one>
  ..

interpretation right_top_product:
  normal_subgroup_product K1 "H \<inter> K" K "(\<cdot>)" \<one>
  ..

interpretation right_bottom_product:
  normal_subgroup_product K1 "K \<inter> H1" K "(\<cdot>)" \<one>
  ..

lemma left_top_eq [simp]: "left_top = left_top_product.HK"
  by (simp add: left_top_def left_top_product.HK_def)

lemma left_bottom_eq [simp]: "left_bottom = left_bottom_product.HK"
  by (simp add: left_bottom_def left_bottom_product.HK_def)

lemma right_top_eq [simp]: "right_top = right_top_product.HK"
  by (simp add: right_top_def right_top_product.HK_def)

lemma right_bottom_eq [simp]: "right_bottom = right_bottom_product.HK"
  by (simp add: right_bottom_def right_bottom_product.HK_def)

lemma left_top_subgroup: "Subgroup left_top H (\<cdot>) \<one>"
  by (simp add: left_top_product.HK_subgroup)

lemma left_bottom_subgroup: "Subgroup left_bottom H (\<cdot>) \<one>"
  by (simp add: left_bottom_product.HK_subgroup)

lemma right_top_subgroup: "Subgroup right_top K (\<cdot>) \<one>"
  by (simp add: right_top_product.HK_subgroup)

lemma right_bottom_subgroup: "Subgroup right_bottom K (\<cdot>) \<one>"
  by (simp add: right_bottom_product.HK_subgroup)

lemma left_bottom_subset_top: "left_bottom \<subseteq> left_top"
  unfolding left_bottom_def left_top_def
  by (rule image_mono) (use K1.sub in blast)

lemma right_bottom_subset_top: "right_bottom \<subseteq> right_top"
  unfolding right_bottom_def right_top_def
  by (rule image_mono) (use H1.sub in blast)

lemma left_top_memE:
  assumes "x \<in> left_top"
  obtains b n where "b \<in> H \<inter> K" "n \<in> H1" "x = b \<cdot> n"
proof -
  have "x \<in> left_top_product.HK" using assms by (simp only: left_top_eq)
  then show thesis using that by (rule left_top_product.HK_memE)
qed

lemma left_bottom_memI:
  "\<lbrakk>c \<in> H \<inter> K1; n \<in> H1\<rbrakk> \<Longrightarrow> c \<cdot> n \<in> left_bottom"
  by (simp only: left_bottom_eq) (rule left_bottom_product.HK_memI)

lemma left_bottom_memE:
  assumes "x \<in> left_bottom"
  obtains c n where "c \<in> H \<inter> K1" "n \<in> H1" "x = c \<cdot> n"
proof -
  have "x \<in> left_bottom_product.HK" using assms by (simp only: left_bottom_eq)
  then show thesis using that by (rule left_bottom_product.HK_memE)
qed

text \<open>The lower subgroup in the left wing is normal in the upper one.\<close>
lemma left_bottom_normal: "normal_subgroup left_bottom left_top (\<cdot>) \<one>"
proof -
  have bottom_top: "Subgroup left_bottom left_top (\<cdot>) \<one>"
    by (rule subgroup_restrict[OF left_bottom_subgroup left_top_subgroup left_bottom_subset_top])
  interpret bottom: Subgroup left_bottom left_top "(\<cdot>)" \<one> by fact
  interpret top_H: Subgroup left_top H "(\<cdot>)" \<one> by (rule left_top_subgroup)
  show ?thesis
  proof
    fix x y
    assume x: "x \<in> left_top" and y: "y \<in> left_bottom"
    obtain b n where b: "b \<in> H \<inter> K" and n: "n \<in> H1" and x_eq: "x = b \<cdot> n"
      using x by (rule left_top_memE)
    obtain c m where c: "c \<in> H \<inter> K1" and m: "m \<in> H1" and y_eq: "y = c \<cdot> m"
      using y by (rule left_bottom_memE)
    have bH: "b \<in> H" and cH: "c \<in> H" and nH: "n \<in> H" and mH: "m \<in> H"
      using b c n m H1.sub by blast+
    have b_middle: "b \<in> H \<inter> K" by fact
    have inv_middle:
      "H.sub.inverse b = Monoid.inverse (H \<inter> K) (\<cdot>) \<one> b"
      by (rule middle_H.subgroup_inverse_equality) (rule b)
    have conjugate_c: "H.sub.inverse b \<cdot> c \<cdot> b \<in> H \<inter> K1"
      using HK1_normal.normal[OF b_middle c]
      by (simp only: inv_middle)
    have conjugate_m: "H.sub.inverse b \<cdot> m \<cdot> b \<in> H1"
      by (rule H1.normal[OF bH m])
    have conjugate_y: "H.sub.inverse b \<cdot> y \<cdot> b \<in> left_bottom"
    proof -
      have conjugate_product: "H.sub.inverse b \<cdot> (c \<cdot> m) \<cdot> b =
            (H.sub.inverse b \<cdot> c \<cdot> b) \<cdot> (H.sub.inverse b \<cdot> m \<cdot> b)"
        by (rule H.sub.conjugate_composition[OF H.sub.invertible[OF bH] bH cH mH])
      have "(H.sub.inverse b \<cdot> c \<cdot> b) \<cdot>
            (H.sub.inverse b \<cdot> m \<cdot> b) \<in> left_bottom"
        by (rule left_bottom_memI[OF conjugate_c conjugate_m])
      then show ?thesis unfolding y_eq by (subst conjugate_product)
    qed
    have inv_n: "H.sub.inverse n \<in> H1"
      by (rule H1.submonoid_inverse_closed[OF H1.sub.invertible[OF n] n])
    have inv_n_bottom: "H.sub.inverse n \<in> left_bottom"
    proof -
      have "H.sub.inverse n \<in> left_bottom_product.HK"
        using left_bottom_product.K_subset_HK inv_n by blast
      then show ?thesis by (simp only: left_bottom_eq)
    qed
    have n_bottom: "n \<in> left_bottom"
    proof -
      have "n \<in> left_bottom_product.HK"
        using left_bottom_product.K_subset_HK n by blast
      then show ?thesis by (simp only: left_bottom_eq)
    qed
    have conjugate_x_y: "H.sub.inverse x \<cdot> y \<cdot> x \<in> left_bottom"
    proof -
      have inv_x: "H.sub.inverse x = H.sub.inverse n \<cdot> H.sub.inverse b"
        unfolding x_eq
        by (rule H.sub.inverse_composition_commute[OF H.sub.invertible[OF bH]
              H.sub.invertible[OF nH] bH nH])
      have inv_b_H: "H.sub.inverse b \<in> H"
        by (rule H.sub.invertible_inverse_closed[OF H.sub.invertible[OF bH] bH])
      have inv_n_H: "H.sub.inverse n \<in> H"
        by (rule H.sub.invertible_inverse_closed[OF H.sub.invertible[OF nH] nH])
      have y_top: "y \<in> left_top" using bottom.subset y by blast
      have yH: "y \<in> H" using top_H.subset y_top by blast
      have conjugate_expansion: "H.sub.inverse x \<cdot> y \<cdot> x =
            H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y \<cdot> b) \<cdot> n"
      proof -
        have "(H.sub.inverse n \<cdot> H.sub.inverse b) \<cdot> y \<cdot> (b \<cdot> n) =
              (H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y)) \<cdot> (b \<cdot> n)"
          by (subst H.sub.associative[OF inv_n_H inv_b_H yH]) rule
        also have "... = (H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y) \<cdot> b) \<cdot> n"
          by (rule H.sub.associative[OF
                H.sub.composition_closed[OF inv_n_H H.sub.composition_closed[OF inv_b_H yH]] bH nH,
                symmetric])
        also have "... = H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y \<cdot> b) \<cdot> n"
          by (subst H.sub.associative[OF inv_n_H H.sub.composition_closed[OF inv_b_H yH] bH]) rule
        finally show ?thesis
          by (subst inv_x, subst x_eq)
      qed
      have "H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y \<cdot> b) \<cdot> n
            \<in> left_bottom"
        by (rule bottom.sub_composition_closed[OF
              bottom.sub_composition_closed[OF inv_n_bottom conjugate_y] n_bottom])
      then show ?thesis by (subst conjugate_expansion)
    qed
    have top_inverse: "H.sub.inverse x = Monoid.inverse left_top (\<cdot>) \<one> x"
      by (rule top_H.subgroup_inverse_equality) (rule x)
    show "Monoid.inverse left_top (\<cdot>) \<one> x \<cdot> y \<cdot> x \<in> left_bottom"
      using conjugate_x_y by (simp only: top_inverse)
  qed
qed

text \<open>
  The following two identities are the algebraic centre of the butterfly.  An
  element of the middle intersection that is written as a product in one wing
  forces its normal-subgroup factor into the opposite subgroup.
\<close>
lemma middle_inter_left_bottom:
  "(H \<inter> K) \<inter> left_bottom =
   (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1))"
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> (H \<inter> K) \<inter> left_bottom"
  have x_bottom: "x \<in> left_bottom" using x by (simp only: Int_iff)
  then obtain p where p_in: "p \<in> (H \<inter> K1) \<times> H1"
    and p_eq: "x = case_prod (\<cdot>) p"
    unfolding left_bottom_def by blast
  obtain c h where p: "p = (c,h)" by (cases p)
  have c: "c \<in> H \<inter> K1" and h: "h \<in> H1"
    using p_in unfolding p by blast+
  have x_eq: "x = c \<cdot> h" using p_eq by (simp only: p prod.case)
  have cK: "c \<in> K" using c K1.sub by blast
  have xK: "x \<in> K" using x by blast
  have cG: "c \<in> G" and hG: "h \<in> G"
    using c h H.sub H1.sub by blast+
  have "G.inverse c \<cdot> x = h"
    unfolding x_eq
    by (rule G.invertible_left_inverse2[OF G.invertible[OF cG] cG hG])
  have inv_c_K: "G.inverse c \<in> K"
    by (rule K.submonoid_inverse_closed[OF K.sub.invertible[OF cK] cK])
  have inv_c_x_K: "G.inverse c \<cdot> x \<in> K"
    by (rule K.sub_composition_closed[OF inv_c_K xK])
  then have hK: "h \<in> K" using \<open>G.inverse c \<cdot> x = h\<close>
    by (simp only: \<open>G.inverse c \<cdot> x = h\<close>)
  show "x \<in> (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1))"
  proof (rule image_eqI[where x="(c,h)"])
    show "(c,h) \<in> (H \<inter> K1) \<times> (K \<inter> H1)" using c h hK by blast
    show "x = case_prod (\<cdot>) (c,h)" using x_eq by (simp only: prod.case)
  qed
next
  fix x
  assume "x \<in> (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1))"
  then obtain p where p_in: "p \<in> (H \<inter> K1) \<times> (K \<inter> H1)"
    and p_eq: "x = case_prod (\<cdot>) p" by blast
  obtain c h where p: "p = (c,h)" by (cases p)
  have c: "c \<in> H \<inter> K1" and h: "h \<in> K \<inter> H1"
    using p_in unfolding p by blast+
  have x_eq: "x = c \<cdot> h" using p_eq by (simp only: p prod.case)
  have cH: "c \<in> H" and cK: "c \<in> K" and hH: "h \<in> H" and hK: "h \<in> K"
    using c h H1.sub K1.sub by blast+
  have "x \<in> H \<inter> K"
    unfolding x_eq
    using H.sub_composition_closed[OF cH hH] K.sub_composition_closed[OF cK hK] by blast
  moreover have "x \<in> left_bottom"
    unfolding left_bottom_def using c h x_eq by blast
  ultimately show "x \<in> (H \<inter> K) \<inter> left_bottom" by blast
qed

interpretation symmetric: zassenhaus G K H K1 H1 "(\<cdot>)" \<one> ..

lemma middle_inter_right_bottom:
  "(H \<inter> K) \<inter> right_bottom =
   (case_prod (\<cdot>)) ` ((K \<inter> H1) \<times> (H \<inter> K1))"
  using symmetric.middle_inter_left_bottom
  unfolding symmetric.left_bottom_def right_bottom_def
  by (simp add: Int_commute)

text \<open>The normality argument for the right wing is exactly the symmetric instance.\<close>
lemma right_bottom_normal: "normal_subgroup right_bottom right_top (\<cdot>) \<one>"
  using symmetric.left_bottom_normal
  unfolding symmetric.left_bottom_def symmetric.left_top_def right_bottom_def right_top_def
  by (simp only: Int_commute)

subsection \<open>The quotient isomorphism\<close>

interpretation left_quotient: normal_subgroup left_bottom left_top "(\<cdot>)" \<one>
  by (rule left_bottom_normal)

interpretation right_quotient: normal_subgroup right_bottom right_top "(\<cdot>)" \<one>
  by (rule right_bottom_normal)

lemma middle_subset_left_top: "H \<inter> K \<subseteq> left_top"
  using left_top_product.H_subset_HK unfolding left_top_eq .

lemma middle_subset_right_top: "H \<inter> K \<subseteq> right_top"
  using right_top_product.H_subset_HK unfolding right_top_eq .

lemma middle_left_top_subgroup: "Subgroup (H \<inter> K) left_top (\<cdot>) \<one>"
  by (rule subgroup_restrict[OF middle_H.Subgroup_axioms left_top_subgroup middle_subset_left_top])

lemma middle_right_top_subgroup: "Subgroup (H \<inter> K) right_top (\<cdot>) \<one>"
  by (rule subgroup_restrict[OF middle_K.Subgroup_axioms right_top_subgroup middle_subset_right_top])

interpretation middle_left_top: subgroup_of_group "H \<inter> K" left_top "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF middle_left_top_subgroup left_quotient.Group_axioms])

interpretation middle_right_top: subgroup_of_group "H \<inter> K" right_top "(\<cdot>)" \<one>
  by (rule subgroup_of_groupI[OF middle_right_top_subgroup right_quotient.Group_axioms])

interpretation left_second:
  second_iso_theorem left_bottom "H \<inter> K" left_top "(\<cdot>)" \<one>
  by unfold_locales

interpretation right_second:
  second_iso_theorem right_bottom "H \<inter> K" right_top "(\<cdot>)" \<one>
  by unfold_locales

lemma left_second_product: "left_second.HK = left_top"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> left_second.HK"
  then obtain h k where h: "h \<in> H \<inter> K" and k: "k \<in> left_bottom"
    and x_eq: "x = h \<cdot> k" by (rule left_second.HK_memE)
  show "x \<in> left_top"
    unfolding x_eq
    by (rule left_quotient.composition_closed[OF middle_subset_left_top[THEN subsetD, OF h]
          left_bottom_subset_top[THEN subsetD, OF k]])
next
  fix x
  assume x: "x \<in> left_top"
  then obtain h n where h: "h \<in> H \<inter> K" and n: "n \<in> H1" and x_eq: "x = h \<cdot> n"
    by (rule left_top_memE)
  have "n \<in> left_bottom"
  proof -
    have unit_inter: "\<one> \<in> H \<inter> K1"
      using H.sub_unit_closed K1.sub_unit_closed by blast
    have unit_n: "\<one> \<cdot> n \<in> left_bottom"
      by (rule left_bottom_memI[OF unit_inter n])
    have nH: "n \<in> H" using H1.sub n by blast
    have "n = \<one> \<cdot> n" by (rule H.sub.left_unit[OF nH, symmetric])
    also have "... \<in> left_bottom" by (rule unit_n)
    finally show ?thesis .
  qed
  then show "x \<in> left_second.HK" unfolding x_eq by (rule left_second.HK_memI[OF h])
qed

lemma right_second_product: "right_second.HK = right_top"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> right_second.HK"
  then obtain h k where h: "h \<in> H \<inter> K" and k: "k \<in> right_bottom"
    and x_eq: "x = h \<cdot> k" by (rule right_second.HK_memE)
  show "x \<in> right_top"
    unfolding x_eq
    by (rule right_quotient.composition_closed[OF middle_subset_right_top[THEN subsetD, OF h]
          right_bottom_subset_top[THEN subsetD, OF k]])
next
  fix x
  assume x: "x \<in> right_top"
  have x_symmetric: "x \<in> symmetric.left_top"
    using x unfolding symmetric.left_top_def right_top_def by (simp only: Int_commute)
  then obtain h n where h': "h \<in> K \<inter> H" and n: "n \<in> K1" and x_eq: "x = h \<cdot> n"
    by (rule symmetric.left_top_memE)
  have h: "h \<in> H \<inter> K" using h' by blast
  have n_bottom: "n \<in> right_bottom"
  proof -
    have unit_inter: "\<one> \<in> K \<inter> H1"
      using K.sub_unit_closed H1.sub_unit_closed by blast
    have unit_n: "\<one> \<cdot> n \<in> right_bottom_product.HK"
      by (rule right_bottom_product.HK_memI[OF unit_inter n])
    have nK: "n \<in> K" using K1.sub n by blast
    have "n = \<one> \<cdot> n" by (rule K.sub.left_unit[OF nK, symmetric])
    also have "... \<in> right_bottom" using unit_n by (simp only: right_bottom_eq)
    finally show ?thesis .
  qed
  show "x \<in> right_second.HK" unfolding x_eq
    by (rule right_second.HK_memI[OF h n_bottom])
qed

lemma left_second_factor_group:
  "left_second.Fract_HK_K = left_quotient.Factor_Group"
  unfolding left_second.Fract_HK_K_def left_second_product
    left_quotient.Partition_def by rule

lemma right_second_factor_group:
  "right_second.Fract_HK_K = right_quotient.Factor_Group"
  unfolding right_second.Fract_HK_K_def right_second_product
    right_quotient.Partition_def by rule

lemma common_denominator:
  "(H \<inter> K) \<inter> left_bottom = (H \<inter> K) \<inter> right_bottom"
proof -
  have commute:
    "(case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1)) =
     (case_prod (\<cdot>)) ` ((K \<inter> H1) \<times> (H \<inter> K1))"
  proof -
    have "K \<inter> H1 \<subseteq> H \<inter> K" by (rule KH1_normal.subset)
    from HK1_normal.set_prod_commute[OF this] show ?thesis by (rule sym)
  qed
  show ?thesis
    unfolding middle_inter_left_bottom middle_inter_right_bottom
    by (rule commute)
qed

interpretation left_common:
  normal_subgroup "(H \<inter> K) \<inter> left_bottom" "H \<inter> K" "(\<cdot>)" \<one>
  by (rule left_quotient.normal_subgroup_intersection[OF
        left_bottom_normal middle_left_top_subgroup])

interpretation right_common:
  normal_subgroup "(H \<inter> K) \<inter> right_bottom" "H \<inter> K" "(\<cdot>)" \<one>
  by (rule right_quotient.normal_subgroup_intersection[OF
        right_bottom_normal middle_right_top_subgroup])

lemma left_wing_isomorphism:
  "(left_quotient.Factor_Group, left_quotient.quotient_composition,
      left_quotient.Class \<one>) \<cong>\<^sub>G
   (left_second.Fract_H_HIntK, left_common.quotient_composition,
      left_common.Class \<one>)"
  using left_second.second_isomorphism
  unfolding left_second_factor_group .

lemma right_wing_isomorphism:
  "(right_quotient.Factor_Group, right_quotient.quotient_composition,
      right_quotient.Class \<one>) \<cong>\<^sub>G
   (right_second.Fract_H_HIntK, right_common.quotient_composition,
      right_common.Class \<one>)"
  using right_second.second_isomorphism
  unfolding right_second_factor_group .

lemma common_factor_group:
  "(left_second.Fract_H_HIntK, left_common.quotient_composition,
      left_common.Class \<one>) =
   (right_second.Fract_H_HIntK, right_common.quotient_composition,
      right_common.Class \<one>)"
  unfolding left_second.Fract_H_HIntK_def right_second.Fract_H_HIntK_def
  unfolding common_denominator
  by rule

text \<open>
  The Zassenhaus lemma: the quotients represented by the two wings of the
  butterfly are isomorphic.  The quotient operations and units are displayed
  explicitly, as is customary in New-Algebra's set-based API.
\<close>
theorem zassenhaus_lemma:
  "(left_quotient.Factor_Group, left_quotient.quotient_composition,
      left_quotient.Class \<one>) \<cong>\<^sub>G
   (right_quotient.Factor_Group, right_quotient.quotient_composition,
      right_quotient.Class \<one>)"
proof -
  have middle_to_right:
    "(left_second.Fract_H_HIntK, left_common.quotient_composition,
        left_common.Class \<one>) \<cong>\<^sub>G
     (right_quotient.Factor_Group, right_quotient.quotient_composition,
        right_quotient.Class \<one>)"
    using isomorphic_as_groups_symmetric[OF right_wing_isomorphism]
    unfolding common_factor_group .
  show ?thesis
    by (rule isomorphic_as_groups_transitive[OF left_wing_isomorphism middle_to_right])
qed

lemmas butterfly_lemma = zassenhaus_lemma

end (* zassenhaus *)

end
