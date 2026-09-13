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
  by (simp add: G.subgroup_intersection H.Subgroup_axioms K.Subgroup_axioms)

interpretation HK1_subG: Subgroup "H \<inter> K1" G "(\<cdot>)" \<one>
  using G.subgroup_intersection H.Subgroup_axioms K.Subgroup_axioms K1.Subgroup_axioms 
  by (meson subgroup_transitive)

interpretation HK1_sub: Subgroup "H \<inter> K1" H "(\<cdot>)" \<one>
  using H.Subgroup_axioms HK1_subG.Subgroup_axioms subgroup_restrict by fastforce

interpretation KH1_sub: Subgroup "K \<inter> H1" K "(\<cdot>)" \<one>
proof -
  have "Subgroup (K \<inter> H1) G (\<cdot>) \<one>"
    using G.subgroup_intersection H.Subgroup_axioms H1.Subgroup_axioms K.Subgroup_axioms
    by (meson subgroup_transitive)
  then show "Subgroup (K \<inter> H1) K (\<cdot>) \<one>"
    using K.Subgroup_axioms subgroup_restrict by force
qed

interpretation HK1_normal: normal_subgroup "H \<inter> K1" "H \<inter> K" "(\<cdot>)" \<one>
proof -
  have I_sub: "Subgroup (H \<inter> K) K (\<cdot>) \<one>"
    using HK_sub.Subgroup_axioms K.Subgroup_axioms subgroup_restrict by fastforce
  have "Subgroup ((H \<inter> K) \<inter> K1) K (\<cdot>) \<one>"
    by (rule K.sub.subgroup_intersection[OF I_sub K1.Subgroup_axioms])
  then have C_K: "Subgroup (H \<inter> K1) K (\<cdot>) \<one>"
    using K1.subset by (smt (cvc5, best) dual_order.refl inf.bounded_iff subset_antisym)
  have C_sub: "Subgroup (H \<inter> K1) (H \<inter> K) (\<cdot>) \<one>"
    using C_K I_sub subgroup_restrict by fastforce
  interpret C: Subgroup "H \<inter> K1" "H \<inter> K" "(\<cdot>)" \<one> by fact
  interpret I: Subgroup "H \<inter> K" K "(\<cdot>)" \<one> by fact
  have I_H_sub: "Subgroup (H \<inter> K) H (\<cdot>) \<one>"
    using H.Subgroup_axioms HK_sub.Subgroup_axioms by (meson inf_sup_ord(1) subgroup_restrict)
  interpret I_H: Subgroup "H \<inter> K" H "(\<cdot>)" \<one> by fact
  show "normal_subgroup (H \<inter> K1) (H \<inter> K) (\<cdot>) \<one>"
  proof
    fix g c
    assume g: "g \<in> H \<inter> K" and c: "c \<in> H \<inter> K1"
    obtain inv_K: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = K.sub.inverse g"
       and inv_H: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = H.sub.inverse g"
      using I_H_sub I_sub g by (metis Subgroup.subgroup_inverse_equality)
    have g_H: "g \<in> H" and c_H: "c \<in> H" and g_K: "g \<in> K" and c_K1: "c \<in> K1"
      using g c by blast+
    have in_H: "H.sub.inverse g \<cdot> c \<cdot> g \<in> H"
      using Monoid.invertible_inverse_closed c_H g_H by blast
    have in_K1: "K.sub.inverse g \<cdot> c \<cdot> g \<in> K1"
      by (rule K1.normal[OF g_K c_K1])
    show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> H \<inter> K1"
      using in_H in_K1 inv_H inv_K by (metis IntI)
  qed
qed

interpretation KH1_normal: normal_subgroup "K \<inter> H1" "H \<inter> K" "(\<cdot>)" \<one>
proof -
  have I_sub: "Subgroup (H \<inter> K) H (\<cdot>) \<one>"
    using H.Subgroup_axioms HK_sub.Subgroup_axioms subgroup_restrict by force
  have "Subgroup ((H \<inter> K) \<inter> H1) H (\<cdot>) \<one>"
    by (simp add: H.sub.subgroup_intersection H1.Subgroup_axioms I_sub)
  then have C_H: "Subgroup (K \<inter> H1) H (\<cdot>) \<one>"
    using H1.subset by (smt (cvc5, best) dual_order.refl inf.bounded_iff subset_antisym)
  have C_sub: "Subgroup (K \<inter> H1) (H \<inter> K) (\<cdot>) \<one>"
    using C_H I_sub subgroup_restrict by fastforce
  interpret C: Subgroup "K \<inter> H1" "H \<inter> K" "(\<cdot>)" \<one> by fact
  interpret I: Subgroup "H \<inter> K" H "(\<cdot>)" \<one> by fact
  have I_K_sub: "Subgroup (H \<inter> K) K (\<cdot>) \<one>"
    using HK_sub.Subgroup_axioms K.Subgroup_axioms subgroup_restrict by fastforce
  interpret I_K: Subgroup "H \<inter> K" K "(\<cdot>)" \<one> by fact
  show "normal_subgroup (K \<inter> H1) (H \<inter> K) (\<cdot>) \<one>"
  proof
    fix g c
    assume g: "g \<in> H \<inter> K" and c: "c \<in> K \<inter> H1"
    have inv_H: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = H.sub.inverse g"
      using I.subgroup_inverse_equality g by presburger
    have inv_K: "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g = K.sub.inverse g"
      using I_K.subgroup_inverse_equality g by presburger
    have g_K: "g \<in> K" and c_K: "c \<in> K" and g_H: "g \<in> H" and c_H1: "c \<in> H1" and in_K: "K.sub.inverse g \<cdot> c \<cdot> g \<in> K"
      using g c by blast+
    have in_H1: "H.sub.inverse g \<cdot> c \<cdot> g \<in> H1"
      by (rule H1.normal[OF g_H c_H1])
    show "Monoid.inverse (H \<inter> K) (\<cdot>) \<one> g \<cdot> c \<cdot> g \<in> K \<inter> H1"
      using in_H1 in_K inv_H inv_K by (metis IntI)
  qed
qed

interpretation middle_H: Subgroup "H \<inter> K" H "(\<cdot>)" \<one>
  using H.Subgroup_axioms HK_sub.Subgroup_axioms subgroup_restrict by force

interpretation middle_K: Subgroup "H \<inter> K" K "(\<cdot>)" \<one>
  using HK_sub.Subgroup_axioms K.Subgroup_axioms subgroup_restrict by force

interpretation middle_H_group: subgroup_of_group "H \<inter> K" H "(\<cdot>)" \<one>
  by (simp add: H.sub.Group_axioms middle_H.Subgroup_axioms subgroup_of_group_def)

interpretation middle_K_group: subgroup_of_group "H \<inter> K" K "(\<cdot>)" \<one>
  by (simp add: K.sub.Group_axioms middle_K.Subgroup_axioms subgroup_of_group_def)

interpretation HK1_group: subgroup_of_group "H \<inter> K1" H "(\<cdot>)" \<one>
  by (simp add: H.sub.Group_axioms HK1_sub.Subgroup_axioms subgroup_of_groupI)

interpretation KH1_group: subgroup_of_group "K \<inter> H1" K "(\<cdot>)" \<one>
  by (simp add: K.sub.Group_axioms KH1_sub.Subgroup_axioms subgroup_of_group_def)

text \<open>The four subgroup products making up the two wings.\<close>
definition left_top where
  "left_top \<equiv> (case_prod (\<cdot>)) ` ((H \<inter> K) \<times> H1)"

definition left_bottom where
  "left_bottom \<equiv> (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> H1)"

definition right_top where
  "right_top \<equiv> (case_prod (\<cdot>)) ` ((H \<inter> K) \<times> K1)"

definition right_bottom where
  "right_bottom \<equiv> (case_prod (\<cdot>)) ` ((K \<inter> H1) \<times> K1)"

interpretation left_top_product: normal_subgroup_product H1 "H \<inter> K" H "(\<cdot>)" \<one> ..

interpretation left_bottom_product: normal_subgroup_product H1 "H \<inter> K1" H "(\<cdot>)" \<one> ..

interpretation right_top_product: normal_subgroup_product K1 "H \<inter> K" K "(\<cdot>)" \<one> ..

interpretation right_bottom_product: normal_subgroup_product K1 "K \<inter> H1" K "(\<cdot>)" \<one> ..

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
  by blast

lemma right_bottom_subset_top: "right_bottom \<subseteq> right_top"
  unfolding right_bottom_def right_top_def
  by blast

lemma left_top_memE:
  assumes "x \<in> left_top"
  obtains b n where "b \<in> H \<inter> K" "n \<in> H1" "x = b \<cdot> n"
  using assms left_top_eq left_top_product.HK_memE by metis

lemma left_bottom_memI:
  "\<lbrakk>c \<in> H \<inter> K1; n \<in> H1\<rbrakk> \<Longrightarrow> c \<cdot> n \<in> left_bottom"
  unfolding left_bottom_eq by (rule left_bottom_product.HK_memI)

lemma left_bottom_memE:
  assumes "x \<in> left_bottom"
  obtains c n where "c \<in> H \<inter> K1" "n \<in> H1" "x = c \<cdot> n"
  using assms left_bottom_eq left_bottom_product.HK_memE by blast

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
    obtain b n where b_middle: "b \<in> H \<inter> K" and n: "n \<in> H1" and x_eq: "x = b \<cdot> n"
      using x by (rule left_top_memE)
    obtain c m where c: "c \<in> H \<inter> K1" and m: "m \<in> H1" and y_eq: "y = c \<cdot> m"
      using y by (rule left_bottom_memE)
    have bH: "b \<in> H" and cH: "c \<in> H" and nH: "n \<in> H" and mH: "m \<in> H"
      using b_middle c n m H1.sub by blast+
    have inv_middle: "H.sub.inverse b = Monoid.inverse (H \<inter> K) (\<cdot>) \<one> b"
      using b_middle middle_H.subgroup_inverse_equality by blast
    have conjugate_c: "H.sub.inverse b \<cdot> c \<cdot> b \<in> H \<inter> K1"
      using HK1_normal.normal b_middle c inv_middle by presburger
    have conjugate_y: "H.sub.inverse b \<cdot> y \<cdot> b \<in> left_bottom"
      using H1.normal[OF bH m] H.sub.conjugate_composition H.sub.invertible bH cH conjugate_c 
            left_bottom_memI mH y_eq   by presburger
    have inv_n: "H.sub.inverse n \<in> H1"
      by (rule H1.submonoid_inverse_closed[OF H1.sub.invertible[OF n] n])
    have inv_n_bottom: "H.sub.inverse n \<in> left_bottom"
      using inv_n left_bottom_eq left_bottom_product.K_subset_HK by blast
    have n_bottom: "n \<in> left_bottom"
      using left_bottom_product.K_subset_HK n by auto
    have inv_x: "H.sub.inverse x = H.sub.inverse n \<cdot> H.sub.inverse b"
      unfolding x_eq using H.sub.inverse_composition_commute bH nH by blast
    obtain inv_b_H: "H.sub.inverse b \<in> H" and inv_n_H: "H.sub.inverse n \<in> H"
      using H.sub.invertible_inverse_closed H1.sub bH inv_n by blast
    have y_top: "y \<in> left_top" using bottom.subset y by blast
    have yH: "y \<in> H" using top_H.subset y_top by blast
    have conjugate_expansion: "H.sub.inverse x \<cdot> y \<cdot> x = H.sub.inverse n \<cdot> (H.sub.inverse b \<cdot> y \<cdot> b) \<cdot> n"
      using H.sub.associative H.sub_composition_closed bH inv_b_H inv_n_H inv_x nH x_eq yH
      by metis
    then have "H.sub.inverse x \<cdot> y \<cdot> x \<in> left_bottom"
      using bottom.sub_composition_closed conjugate_y inv_n_bottom n_bottom by presburger
    then show "Monoid.inverse left_top (\<cdot>) \<one> x \<cdot> y \<cdot> x \<in> left_bottom"
      using top_H.subgroup_inverse_equality x by metis
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
  then obtain p where p_in: "p \<in> (H \<inter> K1) \<times> H1" and p_eq: "x = case_prod (\<cdot>) p"
    unfolding left_bottom_def by blast
  obtain c h where p: "p = (c,h)" by (cases p)
  have c: "c \<in> H \<inter> K1" and h: "h \<in> H1"
    using p_in unfolding p by blast+
  have x_eq: "x = c \<cdot> h" using p_eq by (simp only: p prod.case)
  have cK: "c \<in> K" using c K1.sub by blast
  have xK: "x \<in> K" using x by blast
  have cG: "c \<in> G" and hG: "h \<in> G"
    using c h H.sub H1.sub by blast+
  then have "G.inverse c \<cdot> x = h"
    using G.invertible_left_inverse2 x_eq by blast
  moreover have inv_c_x_K: "G.inverse c \<cdot> x \<in> K"
    using cK xK by blast
  ultimately have hK: "h \<in> K" by meson
  show "x \<in> (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1))"
    using c h hK x_eq by blast
next
  fix x
  assume "x \<in> (case_prod (\<cdot>)) ` ((H \<inter> K1) \<times> (K \<inter> H1))"
  then obtain p c h where p_in: "p \<in> (H \<inter> K1) \<times> (K \<inter> H1)"
    and p_eq: "x = case_prod (\<cdot>) p" and p: "p = (c,h)"  by blast
  have c: "c \<in> H \<inter> K1" and h: "h \<in> K \<inter> H1"
    using p_in unfolding p by blast+
  have x_eq: "x = c \<cdot> h" using p_eq by (simp only: p prod.case)
  have "x \<in> H \<inter> K"
    unfolding x_eq using c h by blast
  moreover have "x \<in> left_bottom"
    unfolding left_bottom_def using c h x_eq by blast
  ultimately show "x \<in> (H \<inter> K) \<inter> left_bottom" by blast
qed

interpretation symmetric: zassenhaus G K H K1 H1 "(\<cdot>)" \<one> ..

lemma middle_inter_right_bottom:
  "(H \<inter> K) \<inter> right_bottom = (case_prod (\<cdot>)) ` ((K \<inter> H1) \<times> (H \<inter> K1))"
  using right_bottom_def symmetric.left_bottom_def symmetric.middle_inter_left_bottom
  by (metis Int_commute)

text \<open>The normality argument for the right wing is exactly the symmetric instance.\<close>
lemma right_bottom_normal: "normal_subgroup right_bottom right_top (\<cdot>) \<one>"
  using right_bottom_eq right_top_eq symmetric.left_bottom_eq symmetric.left_bottom_normal
    symmetric.left_top_eq by (metis inf.commute)

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
  second_iso_theorem left_bottom "H \<inter> K" left_top "(\<cdot>)" \<one> ..

interpretation right_second:
  second_iso_theorem right_bottom "H \<inter> K" right_top "(\<cdot>)" \<one> ..

lemma left_second_product: "left_second.HK = left_top"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> left_second.HK"
  then obtain h k where h: "h \<in> H \<inter> K" and k: "k \<in> left_bottom"
    and x_eq: "x = h \<cdot> k" by (rule left_second.HK_memE)
  show "x \<in> left_top"
    unfolding x_eq using h k by blast
next
  fix x
  assume x: "x \<in> left_top"
  then obtain h n where h: "h \<in> H \<inter> K" and n: "n \<in> H1" and x_eq: "x = h \<cdot> n"
    by (rule left_top_memE)
  have unit_inter: "\<one> \<in> H \<inter> K1"
    using H.sub_unit_closed K1.sub_unit_closed by blast
  then have "n \<in> left_bottom"
    using H1.sub.left_unit left_bottom_memI n by metis
  then show "x \<in> left_second.HK"
    using h left_second.HK_memI x_eq by blast
qed

lemma right_second_product: "right_second.HK = right_top"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> right_second.HK"
  then obtain h k where h: "h \<in> H \<inter> K" and k: "k \<in> right_bottom"
    and x_eq: "x = h \<cdot> k" by (rule right_second.HK_memE)
  show "x \<in> right_top"
    unfolding x_eq using h k by blast
next
  fix x
  assume x: "x \<in> right_top"
  then obtain h n where h': "h \<in> K \<inter> H" and n: "n \<in> K1" and x_eq: "x = h \<cdot> n"
    using right_top_eq right_top_product.HK_memE by (metis Int_commute)
  have unit_inter: "\<one> \<in> K \<inter> H1"
    using K.sub_unit_closed H1.sub_unit_closed by blast
  then have "n \<in> right_bottom"
    using K1.sub.left_unit n right_bottom_eq right_bottom_product.HK_memI by metis
  then show "x \<in> right_second.HK" unfolding x_eq
    using h' right_second.HK_memI by blast
qed

lemma left_second_factor_group:
  "left_second.Fract_HK_K = left_quotient.Factor_Group"
  using left_quotient.Partition_def left_second.Fract_HK_K_def left_second_product by argo


lemma right_second_factor_group:
  "right_second.Fract_HK_K = right_quotient.Factor_Group"
  using right_quotient.Partition_def right_second.Fract_HK_K_def right_second_product by argo

lemma common_denominator:
  "(H \<inter> K) \<inter> left_bottom = (H \<inter> K) \<inter> right_bottom"
  unfolding middle_inter_left_bottom middle_inter_right_bottom
  using HK1_normal.subset KH1_normal.set_prod_commute by metis

interpretation left_common:
  normal_subgroup "(H \<inter> K) \<inter> left_bottom" "H \<inter> K" "(\<cdot>)" \<one>
  using left_bottom_normal left_quotient.normal_subgroup_intersection middle_left_top_subgroup
  by blast

interpretation right_common:
  normal_subgroup "(H \<inter> K) \<inter> right_bottom" "H \<inter> K" "(\<cdot>)" \<one>
  using common_denominator left_common.normal_subgroup_axioms by force

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
  using common_denominator left_second.Fract_H_HIntK_def right_second.Fract_H_HIntK_def
  by presburger

text \<open>
  The Zassenhaus lemma: the quotients represented by the two wings of the
  butterfly are isomorphic.  The quotient operations and units are displayed
  explicitly, as is customary in New-Algebra's set-based API.
\<close>
theorem butterfly_lemma:
  "(left_quotient.Factor_Group, left_quotient.quotient_composition,
      left_quotient.Class \<one>) \<cong>\<^sub>G
   (right_quotient.Factor_Group, right_quotient.quotient_composition,
      right_quotient.Class \<one>)"
  using common_factor_group left_wing_isomorphism right_wing_isomorphism
  by (metis isomorphic_as_groups_symmetric isomorphic_as_groups_transitive)

end (* zassenhaus *)

end
