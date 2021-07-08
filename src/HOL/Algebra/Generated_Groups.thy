(*  Title:      HOL/Algebra/Generated_Groups.thy
    Author:     Paulo Emílio de Vilhena
*)

section \<open>Generated Groups\<close>

theory Generated_Groups
  imports Group Coset
  
begin

subsection \<open>Generated Groups\<close>

inductive_set generate :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for G and H where
    one:  "\<one>\<^bsub>G\<^esub> \<in> generate G H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> generate G H"
  | inv:  "h \<in> H \<Longrightarrow> inv\<^bsub>G\<^esub> h \<in> generate G H"
  | eng:  "h1 \<in> generate G H \<Longrightarrow> h2 \<in> generate G H \<Longrightarrow> h1 \<otimes>\<^bsub>G\<^esub> h2 \<in> generate G H"


subsubsection \<open>Basic Properties\<close>

lemma (in group) generate_consistent:
  assumes "K \<subseteq> H" "subgroup H G" shows "generate (G \<lparr> carrier := H \<rparr>) K = generate G K"
proof
  show "generate (G \<lparr> carrier := H \<rparr>) K \<subseteq> generate G K"
  proof
    fix h assume "h \<in> generate (G \<lparr> carrier := H \<rparr>) K" thus "h \<in> generate G K"
    proof (induction, simp add: one, simp_all add: incl[of _ K G] eng)
      case inv thus ?case
        using m_inv_consistent assms generate.inv[of _ K G] by auto
    qed
  qed
next
  show "generate G K \<subseteq> generate (G \<lparr> carrier := H \<rparr>) K"
  proof
    note gen_simps = one incl eng
    fix h assume "h \<in> generate G K" thus "h \<in> generate (G \<lparr> carrier := H \<rparr>) K"
      using gen_simps[where ?G = "G \<lparr> carrier := H \<rparr>"]
    proof (induction, auto)
      fix h assume "h \<in> K" thus "inv h \<in> generate (G \<lparr> carrier := H \<rparr>) K"
        using m_inv_consistent assms generate.inv[of h K "G \<lparr> carrier := H \<rparr>"] by auto
    qed
  qed
qed

lemma (in group) generate_in_carrier:
  assumes "H \<subseteq> carrier G" and "h \<in> generate G H" shows "h \<in> carrier G"
  using assms(2,1) by (induct h rule: generate.induct) (auto)

lemma (in group) generate_incl:
  assumes "H \<subseteq> carrier G" shows "generate G H \<subseteq> carrier G"
  using generate_in_carrier[OF assms(1)] by auto

lemma (in group) generate_m_inv_closed:
  assumes "H \<subseteq> carrier G" and "h \<in> generate G H" shows "(inv h) \<in> generate G H"
  using assms(2,1)
proof (induction rule: generate.induct, auto simp add: one inv incl)
  fix h1 h2
  assume h1: "h1 \<in> generate G H" "inv h1 \<in> generate G H"
     and h2: "h2 \<in> generate G H" "inv h2 \<in> generate G H"
  hence "inv (h1 \<otimes> h2) = (inv h2) \<otimes> (inv h1)"
    by (meson assms generate_in_carrier group.inv_mult_group is_group)
  thus "inv (h1 \<otimes> h2) \<in> generate G H"
    using generate.eng[OF h2(2) h1(2)] by simp
qed

lemma (in group) generate_is_subgroup:
  assumes "H \<subseteq> carrier G" shows "subgroup (generate G H) G"
  using subgroup.intro[OF generate_incl eng one generate_m_inv_closed] assms by auto

lemma (in group) mono_generate:
  assumes "K \<subseteq> H" shows "generate G K \<subseteq> generate G H"
proof
  fix h assume "h \<in> generate G K" thus "h \<in> generate G H"
    using assms by (induction) (auto simp add: one incl inv eng)
qed

lemma (in group) generate_subgroup_incl:
  assumes "K \<subseteq> H" "subgroup H G" shows "generate G K \<subseteq> H"
  using group.generate_incl[OF subgroup_imp_group[OF assms(2)], of K] assms(1)
  by (simp add: generate_consistent[OF assms])

lemma (in group) generate_minimal:
  assumes "H \<subseteq> carrier G" shows "generate G H = \<Inter> { H'. subgroup H' G \<and> H \<subseteq> H' }"
  using generate_subgroup_incl generate_is_subgroup[OF assms] incl[of _ H] by blast

lemma (in group) generateI:
  assumes "subgroup E G" "H \<subseteq> E" and "\<And>K. \<lbrakk> subgroup K G; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate G H"
proof -
  have subset: "H \<subseteq> carrier G"
    using subgroup.subset assms by auto
  show ?thesis
    using assms unfolding generate_minimal[OF subset] by blast
qed

lemma (in group) normal_generateI:
  assumes "H \<subseteq> carrier G" and "\<And>h g. \<lbrakk> h \<in> H; g \<in> carrier G \<rbrakk> \<Longrightarrow> g \<otimes> h \<otimes> (inv g) \<in> H"
  shows "generate G H \<lhd> G"
proof (rule normal_invI[OF generate_is_subgroup[OF assms(1)]])
  fix g h assume g: "g \<in> carrier G" show "h \<in> generate G H \<Longrightarrow> g \<otimes> h \<otimes> (inv g) \<in> generate G H"
  proof (induct h rule: generate.induct)
    case one thus ?case
      using g generate.one by auto
  next
    case incl show ?case
      using generate.incl[OF assms(2)[OF incl g]] .
  next
    case (inv h)
    hence h: "h \<in> carrier G"
      using assms(1) by auto
    hence "inv (g \<otimes> h \<otimes> (inv g)) = g \<otimes> (inv h) \<otimes> (inv g)"
      using g by (simp add: inv_mult_group m_assoc)
    thus ?case
      using generate_m_inv_closed[OF assms(1) generate.incl[OF assms(2)[OF inv g]]] by simp
  next
    case (eng h1 h2)
    note in_carrier = eng(1,3)[THEN generate_in_carrier[OF assms(1)]]
    have "g \<otimes> (h1 \<otimes> h2) \<otimes> inv g = (g \<otimes> h1 \<otimes> inv g) \<otimes> (g \<otimes> h2 \<otimes> inv g)"
      using in_carrier g by (simp add: inv_solve_left m_assoc)
    thus ?case
      using generate.eng[OF eng(2,4)] by simp
  qed
qed

lemma (in group) subgroup_int_pow_closed:
  assumes "subgroup H G" "h \<in> H" shows "h [^] (k :: int) \<in> H"
  using group.int_pow_closed[OF subgroup_imp_group[OF assms(1)]] assms(2)
  unfolding int_pow_consistent[OF assms] by simp

lemma (in group) generate_pow:
  assumes "a \<in> carrier G" shows "generate G { a } = { a [^] (k :: int) | k. k \<in> UNIV }"
proof
  show "{ a [^] (k :: int) | k. k \<in> UNIV } \<subseteq> generate G { a }"
    using subgroup_int_pow_closed[OF generate_is_subgroup[of "{ a }"] incl[of a]] assms by auto
next
  show "generate G { a } \<subseteq> { a [^] (k :: int) | k. k \<in> UNIV }"
  proof
    fix h assume "h \<in> generate G { a }" hence "\<exists>k :: int. h = a [^] k"
    proof (induction)
      case one
      then show ?case
        using int_pow_0 [of G] by metis
    next
      case (incl h)
      then show ?case
        by (metis assms int_pow_1 singletonD)
    next
      case (inv h)
      then show ?case
        by (metis assms int_pow_1 int_pow_neg singletonD)
    next
      case (eng h1 h2)
      then show ?case
        using assms by (metis int_pow_mult)
    qed
    then show "h \<in> { a [^] (k :: int) | k. k \<in> UNIV }"
      by blast
  qed
qed

corollary (in group) generate_one: "generate G { \<one> } = { \<one> }"
  using generate_pow[of "\<one>", OF one_closed] by simp

corollary (in group) generate_empty: "generate G {} = { \<one> }"
  using mono_generate[of "{}" "{ \<one> }"] generate.one unfolding generate_one by auto

lemma (in group_hom)
  "subgroup K G \<Longrightarrow> subgroup (h ` K) H"
  using subgroup_img_is_subgroup by auto

lemma (in group_hom) generate_img:
  assumes "K \<subseteq> carrier G" shows "generate H (h ` K) = h ` (generate G K)"
proof
  have "h ` K \<subseteq> h ` (generate G K)"
    using incl[of _ K G] by auto
  thus "generate H (h ` K) \<subseteq> h ` (generate G K)"
    using generate_subgroup_incl subgroup_img_is_subgroup[OF G.generate_is_subgroup[OF assms]] by auto
next
  show "h ` (generate G K) \<subseteq> generate H (h ` K)"
  proof
    fix a assume "a \<in> h ` (generate G K)"
    then obtain k where "k \<in> generate G K" "a = h k"
      by blast
    show "a \<in> generate H (h ` K)"
      using \<open>k \<in> generate G K\<close> unfolding \<open>a = h k\<close>
    proof (induct k, auto simp add: generate.one[of H] generate.incl[of _ "h ` K" H])
      case (inv k) show ?case
        using assms generate.inv[of "h k" "h ` K" H] inv by auto  
    next
      case eng show ?case
        using generate.eng[OF eng(2,4)] eng(1,3)[THEN G.generate_in_carrier[OF assms]] by auto
    qed
  qed
qed


subsection \<open>Derived Subgroup\<close>

subsubsection \<open>Definitions\<close>

abbreviation derived_set :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "derived_set G H \<equiv>
           \<Union>h1 \<in> H. (\<Union>h2 \<in> H. { h1 \<otimes>\<^bsub>G\<^esub> h2 \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> h1) \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> h2) })"

definition derived :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "derived G H = generate G (derived_set G H)"


subsubsection \<open>Basic Properties\<close>

lemma (in group) derived_set_incl:
  assumes "K \<subseteq> H" "subgroup H G" shows "derived_set G K \<subseteq> H"
  using assms(1) subgroupE(3-4)[OF assms(2)] by (auto simp add: subset_iff)

lemma (in group) derived_incl:
  assumes "K \<subseteq> H" "subgroup H G" shows "derived G K \<subseteq> H"
  using generate_subgroup_incl[OF derived_set_incl] assms unfolding derived_def by auto

lemma (in group) derived_set_in_carrier:
  assumes "H \<subseteq> carrier G" shows "derived_set G H \<subseteq> carrier G"
  using derived_set_incl[OF assms subgroup_self] .

lemma (in group) derived_in_carrier:
  assumes "H \<subseteq> carrier G" shows "derived G H \<subseteq> carrier G"
  using derived_incl[OF assms subgroup_self] .

lemma (in group) exp_of_derived_in_carrier:
  assumes "H \<subseteq> carrier G" shows "(derived G ^^ n) H \<subseteq> carrier G"
  using assms derived_in_carrier by (induct n) (auto)

lemma (in group) derived_is_subgroup:
  assumes "H \<subseteq> carrier G" shows "subgroup (derived G H) G"
  unfolding derived_def using generate_is_subgroup[OF derived_set_in_carrier[OF assms]] .

lemma (in group) exp_of_derived_is_subgroup:
  assumes "subgroup H G" shows "subgroup ((derived G ^^ n) H) G"
  using assms derived_is_subgroup subgroup.subset by (induct n) (auto)

lemma (in group) exp_of_derived_is_subgroup':
  assumes "H \<subseteq> carrier G" shows "subgroup ((derived G ^^ (Suc n)) H) G"
  using assms derived_is_subgroup[OF subgroup.subset] derived_is_subgroup by (induct n) (auto)

lemma (in group) mono_derived_set:
  assumes "K \<subseteq> H" shows "derived_set G K \<subseteq> derived_set G H"
  using assms by auto

lemma (in group) mono_derived:
  assumes "K \<subseteq> H" shows "derived G K \<subseteq> derived G H"
  unfolding derived_def using mono_generate[OF mono_derived_set[OF assms]] .

lemma (in group) mono_exp_of_derived:
  assumes "K \<subseteq> H" shows "(derived G ^^ n) K \<subseteq> (derived G ^^ n) H"
  using assms mono_derived by (induct n) (auto)

lemma (in group) derived_set_consistent:
  assumes "K \<subseteq> H" "subgroup H G" shows "derived_set (G \<lparr> carrier := H \<rparr>) K = derived_set G K"
  using m_inv_consistent[OF assms(2)] assms(1) by (auto simp add: subset_iff)

lemma (in group) derived_consistent:
  assumes "K \<subseteq> H" "subgroup H G" shows "derived (G \<lparr> carrier := H \<rparr>) K = derived G K"
  using generate_consistent[OF derived_set_incl] derived_set_consistent assms by (simp add: derived_def)

lemma (in comm_group) derived_eq_singleton:
  assumes "H \<subseteq> carrier G" shows "derived G H = { \<one> }"
proof (cases "derived_set G H = {}")
  case True show ?thesis
    using generate_empty unfolding derived_def True by simp
next
  case False
  have aux_lemma: "h \<in> derived_set G H \<Longrightarrow> h = \<one>" for h
    using assms by (auto simp add: subset_iff)
       (metis (no_types, lifting) m_comm m_closed inv_closed inv_solve_right l_inv l_inv_ex)
  have "derived_set G H = { \<one> }"
  proof
    show "derived_set G H \<subseteq> { \<one> }"
      using aux_lemma by auto
  next
    obtain h where h: "h \<in> derived_set G H"
      using False by blast
    thus "{ \<one> } \<subseteq> derived_set G H"
      using aux_lemma[OF h] by auto
  qed
  thus ?thesis
    using generate_one unfolding derived_def by auto
qed

lemma (in group) derived_is_normal:
  assumes "H \<lhd> G" shows "derived G H \<lhd> G"
proof -
  interpret H: normal H G
    using assms .

  show ?thesis
    unfolding derived_def
  proof (rule normal_generateI[OF derived_set_in_carrier[OF H.subset]])
    fix h g assume "h \<in> derived_set G H" and g: "g \<in> carrier G"
    then obtain h1 h2 where h: "h1 \<in> H" "h2 \<in> H" "h = h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2"
      by auto
    hence in_carrier: "h1 \<in> carrier G" "h2 \<in> carrier G" "g \<in> carrier G"
      using H.subset g by auto
    have "g \<otimes> h \<otimes> inv g =
           g \<otimes> h1 \<otimes> (inv g \<otimes> g) \<otimes> h2 \<otimes> (inv g \<otimes> g) \<otimes> inv h1 \<otimes> (inv g \<otimes> g) \<otimes> inv h2 \<otimes> inv g"
      unfolding h(3) by (simp add: in_carrier m_assoc)
    also have " ... =
          (g \<otimes> h1 \<otimes> inv g) \<otimes> (g \<otimes> h2 \<otimes> inv g) \<otimes> (g \<otimes> inv h1 \<otimes> inv g) \<otimes> (g \<otimes> inv h2 \<otimes> inv g)"
      using in_carrier m_assoc inv_closed m_closed by presburger
    finally have "g \<otimes> h \<otimes> inv g =
          (g \<otimes> h1 \<otimes> inv g) \<otimes> (g \<otimes> h2 \<otimes> inv g) \<otimes> inv (g \<otimes> h1 \<otimes> inv g) \<otimes> inv (g \<otimes> h2 \<otimes> inv g)"
      by (simp add: in_carrier inv_mult_group m_assoc)
    thus "g \<otimes> h \<otimes> inv g \<in> derived_set G H"
      using h(1-2)[THEN H.inv_op_closed2[OF g]] by auto
  qed
qed

lemma (in group) normal_self: "carrier G \<lhd> G"
  by (rule normal_invI[OF subgroup_self], simp)

corollary (in group) derived_self_is_normal: "derived G (carrier G) \<lhd> G"
  using derived_is_normal[OF normal_self] .

corollary (in group) derived_subgroup_is_normal:
  assumes "subgroup H G" shows "derived G H \<lhd> G \<lparr> carrier := H \<rparr>"
  using group.derived_self_is_normal[OF subgroup_imp_group[OF assms]]
        derived_consistent[OF _ assms]
  by simp

corollary (in group) derived_quot_is_group: "group (G Mod (derived G (carrier G)))"
  using normal.factorgroup_is_group[OF derived_self_is_normal] by auto

lemma (in group) derived_quot_is_comm_group: "comm_group (G Mod (derived G (carrier G)))"
proof (rule group.group_comm_groupI[OF derived_quot_is_group], simp add: FactGroup_def)
  interpret DG: normal "derived G (carrier G)" G
    using derived_self_is_normal .

  fix H K assume "H \<in> rcosets derived G (carrier G)" and "K \<in> rcosets derived G (carrier G)"
  then obtain g1 g2
    where g1: "g1 \<in> carrier G" "H = derived G (carrier G) #> g1"
      and g2: "g2 \<in> carrier G" "K = derived G (carrier G) #> g2"
    unfolding RCOSETS_def by auto
  hence "H <#> K = derived G (carrier G) #> (g1 \<otimes> g2)"
    by (simp add: DG.rcos_sum)
  also have " ... = derived G (carrier G) #> (g2 \<otimes> g1)"
  proof -
    { fix g1 g2 assume g1: "g1 \<in> carrier G" and g2: "g2 \<in> carrier G"
      have "derived G (carrier G) #> (g1 \<otimes> g2) \<subseteq> derived G (carrier G) #> (g2 \<otimes> g1)"
      proof
        fix h assume "h \<in> derived G (carrier G) #> (g1 \<otimes> g2)"
        then obtain g' where h: "g' \<in> carrier G" "g' \<in> derived G (carrier G)" "h = g' \<otimes> (g1 \<otimes> g2)"
          using DG.subset unfolding r_coset_def by auto
        hence "h = g' \<otimes> (g1 \<otimes> g2) \<otimes> (inv g1 \<otimes> inv g2 \<otimes> g2 \<otimes> g1)"
          using g1 g2 by (simp add: m_assoc)
        hence "h = (g' \<otimes> (g1 \<otimes> g2 \<otimes> inv g1 \<otimes> inv g2)) \<otimes> (g2 \<otimes> g1)"
          using h(1) g1 g2 inv_closed m_assoc m_closed by presburger
        moreover have "g1 \<otimes> g2 \<otimes> inv g1 \<otimes> inv g2 \<in> derived G (carrier G)"
          using incl[of _ "derived_set G (carrier G)"] g1 g2 unfolding derived_def by blast
        hence "g' \<otimes> (g1 \<otimes> g2 \<otimes> inv g1 \<otimes> inv g2) \<in> derived G (carrier G)"
          using DG.m_closed[OF h(2)] by simp
        ultimately show "h \<in> derived G (carrier G) #> (g2 \<otimes> g1)"
          unfolding r_coset_def by blast
      qed }
    thus ?thesis
      using g1(1) g2(1) by auto
  qed
  also have " ... = K <#> H"
    by (simp add: g1 g2 DG.rcos_sum)
  finally show "H <#> K = K <#> H" .
qed

corollary (in group) derived_quot_of_subgroup_is_comm_group:
  assumes "subgroup H G" shows "comm_group ((G \<lparr> carrier := H \<rparr>) Mod (derived G H))"
  using group.derived_quot_is_comm_group[OF subgroup_imp_group[OF assms]]
        derived_consistent[OF _ assms]
  by simp

proposition (in group) derived_minimal:
  assumes "H \<lhd> G" and "comm_group (G Mod H)" shows "derived G (carrier G) \<subseteq> H"
proof -
  interpret H: normal H G
    using assms(1) .

  show ?thesis
    unfolding derived_def
  proof (rule generate_subgroup_incl[OF _ H.subgroup_axioms])
    show "derived_set G (carrier G) \<subseteq> H"
    proof
      fix h assume "h \<in> derived_set G (carrier G)"
      then obtain g1 g2 where h: "g1 \<in> carrier G" "g2 \<in> carrier G" "h = g1 \<otimes> g2 \<otimes> inv g1 \<otimes> inv g2"
        by auto
      have "H #> (g1 \<otimes> g2) = (H #> g1) <#> (H #> g2)"
        by (simp add: h(1-2) H.rcos_sum)
      also have " ... = (H #> g2) <#> (H #> g1)"
        using comm_groupE(4)[OF assms(2)] h(1-2) unfolding FactGroup_def RCOSETS_def by auto
      also have " ... = H #> (g2 \<otimes> g1)"
        by (simp add: h(1-2) H.rcos_sum)
      finally have "H #> (g1 \<otimes> g2) = H #> (g2 \<otimes> g1)" .
      then obtain h' where "h' \<in> H" "\<one> \<otimes> (g1 \<otimes> g2) = h' \<otimes> (g2 \<otimes> g1)"
        using H.one_closed unfolding r_coset_def by blast
      thus "h \<in> H"
        using h m_assoc by auto
    qed
  qed
qed

proposition (in group) derived_of_subgroup_minimal:
  assumes "K \<lhd> G \<lparr> carrier := H \<rparr>" "subgroup H G" and "comm_group ((G \<lparr> carrier := H \<rparr>) Mod K)"
  shows "derived G H \<subseteq> K"
  using group.derived_minimal[OF subgroup_imp_group[OF assms(2)] assms(1,3)]
        derived_consistent[OF _ assms(2)]
  by simp

lemma (in group_hom) derived_img:
  assumes "K \<subseteq> carrier G" shows "derived H (h ` K) = h ` (derived G K)"
proof -
  have "derived_set H (h ` K) = h ` (derived_set G K)"
  proof
    show "derived_set H (h ` K) \<subseteq> h ` derived_set G K"
    proof
      fix a assume "a \<in> derived_set H (h ` K)"
      then obtain k1 k2
        where "k1 \<in> K" "k2 \<in> K" "a = (h k1) \<otimes>\<^bsub>H\<^esub> (h k2) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k1) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k2)"
        by auto
      hence "a = h (k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2)"
        using assms by (simp add: subset_iff)
      from this \<open>k1 \<in> K\<close> and \<open>k2 \<in> K\<close> show "a \<in> h ` derived_set G K" by auto
    qed
  next
    show "h ` (derived_set G K) \<subseteq> derived_set H (h ` K)"
    proof
      fix a assume "a \<in> h ` (derived_set G K)"
      then obtain k1 k2 where "k1 \<in> K" "k2 \<in> K" "a = h (k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2)"
        by auto
      hence "a = (h k1) \<otimes>\<^bsub>H\<^esub> (h k2) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k1) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k2)"
        using assms by (simp add: subset_iff)
      from this \<open>k1 \<in> K\<close> and \<open>k2 \<in> K\<close> show "a \<in> derived_set H (h ` K)" by auto
    qed
  qed
  thus ?thesis
    unfolding derived_def using generate_img[OF G.derived_set_in_carrier[OF assms]] by simp
qed

lemma (in group_hom) exp_of_derived_img:
  assumes "K \<subseteq> carrier G" shows "(derived H ^^ n) (h ` K) = h ` ((derived G ^^ n) K)"
  using derived_img[OF G.exp_of_derived_in_carrier[OF assms]] by (induct n) (auto)


subsubsection \<open>Generated subgroup of a group\<close>

definition subgroup_generated :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) monoid_scheme"
  where "subgroup_generated G S = G\<lparr>carrier := generate G (carrier G \<inter> S)\<rparr>"

lemma carrier_subgroup_generated: "carrier (subgroup_generated G S) = generate G (carrier G \<inter> S)"
  by (auto simp: subgroup_generated_def)

lemma (in group) subgroup_generated_subset_carrier_subset:
   "S \<subseteq> carrier G \<Longrightarrow> S \<subseteq> carrier(subgroup_generated G S)"
  by (simp add: Int_absorb1 carrier_subgroup_generated generate.incl subsetI)

lemma (in group) subgroup_generated_minimal:
   "\<lbrakk>subgroup H G; S \<subseteq> H\<rbrakk> \<Longrightarrow> carrier(subgroup_generated G S) \<subseteq> H"
  by (simp add: carrier_subgroup_generated generate_subgroup_incl le_infI2)

lemma (in group) carrier_subgroup_generated_subset:
   "carrier (subgroup_generated G A) \<subseteq> carrier G"
  apply (clarsimp simp: carrier_subgroup_generated)
  by (meson Int_lower1 generate_in_carrier)

lemma (in group) group_subgroup_generated [simp]: "group (subgroup_generated G S)"
    unfolding subgroup_generated_def
    by (simp add: generate_is_subgroup subgroup_imp_group)

lemma (in group) abelian_subgroup_generated:
  assumes "comm_group G"
  shows "comm_group (subgroup_generated G S)" (is "comm_group ?GS")
proof (rule group.group_comm_groupI)
  show "Group.group ?GS"
    by simp
next
  fix x y
  assume "x \<in> carrier ?GS" "y \<in> carrier ?GS"
  with assms show "x \<otimes>\<^bsub>?GS\<^esub> y = y \<otimes>\<^bsub>?GS\<^esub> x"
    apply (simp add: subgroup_generated_def)
    by (meson Int_lower1 comm_groupE(4) generate_in_carrier)
qed

lemma (in group) subgroup_of_subgroup_generated:
  assumes "H \<subseteq> B" "subgroup H G"
    shows "subgroup H (subgroup_generated G B)"
proof unfold_locales
  fix x
  assume "x \<in> H"
  with assms show "inv\<^bsub>subgroup_generated G B\<^esub> x \<in> H"
    unfolding subgroup_generated_def
    by (metis IntI Int_commute Int_lower2 generate.incl generate_is_subgroup m_inv_consistent subgroup_def subsetCE)
next
  show "H \<subseteq> carrier (subgroup_generated G B)"
    using assms apply (auto simp: carrier_subgroup_generated)
    by (metis Int_iff generate.incl inf.orderE subgroup.mem_carrier)
qed (use assms in \<open>auto simp: subgroup_generated_def subgroup_def\<close>)

lemma carrier_subgroup_generated_alt:
  assumes "Group.group G" "S \<subseteq> carrier G"
  shows "carrier (subgroup_generated G S) = \<Inter>{H. subgroup H G \<and> carrier G \<inter> S \<subseteq> H}"
  using assms by (auto simp: group.generate_minimal subgroup_generated_def)

lemma one_subgroup_generated [simp]: "\<one>\<^bsub>subgroup_generated G S\<^esub> = \<one>\<^bsub>G\<^esub>"
  by (auto simp: subgroup_generated_def)

lemma mult_subgroup_generated [simp]: "mult (subgroup_generated G S) = mult G"
  by (auto simp: subgroup_generated_def)

lemma (in group) inv_subgroup_generated [simp]:
  assumes "f \<in> carrier (subgroup_generated G S)"
  shows "inv\<^bsub>subgroup_generated G S\<^esub> f = inv f"
proof (rule group.inv_equality)
  show "Group.group (subgroup_generated G S)"
    by simp
  have [simp]: "f \<in> carrier G"
    by (metis Int_lower1 assms carrier_subgroup_generated generate_in_carrier)
  show "inv f \<otimes>\<^bsub>subgroup_generated G S\<^esub> f = \<one>\<^bsub>subgroup_generated G S\<^esub>"
    by (simp add: assms)
  show "f \<in> carrier (subgroup_generated G S)"
    using assms by (simp add: generate.incl subgroup_generated_def)
  show "inv f \<in> carrier (subgroup_generated G S)"
    using assms by (simp add: subgroup_generated_def generate_m_inv_closed)
qed

lemma subgroup_generated_restrict [simp]:
   "subgroup_generated G (carrier G \<inter> S) = subgroup_generated G S"
  by (simp add: subgroup_generated_def)

lemma (in subgroup) carrier_subgroup_generated_subgroup [simp]:
  "carrier (subgroup_generated G H) = H"
  by (auto simp: generate.incl carrier_subgroup_generated elim: generate.induct)

lemma (in group) subgroup_subgroup_generated_iff:
   "subgroup H (subgroup_generated G B) \<longleftrightarrow> subgroup H G \<and> H \<subseteq> carrier(subgroup_generated G B)"
 (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have Hsub: "H \<subseteq> generate G (carrier G \<inter> B)"
    by (simp add: subgroup_def subgroup_generated_def)
  then have H: "H \<subseteq> carrier G" "H \<subseteq> carrier(subgroup_generated G B)"
    unfolding carrier_subgroup_generated
    using generate_incl by blast+
  with Hsub have "subgroup H G"
    by (metis Int_commute Int_lower2 L carrier_subgroup_generated generate_consistent
        generate_is_subgroup inf.orderE subgroup.carrier_subgroup_generated_subgroup subgroup_generated_def)
  with H show ?rhs
    by blast
next
  assume ?rhs
  then show ?lhs
    by (simp add: generate_is_subgroup subgroup_generated_def subgroup_incl)
qed

lemma (in group) subgroup_subgroup_generated:
   "subgroup (carrier(subgroup_generated G S)) G"
  using group.subgroup_self group_subgroup_generated subgroup_subgroup_generated_iff by blast

lemma pow_subgroup_generated:
   "pow (subgroup_generated G S) = (pow G :: 'a \<Rightarrow> nat \<Rightarrow> 'a)"
proof -
  have "x [^]\<^bsub>subgroup_generated G S\<^esub> n = x [^]\<^bsub>G\<^esub> n" for x and n::nat
    by (induction n) auto
  then show ?thesis
    by force
qed

lemma (in group) subgroup_generated2 [simp]: "subgroup_generated (subgroup_generated G S) S = subgroup_generated G S"
proof -
  have *: "\<And>A. carrier G \<inter> A \<subseteq> carrier (subgroup_generated (subgroup_generated G A) A)"
    by (metis (no_types, opaque_lifting) Int_assoc carrier_subgroup_generated generate.incl inf.order_iff subset_iff)
  show ?thesis
  apply (auto intro!: monoid.equality)
    using group.carrier_subgroup_generated_subset group_subgroup_generated apply blast
     apply (metis (no_types, opaque_lifting) "*" group.subgroup_subgroup_generated group_subgroup_generated subgroup_generated_minimal
        subgroup_generated_restrict subgroup_subgroup_generated_iff subset_eq)
    apply (simp add: subgroup_generated_def)
    done
qed

lemma (in group) int_pow_subgroup_generated:
  fixes n::int
  assumes "x \<in> carrier (subgroup_generated G S)"
  shows "x [^]\<^bsub>subgroup_generated G S\<^esub> n = x [^]\<^bsub>G\<^esub> n"
proof -
  have "x [^] nat (- n) \<in> carrier (subgroup_generated G S)"
    by (metis assms group.is_monoid group_subgroup_generated monoid.nat_pow_closed pow_subgroup_generated)
  then show ?thesis
    by (metis group.inv_subgroup_generated int_pow_def2 is_group pow_subgroup_generated)
qed

lemma kernel_from_subgroup_generated [simp]:
  "subgroup S G \<Longrightarrow> kernel (subgroup_generated G S) H f = kernel G H f \<inter> S"
  using subgroup.carrier_subgroup_generated_subgroup subgroup.subset
  by (fastforce simp add: kernel_def set_eq_iff)

lemma kernel_to_subgroup_generated [simp]:
  "kernel G (subgroup_generated H S) f = kernel G H f"
  by (simp add: kernel_def)

subsection \<open>And homomorphisms\<close>

lemma (in group) hom_from_subgroup_generated:
   "h \<in> hom G H \<Longrightarrow> h \<in> hom(subgroup_generated G A) H"
  apply (simp add: hom_def carrier_subgroup_generated Pi_iff)
  apply (metis group.generate_in_carrier inf_le1 is_group)
  done

lemma hom_into_subgroup:
   "\<lbrakk>h \<in> hom G G'; h ` (carrier G) \<subseteq> H\<rbrakk> \<Longrightarrow> h \<in> hom G (subgroup_generated G' H)"
  by (auto simp: hom_def carrier_subgroup_generated Pi_iff generate.incl image_subset_iff)

lemma hom_into_subgroup_eq_gen:
    "group G \<Longrightarrow>
     h \<in> hom K (subgroup_generated G H)
 \<longleftrightarrow> h \<in> hom K G \<and> h ` (carrier K) \<subseteq> carrier(subgroup_generated G H)"
  using group.carrier_subgroup_generated_subset [of G H] by (auto simp: hom_def)

lemma hom_into_subgroup_eq:
   "\<lbrakk>subgroup H G; group G\<rbrakk>
    \<Longrightarrow> (h \<in> hom K (subgroup_generated G H) \<longleftrightarrow> h \<in> hom K G \<and> h ` (carrier K) \<subseteq> H)"
  by (simp add: hom_into_subgroup_eq_gen image_subset_iff subgroup.carrier_subgroup_generated_subgroup)

lemma (in group_hom) hom_between_subgroups:
  assumes "h ` A \<subseteq> B"
  shows "h \<in> hom (subgroup_generated G A) (subgroup_generated H B)"
proof -
  have [simp]: "group G" "group H"
    by (simp_all add: G.is_group H.is_group)
  have "x \<in> generate G (carrier G \<inter> A) \<Longrightarrow> h x \<in> generate H (carrier H \<inter> B)" for x
  proof (induction x rule: generate.induct)
    case (incl h)
    then show ?case
      by (meson IntE IntI assms generate.incl hom_closed image_subset_iff)
  next
    case (inv h)
    then show ?case
      by (metis G.inv_closed G.inv_inv IntE IntI assms generate.simps hom_inv image_subset_iff local.inv_closed)
  next
    case (eng h1 h2)
    then show ?case
      by (metis G.generate_in_carrier generate.simps inf.cobounded1 local.hom_mult)
  qed (auto simp: generate.intros)
  then have "h ` carrier (subgroup_generated G A) \<subseteq> carrier (subgroup_generated H B)"
    using group.carrier_subgroup_generated_subset [of G A]
    by (auto simp: carrier_subgroup_generated)
  then show ?thesis
    by (simp add: hom_into_subgroup_eq_gen group.hom_from_subgroup_generated homh)
qed

lemma (in group_hom) subgroup_generated_by_image:
  assumes "S \<subseteq> carrier G"
  shows "carrier (subgroup_generated H (h ` S)) = h ` (carrier(subgroup_generated G S))"
proof
  have "x \<in> generate H (carrier H \<inter> h ` S) \<Longrightarrow> x \<in> h ` generate G (carrier G \<inter> S)" for x
  proof (erule generate.induct)
    show "\<one>\<^bsub>H\<^esub> \<in> h ` generate G (carrier G \<inter> S)"
      using generate.one by force
  next
    fix f
    assume "f \<in> carrier H \<inter> h ` S"
    with assms show "f \<in> h ` generate G (carrier G \<inter> S)" "inv\<^bsub>H\<^esub> f \<in> h ` generate G (carrier G \<inter> S)"
       apply (auto simp: Int_absorb1 generate.incl)
      apply (metis generate.simps hom_inv imageI subsetCE)
      done
  next
    fix h1 h2
    assume
      "h1 \<in> generate H (carrier H \<inter> h ` S)" "h1 \<in> h ` generate G (carrier G \<inter> S)"
      "h2 \<in> generate H (carrier H \<inter> h ` S)" "h2 \<in> h ` generate G (carrier G \<inter> S)"
    then show "h1 \<otimes>\<^bsub>H\<^esub> h2 \<in> h ` generate G (carrier G \<inter> S)"
      using H.subgroupE(4) group.generate_is_subgroup subgroup_img_is_subgroup
      by (simp add: G.generate_is_subgroup)
  qed
  then
  show "carrier (subgroup_generated H (h ` S)) \<subseteq> h ` carrier (subgroup_generated G S)"
    by (auto simp: carrier_subgroup_generated)
next
  have "h ` S \<subseteq> carrier H"
    by (metis (no_types) assms hom_closed image_subset_iff subsetCE)
  then show "h ` carrier (subgroup_generated G S) \<subseteq> carrier (subgroup_generated H (h ` S))"
    apply (clarsimp simp: carrier_subgroup_generated)
    by (metis Int_absorb1 assms generate_img imageI)
qed

lemma (in group_hom) iso_between_subgroups:
  assumes "h \<in> iso G H" "S \<subseteq> carrier G" "h ` S = T"
  shows "h \<in> iso (subgroup_generated G S) (subgroup_generated H T)"
  using assms
  by (metis G.carrier_subgroup_generated_subset Group.iso_iff hom_between_subgroups inj_on_subset subgroup_generated_by_image subsetI)

lemma (in group) subgroup_generated_group_carrier:
  "subgroup_generated G (carrier G) = G"
proof (rule monoid.equality)
  show "carrier (subgroup_generated G (carrier G)) = carrier G"
    by (simp add: subgroup.carrier_subgroup_generated_subgroup subgroup_self)
qed (auto simp: subgroup_generated_def)

lemma iso_onto_image:
  assumes "group G" "group H"
  shows
   "f \<in> iso G (subgroup_generated H (f ` carrier G)) \<longleftrightarrow> f \<in> hom G H \<and> inj_on f (carrier G)"
  using assms
  apply (auto simp: iso_def bij_betw_def hom_into_subgroup_eq_gen carrier_subgroup_generated hom_carrier generate.incl Int_absorb1 Int_absorb2)
  by (metis group.generateI group.subgroupE(1) group.subgroup_self group_hom.generate_img group_hom.intro group_hom_axioms.intro)

lemma (in group) iso_onto_image:
   "group H \<Longrightarrow> f \<in> iso G (subgroup_generated H (f ` carrier G)) \<longleftrightarrow> f \<in> mon G H"
  by (simp add: mon_def epi_def hom_into_subgroup_eq_gen iso_onto_image)

end