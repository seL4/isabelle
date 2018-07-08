(*  Title:      HOL/Algebra/Zassenhaus.thy
    Author:     Martin Baillon
*)

section \<open>The Zassenhaus Lemma\<close>

theory Zassenhaus
  imports Coset Group_Action
begin

text \<open>Proves the second isomorphism theorem and the Zassenhaus lemma.\<close>

subsection \<open>Lemmas about normalizer\<close>

lemma (in group) subgroup_in_normalizer:
  assumes "subgroup H G"
  shows "normal H (G\<lparr>carrier:= (normalizer G H)\<rparr>)"
proof(intro group.normal_invI)
  show "Group.group (G\<lparr>carrier := normalizer G H\<rparr>)"
    by (simp add: assms group.normalizer_imp_subgroup is_group subgroup_imp_group subgroup.subset)
  have K:"H \<subseteq> (normalizer G H)" unfolding normalizer_def
  proof
    fix x assume xH: "x \<in> H"
    from xH have xG : "x \<in> carrier G" using subgroup.subset assms by auto
    have "x <# H = H"
      by (metis \<open>x \<in> H\<close> assms group.lcos_mult_one is_group
         l_repr_independence one_closed subgroup.subset)
    moreover have "H #> inv x = H"
      by (simp add: xH assms is_group subgroup.rcos_const subgroup.m_inv_closed)
    ultimately have "x <# H #> (inv x) = H" by simp
    thus " x \<in> stabilizer G (\<lambda>g. \<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) H"
      using assms xG subgroup.subset unfolding stabilizer_def by auto
  qed
  thus "subgroup H (G\<lparr>carrier:= (normalizer G H)\<rparr>)"
    using subgroup_incl normalizer_imp_subgroup assms by (simp add: subgroup.subset)
  show  " \<And>x h. x \<in> carrier (G\<lparr>carrier := normalizer G H\<rparr>) \<Longrightarrow> h \<in> H \<Longrightarrow>
             x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
               \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H"
    proof-
    fix x h assume xnorm : "x \<in> carrier (G\<lparr>carrier := normalizer G H\<rparr>)" and hH : "h \<in> H"
    have xnormalizer:"x \<in> normalizer G H" using xnorm by simp
    moreover have hnormalizer:"h \<in> normalizer G H" using hH K by auto
    ultimately have "x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h = x \<otimes> h" by simp
    moreover have " inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x =  inv x"
      using xnormalizer
      by (simp add: assms normalizer_imp_subgroup subgroup.subset m_inv_consistent)
    ultimately  have xhxegal: "x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
                \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x
                  = x \<otimes>h \<otimes> inv x"
      using  hnormalizer by simp
    have  "x \<otimes>h \<otimes> inv x \<in> (x <# H #> inv x)"
      unfolding l_coset_def r_coset_def using hH  by auto
    moreover have "x <# H #> inv x = H"
      using xnormalizer assms subgroup.subset[OF assms]
      unfolding normalizer_def stabilizer_def by auto
    ultimately have "x \<otimes>h \<otimes> inv x \<in> H" by simp
    thus  " x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
               \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H"
      using xhxegal hH xnorm by simp
  qed
qed


lemma (in group) normal_imp_subgroup_normalizer:
  assumes "subgroup H G"
    and "N \<lhd> (G\<lparr>carrier := H\<rparr>)"
  shows "subgroup H (G\<lparr>carrier := normalizer G N\<rparr>)"
proof-
  have N_carrierG : "N \<subseteq> carrier(G)"
    using assms normal_imp_subgroup subgroup.subset
    using incl_subgroup by blast
  {have "H \<subseteq> normalizer G N" unfolding normalizer_def stabilizer_def
    proof
      fix x assume xH : "x \<in> H"
      hence xcarrierG : "x \<in> carrier(G)" using assms subgroup.subset  by auto
      have "   N #> x = x <# N" using assms xH
        unfolding r_coset_def l_coset_def normal_def normal_axioms_def subgroup_imp_group by auto
      hence "x <# N #> inv x =(N #> x) #> inv x"
        by simp
      also have "... = N #> \<one>"
        using  assms r_inv xcarrierG coset_mult_assoc[OF N_carrierG] by simp
      finally have "x <# N #> inv x = N" by (simp add: N_carrierG)
      thus "x \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) N = N}"
        using xcarrierG by (simp add : N_carrierG)
    qed}
  thus "subgroup H (G\<lparr>carrier := normalizer G N\<rparr>)"
    using subgroup_incl[OF assms(1) normalizer_imp_subgroup]
      assms normal_imp_subgroup subgroup.subset
    by (metis  group.incl_subgroup is_group)
qed


subsection \<open>Second Isomorphism Theorem\<close>

lemma (in group) mult_norm_subgroup:
  assumes "normal N G"
    and "subgroup H G"
  shows "subgroup (N<#>H) G" unfolding subgroup_def
proof-
  have  A :"N <#> H \<subseteq> carrier G"
    using assms  setmult_subset_G by (simp add: normal_imp_subgroup subgroup.subset)

  have B :"\<And> x y. \<lbrakk>x \<in> (N <#> H); y \<in> (N <#> H)\<rbrakk> \<Longrightarrow> (x \<otimes> y) \<in> (N<#>H)"
  proof-
    fix x y assume B1a: "x \<in> (N <#> H)"  and B1b: "y \<in> (N <#> H)"
    obtain n1 h1 where B2:"n1 \<in> N \<and> h1 \<in> H \<and> n1\<otimes>h1 = x"
      using set_mult_def B1a by (metis (no_types, lifting) UN_E singletonD)
    obtain n2 h2 where B3:"n2 \<in> N \<and> h2 \<in> H \<and> n2\<otimes>h2 = y"
      using set_mult_def B1b by (metis (no_types, lifting) UN_E singletonD)
    have "N #> h1 = h1 <# N"
      using normalI B2 assms normal.coset_eq subgroup.subset by blast
    hence "h1\<otimes>n2 \<in> N #> h1"
      using B2 B3 assms l_coset_def by fastforce
    from this obtain y2 where y2_def:"y2 \<in> N" and y2_prop:"y2\<otimes>h1 = h1\<otimes>n2"
      using singletonD by (metis (no_types, lifting) UN_E r_coset_def)
    have "\<And>a. a \<in> N \<Longrightarrow> a \<in> carrier G"  "\<And>a. a \<in> H \<Longrightarrow> a \<in> carrier G"
      by (meson assms normal_def subgroup.mem_carrier)+
    then have "x\<otimes>y =  n1 \<otimes> y2 \<otimes> h1 \<otimes> h2" using y2_def B2 B3
      by (metis (no_types) B2 B3 \<open>\<And>a. a \<in> N \<Longrightarrow> a \<in> carrier G\<close> m_assoc m_closed y2_def y2_prop)
    moreover have B4 :"n1 \<otimes> y2 \<in>N"
      using B2 y2_def assms normal_imp_subgroup by (metis subgroup_def)
    moreover have "h1 \<otimes> h2 \<in>H" using B2 B3 assms by (simp add: subgroup.m_closed)
    hence "(n1 \<otimes> y2) \<otimes> (h1 \<otimes> h2) \<in>(N<#>H) "
      using B4  unfolding set_mult_def by auto
    hence "n1 \<otimes> y2 \<otimes> h1 \<otimes> h2 \<in>(N<#>H)"
      using m_assoc B2 B3 assms  normal_imp_subgroup by (metis B4 subgroup.mem_carrier)
    ultimately show  "x \<otimes> y \<in> N <#> H" by auto
  qed
  have C :"\<And> x. x\<in>(N<#>H)  \<Longrightarrow> (inv x)\<in>(N<#>H)"

  proof-
    fix x assume C1 : "x \<in> (N<#>H)"
    obtain n h where C2:"n \<in> N \<and> h \<in> H \<and> n\<otimes>h = x"
      using set_mult_def C1 by (metis (no_types, lifting) UN_E singletonD)
    have C3 :"inv(n\<otimes>h) = inv(h)\<otimes>inv(n)"
      by (meson C2  assms inv_mult_group normal_imp_subgroup subgroup.mem_carrier)
    hence "... \<otimes>h \<in> N"
      using assms C2
      by (meson normal.inv_op_closed1 normal_def subgroup.m_inv_closed subgroup.mem_carrier)
    hence  C4:"(inv h \<otimes> inv n \<otimes> h) \<otimes> inv h \<in> (N<#>H)"
      using   C2 assms subgroup.m_inv_closed[of H G h] unfolding set_mult_def by auto
    have "inv h \<otimes> inv n \<otimes> h \<otimes> inv h = inv h \<otimes> inv n"
      using  subgroup.subset[OF assms(2)]
      by (metis A C1 C2 C3 inv_closed inv_solve_right m_closed subsetCE)
    thus "inv(x)\<in>N<#>H" using C4 C2 C3 by simp
  qed

  have D : "\<one> \<in> N <#> H"
  proof-
    have D1 : "\<one> \<in> N"
      using assms by (simp add: normal_def subgroup.one_closed)
     have D2 :"\<one> \<in> H"
      using assms by (simp add: subgroup.one_closed)
    thus "\<one> \<in> (N <#> H)"
      using set_mult_def D1 assms by fastforce
  qed
  thus "(N <#> H \<subseteq> carrier G \<and> (\<forall>x y. x \<in> N <#> H \<longrightarrow> y \<in> N <#> H \<longrightarrow> x \<otimes> y \<in> N <#> H)) \<and>
    \<one> \<in> N <#> H \<and> (\<forall>x. x \<in> N <#> H \<longrightarrow> inv x \<in> N <#> H)" using A B C D assms by blast
qed


lemma (in group) mult_norm_sub_in_sub:
  assumes "normal N (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup H (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup K G"
  shows  "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)"
proof-
  have Hyp:"subgroup (N <#>\<^bsub>G\<lparr>carrier := K\<rparr>\<^esub> H) (G\<lparr>carrier := K\<rparr>)"
    using group.mult_norm_subgroup[where ?G = "G\<lparr>carrier := K\<rparr>"] assms subgroup_imp_group by auto
  have "H \<subseteq> carrier(G\<lparr>carrier := K\<rparr>)" using assms subgroup.subset by blast
  also have "... \<subseteq> K" by simp
  finally have Incl1:"H \<subseteq> K" by simp
  have "N \<subseteq> carrier(G\<lparr>carrier := K\<rparr>)" using assms normal_imp_subgroup subgroup.subset by blast
  also have "... \<subseteq> K" by simp
  finally have Incl2:"N \<subseteq> K" by simp
  have "(N <#>\<^bsub>G\<lparr>carrier := K\<rparr>\<^esub> H) = (N <#> H)"
    using set_mult_consistent by simp
  thus "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)" using Hyp by auto
qed


lemma (in group) subgroup_of_normal_set_mult:
  assumes "normal N G"
and "subgroup H G"
shows "subgroup H (G\<lparr>carrier := N <#> H\<rparr>)"
proof-
  have "\<one> \<in> N" using normal_imp_subgroup assms(1) subgroup_def by blast
  hence "\<one> <# H \<subseteq> N <#> H" unfolding set_mult_def l_coset_def by blast
  hence H_incl : "H \<subseteq> N <#> H"
    by (metis assms(2) lcos_mult_one subgroup_def)
  show "subgroup H (G\<lparr>carrier := N <#> H\<rparr>)"
  using subgroup_incl[OF assms(2) mult_norm_subgroup[OF assms(1) assms(2)] H_incl] .
qed


lemma (in group) normal_in_normal_set_mult:
  assumes "normal N G"
and "subgroup H G"
shows "normal N (G\<lparr>carrier := N <#> H\<rparr>)"
proof-
  have "\<one> \<in> H" using  assms(2) subgroup_def by blast
  hence "N #> \<one>  \<subseteq> N <#> H" unfolding set_mult_def r_coset_def by blast
  hence N_incl : "N \<subseteq> N <#> H"
    by (metis assms(1) normal_imp_subgroup coset_mult_one subgroup_def)
  thus "normal N (G\<lparr>carrier := N <#> H\<rparr>)"
    using normal_inter_subgroup[OF mult_norm_subgroup[OF assms] assms(1)]
    by (simp add : inf_absorb1)
qed


proposition (in group) weak_snd_iso_thme:
  assumes "subgroup  H G"
    and "N\<lhd>G"
  shows "(G\<lparr>carrier := N<#>H\<rparr> Mod N \<cong> G\<lparr>carrier:=H\<rparr> Mod (N\<inter>H))"
proof-
  define f where "f =  (#>) N"
  have GroupNH : "Group.group (G\<lparr>carrier := N<#>H\<rparr>)"
    using subgroup_imp_group assms mult_norm_subgroup by simp
  have  HcarrierNH :"H \<subseteq> carrier(G\<lparr>carrier := N<#>H\<rparr>)"
    using assms subgroup_of_normal_set_mult subgroup.subset by blast
  hence HNH :"H \<subseteq> N<#>H" by simp
  have op_hom : "f \<in> hom (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N <#> H\<rparr> Mod N)" unfolding hom_def
  proof
    have "\<And>x . x \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<Longrightarrow>
       (#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N x \<in>  carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
    proof-
      fix x assume  "x \<in> carrier (G\<lparr>carrier :=H\<rparr>)"
      hence xH : "x \<in> H" by simp
      hence "(#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N x \<in> rcosets\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N"
        using HcarrierNH RCOSETS_def[where ?G = "G\<lparr>carrier := N <#> H\<rparr>"] by blast
      thus "(#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N x \<in>  carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
        unfolding FactGroup_def by simp
    qed
    hence "(#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<rightarrow>
            carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)" by auto
    hence "f \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<rightarrow> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      unfolding r_coset_def f_def  by simp
    moreover have "\<And>x y. x\<in>carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> y\<in>carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow>
                  f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y)"
    proof-
      fix x y assume "x\<in>carrier (G\<lparr>carrier := H\<rparr>)" "y\<in>carrier (G\<lparr>carrier := H\<rparr>)"
      hence xHyH :"x \<in> H" "y \<in> H" by auto
      have Nxeq :"N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x = N #>x" unfolding r_coset_def by simp
      have Nyeq :"N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y = N #>y" unfolding r_coset_def by simp

      have "x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y =x \<otimes>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y" by simp
      hence "N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y
             = N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x \<otimes>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y" by simp
      also have "... = (N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x) <#>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub>
                       (N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y)"
        using normal.rcos_sum[OF normal_in_normal_set_mult[OF assms(2) assms(1)], of x y]
             xHyH assms HcarrierNH by auto
      finally show "f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y)"
        unfolding  FactGroup_def r_coset_def f_def  using Nxeq Nyeq  by auto
    qed
    hence "(\<forall>x\<in>carrier (G\<lparr>carrier := H\<rparr>). \<forall>y\<in>carrier (G\<lparr>carrier := H\<rparr>).
           f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y))" by blast
    ultimately show  " f \<in> carrier (G\<lparr>carrier := H\<rparr>) \<rightarrow> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N) \<and>
    (\<forall>x\<in>carrier (G\<lparr>carrier := H\<rparr>). \<forall>y\<in>carrier (G\<lparr>carrier := H\<rparr>).
     f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y))"
      by auto
  qed
  hence homomorphism : "group_hom (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N <#> H\<rparr> Mod N) f"
    unfolding group_hom_def group_hom_axioms_def using subgroup_imp_group[OF assms(1)]
             normal.factorgroup_is_group[OF normal_in_normal_set_mult[OF assms(2) assms(1)]] by auto
  moreover have im_f :  "(f  ` carrier(G\<lparr>carrier:=H\<rparr>)) = carrier(G\<lparr>carrier := N <#> H\<rparr> Mod N)"
  proof
    show  "f ` carrier (G\<lparr>carrier := H\<rparr>) \<subseteq> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      using op_hom unfolding hom_def using funcset_image by blast
  next
    show "carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N) \<subseteq> f ` carrier (G\<lparr>carrier := H\<rparr>)"
    proof
      fix x assume p : " x \<in> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      hence "x \<in> \<Union>{y. \<exists>x\<in>carrier (G\<lparr>carrier := N <#> H\<rparr>). y = {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> x}}"
        unfolding FactGroup_def RCOSETS_def by auto
      hence hyp :"\<exists>y. \<exists>h\<in>carrier (G\<lparr>carrier := N <#> H\<rparr>). y = {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> h} \<and> x \<in> y"
        using Union_iff by blast
      from hyp obtain nh where nhNH:"nh \<in>carrier (G\<lparr>carrier := N <#> H\<rparr>)"
                          and "x \<in> {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> nh}"
        by blast
      hence K: "x = (#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N nh" by simp
      have "nh \<in> N <#> H" using nhNH by simp
      from this obtain n h where nN : "n \<in> N" and hH : " h \<in> H" and nhnh: "n \<otimes> h = nh"
        unfolding set_mult_def by blast
      have  "x = (#>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub>) N (n \<otimes> h)" using K nhnh by simp
      hence  "x = (#>) N (n \<otimes> h)" using K nhnh unfolding r_coset_def by auto
      also have "... = (N #> n) #>h"
        using coset_mult_assoc hH nN assms subgroup.subset normal_imp_subgroup
        by (metis subgroup.mem_carrier)
      finally have "x = (#>) N h"
        using coset_join2[of n N] nN assms by (simp add: normal_imp_subgroup subgroup.mem_carrier)
      thus "x \<in> f ` carrier (G\<lparr>carrier := H\<rparr>)" using hH unfolding f_def by simp
    qed
  qed
  moreover have ker_f :"kernel (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N<#>H\<rparr> Mod N) f  = N\<inter>H"
    unfolding kernel_def f_def
    proof-
      have "{x \<in> carrier (G\<lparr>carrier := H\<rparr>). N #> x = \<one>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub>} =
            {x \<in> carrier (G\<lparr>carrier := H\<rparr>). N #> x = N}" unfolding FactGroup_def by simp
      also have "... = {x \<in> carrier (G\<lparr>carrier := H\<rparr>). x \<in> N}"
        using coset_join1
        by (metis (no_types, lifting) assms group.subgroup_self incl_subgroup is_group
          normal_imp_subgroup subgroup.mem_carrier subgroup.rcos_const subgroup_imp_group)
      also have "... =N \<inter> (carrier(G\<lparr>carrier := H\<rparr>))" by auto
      finally show "{x \<in> carrier (G\<lparr>carrier := H\<rparr>). N#>x = \<one>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub>} = N \<inter> H"
        by simp
    qed
    ultimately have "(G\<lparr>carrier := H\<rparr> Mod N \<inter> H) \<cong> (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      using group_hom.FactGroup_iso[OF homomorphism im_f] by auto
    hence "G\<lparr>carrier := N <#> H\<rparr> Mod N \<cong> G\<lparr>carrier := H\<rparr> Mod N \<inter> H"
      by (simp add: group.iso_sym assms normal.factorgroup_is_group normal_inter_subgroup)
    thus "G\<lparr>carrier := N <#> H\<rparr> Mod N \<cong> G\<lparr>carrier := H\<rparr> Mod N \<inter> H" by auto
qed


theorem (in group) snd_iso_thme:
  assumes "subgroup H G"
    and "subgroup N G"
    and "subgroup H (G\<lparr>carrier:= (normalizer G N)\<rparr>)"
  shows "(G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong> (G\<lparr>carrier:= H\<rparr> Mod (H\<inter>N))"
proof-
  have "G\<lparr>carrier := normalizer G N, carrier := H\<rparr>
       = G\<lparr>carrier := H\<rparr>"  by simp
  hence "G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
         G\<lparr>carrier := H\<rparr> Mod N \<inter> H" by auto
  moreover have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> =
                G\<lparr>carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr>" by simp
  hence "G\<lparr>carrier := normalizer G N,
          carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N =
          G\<lparr>carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N" by auto
  hence "G\<lparr>carrier := normalizer G N,
          carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
         G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
          (G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>
         G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H"
    using subgroup.subset[OF assms(3)]
          subgroup.subset[OF normal_imp_subgroup[OF subgroup_in_normalizer[OF assms(2)]]]
    by simp
  ultimately have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
                  G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
                 (G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>  G\<lparr>carrier := H\<rparr> Mod N \<inter> H" by auto
  moreover have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
                  G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H"
    using group.weak_snd_iso_thme[OF subgroup_imp_group[OF normalizer_imp_subgroup[OF
          subgroup.subset[OF assms(2)]]] assms(3) subgroup_in_normalizer[OF assms(2)]]
    by simp
  moreover have "H\<inter>N = N\<inter>H" using assms  by auto
  ultimately show "(G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>  G\<lparr>carrier := H\<rparr> Mod H \<inter> N" by auto
qed


corollary (in group) snd_iso_thme_recip :
  assumes "subgroup H G"
    and "subgroup N G"
    and "subgroup H (G\<lparr>carrier:= (normalizer G N)\<rparr>)"
  shows "(G\<lparr>carrier:= H<#>N\<rparr> Mod N)  \<cong> (G\<lparr>carrier:= H\<rparr> Mod (H\<inter>N))"
  by (metis assms commut_normal_subgroup group.subgroup_in_normalizer is_group subgroup.subset
      normalizer_imp_subgroup snd_iso_thme)


subsection\<open>The Zassenhaus Lemma\<close>


lemma (in group) distinc:
  assumes "subgroup  H G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G"
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "subgroup (H\<inter>K) (G\<lparr>carrier:=(normalizer G (H1<#>(H\<inter>K1))) \<rparr>)"
proof (intro subgroup_incl[OF subgroups_Inter_pair[OF assms(1) assms(3)]])
  show "subgroup (normalizer G (H1 <#> H \<inter> K1)) G"
    using normalizer_imp_subgroup assms normal_imp_subgroup subgroup.subset
    by (metis group.incl_subgroup is_group setmult_subset_G subgroups_Inter_pair)
next
  show "H \<inter> K \<subseteq> normalizer G (H1 <#> H \<inter> K1)" unfolding normalizer_def stabilizer_def
  proof
    fix x assume xHK : "x \<in> H \<inter> K"
    hence xG : "{x} \<subseteq> carrier G" "{inv x} \<subseteq> carrier G"
      using subgroup.subset assms inv_closed xHK by auto
    have allG : "H \<subseteq> carrier G" "K \<subseteq> carrier G" "H1 \<subseteq> carrier G"  "K1 \<subseteq> carrier G"
      using assms subgroup.subset normal_imp_subgroup incl_subgroup apply blast+ .
    have HK1: "H \<inter> K1 \<subseteq> carrier G"
      by (simp add: allG(1) le_infI1)
    have HK1_normal: "H\<inter>K1 \<lhd> (G\<lparr>carrier :=  H \<inter> K\<rparr>)" using normal_inter[OF assms(3)assms(1)assms(4)]
      by (simp add : inf_commute)
    have "H \<inter> K \<subseteq> normalizer G (H \<inter> K1)"
      using subgroup.subset[OF normal_imp_subgroup_normalizer[OF subgroups_Inter_pair[OF
            assms(1)assms(3)]HK1_normal]] by auto
    hence "x <# (H \<inter> K1) #> inv x = (H \<inter> K1)"
      using xHK subgroup.subset[OF subgroups_Inter_pair[OF assms(1) incl_subgroup[OF assms(3)
                                                            normal_imp_subgroup[OF assms(4)]]]]
      unfolding normalizer_def stabilizer_def by auto
    moreover have "H \<subseteq>  normalizer G H1"
      using subgroup.subset[OF normal_imp_subgroup_normalizer[OF assms(1)assms(2)]] by auto
    hence "x <# H1 #> inv x = H1"
      using xHK subgroup.subset[OF  incl_subgroup[OF assms(1) normal_imp_subgroup[OF assms(2)]]]
      unfolding normalizer_def stabilizer_def by auto
    ultimately have "H1 <#> H \<inter> K1 = (x <# H1 #> inv x) <#> (x <#  H \<inter> K1 #> inv x)" by auto
    also have "... = ({x} <#> H1) <#> {inv x} <#> ({x} <#>  H \<inter> K1 <#> {inv x})"
      by (simp add : r_coset_eq_set_mult l_coset_eq_set_mult)
    also have "... = ({x} <#> H1 <#> {inv x} <#> {x}) <#>  (H \<inter> K1 <#> {inv x})"
      using HK1 allG(3) set_mult_assoc setmult_subset_G xG(1) by auto
    also have "... = ({x} <#> H1 <#> {\<one>}) <#>  (H \<inter> K1 <#> {inv x})"
      using allG xG coset_mult_assoc by (simp add: r_coset_eq_set_mult setmult_subset_G)
    also have "... =({x} <#> H1) <#>  (H \<inter> K1 <#> {inv x})"
      using coset_mult_one r_coset_eq_set_mult[of G H1 \<one>] set_mult_assoc[OF xG(1) allG(3)] allG
      by auto
    also have "... = {x} <#> (H1 <#> H \<inter> K1) <#> {inv x}"
      using allG xG set_mult_assoc setmult_subset_G by (metis inf.coboundedI2)
    finally have "H1 <#> H \<inter> K1 = x <# (H1 <#> H \<inter> K1) #> inv x"
      using xG setmult_subset_G allG by (simp add: l_coset_eq_set_mult r_coset_eq_set_mult)
    thus "x \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) (H1 <#> H \<inter> K1)
                                                                       = H1 <#> H \<inter> K1}"
      using xG allG setmult_subset_G[OF allG(3), where ?K = "H\<inter>K1"] xHK
      by auto
  qed
qed

lemma (in group) preliminary1:
  assumes "subgroup  H G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G"
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows " (H\<inter>K) \<inter> (H1<#>(H\<inter>K1)) = (H1\<inter>K)<#>(H\<inter>K1)"
proof
  have all_inclG : "H \<subseteq> carrier G" "H1 \<subseteq> carrier G" "K \<subseteq> carrier G" "K1 \<subseteq> carrier G"
    using assms subgroup.subset normal_imp_subgroup incl_subgroup apply blast+.
  show "H \<inter> K \<inter> (H1 <#> H \<inter> K1) \<subseteq> H1 \<inter> K <#> H \<inter> K1"
  proof
    fix x assume x_def : "x \<in> (H \<inter> K) \<inter> (H1 <#> (H \<inter> K1))"
    from x_def have x_incl : "x \<in> H" "x \<in> K" "x \<in> (H1 <#> (H \<inter> K1))" by auto
    then obtain h1 hk1 where h1hk1_def : "h1 \<in> H1" "hk1 \<in> H \<inter> K1" "h1 \<otimes> hk1 = x"
      using assms unfolding set_mult_def by blast
    hence "hk1 \<in> H \<inter> K" using subgroup.subset[OF normal_imp_subgroup[OF assms(4)]] by auto
    hence "inv hk1 \<in> H \<inter> K" using subgroup.m_inv_closed[OF subgroups_Inter_pair] assms by auto
    moreover have "h1 \<otimes> hk1 \<in> H \<inter> K" using x_incl h1hk1_def by auto
    ultimately have "h1 \<otimes> hk1 \<otimes> inv hk1 \<in> H \<inter> K"
      using subgroup.m_closed[OF subgroups_Inter_pair] assms by auto
    hence "h1 \<in> H \<inter> K" using  h1hk1_def assms subgroup.subset incl_subgroup normal_imp_subgroup
      by (metis Int_iff contra_subsetD inv_solve_right m_closed)
    hence "h1 \<in> H1 \<inter> H \<inter> K" using h1hk1_def by auto
    hence "h1 \<in> H1 \<inter> K" using subgroup.subset[OF normal_imp_subgroup[OF assms(2)]] by auto
    hence "h1 \<otimes> hk1 \<in> (H1\<inter>K)<#>(H\<inter>K1)"
      using h1hk1_def unfolding set_mult_def by auto
    thus " x \<in> (H1\<inter>K)<#>(H\<inter>K1)" using h1hk1_def x_def by auto
  qed
  show "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K \<inter> (H1 <#> H \<inter> K1)"
  proof-
    have "H1 \<inter> K \<subseteq> H \<inter> K" using subgroup.subset[OF normal_imp_subgroup[OF assms(2)]] by auto
    moreover have "H \<inter> K1 \<subseteq> H \<inter> K"
      using subgroup.subset[OF normal_imp_subgroup[OF assms(4)]] by auto
    ultimately have "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K" unfolding set_mult_def
      using subgroup.m_closed[OF subgroups_Inter_pair [OF assms(1)assms(3)]] by blast
    moreover have "H1 \<inter> K \<subseteq> H1" by auto
    hence "H1 \<inter> K <#> H \<inter> K1 \<subseteq> (H1 <#> H \<inter> K1)" unfolding set_mult_def by auto
    ultimately show "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K \<inter> (H1 <#> H \<inter> K1)" by auto
  qed
qed

lemma (in group) preliminary2:
  assumes "subgroup  H G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G"
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(H1<#>(H\<inter>K1)) \<lhd> G\<lparr>carrier:=(H1<#>(H\<inter>K))\<rparr>"
proof-
  have all_inclG : "H \<subseteq> carrier G" "H1 \<subseteq> carrier G" "K \<subseteq> carrier G" "K1 \<subseteq> carrier G"
    using assms subgroup.subset normal_imp_subgroup incl_subgroup apply blast+.
  have subH1:"subgroup (H1 <#> H \<inter> K) (G\<lparr>carrier := H\<rparr>)"
    using mult_norm_sub_in_sub[OF assms(2)subgroup_incl[OF subgroups_Inter_pair[OF assms(1)assms(3)]
          assms(1)]] assms by auto
  have "Group.group (G\<lparr>carrier:=(H1<#>(H\<inter>K))\<rparr>)"
    using  subgroup_imp_group[OF incl_subgroup[OF assms(1) subH1]].
  moreover have subH2 : "subgroup (H1 <#> H \<inter> K1) (G\<lparr>carrier := H\<rparr>)"
    using mult_norm_sub_in_sub[OF assms(2) subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1) incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]]] assms by auto
  hence "(H\<inter>K1) \<subseteq> (H\<inter>K)"
    using assms subgroup.subset normal_imp_subgroup monoid.cases_scheme
    by (metis inf.mono  partial_object.simps(1) partial_object.update_convs(1) subset_refl)
  hence incl:"(H1<#>(H\<inter>K1)) \<subseteq> H1<#>(H\<inter>K)" using assms subgroup.subset normal_imp_subgroup
    unfolding set_mult_def by blast
  hence "subgroup (H1 <#> H \<inter> K1) (G\<lparr>carrier := (H1<#>(H\<inter>K))\<rparr>)"
    using assms subgroup_incl[OF incl_subgroup[OF assms(1)subH2]incl_subgroup[OF assms(1)
          subH1]] normal_imp_subgroup subgroup.subset unfolding set_mult_def by blast
  moreover have " (\<And> x. x\<in>carrier (G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>) \<Longrightarrow>
        H1 <#> H\<inter>K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> x = x <#\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> (H1 <#> H\<inter>K1))"
  proof-
    fix x assume  "x \<in>carrier (G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>)"
    hence x_def : "x \<in> H1 <#> H \<inter> K" by simp
    from this obtain h1 hk where h1hk_def :"h1 \<in> H1" "hk \<in> H \<inter> K" "h1 \<otimes> hk = x"
      unfolding set_mult_def by blast
    have HK1: "H \<inter> K1 \<subseteq> carrier G"
      by (simp add: all_inclG(1) le_infI1)
    have xH : "x \<in> H" using subgroup.subset[OF subH1] using x_def by auto
    hence allG : "h1 \<in> carrier G" "hk \<in> carrier G" "x \<in> carrier G"
      using assms subgroup.subset h1hk_def normal_imp_subgroup incl_subgroup apply blast+.
    hence "x <#\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> (H1 <#> H\<inter>K1) =h1 \<otimes> hk <# (H1 <#> H\<inter>K1)"
      using subgroup.subset xH h1hk_def by (simp add: l_coset_def)
    also have "... = h1 <# (hk <# (H1 <#> H\<inter>K1))"
      using lcos_m_assoc[OF subgroup.subset[OF incl_subgroup[OF assms(1) subH1]]allG(1)allG(2)]
      by (metis allG(1) allG(2) assms(1) incl_subgroup lcos_m_assoc subH2 subgroup.subset)
    also have "... = h1 <# (hk <# H1 <#> H\<inter>K1)"
      using set_mult_assoc all_inclG allG by (simp add: l_coset_eq_set_mult inf.coboundedI1)
    also have "... = h1 <# (hk <# H1 #> \<one> <#> H\<inter>K1 #> \<one>)"
      using coset_mult_one allG all_inclG l_coset_subset_G
      by (simp add: inf.coboundedI2 setmult_subset_G)
    also have "... = h1 <# (hk <# H1 #> inv hk #> hk <#> H\<inter>K1 #> inv hk #> hk)"
      using all_inclG allG coset_mult_assoc l_coset_subset_G
      by (simp add: inf.coboundedI1 setmult_subset_G)
    finally have "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) 
                  = h1 <# ((hk <# H1 #> inv hk) <#> (hk <# H\<inter>K1 #> inv hk) #> hk)"
      using rcos_assoc_lcos allG all_inclG HK1
      by (simp add: l_coset_subset_G r_coset_subset_G setmult_rcos_assoc)
    moreover have "H \<subseteq>  normalizer G H1"
      using assms h1hk_def subgroup.subset[OF normal_imp_subgroup_normalizer] by simp
    hence "\<And>g. g \<in> H \<Longrightarrow>  g \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) H1 = H1}"
      using all_inclG assms unfolding normalizer_def stabilizer_def by auto
    hence "\<And>g. g \<in> H \<Longrightarrow>  g <# H1 #> inv g = H1" using all_inclG by simp
    hence "(hk <# H1 #> inv hk) = H1" using h1hk_def all_inclG by simp
    moreover have "H\<inter>K \<subseteq> normalizer G (H\<inter>K1)"
      using normal_inter[OF assms(3)assms(1)assms(4)] assms subgroups_Inter_pair
            subgroup.subset[OF normal_imp_subgroup_normalizer] by (simp add: inf_commute)
    hence "\<And>g. g\<in>H\<inter>K \<Longrightarrow> g\<in>{g\<in>carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) (H\<inter>K1) = H\<inter>K1}"
      using all_inclG assms unfolding normalizer_def stabilizer_def by auto
    hence "\<And>g. g \<in> H\<inter>K \<Longrightarrow>  g <# (H\<inter>K1) #> inv g = H\<inter>K1"
      using subgroup.subset[OF subgroups_Inter_pair[OF assms(1) incl_subgroup[OF
            assms(3)normal_imp_subgroup[OF assms(4)]]]] by auto
    hence "(hk <# H\<inter>K1 #> inv hk) = H\<inter>K1" using h1hk_def by simp
    ultimately have "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) = h1 <#(H1 <#> (H \<inter> K1)#> hk)"
      by auto
    also have "... = h1 <# H1 <#> ((H \<inter> K1)#> hk)"
      using set_mult_assoc[where ?M = "{h1}" and ?H = "H1" and ?K = "(H \<inter> K1)#> hk"] allG all_inclG
      by (simp add: l_coset_eq_set_mult inf.coboundedI2 r_coset_subset_G setmult_rcos_assoc)
    also have "... = H1 <#> ((H \<inter> K1)#> hk)"
      using coset_join3 allG incl_subgroup[OF assms(1)normal_imp_subgroup[OF assms(2)]] h1hk_def
      by auto
    finally have eq1 : "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) = H1 <#> (H \<inter> K1) #> hk"
      by (simp add: allG(2) all_inclG inf.coboundedI2 setmult_rcos_assoc)
    have "H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x = H1 <#> H \<inter> K1 #> (h1 \<otimes> hk)"
      using subgroup.subset xH h1hk_def by (simp add: r_coset_def)
    also have "... = H1 <#> H \<inter> K1 #> h1 #> hk"
      using coset_mult_assoc by (simp add: allG all_inclG inf.coboundedI2 setmult_subset_G)
    also have"... =  H \<inter> K1 <#> H1 #> h1 #> hk"
      using commut_normal_subgroup[OF assms(1)assms(2)subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1)incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]assms(1)]] by simp
    also have "... = H \<inter> K1 <#> H1  #> hk"
      using coset_join2[OF allG(1)incl_subgroup[OF assms(1)normal_imp_subgroup]
            h1hk_def(1)] all_inclG allG assms by (metis inf.coboundedI2 setmult_rcos_assoc)
    finally  have "H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x =H1 <#> H \<inter> K1  #> hk"
      using commut_normal_subgroup[OF assms(1)assms(2)subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1)incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]assms(1)]] by simp
    thus " H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x =
             x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1)" using eq1 by simp
  qed
  ultimately show "H1 <#> H \<inter> K1 \<lhd> G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>"
    unfolding normal_def normal_axioms_def by auto
qed


proposition (in group)  Zassenhaus_1:
  assumes "subgroup  H G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G"
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>H\<inter>K1)) \<cong> (G\<lparr>carrier:= (H\<inter>K)\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1)))"
proof-
  define N  and N1 where "N = (H\<inter>K)" and "N1 =H1<#>(H\<inter>K1)"
  have normal_N_N1 : "subgroup N (G\<lparr>carrier:=(normalizer G N1)\<rparr>)"
    by (simp add: N1_def N_def assms distinc normal_imp_subgroup)
  have Hp:"(G\<lparr>carrier:= N<#>N1\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod (N\<inter>N1))"
  by (metis N1_def N_def assms incl_subgroup inf_le1 mult_norm_sub_in_sub
        normal_N_N1 normal_imp_subgroup snd_iso_thme_recip subgroup_incl subgroups_Inter_pair)
  have H_simp: "N<#>N1 = H1<#> (H\<inter>K)"
  proof-
    have H1_incl_G : "H1 \<subseteq> carrier G"
      using assms normal_imp_subgroup incl_subgroup subgroup.subset by blast
    have K1_incl_G :"K1 \<subseteq> carrier G"
      using assms normal_imp_subgroup incl_subgroup subgroup.subset by blast
    have "N<#>N1=  (H\<inter>K)<#> (H1<#>(H\<inter>K1))" by (auto simp add: N_def N1_def)
    also have "... = ((H\<inter>K)<#>H1) <#>(H\<inter>K1)"
      using set_mult_assoc[where ?M = "H\<inter>K"] K1_incl_G H1_incl_G assms
      by (simp add: inf.coboundedI2 subgroup.subset)
    also have "... = (H1<#>(H\<inter>K))<#>(H\<inter>K1)"
      using commut_normal_subgroup assms subgroup_incl subgroups_Inter_pair by auto
    also have "... =  H1 <#> ((H\<inter>K)<#>(H\<inter>K1))"
      using set_mult_assoc K1_incl_G H1_incl_G assms
      by (simp add: inf.coboundedI2 subgroup.subset)
    also have " ((H\<inter>K)<#>(H\<inter>K1)) = (H\<inter>K)"
    proof (intro set_mult_subgroup_idem[where ?H = "H\<inter>K" and ?N="H\<inter>K1",
             OF subgroups_Inter_pair[OF assms(1) assms(3)]])
      show "subgroup (H \<inter> K1) (G\<lparr>carrier := H \<inter> K\<rparr>)"
        using subgroup_incl[where ?I = "H\<inter>K1" and ?J = "H\<inter>K",OF subgroups_Inter_pair[OF assms(1)
              incl_subgroup[OF assms(3) normal_imp_subgroup]] subgroups_Inter_pair] assms
              normal_imp_subgroup by (metis inf_commute normal_inter)
    qed
    hence " H1 <#> ((H\<inter>K)<#>(H\<inter>K1)) =  H1 <#> ((H\<inter>K))"
      by simp
    thus "N <#> N1 = H1 <#> H \<inter> K"
      by (simp add: calculation)
  qed

  have "N\<inter>N1 = (H1\<inter>K)<#>(H\<inter>K1)"
    using preliminary1 assms N_def N1_def by simp
  thus  "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1)))"
    using H_simp Hp by auto
qed


theorem (in group) Zassenhaus:
  assumes "subgroup  H G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G"
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1)))  \<cong>
         (G\<lparr>carrier:= K1 <#> (H\<inter>K)\<rparr> Mod (K1<#>(K\<inter>H1)))"
proof-
  define Gmod1 Gmod2 Gmod3 Gmod4
    where "Gmod1 = (G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1))) "
      and "Gmod2 = (G\<lparr>carrier:= K1 <#> (K\<inter>H)\<rparr> Mod (K1<#>(K\<inter>H1)))"
      and "Gmod3 = (G\<lparr>carrier:= (H\<inter>K)\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1)))"
      and "Gmod4 = (G\<lparr>carrier:= (K\<inter>H)\<rparr> Mod  ((K1\<inter>H)<#>(K\<inter>H1)))"
  have Hyp :  "Gmod1  \<cong> Gmod3" "Gmod2  \<cong>  Gmod4"
    using Zassenhaus_1 assms Gmod1_def Gmod2_def Gmod3_def Gmod4_def by auto
  have Hp : "Gmod3 = G\<lparr>carrier:= (K\<inter>H)\<rparr> Mod ((K\<inter>H1)<#>(K1\<inter>H))"
    by (simp add: Gmod3_def inf_commute)
  have "(K\<inter>H1)<#>(K1\<inter>H) = (K1\<inter>H)<#>(K\<inter>H1)"
  proof (intro commut_normal_subgroup[OF subgroups_Inter_pair[OF assms(1)assms(3)]])
    show "K1 \<inter> H \<lhd> G\<lparr>carrier := H \<inter> K\<rparr>"
      using normal_inter[OF assms(3)assms(1)assms(4)] by (simp add: inf_commute)
   next
    show "subgroup (K \<inter> H1) (G\<lparr>carrier := H \<inter> K\<rparr>)"
      using subgroup_incl by (simp add: assms inf_commute normal_imp_subgroup normal_inter)
  qed
  hence  "Gmod3  = Gmod4" using Hp Gmod4_def by simp
  hence "Gmod1 \<cong> Gmod2"
    using group.iso_sym group.iso_trans Hyp normal.factorgroup_is_group
    by (metis assms Gmod1_def Gmod2_def preliminary2)
  thus ?thesis using Gmod1_def Gmod2_def by (simp add: inf_commute)
qed

end
