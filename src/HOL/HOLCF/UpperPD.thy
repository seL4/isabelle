(*  Title:      HOL/HOLCF/UpperPD.thy
    Author:     Brian Huffman
*)

header {* Upper powerdomain *}

theory UpperPD
imports Compact_Basis
begin

subsection {* Basis preorder *}

definition
  upper_le :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> bool" (infix "\<le>\<sharp>" 50) where
  "upper_le = (\<lambda>u v. \<forall>y\<in>Rep_pd_basis v. \<exists>x\<in>Rep_pd_basis u. x \<sqsubseteq> y)"

lemma upper_le_refl [simp]: "t \<le>\<sharp> t"
unfolding upper_le_def by fast

lemma upper_le_trans: "\<lbrakk>t \<le>\<sharp> u; u \<le>\<sharp> v\<rbrakk> \<Longrightarrow> t \<le>\<sharp> v"
unfolding upper_le_def
apply (rule ballI)
apply (drule (1) bspec, erule bexE)
apply (drule (1) bspec, erule bexE)
apply (erule rev_bexI)
apply (erule (1) below_trans)
done

interpretation upper_le: preorder upper_le
by (rule preorder.intro, rule upper_le_refl, rule upper_le_trans)

lemma upper_le_minimal [simp]: "PDUnit compact_bot \<le>\<sharp> t"
unfolding upper_le_def Rep_PDUnit by simp

lemma PDUnit_upper_mono: "x \<sqsubseteq> y \<Longrightarrow> PDUnit x \<le>\<sharp> PDUnit y"
unfolding upper_le_def Rep_PDUnit by simp

lemma PDPlus_upper_mono: "\<lbrakk>s \<le>\<sharp> t; u \<le>\<sharp> v\<rbrakk> \<Longrightarrow> PDPlus s u \<le>\<sharp> PDPlus t v"
unfolding upper_le_def Rep_PDPlus by fast

lemma PDPlus_upper_le: "PDPlus t u \<le>\<sharp> t"
unfolding upper_le_def Rep_PDPlus by fast

lemma upper_le_PDUnit_PDUnit_iff [simp]:
  "(PDUnit a \<le>\<sharp> PDUnit b) = (a \<sqsubseteq> b)"
unfolding upper_le_def Rep_PDUnit by fast

lemma upper_le_PDPlus_PDUnit_iff:
  "(PDPlus t u \<le>\<sharp> PDUnit a) = (t \<le>\<sharp> PDUnit a \<or> u \<le>\<sharp> PDUnit a)"
unfolding upper_le_def Rep_PDPlus Rep_PDUnit by fast

lemma upper_le_PDPlus_iff: "(t \<le>\<sharp> PDPlus u v) = (t \<le>\<sharp> u \<and> t \<le>\<sharp> v)"
unfolding upper_le_def Rep_PDPlus by fast

lemma upper_le_induct [induct set: upper_le]:
  assumes le: "t \<le>\<sharp> u"
  assumes 1: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> P (PDUnit a) (PDUnit b)"
  assumes 2: "\<And>t u a. P t (PDUnit a) \<Longrightarrow> P (PDPlus t u) (PDUnit a)"
  assumes 3: "\<And>t u v. \<lbrakk>P t u; P t v\<rbrakk> \<Longrightarrow> P t (PDPlus u v)"
  shows "P t u"
using le apply (induct u arbitrary: t rule: pd_basis_induct)
apply (erule rev_mp)
apply (induct_tac t rule: pd_basis_induct)
apply (simp add: 1)
apply (simp add: upper_le_PDPlus_PDUnit_iff)
apply (simp add: 2)
apply (subst PDPlus_commute)
apply (simp add: 2)
apply (simp add: upper_le_PDPlus_iff 3)
done


subsection {* Type definition *}

typedef 'a upper_pd =
  "{S::'a pd_basis set. upper_le.ideal S}"
by (rule upper_le.ex_ideal)

type_notation (xsymbols) upper_pd ("('(_')\<sharp>)")

instantiation upper_pd :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_upper_pd x \<subseteq> Rep_upper_pd y"

instance ..
end

instance upper_pd :: (bifinite) po
using type_definition_upper_pd below_upper_pd_def
by (rule upper_le.typedef_ideal_po)

instance upper_pd :: (bifinite) cpo
using type_definition_upper_pd below_upper_pd_def
by (rule upper_le.typedef_ideal_cpo)

definition
  upper_principal :: "'a pd_basis \<Rightarrow> 'a upper_pd" where
  "upper_principal t = Abs_upper_pd {u. u \<le>\<sharp> t}"

interpretation upper_pd:
  ideal_completion upper_le upper_principal Rep_upper_pd
using type_definition_upper_pd below_upper_pd_def
using upper_principal_def pd_basis_countable
by (rule upper_le.typedef_ideal_completion)

text {* Upper powerdomain is pointed *}

lemma upper_pd_minimal: "upper_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: upper_pd.principal_induct, simp, simp)

instance upper_pd :: (bifinite) pcpo
by intro_classes (fast intro: upper_pd_minimal)

lemma inst_upper_pd_pcpo: "\<bottom> = upper_principal (PDUnit compact_bot)"
by (rule upper_pd_minimal [THEN bottomI, symmetric])


subsection {* Monadic unit and plus *}

definition
  upper_unit :: "'a \<rightarrow> 'a upper_pd" where
  "upper_unit = compact_basis.extension (\<lambda>a. upper_principal (PDUnit a))"

definition
  upper_plus :: "'a upper_pd \<rightarrow> 'a upper_pd \<rightarrow> 'a upper_pd" where
  "upper_plus = upper_pd.extension (\<lambda>t. upper_pd.extension (\<lambda>u.
      upper_principal (PDPlus t u)))"

abbreviation
  upper_add :: "'a upper_pd \<Rightarrow> 'a upper_pd \<Rightarrow> 'a upper_pd"
    (infixl "\<union>\<sharp>" 65) where
  "xs \<union>\<sharp> ys == upper_plus\<cdot>xs\<cdot>ys"

syntax
  "_upper_pd" :: "args \<Rightarrow> logic" ("{_}\<sharp>")

translations
  "{x,xs}\<sharp>" == "{x}\<sharp> \<union>\<sharp> {xs}\<sharp>"
  "{x}\<sharp>" == "CONST upper_unit\<cdot>x"

lemma upper_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<sharp> = upper_principal (PDUnit a)"
unfolding upper_unit_def
by (simp add: compact_basis.extension_principal PDUnit_upper_mono)

lemma upper_plus_principal [simp]:
  "upper_principal t \<union>\<sharp> upper_principal u = upper_principal (PDPlus t u)"
unfolding upper_plus_def
by (simp add: upper_pd.extension_principal
    upper_pd.extension_mono PDPlus_upper_mono)

interpretation upper_add: semilattice upper_add proof
  fix xs ys zs :: "'a upper_pd"
  show "(xs \<union>\<sharp> ys) \<union>\<sharp> zs = xs \<union>\<sharp> (ys \<union>\<sharp> zs)"
    apply (induct xs rule: upper_pd.principal_induct, simp)
    apply (induct ys rule: upper_pd.principal_induct, simp)
    apply (induct zs rule: upper_pd.principal_induct, simp)
    apply (simp add: PDPlus_assoc)
    done
  show "xs \<union>\<sharp> ys = ys \<union>\<sharp> xs"
    apply (induct xs rule: upper_pd.principal_induct, simp)
    apply (induct ys rule: upper_pd.principal_induct, simp)
    apply (simp add: PDPlus_commute)
    done
  show "xs \<union>\<sharp> xs = xs"
    apply (induct xs rule: upper_pd.principal_induct, simp)
    apply (simp add: PDPlus_absorb)
    done
qed

lemmas upper_plus_assoc = upper_add.assoc
lemmas upper_plus_commute = upper_add.commute
lemmas upper_plus_absorb = upper_add.idem
lemmas upper_plus_left_commute = upper_add.left_commute
lemmas upper_plus_left_absorb = upper_add.left_idem

text {* Useful for @{text "simp add: upper_plus_ac"} *}
lemmas upper_plus_ac =
  upper_plus_assoc upper_plus_commute upper_plus_left_commute

text {* Useful for @{text "simp only: upper_plus_aci"} *}
lemmas upper_plus_aci =
  upper_plus_ac upper_plus_absorb upper_plus_left_absorb

lemma upper_plus_below1: "xs \<union>\<sharp> ys \<sqsubseteq> xs"
apply (induct xs rule: upper_pd.principal_induct, simp)
apply (induct ys rule: upper_pd.principal_induct, simp)
apply (simp add: PDPlus_upper_le)
done

lemma upper_plus_below2: "xs \<union>\<sharp> ys \<sqsubseteq> ys"
by (subst upper_plus_commute, rule upper_plus_below1)

lemma upper_plus_greatest: "\<lbrakk>xs \<sqsubseteq> ys; xs \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs \<sqsubseteq> ys \<union>\<sharp> zs"
apply (subst upper_plus_absorb [of xs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma upper_below_plus_iff [simp]:
  "xs \<sqsubseteq> ys \<union>\<sharp> zs \<longleftrightarrow> xs \<sqsubseteq> ys \<and> xs \<sqsubseteq> zs"
apply safe
apply (erule below_trans [OF _ upper_plus_below1])
apply (erule below_trans [OF _ upper_plus_below2])
apply (erule (1) upper_plus_greatest)
done

lemma upper_plus_below_unit_iff [simp]:
  "xs \<union>\<sharp> ys \<sqsubseteq> {z}\<sharp> \<longleftrightarrow> xs \<sqsubseteq> {z}\<sharp> \<or> ys \<sqsubseteq> {z}\<sharp>"
apply (induct xs rule: upper_pd.principal_induct, simp)
apply (induct ys rule: upper_pd.principal_induct, simp)
apply (induct z rule: compact_basis.principal_induct, simp)
apply (simp add: upper_le_PDPlus_PDUnit_iff)
done

lemma upper_unit_below_iff [simp]: "{x}\<sharp> \<sqsubseteq> {y}\<sharp> \<longleftrightarrow> x \<sqsubseteq> y"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (induct y rule: compact_basis.principal_induct, simp)
apply simp
done

lemmas upper_pd_below_simps =
  upper_unit_below_iff
  upper_below_plus_iff
  upper_plus_below_unit_iff

lemma upper_unit_eq_iff [simp]: "{x}\<sharp> = {y}\<sharp> \<longleftrightarrow> x = y"
unfolding po_eq_conv by simp

lemma upper_unit_strict [simp]: "{\<bottom>}\<sharp> = \<bottom>"
using upper_unit_Rep_compact_basis [of compact_bot]
by (simp add: inst_upper_pd_pcpo)

lemma upper_plus_strict1 [simp]: "\<bottom> \<union>\<sharp> ys = \<bottom>"
by (rule bottomI, rule upper_plus_below1)

lemma upper_plus_strict2 [simp]: "xs \<union>\<sharp> \<bottom> = \<bottom>"
by (rule bottomI, rule upper_plus_below2)

lemma upper_unit_bottom_iff [simp]: "{x}\<sharp> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding upper_unit_strict [symmetric] by (rule upper_unit_eq_iff)

lemma upper_plus_bottom_iff [simp]:
  "xs \<union>\<sharp> ys = \<bottom> \<longleftrightarrow> xs = \<bottom> \<or> ys = \<bottom>"
apply (induct xs rule: upper_pd.principal_induct, simp)
apply (induct ys rule: upper_pd.principal_induct, simp)
apply (simp add: inst_upper_pd_pcpo upper_pd.principal_eq_iff
                 upper_le_PDPlus_PDUnit_iff)
done

lemma compact_upper_unit: "compact x \<Longrightarrow> compact {x}\<sharp>"
by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_upper_unit_iff [simp]: "compact {x}\<sharp> \<longleftrightarrow> compact x"
apply (safe elim!: compact_upper_unit)
apply (simp only: compact_def upper_unit_below_iff [symmetric])
apply (erule adm_subst [OF cont_Rep_cfun2])
done

lemma compact_upper_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs \<union>\<sharp> ys)"
by (auto dest!: upper_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma upper_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<sharp>"
  assumes insert: "\<And>x ys. \<lbrakk>P {x}\<sharp>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<sharp> \<union>\<sharp> ys)"
  shows "P (xs::'a upper_pd)"
apply (induct xs rule: upper_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: upper_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: upper_unit_Rep_compact_basis [symmetric]
                  upper_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma upper_pd_induct
  [case_names adm upper_unit upper_plus, induct type: upper_pd]:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<sharp>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs \<union>\<sharp> ys)"
  shows "P (xs::'a upper_pd)"
apply (induct xs rule: upper_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct)
apply (simp only: upper_unit_Rep_compact_basis [symmetric] unit)
apply (simp only: upper_plus_principal [symmetric] plus)
done


subsection {* Monadic bind *}

definition
  upper_bind_basis ::
  "'a pd_basis \<Rightarrow> ('a \<rightarrow> 'b upper_pd) \<rightarrow> 'b upper_pd" where
  "upper_bind_basis = fold_pd
    (\<lambda>a. \<Lambda> f. f\<cdot>(Rep_compact_basis a))
    (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<sharp> y\<cdot>f)"

lemma ACI_upper_bind:
  "class.ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<sharp> y\<cdot>f)"
apply unfold_locales
apply (simp add: upper_plus_assoc)
apply (simp add: upper_plus_commute)
apply (simp add: eta_cfun)
done

lemma upper_bind_basis_simps [simp]:
  "upper_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "upper_bind_basis (PDPlus t u) =
    (\<Lambda> f. upper_bind_basis t\<cdot>f \<union>\<sharp> upper_bind_basis u\<cdot>f)"
unfolding upper_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_upper_bind])
apply (rule fold_pd_PDPlus [OF ACI_upper_bind])
done

lemma upper_bind_basis_mono:
  "t \<le>\<sharp> u \<Longrightarrow> upper_bind_basis t \<sqsubseteq> upper_bind_basis u"
unfolding cfun_below_iff
apply (erule upper_le_induct, safe)
apply (simp add: monofun_cfun)
apply (simp add: below_trans [OF upper_plus_below1])
apply simp
done

definition
  upper_bind :: "'a upper_pd \<rightarrow> ('a \<rightarrow> 'b upper_pd) \<rightarrow> 'b upper_pd" where
  "upper_bind = upper_pd.extension upper_bind_basis"

syntax
  "_upper_bind" :: "[logic, logic, logic] \<Rightarrow> logic"
    ("(3\<Union>\<sharp>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<Union>\<sharp>x\<in>xs. e" == "CONST upper_bind\<cdot>xs\<cdot>(\<Lambda> x. e)"

lemma upper_bind_principal [simp]:
  "upper_bind\<cdot>(upper_principal t) = upper_bind_basis t"
unfolding upper_bind_def
apply (rule upper_pd.extension_principal)
apply (erule upper_bind_basis_mono)
done

lemma upper_bind_unit [simp]:
  "upper_bind\<cdot>{x}\<sharp>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma upper_bind_plus [simp]:
  "upper_bind\<cdot>(xs \<union>\<sharp> ys)\<cdot>f = upper_bind\<cdot>xs\<cdot>f \<union>\<sharp> upper_bind\<cdot>ys\<cdot>f"
by (induct xs rule: upper_pd.principal_induct, simp,
    induct ys rule: upper_pd.principal_induct, simp, simp)

lemma upper_bind_strict [simp]: "upper_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding upper_unit_strict [symmetric] by (rule upper_bind_unit)

lemma upper_bind_bind:
  "upper_bind\<cdot>(upper_bind\<cdot>xs\<cdot>f)\<cdot>g = upper_bind\<cdot>xs\<cdot>(\<Lambda> x. upper_bind\<cdot>(f\<cdot>x)\<cdot>g)"
by (induct xs, simp_all)


subsection {* Map *}

definition
  upper_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a upper_pd \<rightarrow> 'b upper_pd" where
  "upper_map = (\<Lambda> f xs. upper_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<sharp>))"

lemma upper_map_unit [simp]:
  "upper_map\<cdot>f\<cdot>{x}\<sharp> = {f\<cdot>x}\<sharp>"
unfolding upper_map_def by simp

lemma upper_map_plus [simp]:
  "upper_map\<cdot>f\<cdot>(xs \<union>\<sharp> ys) = upper_map\<cdot>f\<cdot>xs \<union>\<sharp> upper_map\<cdot>f\<cdot>ys"
unfolding upper_map_def by simp

lemma upper_map_bottom [simp]: "upper_map\<cdot>f\<cdot>\<bottom> = {f\<cdot>\<bottom>}\<sharp>"
unfolding upper_map_def by simp

lemma upper_map_ident: "upper_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: upper_pd_induct, simp_all)

lemma upper_map_ID: "upper_map\<cdot>ID = ID"
by (simp add: cfun_eq_iff ID_def upper_map_ident)

lemma upper_map_map:
  "upper_map\<cdot>f\<cdot>(upper_map\<cdot>g\<cdot>xs) = upper_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: upper_pd_induct, simp_all)

lemma upper_bind_map:
  "upper_bind\<cdot>(upper_map\<cdot>f\<cdot>xs)\<cdot>g = upper_bind\<cdot>xs\<cdot>(\<Lambda> x. g\<cdot>(f\<cdot>x))"
by (simp add: upper_map_def upper_bind_bind)

lemma upper_map_bind:
  "upper_map\<cdot>f\<cdot>(upper_bind\<cdot>xs\<cdot>g) = upper_bind\<cdot>xs\<cdot>(\<Lambda> x. upper_map\<cdot>f\<cdot>(g\<cdot>x))"
by (simp add: upper_map_def upper_bind_bind)

lemma ep_pair_upper_map: "ep_pair e p \<Longrightarrow> ep_pair (upper_map\<cdot>e) (upper_map\<cdot>p)"
apply default
apply (induct_tac x rule: upper_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: upper_pd_induct)
apply (simp_all add: ep_pair.e_p_below monofun_cfun del: upper_below_plus_iff)
done

lemma deflation_upper_map: "deflation d \<Longrightarrow> deflation (upper_map\<cdot>d)"
apply default
apply (induct_tac x rule: upper_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: upper_pd_induct)
apply (simp_all add: deflation.below monofun_cfun del: upper_below_plus_iff)
done

(* FIXME: long proof! *)
lemma finite_deflation_upper_map:
  assumes "finite_deflation d" shows "finite_deflation (upper_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (upper_map\<cdot>d)" by (rule deflation_upper_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence *: "finite (upper_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite (range (\<lambda>xs. upper_map\<cdot>d\<cdot>xs))"
    apply (rule rev_finite_subset)
    apply clarsimp
    apply (induct_tac xs rule: upper_pd.principal_induct)
    apply (simp add: adm_mem_finite *)
    apply (rename_tac t, induct_tac t rule: pd_basis_induct)
    apply (simp only: upper_unit_Rep_compact_basis [symmetric] upper_map_unit)
    apply simp
    apply (subgoal_tac "\<exists>b. d\<cdot>(Rep_compact_basis a) = Rep_compact_basis b")
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDUnit)
    apply (rule range_eqI)
    apply (erule sym)
    apply (rule exI)
    apply (rule Abs_compact_basis_inverse [symmetric])
    apply (simp add: d.compact)
    apply (simp only: upper_plus_principal [symmetric] upper_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  thus "finite {xs. upper_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

subsection {* Upper powerdomain is bifinite *}

lemma approx_chain_upper_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. upper_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP upper_map_ID finite_deflation_upper_map)

instance upper_pd :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> 'a upper_pd \<rightarrow> 'a upper_pd). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_upper_map)
qed

subsection {* Join *}

definition
  upper_join :: "'a upper_pd upper_pd \<rightarrow> 'a upper_pd" where
  "upper_join = (\<Lambda> xss. upper_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma upper_join_unit [simp]:
  "upper_join\<cdot>{xs}\<sharp> = xs"
unfolding upper_join_def by simp

lemma upper_join_plus [simp]:
  "upper_join\<cdot>(xss \<union>\<sharp> yss) = upper_join\<cdot>xss \<union>\<sharp> upper_join\<cdot>yss"
unfolding upper_join_def by simp

lemma upper_join_bottom [simp]: "upper_join\<cdot>\<bottom> = \<bottom>"
unfolding upper_join_def by simp

lemma upper_join_map_unit:
  "upper_join\<cdot>(upper_map\<cdot>upper_unit\<cdot>xs) = xs"
by (induct xs rule: upper_pd_induct, simp_all)

lemma upper_join_map_join:
  "upper_join\<cdot>(upper_map\<cdot>upper_join\<cdot>xsss) = upper_join\<cdot>(upper_join\<cdot>xsss)"
by (induct xsss rule: upper_pd_induct, simp_all)

lemma upper_join_map_map:
  "upper_join\<cdot>(upper_map\<cdot>(upper_map\<cdot>f)\<cdot>xss) =
   upper_map\<cdot>f\<cdot>(upper_join\<cdot>xss)"
by (induct xss rule: upper_pd_induct, simp_all)

end
