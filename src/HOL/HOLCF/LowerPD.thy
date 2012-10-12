(*  Title:      HOL/HOLCF/LowerPD.thy
    Author:     Brian Huffman
*)

header {* Lower powerdomain *}

theory LowerPD
imports Compact_Basis
begin

subsection {* Basis preorder *}

definition
  lower_le :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> bool" (infix "\<le>\<flat>" 50) where
  "lower_le = (\<lambda>u v. \<forall>x\<in>Rep_pd_basis u. \<exists>y\<in>Rep_pd_basis v. x \<sqsubseteq> y)"

lemma lower_le_refl [simp]: "t \<le>\<flat> t"
unfolding lower_le_def by fast

lemma lower_le_trans: "\<lbrakk>t \<le>\<flat> u; u \<le>\<flat> v\<rbrakk> \<Longrightarrow> t \<le>\<flat> v"
unfolding lower_le_def
apply (rule ballI)
apply (drule (1) bspec, erule bexE)
apply (drule (1) bspec, erule bexE)
apply (erule rev_bexI)
apply (erule (1) below_trans)
done

interpretation lower_le: preorder lower_le
by (rule preorder.intro, rule lower_le_refl, rule lower_le_trans)

lemma lower_le_minimal [simp]: "PDUnit compact_bot \<le>\<flat> t"
unfolding lower_le_def Rep_PDUnit
by (simp, rule Rep_pd_basis_nonempty [folded ex_in_conv])

lemma PDUnit_lower_mono: "x \<sqsubseteq> y \<Longrightarrow> PDUnit x \<le>\<flat> PDUnit y"
unfolding lower_le_def Rep_PDUnit by fast

lemma PDPlus_lower_mono: "\<lbrakk>s \<le>\<flat> t; u \<le>\<flat> v\<rbrakk> \<Longrightarrow> PDPlus s u \<le>\<flat> PDPlus t v"
unfolding lower_le_def Rep_PDPlus by fast

lemma PDPlus_lower_le: "t \<le>\<flat> PDPlus t u"
unfolding lower_le_def Rep_PDPlus by fast

lemma lower_le_PDUnit_PDUnit_iff [simp]:
  "(PDUnit a \<le>\<flat> PDUnit b) = (a \<sqsubseteq> b)"
unfolding lower_le_def Rep_PDUnit by fast

lemma lower_le_PDUnit_PDPlus_iff:
  "(PDUnit a \<le>\<flat> PDPlus t u) = (PDUnit a \<le>\<flat> t \<or> PDUnit a \<le>\<flat> u)"
unfolding lower_le_def Rep_PDPlus Rep_PDUnit by fast

lemma lower_le_PDPlus_iff: "(PDPlus t u \<le>\<flat> v) = (t \<le>\<flat> v \<and> u \<le>\<flat> v)"
unfolding lower_le_def Rep_PDPlus by fast

lemma lower_le_induct [induct set: lower_le]:
  assumes le: "t \<le>\<flat> u"
  assumes 1: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> P (PDUnit a) (PDUnit b)"
  assumes 2: "\<And>t u a. P (PDUnit a) t \<Longrightarrow> P (PDUnit a) (PDPlus t u)"
  assumes 3: "\<And>t u v. \<lbrakk>P t v; P u v\<rbrakk> \<Longrightarrow> P (PDPlus t u) v"
  shows "P t u"
using le
apply (induct t arbitrary: u rule: pd_basis_induct)
apply (erule rev_mp)
apply (induct_tac u rule: pd_basis_induct)
apply (simp add: 1)
apply (simp add: lower_le_PDUnit_PDPlus_iff)
apply (simp add: 2)
apply (subst PDPlus_commute)
apply (simp add: 2)
apply (simp add: lower_le_PDPlus_iff 3)
done


subsection {* Type definition *}

typedef 'a lower_pd =
  "{S::'a pd_basis set. lower_le.ideal S}"
by (rule lower_le.ex_ideal)

type_notation (xsymbols) lower_pd ("('(_')\<flat>)")

instantiation lower_pd :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_lower_pd x \<subseteq> Rep_lower_pd y"

instance ..
end

instance lower_pd :: (bifinite) po
using type_definition_lower_pd below_lower_pd_def
by (rule lower_le.typedef_ideal_po)

instance lower_pd :: (bifinite) cpo
using type_definition_lower_pd below_lower_pd_def
by (rule lower_le.typedef_ideal_cpo)

definition
  lower_principal :: "'a pd_basis \<Rightarrow> 'a lower_pd" where
  "lower_principal t = Abs_lower_pd {u. u \<le>\<flat> t}"

interpretation lower_pd:
  ideal_completion lower_le lower_principal Rep_lower_pd
using type_definition_lower_pd below_lower_pd_def
using lower_principal_def pd_basis_countable
by (rule lower_le.typedef_ideal_completion)

text {* Lower powerdomain is pointed *}

lemma lower_pd_minimal: "lower_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: lower_pd.principal_induct, simp, simp)

instance lower_pd :: (bifinite) pcpo
by intro_classes (fast intro: lower_pd_minimal)

lemma inst_lower_pd_pcpo: "\<bottom> = lower_principal (PDUnit compact_bot)"
by (rule lower_pd_minimal [THEN bottomI, symmetric])


subsection {* Monadic unit and plus *}

definition
  lower_unit :: "'a \<rightarrow> 'a lower_pd" where
  "lower_unit = compact_basis.extension (\<lambda>a. lower_principal (PDUnit a))"

definition
  lower_plus :: "'a lower_pd \<rightarrow> 'a lower_pd \<rightarrow> 'a lower_pd" where
  "lower_plus = lower_pd.extension (\<lambda>t. lower_pd.extension (\<lambda>u.
      lower_principal (PDPlus t u)))"

abbreviation
  lower_add :: "'a lower_pd \<Rightarrow> 'a lower_pd \<Rightarrow> 'a lower_pd"
    (infixl "\<union>\<flat>" 65) where
  "xs \<union>\<flat> ys == lower_plus\<cdot>xs\<cdot>ys"

syntax
  "_lower_pd" :: "args \<Rightarrow> logic" ("{_}\<flat>")

translations
  "{x,xs}\<flat>" == "{x}\<flat> \<union>\<flat> {xs}\<flat>"
  "{x}\<flat>" == "CONST lower_unit\<cdot>x"

lemma lower_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<flat> = lower_principal (PDUnit a)"
unfolding lower_unit_def
by (simp add: compact_basis.extension_principal PDUnit_lower_mono)

lemma lower_plus_principal [simp]:
  "lower_principal t \<union>\<flat> lower_principal u = lower_principal (PDPlus t u)"
unfolding lower_plus_def
by (simp add: lower_pd.extension_principal
    lower_pd.extension_mono PDPlus_lower_mono)

interpretation lower_add: semilattice lower_add proof
  fix xs ys zs :: "'a lower_pd"
  show "(xs \<union>\<flat> ys) \<union>\<flat> zs = xs \<union>\<flat> (ys \<union>\<flat> zs)"
    apply (induct xs rule: lower_pd.principal_induct, simp)
    apply (induct ys rule: lower_pd.principal_induct, simp)
    apply (induct zs rule: lower_pd.principal_induct, simp)
    apply (simp add: PDPlus_assoc)
    done
  show "xs \<union>\<flat> ys = ys \<union>\<flat> xs"
    apply (induct xs rule: lower_pd.principal_induct, simp)
    apply (induct ys rule: lower_pd.principal_induct, simp)
    apply (simp add: PDPlus_commute)
    done
  show "xs \<union>\<flat> xs = xs"
    apply (induct xs rule: lower_pd.principal_induct, simp)
    apply (simp add: PDPlus_absorb)
    done
qed

lemmas lower_plus_assoc = lower_add.assoc
lemmas lower_plus_commute = lower_add.commute
lemmas lower_plus_absorb = lower_add.idem
lemmas lower_plus_left_commute = lower_add.left_commute
lemmas lower_plus_left_absorb = lower_add.left_idem

text {* Useful for @{text "simp add: lower_plus_ac"} *}
lemmas lower_plus_ac =
  lower_plus_assoc lower_plus_commute lower_plus_left_commute

text {* Useful for @{text "simp only: lower_plus_aci"} *}
lemmas lower_plus_aci =
  lower_plus_ac lower_plus_absorb lower_plus_left_absorb

lemma lower_plus_below1: "xs \<sqsubseteq> xs \<union>\<flat> ys"
apply (induct xs rule: lower_pd.principal_induct, simp)
apply (induct ys rule: lower_pd.principal_induct, simp)
apply (simp add: PDPlus_lower_le)
done

lemma lower_plus_below2: "ys \<sqsubseteq> xs \<union>\<flat> ys"
by (subst lower_plus_commute, rule lower_plus_below1)

lemma lower_plus_least: "\<lbrakk>xs \<sqsubseteq> zs; ys \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs \<union>\<flat> ys \<sqsubseteq> zs"
apply (subst lower_plus_absorb [of zs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma lower_plus_below_iff [simp]:
  "xs \<union>\<flat> ys \<sqsubseteq> zs \<longleftrightarrow> xs \<sqsubseteq> zs \<and> ys \<sqsubseteq> zs"
apply safe
apply (erule below_trans [OF lower_plus_below1])
apply (erule below_trans [OF lower_plus_below2])
apply (erule (1) lower_plus_least)
done

lemma lower_unit_below_plus_iff [simp]:
  "{x}\<flat> \<sqsubseteq> ys \<union>\<flat> zs \<longleftrightarrow> {x}\<flat> \<sqsubseteq> ys \<or> {x}\<flat> \<sqsubseteq> zs"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (induct ys rule: lower_pd.principal_induct, simp)
apply (induct zs rule: lower_pd.principal_induct, simp)
apply (simp add: lower_le_PDUnit_PDPlus_iff)
done

lemma lower_unit_below_iff [simp]: "{x}\<flat> \<sqsubseteq> {y}\<flat> \<longleftrightarrow> x \<sqsubseteq> y"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (induct y rule: compact_basis.principal_induct, simp)
apply simp
done

lemmas lower_pd_below_simps =
  lower_unit_below_iff
  lower_plus_below_iff
  lower_unit_below_plus_iff

lemma lower_unit_eq_iff [simp]: "{x}\<flat> = {y}\<flat> \<longleftrightarrow> x = y"
by (simp add: po_eq_conv)

lemma lower_unit_strict [simp]: "{\<bottom>}\<flat> = \<bottom>"
using lower_unit_Rep_compact_basis [of compact_bot]
by (simp add: inst_lower_pd_pcpo)

lemma lower_unit_bottom_iff [simp]: "{x}\<flat> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding lower_unit_strict [symmetric] by (rule lower_unit_eq_iff)

lemma lower_plus_bottom_iff [simp]:
  "xs \<union>\<flat> ys = \<bottom> \<longleftrightarrow> xs = \<bottom> \<and> ys = \<bottom>"
apply safe
apply (rule bottomI, erule subst, rule lower_plus_below1)
apply (rule bottomI, erule subst, rule lower_plus_below2)
apply (rule lower_plus_absorb)
done

lemma lower_plus_strict1 [simp]: "\<bottom> \<union>\<flat> ys = ys"
apply (rule below_antisym [OF _ lower_plus_below2])
apply (simp add: lower_plus_least)
done

lemma lower_plus_strict2 [simp]: "xs \<union>\<flat> \<bottom> = xs"
apply (rule below_antisym [OF _ lower_plus_below1])
apply (simp add: lower_plus_least)
done

lemma compact_lower_unit: "compact x \<Longrightarrow> compact {x}\<flat>"
by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_lower_unit_iff [simp]: "compact {x}\<flat> \<longleftrightarrow> compact x"
apply (safe elim!: compact_lower_unit)
apply (simp only: compact_def lower_unit_below_iff [symmetric])
apply (erule adm_subst [OF cont_Rep_cfun2])
done

lemma compact_lower_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs \<union>\<flat> ys)"
by (auto dest!: lower_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma lower_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<flat>"
  assumes insert:
    "\<And>x ys. \<lbrakk>P {x}\<flat>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<flat> \<union>\<flat> ys)"
  shows "P (xs::'a lower_pd)"
apply (induct xs rule: lower_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: lower_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: lower_unit_Rep_compact_basis [symmetric]
                  lower_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma lower_pd_induct
  [case_names adm lower_unit lower_plus, induct type: lower_pd]:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<flat>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs \<union>\<flat> ys)"
  shows "P (xs::'a lower_pd)"
apply (induct xs rule: lower_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct)
apply (simp only: lower_unit_Rep_compact_basis [symmetric] unit)
apply (simp only: lower_plus_principal [symmetric] plus)
done


subsection {* Monadic bind *}

definition
  lower_bind_basis ::
  "'a pd_basis \<Rightarrow> ('a \<rightarrow> 'b lower_pd) \<rightarrow> 'b lower_pd" where
  "lower_bind_basis = fold_pd
    (\<lambda>a. \<Lambda> f. f\<cdot>(Rep_compact_basis a))
    (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<flat> y\<cdot>f)"

lemma ACI_lower_bind:
  "class.ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<flat> y\<cdot>f)"
apply unfold_locales
apply (simp add: lower_plus_assoc)
apply (simp add: lower_plus_commute)
apply (simp add: eta_cfun)
done

lemma lower_bind_basis_simps [simp]:
  "lower_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "lower_bind_basis (PDPlus t u) =
    (\<Lambda> f. lower_bind_basis t\<cdot>f \<union>\<flat> lower_bind_basis u\<cdot>f)"
unfolding lower_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_lower_bind])
apply (rule fold_pd_PDPlus [OF ACI_lower_bind])
done

lemma lower_bind_basis_mono:
  "t \<le>\<flat> u \<Longrightarrow> lower_bind_basis t \<sqsubseteq> lower_bind_basis u"
unfolding cfun_below_iff
apply (erule lower_le_induct, safe)
apply (simp add: monofun_cfun)
apply (simp add: rev_below_trans [OF lower_plus_below1])
apply simp
done

definition
  lower_bind :: "'a lower_pd \<rightarrow> ('a \<rightarrow> 'b lower_pd) \<rightarrow> 'b lower_pd" where
  "lower_bind = lower_pd.extension lower_bind_basis"

syntax
  "_lower_bind" :: "[logic, logic, logic] \<Rightarrow> logic"
    ("(3\<Union>\<flat>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<Union>\<flat>x\<in>xs. e" == "CONST lower_bind\<cdot>xs\<cdot>(\<Lambda> x. e)"

lemma lower_bind_principal [simp]:
  "lower_bind\<cdot>(lower_principal t) = lower_bind_basis t"
unfolding lower_bind_def
apply (rule lower_pd.extension_principal)
apply (erule lower_bind_basis_mono)
done

lemma lower_bind_unit [simp]:
  "lower_bind\<cdot>{x}\<flat>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma lower_bind_plus [simp]:
  "lower_bind\<cdot>(xs \<union>\<flat> ys)\<cdot>f = lower_bind\<cdot>xs\<cdot>f \<union>\<flat> lower_bind\<cdot>ys\<cdot>f"
by (induct xs rule: lower_pd.principal_induct, simp,
    induct ys rule: lower_pd.principal_induct, simp, simp)

lemma lower_bind_strict [simp]: "lower_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding lower_unit_strict [symmetric] by (rule lower_bind_unit)

lemma lower_bind_bind:
  "lower_bind\<cdot>(lower_bind\<cdot>xs\<cdot>f)\<cdot>g = lower_bind\<cdot>xs\<cdot>(\<Lambda> x. lower_bind\<cdot>(f\<cdot>x)\<cdot>g)"
by (induct xs, simp_all)


subsection {* Map *}

definition
  lower_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a lower_pd \<rightarrow> 'b lower_pd" where
  "lower_map = (\<Lambda> f xs. lower_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<flat>))"

lemma lower_map_unit [simp]:
  "lower_map\<cdot>f\<cdot>{x}\<flat> = {f\<cdot>x}\<flat>"
unfolding lower_map_def by simp

lemma lower_map_plus [simp]:
  "lower_map\<cdot>f\<cdot>(xs \<union>\<flat> ys) = lower_map\<cdot>f\<cdot>xs \<union>\<flat> lower_map\<cdot>f\<cdot>ys"
unfolding lower_map_def by simp

lemma lower_map_bottom [simp]: "lower_map\<cdot>f\<cdot>\<bottom> = {f\<cdot>\<bottom>}\<flat>"
unfolding lower_map_def by simp

lemma lower_map_ident: "lower_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma lower_map_ID: "lower_map\<cdot>ID = ID"
by (simp add: cfun_eq_iff ID_def lower_map_ident)

lemma lower_map_map:
  "lower_map\<cdot>f\<cdot>(lower_map\<cdot>g\<cdot>xs) = lower_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma lower_bind_map:
  "lower_bind\<cdot>(lower_map\<cdot>f\<cdot>xs)\<cdot>g = lower_bind\<cdot>xs\<cdot>(\<Lambda> x. g\<cdot>(f\<cdot>x))"
by (simp add: lower_map_def lower_bind_bind)

lemma lower_map_bind:
  "lower_map\<cdot>f\<cdot>(lower_bind\<cdot>xs\<cdot>g) = lower_bind\<cdot>xs\<cdot>(\<Lambda> x. lower_map\<cdot>f\<cdot>(g\<cdot>x))"
by (simp add: lower_map_def lower_bind_bind)

lemma ep_pair_lower_map: "ep_pair e p \<Longrightarrow> ep_pair (lower_map\<cdot>e) (lower_map\<cdot>p)"
apply default
apply (induct_tac x rule: lower_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: lower_pd_induct)
apply (simp_all add: ep_pair.e_p_below monofun_cfun del: lower_plus_below_iff)
done

lemma deflation_lower_map: "deflation d \<Longrightarrow> deflation (lower_map\<cdot>d)"
apply default
apply (induct_tac x rule: lower_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: lower_pd_induct)
apply (simp_all add: deflation.below monofun_cfun del: lower_plus_below_iff)
done

(* FIXME: long proof! *)
lemma finite_deflation_lower_map:
  assumes "finite_deflation d" shows "finite_deflation (lower_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (lower_map\<cdot>d)" by (rule deflation_lower_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence *: "finite (lower_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite (range (\<lambda>xs. lower_map\<cdot>d\<cdot>xs))"
    apply (rule rev_finite_subset)
    apply clarsimp
    apply (induct_tac xs rule: lower_pd.principal_induct)
    apply (simp add: adm_mem_finite *)
    apply (rename_tac t, induct_tac t rule: pd_basis_induct)
    apply (simp only: lower_unit_Rep_compact_basis [symmetric] lower_map_unit)
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
    apply (simp only: lower_plus_principal [symmetric] lower_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  thus "finite {xs. lower_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

subsection {* Lower powerdomain is bifinite *}

lemma approx_chain_lower_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. lower_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP lower_map_ID finite_deflation_lower_map)

instance lower_pd :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> 'a lower_pd \<rightarrow> 'a lower_pd). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_lower_map)
qed

subsection {* Join *}

definition
  lower_join :: "'a lower_pd lower_pd \<rightarrow> 'a lower_pd" where
  "lower_join = (\<Lambda> xss. lower_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma lower_join_unit [simp]:
  "lower_join\<cdot>{xs}\<flat> = xs"
unfolding lower_join_def by simp

lemma lower_join_plus [simp]:
  "lower_join\<cdot>(xss \<union>\<flat> yss) = lower_join\<cdot>xss \<union>\<flat> lower_join\<cdot>yss"
unfolding lower_join_def by simp

lemma lower_join_bottom [simp]: "lower_join\<cdot>\<bottom> = \<bottom>"
unfolding lower_join_def by simp

lemma lower_join_map_unit:
  "lower_join\<cdot>(lower_map\<cdot>lower_unit\<cdot>xs) = xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma lower_join_map_join:
  "lower_join\<cdot>(lower_map\<cdot>lower_join\<cdot>xsss) = lower_join\<cdot>(lower_join\<cdot>xsss)"
by (induct xsss rule: lower_pd_induct, simp_all)

lemma lower_join_map_map:
  "lower_join\<cdot>(lower_map\<cdot>(lower_map\<cdot>f)\<cdot>xss) =
   lower_map\<cdot>f\<cdot>(lower_join\<cdot>xss)"
by (induct xss rule: lower_pd_induct, simp_all)

end
