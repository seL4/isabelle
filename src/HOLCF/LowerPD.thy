(*  Title:      HOLCF/LowerPD.thy
    Author:     Brian Huffman
*)

header {* Lower powerdomain *}

theory LowerPD
imports CompactBasis
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
  "(PDUnit a \<le>\<flat> PDUnit b) = a \<sqsubseteq> b"
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

typedef (open) 'a lower_pd =
  "{S::'a pd_basis set. lower_le.ideal S}"
by (fast intro: lower_le.ideal_principal)

instantiation lower_pd :: (sfp) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_lower_pd x \<subseteq> Rep_lower_pd y"

instance ..
end

instance lower_pd :: (sfp) po
by (rule lower_le.typedef_ideal_po
    [OF type_definition_lower_pd below_lower_pd_def])

instance lower_pd :: (sfp) cpo
by (rule lower_le.typedef_ideal_cpo
    [OF type_definition_lower_pd below_lower_pd_def])

lemma Rep_lower_pd_lub:
  "chain Y \<Longrightarrow> Rep_lower_pd (\<Squnion>i. Y i) = (\<Union>i. Rep_lower_pd (Y i))"
by (rule lower_le.typedef_ideal_rep_contlub
    [OF type_definition_lower_pd below_lower_pd_def])

lemma ideal_Rep_lower_pd: "lower_le.ideal (Rep_lower_pd xs)"
by (rule Rep_lower_pd [unfolded mem_Collect_eq])

definition
  lower_principal :: "'a pd_basis \<Rightarrow> 'a lower_pd" where
  "lower_principal t = Abs_lower_pd {u. u \<le>\<flat> t}"

lemma Rep_lower_principal:
  "Rep_lower_pd (lower_principal t) = {u. u \<le>\<flat> t}"
unfolding lower_principal_def
by (simp add: Abs_lower_pd_inverse lower_le.ideal_principal)

interpretation lower_pd:
  ideal_completion lower_le lower_principal Rep_lower_pd
apply unfold_locales
apply (rule ideal_Rep_lower_pd)
apply (erule Rep_lower_pd_lub)
apply (rule Rep_lower_principal)
apply (simp only: below_lower_pd_def)
apply (rule pd_basis_countable)
done

text {* Lower powerdomain is pointed *}

lemma lower_pd_minimal: "lower_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: lower_pd.principal_induct, simp, simp)

instance lower_pd :: (sfp) pcpo
by intro_classes (fast intro: lower_pd_minimal)

lemma inst_lower_pd_pcpo: "\<bottom> = lower_principal (PDUnit compact_bot)"
by (rule lower_pd_minimal [THEN UU_I, symmetric])


subsection {* Monadic unit and plus *}

definition
  lower_unit :: "'a \<rightarrow> 'a lower_pd" where
  "lower_unit = compact_basis.basis_fun (\<lambda>a. lower_principal (PDUnit a))"

definition
  lower_plus :: "'a lower_pd \<rightarrow> 'a lower_pd \<rightarrow> 'a lower_pd" where
  "lower_plus = lower_pd.basis_fun (\<lambda>t. lower_pd.basis_fun (\<lambda>u.
      lower_principal (PDPlus t u)))"

abbreviation
  lower_add :: "'a lower_pd \<Rightarrow> 'a lower_pd \<Rightarrow> 'a lower_pd"
    (infixl "+\<flat>" 65) where
  "xs +\<flat> ys == lower_plus\<cdot>xs\<cdot>ys"

syntax
  "_lower_pd" :: "args \<Rightarrow> 'a lower_pd" ("{_}\<flat>")

translations
  "{x,xs}\<flat>" == "{x}\<flat> +\<flat> {xs}\<flat>"
  "{x}\<flat>" == "CONST lower_unit\<cdot>x"

lemma lower_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<flat> = lower_principal (PDUnit a)"
unfolding lower_unit_def
by (simp add: compact_basis.basis_fun_principal PDUnit_lower_mono)

lemma lower_plus_principal [simp]:
  "lower_principal t +\<flat> lower_principal u = lower_principal (PDPlus t u)"
unfolding lower_plus_def
by (simp add: lower_pd.basis_fun_principal
    lower_pd.basis_fun_mono PDPlus_lower_mono)

interpretation lower_add: semilattice lower_add proof
  fix xs ys zs :: "'a lower_pd"
  show "(xs +\<flat> ys) +\<flat> zs = xs +\<flat> (ys +\<flat> zs)"
    apply (induct xs ys arbitrary: zs rule: lower_pd.principal_induct2, simp, simp)
    apply (rule_tac x=zs in lower_pd.principal_induct, simp)
    apply (simp add: PDPlus_assoc)
    done
  show "xs +\<flat> ys = ys +\<flat> xs"
    apply (induct xs ys rule: lower_pd.principal_induct2, simp, simp)
    apply (simp add: PDPlus_commute)
    done
  show "xs +\<flat> xs = xs"
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

lemma lower_plus_below1: "xs \<sqsubseteq> xs +\<flat> ys"
apply (induct xs ys rule: lower_pd.principal_induct2, simp, simp)
apply (simp add: PDPlus_lower_le)
done

lemma lower_plus_below2: "ys \<sqsubseteq> xs +\<flat> ys"
by (subst lower_plus_commute, rule lower_plus_below1)

lemma lower_plus_least: "\<lbrakk>xs \<sqsubseteq> zs; ys \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs +\<flat> ys \<sqsubseteq> zs"
apply (subst lower_plus_absorb [of zs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma lower_plus_below_iff:
  "xs +\<flat> ys \<sqsubseteq> zs \<longleftrightarrow> xs \<sqsubseteq> zs \<and> ys \<sqsubseteq> zs"
apply safe
apply (erule below_trans [OF lower_plus_below1])
apply (erule below_trans [OF lower_plus_below2])
apply (erule (1) lower_plus_least)
done

lemma lower_unit_below_plus_iff:
  "{x}\<flat> \<sqsubseteq> ys +\<flat> zs \<longleftrightarrow> {x}\<flat> \<sqsubseteq> ys \<or> {x}\<flat> \<sqsubseteq> zs"
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

lemma lower_unit_strict_iff [simp]: "{x}\<flat> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding lower_unit_strict [symmetric] by (rule lower_unit_eq_iff)

lemma lower_plus_strict_iff [simp]:
  "xs +\<flat> ys = \<bottom> \<longleftrightarrow> xs = \<bottom> \<and> ys = \<bottom>"
apply safe
apply (rule UU_I, erule subst, rule lower_plus_below1)
apply (rule UU_I, erule subst, rule lower_plus_below2)
apply (rule lower_plus_absorb)
done

lemma lower_plus_strict1 [simp]: "\<bottom> +\<flat> ys = ys"
apply (rule below_antisym [OF _ lower_plus_below2])
apply (simp add: lower_plus_least)
done

lemma lower_plus_strict2 [simp]: "xs +\<flat> \<bottom> = xs"
apply (rule below_antisym [OF _ lower_plus_below1])
apply (simp add: lower_plus_least)
done

lemma compact_lower_unit: "compact x \<Longrightarrow> compact {x}\<flat>"
by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_lower_unit_iff [simp]: "compact {x}\<flat> \<longleftrightarrow> compact x"
apply (safe elim!: compact_lower_unit)
apply (simp only: compact_def lower_unit_below_iff [symmetric])
apply (erule adm_subst [OF cont_Rep_CFun2])
done

lemma compact_lower_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs +\<flat> ys)"
by (auto dest!: lower_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma lower_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<flat>"
  assumes insert:
    "\<And>x ys. \<lbrakk>P {x}\<flat>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<flat> +\<flat> ys)"
  shows "P (xs::'a lower_pd)"
apply (induct xs rule: lower_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: lower_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: lower_unit_Rep_compact_basis [symmetric]
                  lower_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma lower_pd_induct:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<flat>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs +\<flat> ys)"
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
    (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<flat> y\<cdot>f)"

lemma ACI_lower_bind:
  "class.ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<flat> y\<cdot>f)"
apply unfold_locales
apply (simp add: lower_plus_assoc)
apply (simp add: lower_plus_commute)
apply (simp add: eta_cfun)
done

lemma lower_bind_basis_simps [simp]:
  "lower_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "lower_bind_basis (PDPlus t u) =
    (\<Lambda> f. lower_bind_basis t\<cdot>f +\<flat> lower_bind_basis u\<cdot>f)"
unfolding lower_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_lower_bind])
apply (rule fold_pd_PDPlus [OF ACI_lower_bind])
done

lemma lower_bind_basis_mono:
  "t \<le>\<flat> u \<Longrightarrow> lower_bind_basis t \<sqsubseteq> lower_bind_basis u"
unfolding expand_cfun_below
apply (erule lower_le_induct, safe)
apply (simp add: monofun_cfun)
apply (simp add: rev_below_trans [OF lower_plus_below1])
apply (simp add: lower_plus_below_iff)
done

definition
  lower_bind :: "'a lower_pd \<rightarrow> ('a \<rightarrow> 'b lower_pd) \<rightarrow> 'b lower_pd" where
  "lower_bind = lower_pd.basis_fun lower_bind_basis"

lemma lower_bind_principal [simp]:
  "lower_bind\<cdot>(lower_principal t) = lower_bind_basis t"
unfolding lower_bind_def
apply (rule lower_pd.basis_fun_principal)
apply (erule lower_bind_basis_mono)
done

lemma lower_bind_unit [simp]:
  "lower_bind\<cdot>{x}\<flat>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma lower_bind_plus [simp]:
  "lower_bind\<cdot>(xs +\<flat> ys)\<cdot>f = lower_bind\<cdot>xs\<cdot>f +\<flat> lower_bind\<cdot>ys\<cdot>f"
by (induct xs ys rule: lower_pd.principal_induct2, simp, simp, simp)

lemma lower_bind_strict [simp]: "lower_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding lower_unit_strict [symmetric] by (rule lower_bind_unit)


subsection {* Map *}

definition
  lower_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a lower_pd \<rightarrow> 'b lower_pd" where
  "lower_map = (\<Lambda> f xs. lower_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<flat>))"

lemma lower_map_unit [simp]:
  "lower_map\<cdot>f\<cdot>{x}\<flat> = {f\<cdot>x}\<flat>"
unfolding lower_map_def by simp

lemma lower_map_plus [simp]:
  "lower_map\<cdot>f\<cdot>(xs +\<flat> ys) = lower_map\<cdot>f\<cdot>xs +\<flat> lower_map\<cdot>f\<cdot>ys"
unfolding lower_map_def by simp

lemma lower_map_ident: "lower_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma lower_map_ID: "lower_map\<cdot>ID = ID"
by (simp add: expand_cfun_eq ID_def lower_map_ident)

lemma lower_map_map:
  "lower_map\<cdot>f\<cdot>(lower_map\<cdot>g\<cdot>xs) = lower_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma ep_pair_lower_map: "ep_pair e p \<Longrightarrow> ep_pair (lower_map\<cdot>e) (lower_map\<cdot>p)"
apply default
apply (induct_tac x rule: lower_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: lower_pd_induct)
apply (simp_all add: ep_pair.e_p_below monofun_cfun)
done

lemma deflation_lower_map: "deflation d \<Longrightarrow> deflation (lower_map\<cdot>d)"
apply default
apply (induct_tac x rule: lower_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: lower_pd_induct)
apply (simp_all add: deflation.below monofun_cfun)
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

subsection {* Lower powerdomain is an SFP domain *}

definition
  lower_approx :: "nat \<Rightarrow> udom lower_pd \<rightarrow> udom lower_pd"
where
  "lower_approx = (\<lambda>i. lower_map\<cdot>(udom_approx i))"

lemma lower_approx: "approx_chain lower_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. lower_approx i)"
    unfolding lower_approx_def by simp
  show "(\<Squnion>i. lower_approx i) = ID"
    unfolding lower_approx_def
    by (simp add: lub_distribs lower_map_ID)
  show "\<And>i. finite_deflation (lower_approx i)"
    unfolding lower_approx_def
    by (intro finite_deflation_lower_map finite_deflation_udom_approx)
qed

definition lower_sfp :: "sfp \<rightarrow> sfp"
where "lower_sfp = sfp_fun1 lower_approx lower_map"

lemma cast_lower_sfp:
  "cast\<cdot>(lower_sfp\<cdot>A) =
    udom_emb lower_approx oo lower_map\<cdot>(cast\<cdot>A) oo udom_prj lower_approx"
unfolding lower_sfp_def
apply (rule cast_sfp_fun1 [OF lower_approx])
apply (erule finite_deflation_lower_map)
done

instantiation lower_pd :: (sfp) sfp
begin

definition
  "emb = udom_emb lower_approx oo lower_map\<cdot>emb"

definition
  "prj = lower_map\<cdot>prj oo udom_prj lower_approx"

definition
  "sfp (t::'a lower_pd itself) = lower_sfp\<cdot>SFP('a)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def
    using ep_pair_udom [OF lower_approx]
    by (intro ep_pair_comp ep_pair_lower_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a lower_pd) = emb oo (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def sfp_lower_pd_def cast_lower_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq lower_map_map)
qed

end

text {* SFP of type constructor = type combinator *}

lemma SFP_lower: "SFP('a lower_pd) = lower_sfp\<cdot>SFP('a)"
by (rule sfp_lower_pd_def)


subsection {* Join *}

definition
  lower_join :: "'a lower_pd lower_pd \<rightarrow> 'a lower_pd" where
  "lower_join = (\<Lambda> xss. lower_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma lower_join_unit [simp]:
  "lower_join\<cdot>{xs}\<flat> = xs"
unfolding lower_join_def by simp

lemma lower_join_plus [simp]:
  "lower_join\<cdot>(xss +\<flat> yss) = lower_join\<cdot>xss +\<flat> lower_join\<cdot>yss"
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
