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
apply (erule (1) trans_less)
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

lemma PDPlus_lower_less: "t \<le>\<flat> PDPlus t u"
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

lemma pd_take_lower_chain:
  "pd_take n t \<le>\<flat> pd_take (Suc n) t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_chain)
apply (simp add: PDPlus_lower_mono)
done

lemma pd_take_lower_le: "pd_take i t \<le>\<flat> t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_less)
apply (simp add: PDPlus_lower_mono)
done

lemma pd_take_lower_mono:
  "t \<le>\<flat> u \<Longrightarrow> pd_take n t \<le>\<flat> pd_take n u"
apply (erule lower_le_induct)
apply (simp add: compact_basis.take_mono)
apply (simp add: lower_le_PDUnit_PDPlus_iff)
apply (simp add: lower_le_PDPlus_iff)
done


subsection {* Type definition *}

typedef (open) 'a lower_pd =
  "{S::'a pd_basis set. lower_le.ideal S}"
by (fast intro: lower_le.ideal_principal)

instantiation lower_pd :: (profinite) sq_ord
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_lower_pd x \<subseteq> Rep_lower_pd y"

instance ..
end

instance lower_pd :: (profinite) po
by (rule lower_le.typedef_ideal_po
    [OF type_definition_lower_pd sq_le_lower_pd_def])

instance lower_pd :: (profinite) cpo
by (rule lower_le.typedef_ideal_cpo
    [OF type_definition_lower_pd sq_le_lower_pd_def])

lemma Rep_lower_pd_lub:
  "chain Y \<Longrightarrow> Rep_lower_pd (\<Squnion>i. Y i) = (\<Union>i. Rep_lower_pd (Y i))"
by (rule lower_le.typedef_ideal_rep_contlub
    [OF type_definition_lower_pd sq_le_lower_pd_def])

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
  ideal_completion lower_le pd_take lower_principal Rep_lower_pd
apply unfold_locales
apply (rule pd_take_lower_le)
apply (rule pd_take_idem)
apply (erule pd_take_lower_mono)
apply (rule pd_take_lower_chain)
apply (rule finite_range_pd_take)
apply (rule pd_take_covers)
apply (rule ideal_Rep_lower_pd)
apply (erule Rep_lower_pd_lub)
apply (rule Rep_lower_principal)
apply (simp only: sq_le_lower_pd_def)
done

text {* Lower powerdomain is pointed *}

lemma lower_pd_minimal: "lower_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: lower_pd.principal_induct, simp, simp)

instance lower_pd :: (bifinite) pcpo
by intro_classes (fast intro: lower_pd_minimal)

lemma inst_lower_pd_pcpo: "\<bottom> = lower_principal (PDUnit compact_bot)"
by (rule lower_pd_minimal [THEN UU_I, symmetric])

text {* Lower powerdomain is profinite *}

instantiation lower_pd :: (profinite) profinite
begin

definition
  approx_lower_pd_def: "approx = lower_pd.completion_approx"

instance
apply (intro_classes, unfold approx_lower_pd_def)
apply (rule lower_pd.chain_completion_approx)
apply (rule lower_pd.lub_completion_approx)
apply (rule lower_pd.completion_approx_idem)
apply (rule lower_pd.finite_fixes_completion_approx)
done

end

instance lower_pd :: (bifinite) bifinite ..

lemma approx_lower_principal [simp]:
  "approx n\<cdot>(lower_principal t) = lower_principal (pd_take n t)"
unfolding approx_lower_pd_def
by (rule lower_pd.completion_approx_principal)

lemma approx_eq_lower_principal:
  "\<exists>t\<in>Rep_lower_pd xs. approx n\<cdot>xs = lower_principal (pd_take n t)"
unfolding approx_lower_pd_def
by (rule lower_pd.completion_approx_eq_principal)


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

lemma approx_lower_unit [simp]:
  "approx n\<cdot>{x}\<flat> = {approx n\<cdot>x}\<flat>"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (simp add: approx_Rep_compact_basis)
done

lemma approx_lower_plus [simp]:
  "approx n\<cdot>(xs +\<flat> ys) = (approx n\<cdot>xs) +\<flat> (approx n\<cdot>ys)"
by (induct xs ys rule: lower_pd.principal_induct2, simp, simp, simp)

lemma lower_plus_assoc: "(xs +\<flat> ys) +\<flat> zs = xs +\<flat> (ys +\<flat> zs)"
apply (induct xs ys arbitrary: zs rule: lower_pd.principal_induct2, simp, simp)
apply (rule_tac x=zs in lower_pd.principal_induct, simp)
apply (simp add: PDPlus_assoc)
done

lemma lower_plus_commute: "xs +\<flat> ys = ys +\<flat> xs"
apply (induct xs ys rule: lower_pd.principal_induct2, simp, simp)
apply (simp add: PDPlus_commute)
done

lemma lower_plus_absorb [simp]: "xs +\<flat> xs = xs"
apply (induct xs rule: lower_pd.principal_induct, simp)
apply (simp add: PDPlus_absorb)
done

lemma lower_plus_left_commute: "xs +\<flat> (ys +\<flat> zs) = ys +\<flat> (xs +\<flat> zs)"
by (rule mk_left_commute [of "op +\<flat>", OF lower_plus_assoc lower_plus_commute])

lemma lower_plus_left_absorb [simp]: "xs +\<flat> (xs +\<flat> ys) = xs +\<flat> ys"
by (simp only: lower_plus_assoc [symmetric] lower_plus_absorb)

text {* Useful for @{text "simp add: lower_plus_ac"} *}
lemmas lower_plus_ac =
  lower_plus_assoc lower_plus_commute lower_plus_left_commute

text {* Useful for @{text "simp only: lower_plus_aci"} *}
lemmas lower_plus_aci =
  lower_plus_ac lower_plus_absorb lower_plus_left_absorb

lemma lower_plus_less1: "xs \<sqsubseteq> xs +\<flat> ys"
apply (induct xs ys rule: lower_pd.principal_induct2, simp, simp)
apply (simp add: PDPlus_lower_less)
done

lemma lower_plus_less2: "ys \<sqsubseteq> xs +\<flat> ys"
by (subst lower_plus_commute, rule lower_plus_less1)

lemma lower_plus_least: "\<lbrakk>xs \<sqsubseteq> zs; ys \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs +\<flat> ys \<sqsubseteq> zs"
apply (subst lower_plus_absorb [of zs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma lower_plus_less_iff:
  "xs +\<flat> ys \<sqsubseteq> zs \<longleftrightarrow> xs \<sqsubseteq> zs \<and> ys \<sqsubseteq> zs"
apply safe
apply (erule trans_less [OF lower_plus_less1])
apply (erule trans_less [OF lower_plus_less2])
apply (erule (1) lower_plus_least)
done

lemma lower_unit_less_plus_iff:
  "{x}\<flat> \<sqsubseteq> ys +\<flat> zs \<longleftrightarrow> {x}\<flat> \<sqsubseteq> ys \<or> {x}\<flat> \<sqsubseteq> zs"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>{x}\<flat> \<sqsubseteq> f\<cdot>ys \<or> f\<cdot>{x}\<flat> \<sqsubseteq> f\<cdot>zs)")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac x="approx i\<cdot>x" in compact_basis.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>ys" in lower_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>zs" in lower_pd.compact_imp_principal, simp)
    apply (clarify, simp add: lower_le_PDUnit_PDPlus_iff)
   apply simp
  apply simp
 apply (erule disjE)
  apply (erule trans_less [OF _ lower_plus_less1])
 apply (erule trans_less [OF _ lower_plus_less2])
done

lemma lower_unit_less_iff [simp]: "{x}\<flat> \<sqsubseteq> {y}\<flat> \<longleftrightarrow> x \<sqsubseteq> y"
 apply (rule iffI)
  apply (rule profinite_less_ext)
  apply (drule_tac f="approx i" in monofun_cfun_arg, simp)
  apply (cut_tac x="approx i\<cdot>x" in compact_basis.compact_imp_principal, simp)
  apply (cut_tac x="approx i\<cdot>y" in compact_basis.compact_imp_principal, simp)
  apply clarsimp
 apply (erule monofun_cfun_arg)
done

lemmas lower_pd_less_simps =
  lower_unit_less_iff
  lower_plus_less_iff
  lower_unit_less_plus_iff

lemma lower_unit_eq_iff [simp]: "{x}\<flat> = {y}\<flat> \<longleftrightarrow> x = y"
by (simp add: po_eq_conv)

lemma lower_unit_strict [simp]: "{\<bottom>}\<flat> = \<bottom>"
unfolding inst_lower_pd_pcpo Rep_compact_bot [symmetric] by simp

lemma lower_unit_strict_iff [simp]: "{x}\<flat> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding lower_unit_strict [symmetric] by (rule lower_unit_eq_iff)

lemma lower_plus_strict_iff [simp]:
  "xs +\<flat> ys = \<bottom> \<longleftrightarrow> xs = \<bottom> \<and> ys = \<bottom>"
apply safe
apply (rule UU_I, erule subst, rule lower_plus_less1)
apply (rule UU_I, erule subst, rule lower_plus_less2)
apply (rule lower_plus_absorb)
done

lemma lower_plus_strict1 [simp]: "\<bottom> +\<flat> ys = ys"
apply (rule antisym_less [OF _ lower_plus_less2])
apply (simp add: lower_plus_least)
done

lemma lower_plus_strict2 [simp]: "xs +\<flat> \<bottom> = xs"
apply (rule antisym_less [OF _ lower_plus_less1])
apply (simp add: lower_plus_least)
done

lemma compact_lower_unit_iff [simp]: "compact {x}\<flat> \<longleftrightarrow> compact x"
unfolding profinite_compact_iff by simp

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
  "ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<flat> y\<cdot>f)"
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
unfolding expand_cfun_less
apply (erule lower_le_induct, safe)
apply (simp add: monofun_cfun)
apply (simp add: rev_trans_less [OF lower_plus_less1])
apply (simp add: lower_plus_less_iff)
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


subsection {* Map and join *}

definition
  lower_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a lower_pd \<rightarrow> 'b lower_pd" where
  "lower_map = (\<Lambda> f xs. lower_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<flat>))"

definition
  lower_join :: "'a lower_pd lower_pd \<rightarrow> 'a lower_pd" where
  "lower_join = (\<Lambda> xss. lower_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma lower_map_unit [simp]:
  "lower_map\<cdot>f\<cdot>{x}\<flat> = {f\<cdot>x}\<flat>"
unfolding lower_map_def by simp

lemma lower_map_plus [simp]:
  "lower_map\<cdot>f\<cdot>(xs +\<flat> ys) = lower_map\<cdot>f\<cdot>xs +\<flat> lower_map\<cdot>f\<cdot>ys"
unfolding lower_map_def by simp

lemma lower_join_unit [simp]:
  "lower_join\<cdot>{xs}\<flat> = xs"
unfolding lower_join_def by simp

lemma lower_join_plus [simp]:
  "lower_join\<cdot>(xss +\<flat> yss) = lower_join\<cdot>xss +\<flat> lower_join\<cdot>yss"
unfolding lower_join_def by simp

lemma lower_map_ident: "lower_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: lower_pd_induct, simp_all)

lemma lower_map_map:
  "lower_map\<cdot>f\<cdot>(lower_map\<cdot>g\<cdot>xs) = lower_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: lower_pd_induct, simp_all)

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

lemma lower_map_approx: "lower_map\<cdot>(approx n)\<cdot>xs = approx n\<cdot>xs"
by (induct xs rule: lower_pd_induct, simp_all)

end
