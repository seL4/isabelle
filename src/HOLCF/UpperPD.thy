(*  Title:      HOLCF/UpperPD.thy
    Author:     Brian Huffman
*)

header {* Upper powerdomain *}

theory UpperPD
imports CompactBasis
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
  "(PDUnit a \<le>\<sharp> PDUnit b) = a \<sqsubseteq> b"
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

lemma pd_take_upper_chain:
  "pd_take n t \<le>\<sharp> pd_take (Suc n) t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_chain)
apply (simp add: PDPlus_upper_mono)
done

lemma pd_take_upper_le: "pd_take i t \<le>\<sharp> t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_less)
apply (simp add: PDPlus_upper_mono)
done

lemma pd_take_upper_mono:
  "t \<le>\<sharp> u \<Longrightarrow> pd_take n t \<le>\<sharp> pd_take n u"
apply (erule upper_le_induct)
apply (simp add: compact_basis.take_mono)
apply (simp add: upper_le_PDPlus_PDUnit_iff)
apply (simp add: upper_le_PDPlus_iff)
done


subsection {* Type definition *}

typedef (open) 'a upper_pd =
  "{S::'a pd_basis set. upper_le.ideal S}"
by (fast intro: upper_le.ideal_principal)

instantiation upper_pd :: (profinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_upper_pd x \<subseteq> Rep_upper_pd y"

instance ..
end

instance upper_pd :: (profinite) po
by (rule upper_le.typedef_ideal_po
    [OF type_definition_upper_pd below_upper_pd_def])

instance upper_pd :: (profinite) cpo
by (rule upper_le.typedef_ideal_cpo
    [OF type_definition_upper_pd below_upper_pd_def])

lemma Rep_upper_pd_lub:
  "chain Y \<Longrightarrow> Rep_upper_pd (\<Squnion>i. Y i) = (\<Union>i. Rep_upper_pd (Y i))"
by (rule upper_le.typedef_ideal_rep_contlub
    [OF type_definition_upper_pd below_upper_pd_def])

lemma ideal_Rep_upper_pd: "upper_le.ideal (Rep_upper_pd xs)"
by (rule Rep_upper_pd [unfolded mem_Collect_eq])

definition
  upper_principal :: "'a pd_basis \<Rightarrow> 'a upper_pd" where
  "upper_principal t = Abs_upper_pd {u. u \<le>\<sharp> t}"

lemma Rep_upper_principal:
  "Rep_upper_pd (upper_principal t) = {u. u \<le>\<sharp> t}"
unfolding upper_principal_def
by (simp add: Abs_upper_pd_inverse upper_le.ideal_principal)

interpretation upper_pd:
  ideal_completion upper_le pd_take upper_principal Rep_upper_pd
apply unfold_locales
apply (rule pd_take_upper_le)
apply (rule pd_take_idem)
apply (erule pd_take_upper_mono)
apply (rule pd_take_upper_chain)
apply (rule finite_range_pd_take)
apply (rule pd_take_covers)
apply (rule ideal_Rep_upper_pd)
apply (erule Rep_upper_pd_lub)
apply (rule Rep_upper_principal)
apply (simp only: below_upper_pd_def)
done

text {* Upper powerdomain is pointed *}

lemma upper_pd_minimal: "upper_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: upper_pd.principal_induct, simp, simp)

instance upper_pd :: (bifinite) pcpo
by intro_classes (fast intro: upper_pd_minimal)

lemma inst_upper_pd_pcpo: "\<bottom> = upper_principal (PDUnit compact_bot)"
by (rule upper_pd_minimal [THEN UU_I, symmetric])

text {* Upper powerdomain is profinite *}

instantiation upper_pd :: (profinite) profinite
begin

definition
  approx_upper_pd_def: "approx = upper_pd.completion_approx"

instance
apply (intro_classes, unfold approx_upper_pd_def)
apply (rule upper_pd.chain_completion_approx)
apply (rule upper_pd.lub_completion_approx)
apply (rule upper_pd.completion_approx_idem)
apply (rule upper_pd.finite_fixes_completion_approx)
done

end

instance upper_pd :: (bifinite) bifinite ..

lemma approx_upper_principal [simp]:
  "approx n\<cdot>(upper_principal t) = upper_principal (pd_take n t)"
unfolding approx_upper_pd_def
by (rule upper_pd.completion_approx_principal)

lemma approx_eq_upper_principal:
  "\<exists>t\<in>Rep_upper_pd xs. approx n\<cdot>xs = upper_principal (pd_take n t)"
unfolding approx_upper_pd_def
by (rule upper_pd.completion_approx_eq_principal)


subsection {* Monadic unit and plus *}

definition
  upper_unit :: "'a \<rightarrow> 'a upper_pd" where
  "upper_unit = compact_basis.basis_fun (\<lambda>a. upper_principal (PDUnit a))"

definition
  upper_plus :: "'a upper_pd \<rightarrow> 'a upper_pd \<rightarrow> 'a upper_pd" where
  "upper_plus = upper_pd.basis_fun (\<lambda>t. upper_pd.basis_fun (\<lambda>u.
      upper_principal (PDPlus t u)))"

abbreviation
  upper_add :: "'a upper_pd \<Rightarrow> 'a upper_pd \<Rightarrow> 'a upper_pd"
    (infixl "+\<sharp>" 65) where
  "xs +\<sharp> ys == upper_plus\<cdot>xs\<cdot>ys"

syntax
  "_upper_pd" :: "args \<Rightarrow> 'a upper_pd" ("{_}\<sharp>")

translations
  "{x,xs}\<sharp>" == "{x}\<sharp> +\<sharp> {xs}\<sharp>"
  "{x}\<sharp>" == "CONST upper_unit\<cdot>x"

lemma upper_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<sharp> = upper_principal (PDUnit a)"
unfolding upper_unit_def
by (simp add: compact_basis.basis_fun_principal PDUnit_upper_mono)

lemma upper_plus_principal [simp]:
  "upper_principal t +\<sharp> upper_principal u = upper_principal (PDPlus t u)"
unfolding upper_plus_def
by (simp add: upper_pd.basis_fun_principal
    upper_pd.basis_fun_mono PDPlus_upper_mono)

lemma approx_upper_unit [simp]:
  "approx n\<cdot>{x}\<sharp> = {approx n\<cdot>x}\<sharp>"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (simp add: approx_Rep_compact_basis)
done

lemma approx_upper_plus [simp]:
  "approx n\<cdot>(xs +\<sharp> ys) = (approx n\<cdot>xs) +\<sharp> (approx n\<cdot>ys)"
by (induct xs ys rule: upper_pd.principal_induct2, simp, simp, simp)

interpretation upper_add!: semilattice upper_add proof
  fix xs ys zs :: "'a upper_pd"
  show "(xs +\<sharp> ys) +\<sharp> zs = xs +\<sharp> (ys +\<sharp> zs)"
    apply (induct xs ys arbitrary: zs rule: upper_pd.principal_induct2, simp, simp)
    apply (rule_tac x=zs in upper_pd.principal_induct, simp)
    apply (simp add: PDPlus_assoc)
    done
  show "xs +\<sharp> ys = ys +\<sharp> xs"
    apply (induct xs ys rule: upper_pd.principal_induct2, simp, simp)
    apply (simp add: PDPlus_commute)
    done
  show "xs +\<sharp> xs = xs"
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

lemma upper_plus_below1: "xs +\<sharp> ys \<sqsubseteq> xs"
apply (induct xs ys rule: upper_pd.principal_induct2, simp, simp)
apply (simp add: PDPlus_upper_le)
done

lemma upper_plus_below2: "xs +\<sharp> ys \<sqsubseteq> ys"
by (subst upper_plus_commute, rule upper_plus_below1)

lemma upper_plus_greatest: "\<lbrakk>xs \<sqsubseteq> ys; xs \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs \<sqsubseteq> ys +\<sharp> zs"
apply (subst upper_plus_absorb [of xs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma upper_below_plus_iff:
  "xs \<sqsubseteq> ys +\<sharp> zs \<longleftrightarrow> xs \<sqsubseteq> ys \<and> xs \<sqsubseteq> zs"
apply safe
apply (erule below_trans [OF _ upper_plus_below1])
apply (erule below_trans [OF _ upper_plus_below2])
apply (erule (1) upper_plus_greatest)
done

lemma upper_plus_below_unit_iff:
  "xs +\<sharp> ys \<sqsubseteq> {z}\<sharp> \<longleftrightarrow> xs \<sqsubseteq> {z}\<sharp> \<or> ys \<sqsubseteq> {z}\<sharp>"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>xs \<sqsubseteq> f\<cdot>{z}\<sharp> \<or> f\<cdot>ys \<sqsubseteq> f\<cdot>{z}\<sharp>)")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac x="approx i\<cdot>xs" in upper_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>ys" in upper_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>z" in compact_basis.compact_imp_principal, simp)
    apply (clarify, simp add: upper_le_PDPlus_PDUnit_iff)
   apply simp
  apply simp
 apply (erule disjE)
  apply (erule below_trans [OF upper_plus_below1])
 apply (erule below_trans [OF upper_plus_below2])
done

lemma upper_unit_below_iff [simp]: "{x}\<sharp> \<sqsubseteq> {y}\<sharp> \<longleftrightarrow> x \<sqsubseteq> y"
 apply (rule iffI)
  apply (rule profinite_below_ext)
  apply (drule_tac f="approx i" in monofun_cfun_arg, simp)
  apply (cut_tac x="approx i\<cdot>x" in compact_basis.compact_imp_principal, simp)
  apply (cut_tac x="approx i\<cdot>y" in compact_basis.compact_imp_principal, simp)
  apply clarsimp
 apply (erule monofun_cfun_arg)
done

lemmas upper_pd_below_simps =
  upper_unit_below_iff
  upper_below_plus_iff
  upper_plus_below_unit_iff

lemma upper_unit_eq_iff [simp]: "{x}\<sharp> = {y}\<sharp> \<longleftrightarrow> x = y"
unfolding po_eq_conv by simp

lemma upper_unit_strict [simp]: "{\<bottom>}\<sharp> = \<bottom>"
unfolding inst_upper_pd_pcpo Rep_compact_bot [symmetric] by simp

lemma upper_plus_strict1 [simp]: "\<bottom> +\<sharp> ys = \<bottom>"
by (rule UU_I, rule upper_plus_below1)

lemma upper_plus_strict2 [simp]: "xs +\<sharp> \<bottom> = \<bottom>"
by (rule UU_I, rule upper_plus_below2)

lemma upper_unit_strict_iff [simp]: "{x}\<sharp> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding upper_unit_strict [symmetric] by (rule upper_unit_eq_iff)

lemma upper_plus_strict_iff [simp]:
  "xs +\<sharp> ys = \<bottom> \<longleftrightarrow> xs = \<bottom> \<or> ys = \<bottom>"
apply (rule iffI)
apply (erule rev_mp)
apply (rule upper_pd.principal_induct2 [where x=xs and y=ys], simp, simp)
apply (simp add: inst_upper_pd_pcpo upper_pd.principal_eq_iff
                 upper_le_PDPlus_PDUnit_iff)
apply auto
done

lemma compact_upper_unit_iff [simp]: "compact {x}\<sharp> \<longleftrightarrow> compact x"
unfolding profinite_compact_iff by simp

lemma compact_upper_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs +\<sharp> ys)"
by (auto dest!: upper_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma upper_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<sharp>"
  assumes insert: "\<And>x ys. \<lbrakk>P {x}\<sharp>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<sharp> +\<sharp> ys)"
  shows "P (xs::'a upper_pd)"
apply (induct xs rule: upper_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: upper_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: upper_unit_Rep_compact_basis [symmetric]
                  upper_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma upper_pd_induct:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<sharp>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs +\<sharp> ys)"
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
    (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<sharp> y\<cdot>f)"

lemma ACI_upper_bind:
  "ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<sharp> y\<cdot>f)"
apply unfold_locales
apply (simp add: upper_plus_assoc)
apply (simp add: upper_plus_commute)
apply (simp add: eta_cfun)
done

lemma upper_bind_basis_simps [simp]:
  "upper_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "upper_bind_basis (PDPlus t u) =
    (\<Lambda> f. upper_bind_basis t\<cdot>f +\<sharp> upper_bind_basis u\<cdot>f)"
unfolding upper_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_upper_bind])
apply (rule fold_pd_PDPlus [OF ACI_upper_bind])
done

lemma upper_bind_basis_mono:
  "t \<le>\<sharp> u \<Longrightarrow> upper_bind_basis t \<sqsubseteq> upper_bind_basis u"
unfolding expand_cfun_below
apply (erule upper_le_induct, safe)
apply (simp add: monofun_cfun)
apply (simp add: below_trans [OF upper_plus_below1])
apply (simp add: upper_below_plus_iff)
done

definition
  upper_bind :: "'a upper_pd \<rightarrow> ('a \<rightarrow> 'b upper_pd) \<rightarrow> 'b upper_pd" where
  "upper_bind = upper_pd.basis_fun upper_bind_basis"

lemma upper_bind_principal [simp]:
  "upper_bind\<cdot>(upper_principal t) = upper_bind_basis t"
unfolding upper_bind_def
apply (rule upper_pd.basis_fun_principal)
apply (erule upper_bind_basis_mono)
done

lemma upper_bind_unit [simp]:
  "upper_bind\<cdot>{x}\<sharp>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma upper_bind_plus [simp]:
  "upper_bind\<cdot>(xs +\<sharp> ys)\<cdot>f = upper_bind\<cdot>xs\<cdot>f +\<sharp> upper_bind\<cdot>ys\<cdot>f"
by (induct xs ys rule: upper_pd.principal_induct2, simp, simp, simp)

lemma upper_bind_strict [simp]: "upper_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding upper_unit_strict [symmetric] by (rule upper_bind_unit)


subsection {* Map and join *}

definition
  upper_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a upper_pd \<rightarrow> 'b upper_pd" where
  "upper_map = (\<Lambda> f xs. upper_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<sharp>))"

definition
  upper_join :: "'a upper_pd upper_pd \<rightarrow> 'a upper_pd" where
  "upper_join = (\<Lambda> xss. upper_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma upper_map_unit [simp]:
  "upper_map\<cdot>f\<cdot>{x}\<sharp> = {f\<cdot>x}\<sharp>"
unfolding upper_map_def by simp

lemma upper_map_plus [simp]:
  "upper_map\<cdot>f\<cdot>(xs +\<sharp> ys) = upper_map\<cdot>f\<cdot>xs +\<sharp> upper_map\<cdot>f\<cdot>ys"
unfolding upper_map_def by simp

lemma upper_join_unit [simp]:
  "upper_join\<cdot>{xs}\<sharp> = xs"
unfolding upper_join_def by simp

lemma upper_join_plus [simp]:
  "upper_join\<cdot>(xss +\<sharp> yss) = upper_join\<cdot>xss +\<sharp> upper_join\<cdot>yss"
unfolding upper_join_def by simp

lemma upper_map_ident: "upper_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: upper_pd_induct, simp_all)

lemma upper_map_ID: "upper_map\<cdot>ID = ID"
by (simp add: expand_cfun_eq ID_def upper_map_ident)

lemma upper_map_map:
  "upper_map\<cdot>f\<cdot>(upper_map\<cdot>g\<cdot>xs) = upper_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: upper_pd_induct, simp_all)

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

lemma upper_map_approx: "upper_map\<cdot>(approx n)\<cdot>xs = approx n\<cdot>xs"
by (induct xs rule: upper_pd_induct, simp_all)

lemma ep_pair_upper_map: "ep_pair e p \<Longrightarrow> ep_pair (upper_map\<cdot>e) (upper_map\<cdot>p)"
apply default
apply (induct_tac x rule: upper_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: upper_pd_induct, simp_all add: ep_pair.e_p_below monofun_cfun)
done

lemma deflation_upper_map: "deflation d \<Longrightarrow> deflation (upper_map\<cdot>d)"
apply default
apply (induct_tac x rule: upper_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: upper_pd_induct, simp_all add: deflation.below monofun_cfun)
done

end
