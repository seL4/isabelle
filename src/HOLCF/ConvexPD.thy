(*  Title:      HOLCF/ConvexPD.thy
    Author:     Brian Huffman
*)

header {* Convex powerdomain *}

theory ConvexPD
imports UpperPD LowerPD
begin

subsection {* Basis preorder *}

definition
  convex_le :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> bool" (infix "\<le>\<natural>" 50) where
  "convex_le = (\<lambda>u v. u \<le>\<sharp> v \<and> u \<le>\<flat> v)"

lemma convex_le_refl [simp]: "t \<le>\<natural> t"
unfolding convex_le_def by (fast intro: upper_le_refl lower_le_refl)

lemma convex_le_trans: "\<lbrakk>t \<le>\<natural> u; u \<le>\<natural> v\<rbrakk> \<Longrightarrow> t \<le>\<natural> v"
unfolding convex_le_def by (fast intro: upper_le_trans lower_le_trans)

interpretation convex_le: preorder convex_le
by (rule preorder.intro, rule convex_le_refl, rule convex_le_trans)

lemma upper_le_minimal [simp]: "PDUnit compact_bot \<le>\<natural> t"
unfolding convex_le_def Rep_PDUnit by simp

lemma PDUnit_convex_mono: "x \<sqsubseteq> y \<Longrightarrow> PDUnit x \<le>\<natural> PDUnit y"
unfolding convex_le_def by (fast intro: PDUnit_upper_mono PDUnit_lower_mono)

lemma PDPlus_convex_mono: "\<lbrakk>s \<le>\<natural> t; u \<le>\<natural> v\<rbrakk> \<Longrightarrow> PDPlus s u \<le>\<natural> PDPlus t v"
unfolding convex_le_def by (fast intro: PDPlus_upper_mono PDPlus_lower_mono)

lemma convex_le_PDUnit_PDUnit_iff [simp]:
  "(PDUnit a \<le>\<natural> PDUnit b) = a \<sqsubseteq> b"
unfolding convex_le_def upper_le_def lower_le_def Rep_PDUnit by fast

lemma convex_le_PDUnit_lemma1:
  "(PDUnit a \<le>\<natural> t) = (\<forall>b\<in>Rep_pd_basis t. a \<sqsubseteq> b)"
unfolding convex_le_def upper_le_def lower_le_def Rep_PDUnit
using Rep_pd_basis_nonempty [of t, folded ex_in_conv] by fast

lemma convex_le_PDUnit_PDPlus_iff [simp]:
  "(PDUnit a \<le>\<natural> PDPlus t u) = (PDUnit a \<le>\<natural> t \<and> PDUnit a \<le>\<natural> u)"
unfolding convex_le_PDUnit_lemma1 Rep_PDPlus by fast

lemma convex_le_PDUnit_lemma2:
  "(t \<le>\<natural> PDUnit b) = (\<forall>a\<in>Rep_pd_basis t. a \<sqsubseteq> b)"
unfolding convex_le_def upper_le_def lower_le_def Rep_PDUnit
using Rep_pd_basis_nonempty [of t, folded ex_in_conv] by fast

lemma convex_le_PDPlus_PDUnit_iff [simp]:
  "(PDPlus t u \<le>\<natural> PDUnit a) = (t \<le>\<natural> PDUnit a \<and> u \<le>\<natural> PDUnit a)"
unfolding convex_le_PDUnit_lemma2 Rep_PDPlus by fast

lemma convex_le_PDPlus_lemma:
  assumes z: "PDPlus t u \<le>\<natural> z"
  shows "\<exists>v w. z = PDPlus v w \<and> t \<le>\<natural> v \<and> u \<le>\<natural> w"
proof (intro exI conjI)
  let ?A = "{b\<in>Rep_pd_basis z. \<exists>a\<in>Rep_pd_basis t. a \<sqsubseteq> b}"
  let ?B = "{b\<in>Rep_pd_basis z. \<exists>a\<in>Rep_pd_basis u. a \<sqsubseteq> b}"
  let ?v = "Abs_pd_basis ?A"
  let ?w = "Abs_pd_basis ?B"
  have Rep_v: "Rep_pd_basis ?v = ?A"
    apply (rule Abs_pd_basis_inverse)
    apply (rule Rep_pd_basis_nonempty [of t, folded ex_in_conv, THEN exE])
    apply (cut_tac z, simp only: convex_le_def lower_le_def, clarify)
    apply (drule_tac x=x in bspec, simp add: Rep_PDPlus, erule bexE)
    apply (simp add: pd_basis_def)
    apply fast
    done
  have Rep_w: "Rep_pd_basis ?w = ?B"
    apply (rule Abs_pd_basis_inverse)
    apply (rule Rep_pd_basis_nonempty [of u, folded ex_in_conv, THEN exE])
    apply (cut_tac z, simp only: convex_le_def lower_le_def, clarify)
    apply (drule_tac x=x in bspec, simp add: Rep_PDPlus, erule bexE)
    apply (simp add: pd_basis_def)
    apply fast
    done
  show "z = PDPlus ?v ?w"
    apply (insert z)
    apply (simp add: convex_le_def, erule conjE)
    apply (simp add: Rep_pd_basis_inject [symmetric] Rep_PDPlus)
    apply (simp add: Rep_v Rep_w)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (simp only: upper_le_def)
     apply (drule (1) bspec, erule bexE)
     apply (simp add: Rep_PDPlus)
     apply fast
    apply fast
    done
  show "t \<le>\<natural> ?v" "u \<le>\<natural> ?w"
   apply (insert z)
   apply (simp_all add: convex_le_def upper_le_def lower_le_def Rep_PDPlus Rep_v Rep_w)
   apply fast+
   done
qed

lemma convex_le_induct [induct set: convex_le]:
  assumes le: "t \<le>\<natural> u"
  assumes 2: "\<And>t u v. \<lbrakk>P t u; P u v\<rbrakk> \<Longrightarrow> P t v"
  assumes 3: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> P (PDUnit a) (PDUnit b)"
  assumes 4: "\<And>t u v w. \<lbrakk>P t v; P u w\<rbrakk> \<Longrightarrow> P (PDPlus t u) (PDPlus v w)"
  shows "P t u"
using le apply (induct t arbitrary: u rule: pd_basis_induct)
apply (erule rev_mp)
apply (induct_tac u rule: pd_basis_induct1)
apply (simp add: 3)
apply (simp, clarify, rename_tac a b t)
apply (subgoal_tac "P (PDPlus (PDUnit a) (PDUnit a)) (PDPlus (PDUnit b) t)")
apply (simp add: PDPlus_absorb)
apply (erule (1) 4 [OF 3])
apply (drule convex_le_PDPlus_lemma, clarify)
apply (simp add: 4)
done

lemma pd_take_convex_chain:
  "pd_take n t \<le>\<natural> pd_take (Suc n) t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_chain)
apply (simp add: PDPlus_convex_mono)
done

lemma pd_take_convex_le: "pd_take i t \<le>\<natural> t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_less)
apply (simp add: PDPlus_convex_mono)
done

lemma pd_take_convex_mono:
  "t \<le>\<natural> u \<Longrightarrow> pd_take n t \<le>\<natural> pd_take n u"
apply (erule convex_le_induct)
apply (erule (1) convex_le_trans)
apply (simp add: compact_basis.take_mono)
apply (simp add: PDPlus_convex_mono)
done


subsection {* Type definition *}

typedef (open) 'a convex_pd =
  "{S::'a pd_basis set. convex_le.ideal S}"
by (fast intro: convex_le.ideal_principal)

instantiation convex_pd :: (profinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_convex_pd x \<subseteq> Rep_convex_pd y"

instance ..
end

instance convex_pd :: (profinite) po
by (rule convex_le.typedef_ideal_po
    [OF type_definition_convex_pd below_convex_pd_def])

instance convex_pd :: (profinite) cpo
by (rule convex_le.typedef_ideal_cpo
    [OF type_definition_convex_pd below_convex_pd_def])

lemma Rep_convex_pd_lub:
  "chain Y \<Longrightarrow> Rep_convex_pd (\<Squnion>i. Y i) = (\<Union>i. Rep_convex_pd (Y i))"
by (rule convex_le.typedef_ideal_rep_contlub
    [OF type_definition_convex_pd below_convex_pd_def])

lemma ideal_Rep_convex_pd: "convex_le.ideal (Rep_convex_pd xs)"
by (rule Rep_convex_pd [unfolded mem_Collect_eq])

definition
  convex_principal :: "'a pd_basis \<Rightarrow> 'a convex_pd" where
  "convex_principal t = Abs_convex_pd {u. u \<le>\<natural> t}"

lemma Rep_convex_principal:
  "Rep_convex_pd (convex_principal t) = {u. u \<le>\<natural> t}"
unfolding convex_principal_def
by (simp add: Abs_convex_pd_inverse convex_le.ideal_principal)

interpretation convex_pd:
  ideal_completion convex_le pd_take convex_principal Rep_convex_pd
apply unfold_locales
apply (rule pd_take_convex_le)
apply (rule pd_take_idem)
apply (erule pd_take_convex_mono)
apply (rule pd_take_convex_chain)
apply (rule finite_range_pd_take)
apply (rule pd_take_covers)
apply (rule ideal_Rep_convex_pd)
apply (erule Rep_convex_pd_lub)
apply (rule Rep_convex_principal)
apply (simp only: below_convex_pd_def)
done

text {* Convex powerdomain is pointed *}

lemma convex_pd_minimal: "convex_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: convex_pd.principal_induct, simp, simp)

instance convex_pd :: (bifinite) pcpo
by intro_classes (fast intro: convex_pd_minimal)

lemma inst_convex_pd_pcpo: "\<bottom> = convex_principal (PDUnit compact_bot)"
by (rule convex_pd_minimal [THEN UU_I, symmetric])

text {* Convex powerdomain is profinite *}

instantiation convex_pd :: (profinite) profinite
begin

definition
  approx_convex_pd_def: "approx = convex_pd.completion_approx"

instance
apply (intro_classes, unfold approx_convex_pd_def)
apply (rule convex_pd.chain_completion_approx)
apply (rule convex_pd.lub_completion_approx)
apply (rule convex_pd.completion_approx_idem)
apply (rule convex_pd.finite_fixes_completion_approx)
done

end

instance convex_pd :: (bifinite) bifinite ..

lemma approx_convex_principal [simp]:
  "approx n\<cdot>(convex_principal t) = convex_principal (pd_take n t)"
unfolding approx_convex_pd_def
by (rule convex_pd.completion_approx_principal)

lemma approx_eq_convex_principal:
  "\<exists>t\<in>Rep_convex_pd xs. approx n\<cdot>xs = convex_principal (pd_take n t)"
unfolding approx_convex_pd_def
by (rule convex_pd.completion_approx_eq_principal)


subsection {* Monadic unit and plus *}

definition
  convex_unit :: "'a \<rightarrow> 'a convex_pd" where
  "convex_unit = compact_basis.basis_fun (\<lambda>a. convex_principal (PDUnit a))"

definition
  convex_plus :: "'a convex_pd \<rightarrow> 'a convex_pd \<rightarrow> 'a convex_pd" where
  "convex_plus = convex_pd.basis_fun (\<lambda>t. convex_pd.basis_fun (\<lambda>u.
      convex_principal (PDPlus t u)))"

abbreviation
  convex_add :: "'a convex_pd \<Rightarrow> 'a convex_pd \<Rightarrow> 'a convex_pd"
    (infixl "+\<natural>" 65) where
  "xs +\<natural> ys == convex_plus\<cdot>xs\<cdot>ys"

syntax
  "_convex_pd" :: "args \<Rightarrow> 'a convex_pd" ("{_}\<natural>")

translations
  "{x,xs}\<natural>" == "{x}\<natural> +\<natural> {xs}\<natural>"
  "{x}\<natural>" == "CONST convex_unit\<cdot>x"

lemma convex_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<natural> = convex_principal (PDUnit a)"
unfolding convex_unit_def
by (simp add: compact_basis.basis_fun_principal PDUnit_convex_mono)

lemma convex_plus_principal [simp]:
  "convex_principal t +\<natural> convex_principal u = convex_principal (PDPlus t u)"
unfolding convex_plus_def
by (simp add: convex_pd.basis_fun_principal
    convex_pd.basis_fun_mono PDPlus_convex_mono)

lemma approx_convex_unit [simp]:
  "approx n\<cdot>{x}\<natural> = {approx n\<cdot>x}\<natural>"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (simp add: approx_Rep_compact_basis)
done

lemma approx_convex_plus [simp]:
  "approx n\<cdot>(xs +\<natural> ys) = approx n\<cdot>xs +\<natural> approx n\<cdot>ys"
by (induct xs ys rule: convex_pd.principal_induct2, simp, simp, simp)

lemma convex_plus_assoc:
  "(xs +\<natural> ys) +\<natural> zs = xs +\<natural> (ys +\<natural> zs)"
apply (induct xs ys arbitrary: zs rule: convex_pd.principal_induct2, simp, simp)
apply (rule_tac x=zs in convex_pd.principal_induct, simp)
apply (simp add: PDPlus_assoc)
done

lemma convex_plus_commute: "xs +\<natural> ys = ys +\<natural> xs"
apply (induct xs ys rule: convex_pd.principal_induct2, simp, simp)
apply (simp add: PDPlus_commute)
done

lemma convex_plus_absorb [simp]: "xs +\<natural> xs = xs"
apply (induct xs rule: convex_pd.principal_induct, simp)
apply (simp add: PDPlus_absorb)
done

lemma convex_plus_left_commute: "xs +\<natural> (ys +\<natural> zs) = ys +\<natural> (xs +\<natural> zs)"
by (rule mk_left_commute
    [of "op +\<natural>", OF convex_plus_assoc convex_plus_commute])

lemma convex_plus_left_absorb [simp]: "xs +\<natural> (xs +\<natural> ys) = xs +\<natural> ys"
by (simp only: convex_plus_assoc [symmetric] convex_plus_absorb)

text {* Useful for @{text "simp add: convex_plus_ac"} *}
lemmas convex_plus_ac =
  convex_plus_assoc convex_plus_commute convex_plus_left_commute

text {* Useful for @{text "simp only: convex_plus_aci"} *}
lemmas convex_plus_aci =
  convex_plus_ac convex_plus_absorb convex_plus_left_absorb

lemma convex_unit_below_plus_iff [simp]:
  "{x}\<natural> \<sqsubseteq> ys +\<natural> zs \<longleftrightarrow> {x}\<natural> \<sqsubseteq> ys \<and> {x}\<natural> \<sqsubseteq> zs"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>{x}\<natural> \<sqsubseteq> f\<cdot>ys \<and> f\<cdot>{x}\<natural> \<sqsubseteq> f\<cdot>zs)")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac x="approx i\<cdot>x" in compact_basis.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>ys" in convex_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>zs" in convex_pd.compact_imp_principal, simp)
    apply (clarify, simp)
   apply simp
  apply simp
 apply (erule conjE)
 apply (subst convex_plus_absorb [of "{x}\<natural>", symmetric])
 apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma convex_plus_below_unit_iff [simp]:
  "xs +\<natural> ys \<sqsubseteq> {z}\<natural> \<longleftrightarrow> xs \<sqsubseteq> {z}\<natural> \<and> ys \<sqsubseteq> {z}\<natural>"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>xs \<sqsubseteq> f\<cdot>{z}\<natural> \<and> f\<cdot>ys \<sqsubseteq> f\<cdot>{z}\<natural>)")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac x="approx i\<cdot>xs" in convex_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>ys" in convex_pd.compact_imp_principal, simp)
    apply (cut_tac x="approx i\<cdot>z" in compact_basis.compact_imp_principal, simp)
    apply (clarify, simp)
   apply simp
  apply simp
 apply (erule conjE)
 apply (subst convex_plus_absorb [of "{z}\<natural>", symmetric])
 apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma convex_unit_below_iff [simp]: "{x}\<natural> \<sqsubseteq> {y}\<natural> \<longleftrightarrow> x \<sqsubseteq> y"
 apply (rule iffI)
  apply (rule profinite_below_ext)
  apply (drule_tac f="approx i" in monofun_cfun_arg, simp)
  apply (cut_tac x="approx i\<cdot>x" in compact_basis.compact_imp_principal, simp)
  apply (cut_tac x="approx i\<cdot>y" in compact_basis.compact_imp_principal, simp)
  apply clarsimp
 apply (erule monofun_cfun_arg)
done

lemma convex_unit_eq_iff [simp]: "{x}\<natural> = {y}\<natural> \<longleftrightarrow> x = y"
unfolding po_eq_conv by simp

lemma convex_unit_strict [simp]: "{\<bottom>}\<natural> = \<bottom>"
unfolding inst_convex_pd_pcpo Rep_compact_bot [symmetric] by simp

lemma convex_unit_strict_iff [simp]: "{x}\<natural> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding convex_unit_strict [symmetric] by (rule convex_unit_eq_iff)

lemma compact_convex_unit_iff [simp]:
  "compact {x}\<natural> \<longleftrightarrow> compact x"
unfolding profinite_compact_iff by simp

lemma compact_convex_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs +\<natural> ys)"
by (auto dest!: convex_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma convex_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<natural>"
  assumes insert: "\<And>x ys. \<lbrakk>P {x}\<natural>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<natural> +\<natural> ys)"
  shows "P (xs::'a convex_pd)"
apply (induct xs rule: convex_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: convex_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: convex_unit_Rep_compact_basis [symmetric]
                  convex_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma convex_pd_induct:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<natural>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs +\<natural> ys)"
  shows "P (xs::'a convex_pd)"
apply (induct xs rule: convex_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct)
apply (simp only: convex_unit_Rep_compact_basis [symmetric] unit)
apply (simp only: convex_plus_principal [symmetric] plus)
done


subsection {* Monadic bind *}

definition
  convex_bind_basis ::
  "'a pd_basis \<Rightarrow> ('a \<rightarrow> 'b convex_pd) \<rightarrow> 'b convex_pd" where
  "convex_bind_basis = fold_pd
    (\<lambda>a. \<Lambda> f. f\<cdot>(Rep_compact_basis a))
    (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<natural> y\<cdot>f)"

lemma ACI_convex_bind:
  "ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f +\<natural> y\<cdot>f)"
apply unfold_locales
apply (simp add: convex_plus_assoc)
apply (simp add: convex_plus_commute)
apply (simp add: eta_cfun)
done

lemma convex_bind_basis_simps [simp]:
  "convex_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "convex_bind_basis (PDPlus t u) =
    (\<Lambda> f. convex_bind_basis t\<cdot>f +\<natural> convex_bind_basis u\<cdot>f)"
unfolding convex_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_convex_bind])
apply (rule fold_pd_PDPlus [OF ACI_convex_bind])
done

lemma monofun_LAM:
  "\<lbrakk>cont f; cont g; \<And>x. f x \<sqsubseteq> g x\<rbrakk> \<Longrightarrow> (\<Lambda> x. f x) \<sqsubseteq> (\<Lambda> x. g x)"
by (simp add: expand_cfun_below)

lemma convex_bind_basis_mono:
  "t \<le>\<natural> u \<Longrightarrow> convex_bind_basis t \<sqsubseteq> convex_bind_basis u"
apply (erule convex_le_induct)
apply (erule (1) below_trans)
apply (simp add: monofun_LAM monofun_cfun)
apply (simp add: monofun_LAM monofun_cfun)
done

definition
  convex_bind :: "'a convex_pd \<rightarrow> ('a \<rightarrow> 'b convex_pd) \<rightarrow> 'b convex_pd" where
  "convex_bind = convex_pd.basis_fun convex_bind_basis"

lemma convex_bind_principal [simp]:
  "convex_bind\<cdot>(convex_principal t) = convex_bind_basis t"
unfolding convex_bind_def
apply (rule convex_pd.basis_fun_principal)
apply (erule convex_bind_basis_mono)
done

lemma convex_bind_unit [simp]:
  "convex_bind\<cdot>{x}\<natural>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_bind_plus [simp]:
  "convex_bind\<cdot>(xs +\<natural> ys)\<cdot>f = convex_bind\<cdot>xs\<cdot>f +\<natural> convex_bind\<cdot>ys\<cdot>f"
by (induct xs ys rule: convex_pd.principal_induct2, simp, simp, simp)

lemma convex_bind_strict [simp]: "convex_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding convex_unit_strict [symmetric] by (rule convex_bind_unit)


subsection {* Map and join *}

definition
  convex_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a convex_pd \<rightarrow> 'b convex_pd" where
  "convex_map = (\<Lambda> f xs. convex_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<natural>))"

definition
  convex_join :: "'a convex_pd convex_pd \<rightarrow> 'a convex_pd" where
  "convex_join = (\<Lambda> xss. convex_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma convex_map_unit [simp]:
  "convex_map\<cdot>f\<cdot>(convex_unit\<cdot>x) = convex_unit\<cdot>(f\<cdot>x)"
unfolding convex_map_def by simp

lemma convex_map_plus [simp]:
  "convex_map\<cdot>f\<cdot>(xs +\<natural> ys) = convex_map\<cdot>f\<cdot>xs +\<natural> convex_map\<cdot>f\<cdot>ys"
unfolding convex_map_def by simp

lemma convex_join_unit [simp]:
  "convex_join\<cdot>{xs}\<natural> = xs"
unfolding convex_join_def by simp

lemma convex_join_plus [simp]:
  "convex_join\<cdot>(xss +\<natural> yss) = convex_join\<cdot>xss +\<natural> convex_join\<cdot>yss"
unfolding convex_join_def by simp

lemma convex_map_ident: "convex_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma convex_map_ID: "convex_map\<cdot>ID = ID"
by (simp add: expand_cfun_eq ID_def convex_map_ident)

lemma convex_map_map:
  "convex_map\<cdot>f\<cdot>(convex_map\<cdot>g\<cdot>xs) = convex_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma convex_join_map_unit:
  "convex_join\<cdot>(convex_map\<cdot>convex_unit\<cdot>xs) = xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma convex_join_map_join:
  "convex_join\<cdot>(convex_map\<cdot>convex_join\<cdot>xsss) = convex_join\<cdot>(convex_join\<cdot>xsss)"
by (induct xsss rule: convex_pd_induct, simp_all)

lemma convex_join_map_map:
  "convex_join\<cdot>(convex_map\<cdot>(convex_map\<cdot>f)\<cdot>xss) =
   convex_map\<cdot>f\<cdot>(convex_join\<cdot>xss)"
by (induct xss rule: convex_pd_induct, simp_all)

lemma convex_map_approx: "convex_map\<cdot>(approx n)\<cdot>xs = approx n\<cdot>xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma ep_pair_convex_map: "ep_pair e p \<Longrightarrow> ep_pair (convex_map\<cdot>e) (convex_map\<cdot>p)"
apply default
apply (induct_tac x rule: convex_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: convex_pd_induct, simp_all add: ep_pair.e_p_below monofun_cfun)
done

lemma deflation_convex_map: "deflation d \<Longrightarrow> deflation (convex_map\<cdot>d)"
apply default
apply (induct_tac x rule: convex_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: convex_pd_induct, simp_all add: deflation.below monofun_cfun)
done


subsection {* Conversions to other powerdomains *}

text {* Convex to upper *}

lemma convex_le_imp_upper_le: "t \<le>\<natural> u \<Longrightarrow> t \<le>\<sharp> u"
unfolding convex_le_def by simp

definition
  convex_to_upper :: "'a convex_pd \<rightarrow> 'a upper_pd" where
  "convex_to_upper = convex_pd.basis_fun upper_principal"

lemma convex_to_upper_principal [simp]:
  "convex_to_upper\<cdot>(convex_principal t) = upper_principal t"
unfolding convex_to_upper_def
apply (rule convex_pd.basis_fun_principal)
apply (rule upper_pd.principal_mono)
apply (erule convex_le_imp_upper_le)
done

lemma convex_to_upper_unit [simp]:
  "convex_to_upper\<cdot>{x}\<natural> = {x}\<sharp>"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_to_upper_plus [simp]:
  "convex_to_upper\<cdot>(xs +\<natural> ys) = convex_to_upper\<cdot>xs +\<sharp> convex_to_upper\<cdot>ys"
by (induct xs ys rule: convex_pd.principal_induct2, simp, simp, simp)

lemma approx_convex_to_upper:
  "approx i\<cdot>(convex_to_upper\<cdot>xs) = convex_to_upper\<cdot>(approx i\<cdot>xs)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

lemma convex_to_upper_bind [simp]:
  "convex_to_upper\<cdot>(convex_bind\<cdot>xs\<cdot>f) =
    upper_bind\<cdot>(convex_to_upper\<cdot>xs)\<cdot>(convex_to_upper oo f)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

lemma convex_to_upper_map [simp]:
  "convex_to_upper\<cdot>(convex_map\<cdot>f\<cdot>xs) = upper_map\<cdot>f\<cdot>(convex_to_upper\<cdot>xs)"
by (simp add: convex_map_def upper_map_def cfcomp_LAM)

lemma convex_to_upper_join [simp]:
  "convex_to_upper\<cdot>(convex_join\<cdot>xss) =
    upper_bind\<cdot>(convex_to_upper\<cdot>xss)\<cdot>convex_to_upper"
by (simp add: convex_join_def upper_join_def cfcomp_LAM eta_cfun)

text {* Convex to lower *}

lemma convex_le_imp_lower_le: "t \<le>\<natural> u \<Longrightarrow> t \<le>\<flat> u"
unfolding convex_le_def by simp

definition
  convex_to_lower :: "'a convex_pd \<rightarrow> 'a lower_pd" where
  "convex_to_lower = convex_pd.basis_fun lower_principal"

lemma convex_to_lower_principal [simp]:
  "convex_to_lower\<cdot>(convex_principal t) = lower_principal t"
unfolding convex_to_lower_def
apply (rule convex_pd.basis_fun_principal)
apply (rule lower_pd.principal_mono)
apply (erule convex_le_imp_lower_le)
done

lemma convex_to_lower_unit [simp]:
  "convex_to_lower\<cdot>{x}\<natural> = {x}\<flat>"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_to_lower_plus [simp]:
  "convex_to_lower\<cdot>(xs +\<natural> ys) = convex_to_lower\<cdot>xs +\<flat> convex_to_lower\<cdot>ys"
by (induct xs ys rule: convex_pd.principal_induct2, simp, simp, simp)

lemma approx_convex_to_lower:
  "approx i\<cdot>(convex_to_lower\<cdot>xs) = convex_to_lower\<cdot>(approx i\<cdot>xs)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

lemma convex_to_lower_bind [simp]:
  "convex_to_lower\<cdot>(convex_bind\<cdot>xs\<cdot>f) =
    lower_bind\<cdot>(convex_to_lower\<cdot>xs)\<cdot>(convex_to_lower oo f)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

lemma convex_to_lower_map [simp]:
  "convex_to_lower\<cdot>(convex_map\<cdot>f\<cdot>xs) = lower_map\<cdot>f\<cdot>(convex_to_lower\<cdot>xs)"
by (simp add: convex_map_def lower_map_def cfcomp_LAM)

lemma convex_to_lower_join [simp]:
  "convex_to_lower\<cdot>(convex_join\<cdot>xss) =
    lower_bind\<cdot>(convex_to_lower\<cdot>xss)\<cdot>convex_to_lower"
by (simp add: convex_join_def lower_join_def cfcomp_LAM eta_cfun)

text {* Ordering property *}

lemma convex_pd_below_iff:
  "(xs \<sqsubseteq> ys) =
    (convex_to_upper\<cdot>xs \<sqsubseteq> convex_to_upper\<cdot>ys \<and>
     convex_to_lower\<cdot>xs \<sqsubseteq> convex_to_lower\<cdot>ys)"
 apply (safe elim!: monofun_cfun_arg)
 apply (rule profinite_below_ext)
 apply (drule_tac f="approx i" in monofun_cfun_arg)
 apply (drule_tac f="approx i" in monofun_cfun_arg)
 apply (cut_tac x="approx i\<cdot>xs" in convex_pd.compact_imp_principal, simp)
 apply (cut_tac x="approx i\<cdot>ys" in convex_pd.compact_imp_principal, simp)
 apply clarify
 apply (simp add: approx_convex_to_upper approx_convex_to_lower convex_le_def)
done

lemmas convex_plus_below_plus_iff =
  convex_pd_below_iff [where xs="xs +\<natural> ys" and ys="zs +\<natural> ws", standard]

lemmas convex_pd_below_simps =
  convex_unit_below_plus_iff
  convex_plus_below_unit_iff
  convex_plus_below_plus_iff
  convex_unit_below_iff
  convex_to_upper_unit
  convex_to_upper_plus
  convex_to_lower_unit
  convex_to_lower_plus
  upper_pd_below_simps
  lower_pd_below_simps

end
