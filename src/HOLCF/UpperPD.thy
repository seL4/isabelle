(*  Title:      HOLCF/UpperPD.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Upper powerdomain *}

theory UpperPD
imports CompactBasis
begin

subsection {* Basis preorder *}

definition
  upper_le :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> bool" (infix "\<le>\<sharp>" 50) where
  "upper_le = (\<lambda>u v. \<forall>y\<in>Rep_pd_basis v. \<exists>x\<in>Rep_pd_basis u. compact_le x y)"

lemma upper_le_refl [simp]: "t \<le>\<sharp> t"
unfolding upper_le_def by (fast intro: compact_le_refl)

lemma upper_le_trans: "\<lbrakk>t \<le>\<sharp> u; u \<le>\<sharp> v\<rbrakk> \<Longrightarrow> t \<le>\<sharp> v"
unfolding upper_le_def
apply (rule ballI)
apply (drule (1) bspec, erule bexE)
apply (drule (1) bspec, erule bexE)
apply (erule rev_bexI)
apply (erule (1) compact_le_trans)
done

interpretation upper_le: preorder [upper_le]
by (rule preorder.intro, rule upper_le_refl, rule upper_le_trans)

lemma upper_le_minimal [simp]: "PDUnit compact_bot \<le>\<sharp> t"
unfolding upper_le_def Rep_PDUnit by simp

lemma PDUnit_upper_mono: "compact_le x y \<Longrightarrow> PDUnit x \<le>\<sharp> PDUnit y"
unfolding upper_le_def Rep_PDUnit by simp

lemma PDPlus_upper_mono: "\<lbrakk>s \<le>\<sharp> t; u \<le>\<sharp> v\<rbrakk> \<Longrightarrow> PDPlus s u \<le>\<sharp> PDPlus t v"
unfolding upper_le_def Rep_PDPlus by fast

lemma PDPlus_upper_less: "PDPlus t u \<le>\<sharp> t"
unfolding upper_le_def Rep_PDPlus by (fast intro: compact_le_refl)

lemma upper_le_PDUnit_PDUnit_iff [simp]:
  "(PDUnit a \<le>\<sharp> PDUnit b) = compact_le a b"
unfolding upper_le_def Rep_PDUnit by fast

lemma upper_le_PDPlus_PDUnit_iff:
  "(PDPlus t u \<le>\<sharp> PDUnit a) = (t \<le>\<sharp> PDUnit a \<or> u \<le>\<sharp> PDUnit a)"
unfolding upper_le_def Rep_PDPlus Rep_PDUnit by fast

lemma upper_le_PDPlus_iff: "(t \<le>\<sharp> PDPlus u v) = (t \<le>\<sharp> u \<and> t \<le>\<sharp> v)"
unfolding upper_le_def Rep_PDPlus by fast

lemma upper_le_induct [induct set: upper_le]:
  assumes le: "t \<le>\<sharp> u"
  assumes 1: "\<And>a b. compact_le a b \<Longrightarrow> P (PDUnit a) (PDUnit b)"
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

lemma approx_pd_upper_mono1:
  "i \<le> j \<Longrightarrow> approx_pd i t \<le>\<sharp> approx_pd j t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_approx_mono1)
apply (simp add: PDPlus_upper_mono)
done

lemma approx_pd_upper_le: "approx_pd i t \<le>\<sharp> t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_approx_le)
apply (simp add: PDPlus_upper_mono)
done

lemma approx_pd_upper_mono:
  "t \<le>\<sharp> u \<Longrightarrow> approx_pd n t \<le>\<sharp> approx_pd n u"
apply (erule upper_le_induct)
apply (simp add: compact_approx_mono)
apply (simp add: upper_le_PDPlus_PDUnit_iff)
apply (simp add: upper_le_PDPlus_iff)
done


subsection {* Type definition *}

cpodef (open) 'a upper_pd =
  "{S::'a::bifinite pd_basis set. upper_le.ideal S}"
apply (simp add: upper_le.adm_ideal)
apply (fast intro: upper_le.ideal_principal)
done

lemma ideal_Rep_upper_pd: "upper_le.ideal (Rep_upper_pd x)"
by (rule Rep_upper_pd [simplified])

definition
  upper_principal :: "'a pd_basis \<Rightarrow> 'a upper_pd" where
  "upper_principal t = Abs_upper_pd {u. u \<le>\<sharp> t}"

lemma Rep_upper_principal:
  "Rep_upper_pd (upper_principal t) = {u. u \<le>\<sharp> t}"
unfolding upper_principal_def
apply (rule Abs_upper_pd_inverse [simplified])
apply (rule upper_le.ideal_principal)
done

interpretation upper_pd:
  bifinite_basis [upper_le upper_principal Rep_upper_pd approx_pd]
apply unfold_locales
apply (rule ideal_Rep_upper_pd)
apply (rule cont_Rep_upper_pd)
apply (rule Rep_upper_principal)
apply (simp only: less_upper_pd_def less_set_def)
apply (rule approx_pd_upper_le)
apply (rule approx_pd_idem)
apply (erule approx_pd_upper_mono)
apply (rule approx_pd_upper_mono1, simp)
apply (rule finite_range_approx_pd)
apply (rule ex_approx_pd_eq)
done

lemma upper_principal_less_iff [simp]:
  "(upper_principal t \<sqsubseteq> upper_principal u) = (t \<le>\<sharp> u)"
unfolding less_upper_pd_def Rep_upper_principal less_set_def
by (fast intro: upper_le_refl elim: upper_le_trans)

lemma upper_principal_mono:
  "t \<le>\<sharp> u \<Longrightarrow> upper_principal t \<sqsubseteq> upper_principal u"
by (rule upper_pd.principal_mono)

lemma compact_upper_principal: "compact (upper_principal t)"
by (rule upper_pd.compact_principal)

lemma upper_pd_minimal: "upper_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: upper_pd.principal_induct, simp, simp)

instance upper_pd :: (bifinite) pcpo
by (intro_classes, fast intro: upper_pd_minimal)

lemma inst_upper_pd_pcpo: "\<bottom> = upper_principal (PDUnit compact_bot)"
by (rule upper_pd_minimal [THEN UU_I, symmetric])


subsection {* Approximation *}

instance upper_pd :: (bifinite) approx ..

defs (overloaded)
  approx_upper_pd_def:
    "approx \<equiv> (\<lambda>n. upper_pd.basis_fun (\<lambda>t. upper_principal (approx_pd n t)))"

lemma approx_upper_principal [simp]:
  "approx n\<cdot>(upper_principal t) = upper_principal (approx_pd n t)"
unfolding approx_upper_pd_def
apply (rule upper_pd.basis_fun_principal)
apply (erule upper_principal_mono [OF approx_pd_upper_mono])
done

lemma chain_approx_upper_pd:
  "chain (approx :: nat \<Rightarrow> 'a upper_pd \<rightarrow> 'a upper_pd)"
unfolding approx_upper_pd_def
by (rule upper_pd.chain_basis_fun_take)

lemma lub_approx_upper_pd:
  "(\<Squnion>i. approx i\<cdot>xs) = (xs::'a upper_pd)"
unfolding approx_upper_pd_def
by (rule upper_pd.lub_basis_fun_take)

lemma approx_upper_pd_idem:
  "approx n\<cdot>(approx n\<cdot>xs) = approx n\<cdot>(xs::'a upper_pd)"
apply (induct xs rule: upper_pd.principal_induct, simp)
apply (simp add: approx_pd_idem)
done

lemma approx_eq_upper_principal:
  "\<exists>t\<in>Rep_upper_pd xs. approx n\<cdot>xs = upper_principal (approx_pd n t)"
unfolding approx_upper_pd_def
by (rule upper_pd.basis_fun_take_eq_principal)

lemma finite_fixes_approx_upper_pd:
  "finite {xs::'a upper_pd. approx n\<cdot>xs = xs}"
unfolding approx_upper_pd_def
by (rule upper_pd.finite_fixes_basis_fun_take)

instance upper_pd :: (bifinite) bifinite
apply intro_classes
apply (simp add: chain_approx_upper_pd)
apply (rule lub_approx_upper_pd)
apply (rule approx_upper_pd_idem)
apply (rule finite_fixes_approx_upper_pd)
done

lemma compact_imp_upper_principal:
  "compact xs \<Longrightarrow> \<exists>t. xs = upper_principal t"
apply (drule bifinite_compact_eq_approx)
apply (erule exE)
apply (erule subst)
apply (cut_tac n=i and xs=xs in approx_eq_upper_principal)
apply fast
done

lemma upper_principal_induct:
  "\<lbrakk>adm P; \<And>t. P (upper_principal t)\<rbrakk> \<Longrightarrow> P xs"
apply (erule approx_induct, rename_tac xs)
apply (cut_tac n=n and xs=xs in approx_eq_upper_principal)
apply (clarify, simp)
done

lemma upper_principal_induct2:
  "\<lbrakk>\<And>ys. adm (\<lambda>xs. P xs ys); \<And>xs. adm (\<lambda>ys. P xs ys);
    \<And>t u. P (upper_principal t) (upper_principal u)\<rbrakk> \<Longrightarrow> P xs ys"
apply (rule_tac x=ys in spec)
apply (rule_tac xs=xs in upper_principal_induct, simp)
apply (rule allI, rename_tac ys)
apply (rule_tac xs=ys in upper_principal_induct, simp)
apply simp
done


subsection {* Monadic unit *}

definition
  upper_unit :: "'a \<rightarrow> 'a upper_pd" where
  "upper_unit = compact_basis.basis_fun (\<lambda>a. upper_principal (PDUnit a))"

lemma upper_unit_Rep_compact_basis [simp]:
  "upper_unit\<cdot>(Rep_compact_basis a) = upper_principal (PDUnit a)"
unfolding upper_unit_def
apply (rule compact_basis.basis_fun_principal)
apply (rule upper_principal_mono)
apply (erule PDUnit_upper_mono)
done

lemma upper_unit_strict [simp]: "upper_unit\<cdot>\<bottom> = \<bottom>"
unfolding inst_upper_pd_pcpo Rep_compact_bot [symmetric] by simp

lemma approx_upper_unit [simp]:
  "approx n\<cdot>(upper_unit\<cdot>x) = upper_unit\<cdot>(approx n\<cdot>x)"
apply (induct x rule: compact_basis_induct, simp)
apply (simp add: approx_Rep_compact_basis)
done

lemma upper_unit_less_iff [simp]:
  "(upper_unit\<cdot>x \<sqsubseteq> upper_unit\<cdot>y) = (x \<sqsubseteq> y)"
 apply (rule iffI)
  apply (rule bifinite_less_ext)
  apply (drule_tac f="approx i" in monofun_cfun_arg, simp)
  apply (cut_tac x="approx i\<cdot>x" in compact_imp_Rep_compact_basis, simp)
  apply (cut_tac x="approx i\<cdot>y" in compact_imp_Rep_compact_basis, simp)
  apply (clarify, simp add: compact_le_def)
 apply (erule monofun_cfun_arg)
done

lemma upper_unit_eq_iff [simp]:
  "(upper_unit\<cdot>x = upper_unit\<cdot>y) = (x = y)"
unfolding po_eq_conv by simp

lemma upper_unit_strict_iff [simp]: "(upper_unit\<cdot>x = \<bottom>) = (x = \<bottom>)"
unfolding upper_unit_strict [symmetric] by (rule upper_unit_eq_iff)

lemma compact_upper_unit_iff [simp]:
  "compact (upper_unit\<cdot>x) = compact x"
unfolding bifinite_compact_iff by simp


subsection {* Monadic plus *}

definition
  upper_plus :: "'a upper_pd \<rightarrow> 'a upper_pd \<rightarrow> 'a upper_pd" where
  "upper_plus = upper_pd.basis_fun (\<lambda>t. upper_pd.basis_fun (\<lambda>u.
      upper_principal (PDPlus t u)))"

abbreviation
  upper_add :: "'a upper_pd \<Rightarrow> 'a upper_pd \<Rightarrow> 'a upper_pd"
    (infixl "+\<sharp>" 65) where
  "xs +\<sharp> ys == upper_plus\<cdot>xs\<cdot>ys"

lemma upper_plus_principal [simp]:
  "upper_plus\<cdot>(upper_principal t)\<cdot>(upper_principal u) =
   upper_principal (PDPlus t u)"
unfolding upper_plus_def
by (simp add: upper_pd.basis_fun_principal
    upper_pd.basis_fun_mono PDPlus_upper_mono)

lemma approx_upper_plus [simp]:
  "approx n\<cdot>(upper_plus\<cdot>xs\<cdot>ys) = upper_plus\<cdot>(approx n\<cdot>xs)\<cdot>(approx n\<cdot>ys)"
by (induct xs ys rule: upper_principal_induct2, simp, simp, simp)

lemma upper_plus_commute: "upper_plus\<cdot>xs\<cdot>ys = upper_plus\<cdot>ys\<cdot>xs"
apply (induct xs ys rule: upper_principal_induct2, simp, simp)
apply (simp add: PDPlus_commute)
done

lemma upper_plus_assoc:
  "upper_plus\<cdot>(upper_plus\<cdot>xs\<cdot>ys)\<cdot>zs = upper_plus\<cdot>xs\<cdot>(upper_plus\<cdot>ys\<cdot>zs)"
apply (induct xs ys arbitrary: zs rule: upper_principal_induct2, simp, simp)
apply (rule_tac xs=zs in upper_principal_induct, simp)
apply (simp add: PDPlus_assoc)
done

lemma upper_plus_absorb: "upper_plus\<cdot>xs\<cdot>xs = xs"
apply (induct xs rule: upper_principal_induct, simp)
apply (simp add: PDPlus_absorb)
done

lemma upper_plus_less1: "upper_plus\<cdot>xs\<cdot>ys \<sqsubseteq> xs"
apply (induct xs ys rule: upper_principal_induct2, simp, simp)
apply (simp add: PDPlus_upper_less)
done

lemma upper_plus_less2: "upper_plus\<cdot>xs\<cdot>ys \<sqsubseteq> ys"
by (subst upper_plus_commute, rule upper_plus_less1)

lemma upper_plus_greatest: "\<lbrakk>xs \<sqsubseteq> ys; xs \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> xs \<sqsubseteq> upper_plus\<cdot>ys\<cdot>zs"
apply (subst upper_plus_absorb [of xs, symmetric])
apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma upper_less_plus_iff:
  "(xs \<sqsubseteq> upper_plus\<cdot>ys\<cdot>zs) = (xs \<sqsubseteq> ys \<and> xs \<sqsubseteq> zs)"
apply safe
apply (erule trans_less [OF _ upper_plus_less1])
apply (erule trans_less [OF _ upper_plus_less2])
apply (erule (1) upper_plus_greatest)
done

lemma upper_plus_strict1 [simp]: "upper_plus\<cdot>\<bottom>\<cdot>ys = \<bottom>"
by (rule UU_I, rule upper_plus_less1)

lemma upper_plus_strict2 [simp]: "upper_plus\<cdot>xs\<cdot>\<bottom> = \<bottom>"
by (rule UU_I, rule upper_plus_less2)

lemma upper_plus_less_unit_iff:
  "(upper_plus\<cdot>xs\<cdot>ys \<sqsubseteq> upper_unit\<cdot>z) =
    (xs \<sqsubseteq> upper_unit\<cdot>z \<or> ys \<sqsubseteq> upper_unit\<cdot>z)"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>xs \<sqsubseteq> f\<cdot>(upper_unit\<cdot>z) \<or> f\<cdot>ys \<sqsubseteq> f\<cdot>(upper_unit\<cdot>z))")
   apply (drule admD [rule_format], rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac xs="approx i\<cdot>xs" in compact_imp_upper_principal, simp)
    apply (cut_tac xs="approx i\<cdot>ys" in compact_imp_upper_principal, simp)
    apply (cut_tac x="approx i\<cdot>z" in compact_imp_Rep_compact_basis, simp)
    apply (clarify, simp add: upper_le_PDPlus_PDUnit_iff)
   apply simp
  apply simp
 apply (erule disjE)
  apply (erule trans_less [OF upper_plus_less1])
 apply (erule trans_less [OF upper_plus_less2])
done

lemmas upper_pd_less_simps =
  upper_unit_less_iff
  upper_less_plus_iff
  upper_plus_less_unit_iff


subsection {* Induction rules *}

lemma upper_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P (upper_unit\<cdot>x)"
  assumes insert:
    "\<And>x ys. \<lbrakk>P (upper_unit\<cdot>x); P ys\<rbrakk> \<Longrightarrow> P (upper_plus\<cdot>(upper_unit\<cdot>x)\<cdot>ys)"
  shows "P (xs::'a upper_pd)"
apply (induct xs rule: upper_principal_induct, rule P)
apply (induct_tac t rule: pd_basis_induct1)
apply (simp only: upper_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: upper_unit_Rep_compact_basis [symmetric]
                  upper_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma upper_pd_induct:
  assumes P: "adm P"
  assumes unit: "\<And>x. P (upper_unit\<cdot>x)"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (upper_plus\<cdot>xs\<cdot>ys)"
  shows "P (xs::'a upper_pd)"
apply (induct xs rule: upper_principal_induct, rule P)
apply (induct_tac t rule: pd_basis_induct)
apply (simp only: upper_unit_Rep_compact_basis [symmetric] unit)
apply (simp only: upper_plus_principal [symmetric] plus)
done


subsection {* Monadic bind *}

definition
  upper_bind_basis ::
  "'a pd_basis \<Rightarrow> ('a \<rightarrow> 'b upper_pd) \<rightarrow> 'b upper_pd" where
  "upper_bind_basis = fold_pd
    (\<lambda>a. \<Lambda> f. f\<cdot>(Rep_compact_basis a))
    (\<lambda>x y. \<Lambda> f. upper_plus\<cdot>(x\<cdot>f)\<cdot>(y\<cdot>f))"

lemma ACI_upper_bind: "ACIf (\<lambda>x y. \<Lambda> f. upper_plus\<cdot>(x\<cdot>f)\<cdot>(y\<cdot>f))"
apply unfold_locales
apply (simp add: upper_plus_commute)
apply (simp add: upper_plus_assoc)
apply (simp add: upper_plus_absorb eta_cfun)
done

lemma upper_bind_basis_simps [simp]:
  "upper_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "upper_bind_basis (PDPlus t u) =
    (\<Lambda> f. upper_plus\<cdot>(upper_bind_basis t\<cdot>f)\<cdot>(upper_bind_basis u\<cdot>f))"
unfolding upper_bind_basis_def
apply -
apply (rule ACIf.fold_pd_PDUnit [OF ACI_upper_bind])
apply (rule ACIf.fold_pd_PDPlus [OF ACI_upper_bind])
done

lemma upper_bind_basis_mono:
  "t \<le>\<sharp> u \<Longrightarrow> upper_bind_basis t \<sqsubseteq> upper_bind_basis u"
unfolding expand_cfun_less
apply (erule upper_le_induct, safe)
apply (simp add: compact_le_def monofun_cfun)
apply (simp add: trans_less [OF upper_plus_less1])
apply (simp add: upper_less_plus_iff)
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
  "upper_bind\<cdot>(upper_unit\<cdot>x)\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis_induct, simp, simp)

lemma upper_bind_plus [simp]:
  "upper_bind\<cdot>(upper_plus\<cdot>xs\<cdot>ys)\<cdot>f =
   upper_plus\<cdot>(upper_bind\<cdot>xs\<cdot>f)\<cdot>(upper_bind\<cdot>ys\<cdot>f)"
by (induct xs ys rule: upper_principal_induct2, simp, simp, simp)

lemma upper_bind_strict [simp]: "upper_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding upper_unit_strict [symmetric] by (rule upper_bind_unit)


subsection {* Map and join *}

definition
  upper_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a upper_pd \<rightarrow> 'b upper_pd" where
  "upper_map = (\<Lambda> f xs. upper_bind\<cdot>xs\<cdot>(\<Lambda> x. upper_unit\<cdot>(f\<cdot>x)))"

definition
  upper_join :: "'a upper_pd upper_pd \<rightarrow> 'a upper_pd" where
  "upper_join = (\<Lambda> xss. upper_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma upper_map_unit [simp]:
  "upper_map\<cdot>f\<cdot>(upper_unit\<cdot>x) = upper_unit\<cdot>(f\<cdot>x)"
unfolding upper_map_def by simp

lemma upper_map_plus [simp]:
  "upper_map\<cdot>f\<cdot>(upper_plus\<cdot>xs\<cdot>ys) =
   upper_plus\<cdot>(upper_map\<cdot>f\<cdot>xs)\<cdot>(upper_map\<cdot>f\<cdot>ys)"
unfolding upper_map_def by simp

lemma upper_join_unit [simp]:
  "upper_join\<cdot>(upper_unit\<cdot>xs) = xs"
unfolding upper_join_def by simp

lemma upper_join_plus [simp]:
  "upper_join\<cdot>(upper_plus\<cdot>xss\<cdot>yss) =
   upper_plus\<cdot>(upper_join\<cdot>xss)\<cdot>(upper_join\<cdot>yss)"
unfolding upper_join_def by simp

lemma upper_map_ident: "upper_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: upper_pd_induct, simp_all)

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

end
