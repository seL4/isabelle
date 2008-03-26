(*  Title:      HOLCF/ConvexPD.thy
    ID:         $Id$
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

interpretation convex_le: preorder [convex_le]
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

lemma approx_pd_convex_mono1:
  "i \<le> j \<Longrightarrow> approx_pd i t \<le>\<natural> approx_pd j t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_approx_mono1)
apply (simp add: PDPlus_convex_mono)
done

lemma approx_pd_convex_le: "approx_pd i t \<le>\<natural> t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_approx_le)
apply (simp add: PDPlus_convex_mono)
done

lemma approx_pd_convex_mono:
  "t \<le>\<natural> u \<Longrightarrow> approx_pd n t \<le>\<natural> approx_pd n u"
apply (erule convex_le_induct)
apply (erule (1) convex_le_trans)
apply (simp add: compact_approx_mono)
apply (simp add: PDPlus_convex_mono)
done


subsection {* Type definition *}

cpodef (open) 'a convex_pd =
  "{S::'a::profinite pd_basis set. convex_le.ideal S}"
apply (simp add: convex_le.adm_ideal)
apply (fast intro: convex_le.ideal_principal)
done

lemma ideal_Rep_convex_pd: "convex_le.ideal (Rep_convex_pd xs)"
by (rule Rep_convex_pd [simplified])

lemma Rep_convex_pd_mono: "xs \<sqsubseteq> ys \<Longrightarrow> Rep_convex_pd xs \<subseteq> Rep_convex_pd ys"
unfolding less_convex_pd_def less_set_def .


subsection {* Principal ideals *}

definition
  convex_principal :: "'a pd_basis \<Rightarrow> 'a convex_pd" where
  "convex_principal t = Abs_convex_pd {u. u \<le>\<natural> t}"

lemma Rep_convex_principal:
  "Rep_convex_pd (convex_principal t) = {u. u \<le>\<natural> t}"
unfolding convex_principal_def
apply (rule Abs_convex_pd_inverse [simplified])
apply (rule convex_le.ideal_principal)
done

interpretation convex_pd:
  bifinite_basis [convex_le approx_pd convex_principal Rep_convex_pd]
apply unfold_locales
apply (rule approx_pd_convex_le)
apply (rule approx_pd_idem)
apply (erule approx_pd_convex_mono)
apply (rule approx_pd_convex_mono1, simp)
apply (rule finite_range_approx_pd)
apply (rule ex_approx_pd_eq)
apply (rule ideal_Rep_convex_pd)
apply (rule cont_Rep_convex_pd)
apply (rule Rep_convex_principal)
apply (simp only: less_convex_pd_def less_set_def)
done

lemma convex_principal_less_iff [simp]:
  "(convex_principal t \<sqsubseteq> convex_principal u) = (t \<le>\<natural> u)"
unfolding less_convex_pd_def Rep_convex_principal less_set_def
by (fast intro: convex_le_refl elim: convex_le_trans)

lemma convex_principal_mono:
  "t \<le>\<natural> u \<Longrightarrow> convex_principal t \<sqsubseteq> convex_principal u"
by (rule convex_principal_less_iff [THEN iffD2])

lemma compact_convex_principal: "compact (convex_principal t)"
by (rule convex_pd.compact_principal)

lemma convex_pd_minimal: "convex_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: convex_pd.principal_induct, simp, simp)

instance convex_pd :: (bifinite) pcpo
by (intro_classes, fast intro: convex_pd_minimal)

lemma inst_convex_pd_pcpo: "\<bottom> = convex_principal (PDUnit compact_bot)"
by (rule convex_pd_minimal [THEN UU_I, symmetric])


subsection {* Approximation *}

instance convex_pd :: (profinite) approx ..

defs (overloaded)
  approx_convex_pd_def:
    "approx \<equiv> (\<lambda>n. convex_pd.basis_fun (\<lambda>t. convex_principal (approx_pd n t)))"

lemma approx_convex_principal [simp]:
  "approx n\<cdot>(convex_principal t) = convex_principal (approx_pd n t)"
unfolding approx_convex_pd_def
apply (rule convex_pd.basis_fun_principal)
apply (erule convex_principal_mono [OF approx_pd_convex_mono])
done

lemma chain_approx_convex_pd:
  "chain (approx :: nat \<Rightarrow> 'a convex_pd \<rightarrow> 'a convex_pd)"
unfolding approx_convex_pd_def
by (rule convex_pd.chain_basis_fun_take)

lemma lub_approx_convex_pd:
  "(\<Squnion>i. approx i\<cdot>xs) = (xs::'a convex_pd)"
unfolding approx_convex_pd_def
by (rule convex_pd.lub_basis_fun_take)

lemma approx_convex_pd_idem:
  "approx n\<cdot>(approx n\<cdot>xs) = approx n\<cdot>(xs::'a convex_pd)"
apply (induct xs rule: convex_pd.principal_induct, simp)
apply (simp add: approx_pd_idem)
done

lemma approx_eq_convex_principal:
  "\<exists>t\<in>Rep_convex_pd xs. approx n\<cdot>xs = convex_principal (approx_pd n t)"
unfolding approx_convex_pd_def
by (rule convex_pd.basis_fun_take_eq_principal)

lemma finite_fixes_approx_convex_pd:
  "finite {xs::'a convex_pd. approx n\<cdot>xs = xs}"
unfolding approx_convex_pd_def
by (rule convex_pd.finite_fixes_basis_fun_take)

instance convex_pd :: (profinite) profinite
apply intro_classes
apply (simp add: chain_approx_convex_pd)
apply (rule lub_approx_convex_pd)
apply (rule approx_convex_pd_idem)
apply (rule finite_fixes_approx_convex_pd)
done

instance convex_pd :: (bifinite) bifinite ..

lemma compact_imp_convex_principal:
  "compact xs \<Longrightarrow> \<exists>t. xs = convex_principal t"
apply (drule bifinite_compact_eq_approx)
apply (erule exE)
apply (erule subst)
apply (cut_tac n=i and xs=xs in approx_eq_convex_principal)
apply fast
done

lemma convex_principal_induct:
  "\<lbrakk>adm P; \<And>t. P (convex_principal t)\<rbrakk> \<Longrightarrow> P xs"
apply (erule approx_induct, rename_tac xs)
apply (cut_tac n=n and xs=xs in approx_eq_convex_principal)
apply (clarify, simp)
done

lemma convex_principal_induct2:
  "\<lbrakk>\<And>ys. adm (\<lambda>xs. P xs ys); \<And>xs. adm (\<lambda>ys. P xs ys);
    \<And>t u. P (convex_principal t) (convex_principal u)\<rbrakk> \<Longrightarrow> P xs ys"
apply (rule_tac x=ys in spec)
apply (rule_tac xs=xs in convex_principal_induct, simp)
apply (rule allI, rename_tac ys)
apply (rule_tac xs=ys in convex_principal_induct, simp)
apply simp
done


subsection {* Monadic unit *}

definition
  convex_unit :: "'a \<rightarrow> 'a convex_pd" where
  "convex_unit = compact_basis.basis_fun (\<lambda>a. convex_principal (PDUnit a))"

lemma convex_unit_Rep_compact_basis [simp]:
  "convex_unit\<cdot>(Rep_compact_basis a) = convex_principal (PDUnit a)"
unfolding convex_unit_def
apply (rule compact_basis.basis_fun_principal)
apply (rule convex_principal_mono)
apply (erule PDUnit_convex_mono)
done

lemma convex_unit_strict [simp]: "convex_unit\<cdot>\<bottom> = \<bottom>"
unfolding inst_convex_pd_pcpo Rep_compact_bot [symmetric] by simp

lemma approx_convex_unit [simp]:
  "approx n\<cdot>(convex_unit\<cdot>x) = convex_unit\<cdot>(approx n\<cdot>x)"
apply (induct x rule: compact_basis_induct, simp)
apply (simp add: approx_Rep_compact_basis)
done

lemma convex_unit_less_iff [simp]:
  "(convex_unit\<cdot>x \<sqsubseteq> convex_unit\<cdot>y) = (x \<sqsubseteq> y)"
 apply (rule iffI)
  apply (rule bifinite_less_ext)
  apply (drule_tac f="approx i" in monofun_cfun_arg, simp)
  apply (cut_tac x="approx i\<cdot>x" in compact_imp_Rep_compact_basis, simp)
  apply (cut_tac x="approx i\<cdot>y" in compact_imp_Rep_compact_basis, simp)
  apply (clarify, simp add: compact_le_def)
 apply (erule monofun_cfun_arg)
done

lemma convex_unit_eq_iff [simp]:
  "(convex_unit\<cdot>x = convex_unit\<cdot>y) = (x = y)"
unfolding po_eq_conv by simp

lemma convex_unit_strict_iff [simp]: "(convex_unit\<cdot>x = \<bottom>) = (x = \<bottom>)"
unfolding convex_unit_strict [symmetric] by (rule convex_unit_eq_iff)

lemma compact_convex_unit_iff [simp]:
  "compact (convex_unit\<cdot>x) = compact x"
unfolding bifinite_compact_iff by simp


subsection {* Monadic plus *}

definition
  convex_plus :: "'a convex_pd \<rightarrow> 'a convex_pd \<rightarrow> 'a convex_pd" where
  "convex_plus = convex_pd.basis_fun (\<lambda>t. convex_pd.basis_fun (\<lambda>u.
      convex_principal (PDPlus t u)))"

abbreviation
  convex_add :: "'a convex_pd \<Rightarrow> 'a convex_pd \<Rightarrow> 'a convex_pd"
    (infixl "+\<natural>" 65) where
  "xs +\<natural> ys == convex_plus\<cdot>xs\<cdot>ys"

lemma convex_plus_principal [simp]:
  "convex_plus\<cdot>(convex_principal t)\<cdot>(convex_principal u) =
   convex_principal (PDPlus t u)"
unfolding convex_plus_def
by (simp add: convex_pd.basis_fun_principal
    convex_pd.basis_fun_mono PDPlus_convex_mono)

lemma approx_convex_plus [simp]:
  "approx n\<cdot>(convex_plus\<cdot>xs\<cdot>ys) = convex_plus\<cdot>(approx n\<cdot>xs)\<cdot>(approx n\<cdot>ys)"
by (induct xs ys rule: convex_principal_induct2, simp, simp, simp)

lemma convex_plus_commute: "convex_plus\<cdot>xs\<cdot>ys = convex_plus\<cdot>ys\<cdot>xs"
apply (induct xs ys rule: convex_principal_induct2, simp, simp)
apply (simp add: PDPlus_commute)
done

lemma convex_plus_assoc:
  "convex_plus\<cdot>(convex_plus\<cdot>xs\<cdot>ys)\<cdot>zs = convex_plus\<cdot>xs\<cdot>(convex_plus\<cdot>ys\<cdot>zs)"
apply (induct xs ys arbitrary: zs rule: convex_principal_induct2, simp, simp)
apply (rule_tac xs=zs in convex_principal_induct, simp)
apply (simp add: PDPlus_assoc)
done

lemma convex_plus_absorb: "convex_plus\<cdot>xs\<cdot>xs = xs"
apply (induct xs rule: convex_principal_induct, simp)
apply (simp add: PDPlus_absorb)
done

lemma convex_unit_less_plus_iff [simp]:
  "(convex_unit\<cdot>x \<sqsubseteq> convex_plus\<cdot>ys\<cdot>zs) =
   (convex_unit\<cdot>x \<sqsubseteq> ys \<and> convex_unit\<cdot>x \<sqsubseteq> zs)"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>(convex_unit\<cdot>x) \<sqsubseteq> f\<cdot>ys \<and> f\<cdot>(convex_unit\<cdot>x) \<sqsubseteq> f\<cdot>zs)")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac x="approx i\<cdot>x" in compact_imp_Rep_compact_basis, simp)
    apply (cut_tac xs="approx i\<cdot>ys" in compact_imp_convex_principal, simp)
    apply (cut_tac xs="approx i\<cdot>zs" in compact_imp_convex_principal, simp)
    apply (clarify, simp)
   apply simp
  apply simp
 apply (erule conjE)
 apply (subst convex_plus_absorb [of "convex_unit\<cdot>x", symmetric])
 apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done

lemma convex_plus_less_unit_iff [simp]:
  "(convex_plus\<cdot>xs\<cdot>ys \<sqsubseteq> convex_unit\<cdot>z) =
   (xs \<sqsubseteq> convex_unit\<cdot>z \<and> ys \<sqsubseteq> convex_unit\<cdot>z)"
 apply (rule iffI)
  apply (subgoal_tac
    "adm (\<lambda>f. f\<cdot>xs \<sqsubseteq> f\<cdot>(convex_unit\<cdot>z) \<and> f\<cdot>ys \<sqsubseteq> f\<cdot>(convex_unit\<cdot>z))")
   apply (drule admD, rule chain_approx)
    apply (drule_tac f="approx i" in monofun_cfun_arg)
    apply (cut_tac xs="approx i\<cdot>xs" in compact_imp_convex_principal, simp)
    apply (cut_tac xs="approx i\<cdot>ys" in compact_imp_convex_principal, simp)
    apply (cut_tac x="approx i\<cdot>z" in compact_imp_Rep_compact_basis, simp)
    apply (clarify, simp)
   apply simp
  apply simp
 apply (erule conjE)
 apply (subst convex_plus_absorb [of "convex_unit\<cdot>z", symmetric])
 apply (erule (1) monofun_cfun [OF monofun_cfun_arg])
done


subsection {* Induction rules *}

lemma convex_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P (convex_unit\<cdot>x)"
  assumes insert:
    "\<And>x ys. \<lbrakk>P (convex_unit\<cdot>x); P ys\<rbrakk> \<Longrightarrow> P (convex_plus\<cdot>(convex_unit\<cdot>x)\<cdot>ys)"
  shows "P (xs::'a convex_pd)"
apply (induct xs rule: convex_principal_induct, rule P)
apply (induct_tac t rule: pd_basis_induct1)
apply (simp only: convex_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: convex_unit_Rep_compact_basis [symmetric]
                  convex_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma convex_pd_induct:
  assumes P: "adm P"
  assumes unit: "\<And>x. P (convex_unit\<cdot>x)"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (convex_plus\<cdot>xs\<cdot>ys)"
  shows "P (xs::'a convex_pd)"
apply (induct xs rule: convex_principal_induct, rule P)
apply (induct_tac t rule: pd_basis_induct)
apply (simp only: convex_unit_Rep_compact_basis [symmetric] unit)
apply (simp only: convex_plus_principal [symmetric] plus)
done


subsection {* Monadic bind *}

definition
  convex_bind_basis ::
  "'a pd_basis \<Rightarrow> ('a \<rightarrow> 'b convex_pd) \<rightarrow> 'b convex_pd" where
  "convex_bind_basis = fold_pd
    (\<lambda>a. \<Lambda> f. f\<cdot>(Rep_compact_basis a))
    (\<lambda>x y. \<Lambda> f. convex_plus\<cdot>(x\<cdot>f)\<cdot>(y\<cdot>f))"

lemma ACI_convex_bind: "ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. convex_plus\<cdot>(x\<cdot>f)\<cdot>(y\<cdot>f))"
apply unfold_locales
apply (simp add: convex_plus_assoc)
apply (simp add: convex_plus_commute)
apply (simp add: convex_plus_absorb eta_cfun)
done

lemma convex_bind_basis_simps [simp]:
  "convex_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "convex_bind_basis (PDPlus t u) =
    (\<Lambda> f. convex_plus\<cdot>(convex_bind_basis t\<cdot>f)\<cdot>(convex_bind_basis u\<cdot>f))"
unfolding convex_bind_basis_def
apply -
apply (rule ab_semigroup_idem_mult.fold_pd_PDUnit [OF ACI_convex_bind])
apply (rule ab_semigroup_idem_mult.fold_pd_PDPlus [OF ACI_convex_bind])
done

lemma monofun_LAM:
  "\<lbrakk>cont f; cont g; \<And>x. f x \<sqsubseteq> g x\<rbrakk> \<Longrightarrow> (\<Lambda> x. f x) \<sqsubseteq> (\<Lambda> x. g x)"
by (simp add: expand_cfun_less)

lemma convex_bind_basis_mono:
  "t \<le>\<natural> u \<Longrightarrow> convex_bind_basis t \<sqsubseteq> convex_bind_basis u"
apply (erule convex_le_induct)
apply (erule (1) trans_less)
apply (simp add: monofun_LAM compact_le_def monofun_cfun)
apply (simp add: monofun_LAM compact_le_def monofun_cfun)
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
  "convex_bind\<cdot>(convex_unit\<cdot>x)\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis_induct, simp, simp)

lemma convex_bind_plus [simp]:
  "convex_bind\<cdot>(convex_plus\<cdot>xs\<cdot>ys)\<cdot>f =
   convex_plus\<cdot>(convex_bind\<cdot>xs\<cdot>f)\<cdot>(convex_bind\<cdot>ys\<cdot>f)"
by (induct xs ys rule: convex_principal_induct2, simp, simp, simp)

lemma convex_bind_strict [simp]: "convex_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding convex_unit_strict [symmetric] by (rule convex_bind_unit)


subsection {* Map and join *}

definition
  convex_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a convex_pd \<rightarrow> 'b convex_pd" where
  "convex_map = (\<Lambda> f xs. convex_bind\<cdot>xs\<cdot>(\<Lambda> x. convex_unit\<cdot>(f\<cdot>x)))"

definition
  convex_join :: "'a convex_pd convex_pd \<rightarrow> 'a convex_pd" where
  "convex_join = (\<Lambda> xss. convex_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma convex_map_unit [simp]:
  "convex_map\<cdot>f\<cdot>(convex_unit\<cdot>x) = convex_unit\<cdot>(f\<cdot>x)"
unfolding convex_map_def by simp

lemma convex_map_plus [simp]:
  "convex_map\<cdot>f\<cdot>(convex_plus\<cdot>xs\<cdot>ys) =
   convex_plus\<cdot>(convex_map\<cdot>f\<cdot>xs)\<cdot>(convex_map\<cdot>f\<cdot>ys)"
unfolding convex_map_def by simp

lemma convex_join_unit [simp]:
  "convex_join\<cdot>(convex_unit\<cdot>xs) = xs"
unfolding convex_join_def by simp

lemma convex_join_plus [simp]:
  "convex_join\<cdot>(convex_plus\<cdot>xss\<cdot>yss) =
   convex_plus\<cdot>(convex_join\<cdot>xss)\<cdot>(convex_join\<cdot>yss)"
unfolding convex_join_def by simp

lemma convex_map_ident: "convex_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: convex_pd_induct, simp_all)

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
apply (rule upper_principal_mono)
apply (erule convex_le_imp_upper_le)
done

lemma convex_to_upper_unit [simp]:
  "convex_to_upper\<cdot>(convex_unit\<cdot>x) = upper_unit\<cdot>x"
by (induct x rule: compact_basis_induct, simp, simp)

lemma convex_to_upper_plus [simp]:
  "convex_to_upper\<cdot>(convex_plus\<cdot>xs\<cdot>ys) =
   upper_plus\<cdot>(convex_to_upper\<cdot>xs)\<cdot>(convex_to_upper\<cdot>ys)"
by (induct xs ys rule: convex_principal_induct2, simp, simp, simp)

lemma approx_convex_to_upper:
  "approx i\<cdot>(convex_to_upper\<cdot>xs) = convex_to_upper\<cdot>(approx i\<cdot>xs)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

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
apply (rule lower_principal_mono)
apply (erule convex_le_imp_lower_le)
done

lemma convex_to_lower_unit [simp]:
  "convex_to_lower\<cdot>(convex_unit\<cdot>x) = lower_unit\<cdot>x"
by (induct x rule: compact_basis_induct, simp, simp)

lemma convex_to_lower_plus [simp]:
  "convex_to_lower\<cdot>(convex_plus\<cdot>xs\<cdot>ys) =
   lower_plus\<cdot>(convex_to_lower\<cdot>xs)\<cdot>(convex_to_lower\<cdot>ys)"
by (induct xs ys rule: convex_principal_induct2, simp, simp, simp)

lemma approx_convex_to_lower:
  "approx i\<cdot>(convex_to_lower\<cdot>xs) = convex_to_lower\<cdot>(approx i\<cdot>xs)"
by (induct xs rule: convex_pd_induct, simp, simp, simp)

text {* Ordering property *}

lemma convex_pd_less_iff:
  "(xs \<sqsubseteq> ys) =
    (convex_to_upper\<cdot>xs \<sqsubseteq> convex_to_upper\<cdot>ys \<and>
     convex_to_lower\<cdot>xs \<sqsubseteq> convex_to_lower\<cdot>ys)"
 apply (safe elim!: monofun_cfun_arg)
 apply (rule bifinite_less_ext)
 apply (drule_tac f="approx i" in monofun_cfun_arg)
 apply (drule_tac f="approx i" in monofun_cfun_arg)
 apply (cut_tac xs="approx i\<cdot>xs" in compact_imp_convex_principal, simp)
 apply (cut_tac xs="approx i\<cdot>ys" in compact_imp_convex_principal, simp)
 apply clarify
 apply (simp add: approx_convex_to_upper approx_convex_to_lower convex_le_def)
done

end
