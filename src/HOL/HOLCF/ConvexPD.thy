(*  Title:      HOL/HOLCF/ConvexPD.thy
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
  "(PDUnit a \<le>\<natural> PDUnit b) = (a \<sqsubseteq> b)"
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


subsection {* Type definition *}

typedef (open) 'a convex_pd =
  "{S::'a pd_basis set. convex_le.ideal S}"
by (rule convex_le.ex_ideal)

type_notation (xsymbols) convex_pd ("('(_')\<natural>)")

instantiation convex_pd :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_convex_pd x \<subseteq> Rep_convex_pd y"

instance ..
end

instance convex_pd :: (bifinite) po
using type_definition_convex_pd below_convex_pd_def
by (rule convex_le.typedef_ideal_po)

instance convex_pd :: (bifinite) cpo
using type_definition_convex_pd below_convex_pd_def
by (rule convex_le.typedef_ideal_cpo)

definition
  convex_principal :: "'a pd_basis \<Rightarrow> 'a convex_pd" where
  "convex_principal t = Abs_convex_pd {u. u \<le>\<natural> t}"

interpretation convex_pd:
  ideal_completion convex_le convex_principal Rep_convex_pd
using type_definition_convex_pd below_convex_pd_def
using convex_principal_def pd_basis_countable
by (rule convex_le.typedef_ideal_completion)

text {* Convex powerdomain is pointed *}

lemma convex_pd_minimal: "convex_principal (PDUnit compact_bot) \<sqsubseteq> ys"
by (induct ys rule: convex_pd.principal_induct, simp, simp)

instance convex_pd :: (bifinite) pcpo
by intro_classes (fast intro: convex_pd_minimal)

lemma inst_convex_pd_pcpo: "\<bottom> = convex_principal (PDUnit compact_bot)"
by (rule convex_pd_minimal [THEN bottomI, symmetric])


subsection {* Monadic unit and plus *}

definition
  convex_unit :: "'a \<rightarrow> 'a convex_pd" where
  "convex_unit = compact_basis.extension (\<lambda>a. convex_principal (PDUnit a))"

definition
  convex_plus :: "'a convex_pd \<rightarrow> 'a convex_pd \<rightarrow> 'a convex_pd" where
  "convex_plus = convex_pd.extension (\<lambda>t. convex_pd.extension (\<lambda>u.
      convex_principal (PDPlus t u)))"

abbreviation
  convex_add :: "'a convex_pd \<Rightarrow> 'a convex_pd \<Rightarrow> 'a convex_pd"
    (infixl "\<union>\<natural>" 65) where
  "xs \<union>\<natural> ys == convex_plus\<cdot>xs\<cdot>ys"

syntax
  "_convex_pd" :: "args \<Rightarrow> logic" ("{_}\<natural>")

translations
  "{x,xs}\<natural>" == "{x}\<natural> \<union>\<natural> {xs}\<natural>"
  "{x}\<natural>" == "CONST convex_unit\<cdot>x"

lemma convex_unit_Rep_compact_basis [simp]:
  "{Rep_compact_basis a}\<natural> = convex_principal (PDUnit a)"
unfolding convex_unit_def
by (simp add: compact_basis.extension_principal PDUnit_convex_mono)

lemma convex_plus_principal [simp]:
  "convex_principal t \<union>\<natural> convex_principal u = convex_principal (PDPlus t u)"
unfolding convex_plus_def
by (simp add: convex_pd.extension_principal
    convex_pd.extension_mono PDPlus_convex_mono)

interpretation convex_add: semilattice convex_add proof
  fix xs ys zs :: "'a convex_pd"
  show "(xs \<union>\<natural> ys) \<union>\<natural> zs = xs \<union>\<natural> (ys \<union>\<natural> zs)"
    apply (induct xs rule: convex_pd.principal_induct, simp)
    apply (induct ys rule: convex_pd.principal_induct, simp)
    apply (induct zs rule: convex_pd.principal_induct, simp)
    apply (simp add: PDPlus_assoc)
    done
  show "xs \<union>\<natural> ys = ys \<union>\<natural> xs"
    apply (induct xs rule: convex_pd.principal_induct, simp)
    apply (induct ys rule: convex_pd.principal_induct, simp)
    apply (simp add: PDPlus_commute)
    done
  show "xs \<union>\<natural> xs = xs"
    apply (induct xs rule: convex_pd.principal_induct, simp)
    apply (simp add: PDPlus_absorb)
    done
qed

lemmas convex_plus_assoc = convex_add.assoc
lemmas convex_plus_commute = convex_add.commute
lemmas convex_plus_absorb = convex_add.idem
lemmas convex_plus_left_commute = convex_add.left_commute
lemmas convex_plus_left_absorb = convex_add.left_idem

text {* Useful for @{text "simp add: convex_plus_ac"} *}
lemmas convex_plus_ac =
  convex_plus_assoc convex_plus_commute convex_plus_left_commute

text {* Useful for @{text "simp only: convex_plus_aci"} *}
lemmas convex_plus_aci =
  convex_plus_ac convex_plus_absorb convex_plus_left_absorb

lemma convex_unit_below_plus_iff [simp]:
  "{x}\<natural> \<sqsubseteq> ys \<union>\<natural> zs \<longleftrightarrow> {x}\<natural> \<sqsubseteq> ys \<and> {x}\<natural> \<sqsubseteq> zs"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (induct ys rule: convex_pd.principal_induct, simp)
apply (induct zs rule: convex_pd.principal_induct, simp)
apply simp
done

lemma convex_plus_below_unit_iff [simp]:
  "xs \<union>\<natural> ys \<sqsubseteq> {z}\<natural> \<longleftrightarrow> xs \<sqsubseteq> {z}\<natural> \<and> ys \<sqsubseteq> {z}\<natural>"
apply (induct xs rule: convex_pd.principal_induct, simp)
apply (induct ys rule: convex_pd.principal_induct, simp)
apply (induct z rule: compact_basis.principal_induct, simp)
apply simp
done

lemma convex_unit_below_iff [simp]: "{x}\<natural> \<sqsubseteq> {y}\<natural> \<longleftrightarrow> x \<sqsubseteq> y"
apply (induct x rule: compact_basis.principal_induct, simp)
apply (induct y rule: compact_basis.principal_induct, simp)
apply simp
done

lemma convex_unit_eq_iff [simp]: "{x}\<natural> = {y}\<natural> \<longleftrightarrow> x = y"
unfolding po_eq_conv by simp

lemma convex_unit_strict [simp]: "{\<bottom>}\<natural> = \<bottom>"
using convex_unit_Rep_compact_basis [of compact_bot]
by (simp add: inst_convex_pd_pcpo)

lemma convex_unit_bottom_iff [simp]: "{x}\<natural> = \<bottom> \<longleftrightarrow> x = \<bottom>"
unfolding convex_unit_strict [symmetric] by (rule convex_unit_eq_iff)

lemma compact_convex_unit: "compact x \<Longrightarrow> compact {x}\<natural>"
by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_convex_unit_iff [simp]: "compact {x}\<natural> \<longleftrightarrow> compact x"
apply (safe elim!: compact_convex_unit)
apply (simp only: compact_def convex_unit_below_iff [symmetric])
apply (erule adm_subst [OF cont_Rep_cfun2])
done

lemma compact_convex_plus [simp]:
  "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs \<union>\<natural> ys)"
by (auto dest!: convex_pd.compact_imp_principal)


subsection {* Induction rules *}

lemma convex_pd_induct1:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<natural>"
  assumes insert: "\<And>x ys. \<lbrakk>P {x}\<natural>; P ys\<rbrakk> \<Longrightarrow> P ({x}\<natural> \<union>\<natural> ys)"
  shows "P (xs::'a convex_pd)"
apply (induct xs rule: convex_pd.principal_induct, rule P)
apply (induct_tac a rule: pd_basis_induct1)
apply (simp only: convex_unit_Rep_compact_basis [symmetric])
apply (rule unit)
apply (simp only: convex_unit_Rep_compact_basis [symmetric]
                  convex_plus_principal [symmetric])
apply (erule insert [OF unit])
done

lemma convex_pd_induct
  [case_names adm convex_unit convex_plus, induct type: convex_pd]:
  assumes P: "adm P"
  assumes unit: "\<And>x. P {x}\<natural>"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs \<union>\<natural> ys)"
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
    (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<natural> y\<cdot>f)"

lemma ACI_convex_bind:
  "class.ab_semigroup_idem_mult (\<lambda>x y. \<Lambda> f. x\<cdot>f \<union>\<natural> y\<cdot>f)"
apply unfold_locales
apply (simp add: convex_plus_assoc)
apply (simp add: convex_plus_commute)
apply (simp add: eta_cfun)
done

lemma convex_bind_basis_simps [simp]:
  "convex_bind_basis (PDUnit a) =
    (\<Lambda> f. f\<cdot>(Rep_compact_basis a))"
  "convex_bind_basis (PDPlus t u) =
    (\<Lambda> f. convex_bind_basis t\<cdot>f \<union>\<natural> convex_bind_basis u\<cdot>f)"
unfolding convex_bind_basis_def
apply -
apply (rule fold_pd_PDUnit [OF ACI_convex_bind])
apply (rule fold_pd_PDPlus [OF ACI_convex_bind])
done

lemma convex_bind_basis_mono:
  "t \<le>\<natural> u \<Longrightarrow> convex_bind_basis t \<sqsubseteq> convex_bind_basis u"
apply (erule convex_le_induct)
apply (erule (1) below_trans)
apply (simp add: monofun_LAM monofun_cfun)
apply (simp add: monofun_LAM monofun_cfun)
done

definition
  convex_bind :: "'a convex_pd \<rightarrow> ('a \<rightarrow> 'b convex_pd) \<rightarrow> 'b convex_pd" where
  "convex_bind = convex_pd.extension convex_bind_basis"

syntax
  "_convex_bind" :: "[logic, logic, logic] \<Rightarrow> logic"
    ("(3\<Union>\<natural>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<Union>\<natural>x\<in>xs. e" == "CONST convex_bind\<cdot>xs\<cdot>(\<Lambda> x. e)"

lemma convex_bind_principal [simp]:
  "convex_bind\<cdot>(convex_principal t) = convex_bind_basis t"
unfolding convex_bind_def
apply (rule convex_pd.extension_principal)
apply (erule convex_bind_basis_mono)
done

lemma convex_bind_unit [simp]:
  "convex_bind\<cdot>{x}\<natural>\<cdot>f = f\<cdot>x"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_bind_plus [simp]:
  "convex_bind\<cdot>(xs \<union>\<natural> ys)\<cdot>f = convex_bind\<cdot>xs\<cdot>f \<union>\<natural> convex_bind\<cdot>ys\<cdot>f"
by (induct xs rule: convex_pd.principal_induct, simp,
    induct ys rule: convex_pd.principal_induct, simp, simp)

lemma convex_bind_strict [simp]: "convex_bind\<cdot>\<bottom>\<cdot>f = f\<cdot>\<bottom>"
unfolding convex_unit_strict [symmetric] by (rule convex_bind_unit)

lemma convex_bind_bind:
  "convex_bind\<cdot>(convex_bind\<cdot>xs\<cdot>f)\<cdot>g =
    convex_bind\<cdot>xs\<cdot>(\<Lambda> x. convex_bind\<cdot>(f\<cdot>x)\<cdot>g)"
by (induct xs, simp_all)


subsection {* Map *}

definition
  convex_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a convex_pd \<rightarrow> 'b convex_pd" where
  "convex_map = (\<Lambda> f xs. convex_bind\<cdot>xs\<cdot>(\<Lambda> x. {f\<cdot>x}\<natural>))"

lemma convex_map_unit [simp]:
  "convex_map\<cdot>f\<cdot>{x}\<natural> = {f\<cdot>x}\<natural>"
unfolding convex_map_def by simp

lemma convex_map_plus [simp]:
  "convex_map\<cdot>f\<cdot>(xs \<union>\<natural> ys) = convex_map\<cdot>f\<cdot>xs \<union>\<natural> convex_map\<cdot>f\<cdot>ys"
unfolding convex_map_def by simp

lemma convex_map_bottom [simp]: "convex_map\<cdot>f\<cdot>\<bottom> = {f\<cdot>\<bottom>}\<natural>"
unfolding convex_map_def by simp

lemma convex_map_ident: "convex_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma convex_map_ID: "convex_map\<cdot>ID = ID"
by (simp add: cfun_eq_iff ID_def convex_map_ident)

lemma convex_map_map:
  "convex_map\<cdot>f\<cdot>(convex_map\<cdot>g\<cdot>xs) = convex_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
by (induct xs rule: convex_pd_induct, simp_all)

lemma convex_bind_map:
  "convex_bind\<cdot>(convex_map\<cdot>f\<cdot>xs)\<cdot>g = convex_bind\<cdot>xs\<cdot>(\<Lambda> x. g\<cdot>(f\<cdot>x))"
by (simp add: convex_map_def convex_bind_bind)

lemma convex_map_bind:
  "convex_map\<cdot>f\<cdot>(convex_bind\<cdot>xs\<cdot>g) = convex_bind\<cdot>xs\<cdot>(\<Lambda> x. convex_map\<cdot>f\<cdot>(g\<cdot>x))"
by (simp add: convex_map_def convex_bind_bind)

lemma ep_pair_convex_map: "ep_pair e p \<Longrightarrow> ep_pair (convex_map\<cdot>e) (convex_map\<cdot>p)"
apply default
apply (induct_tac x rule: convex_pd_induct, simp_all add: ep_pair.e_inverse)
apply (induct_tac y rule: convex_pd_induct)
apply (simp_all add: ep_pair.e_p_below monofun_cfun)
done

lemma deflation_convex_map: "deflation d \<Longrightarrow> deflation (convex_map\<cdot>d)"
apply default
apply (induct_tac x rule: convex_pd_induct, simp_all add: deflation.idem)
apply (induct_tac x rule: convex_pd_induct)
apply (simp_all add: deflation.below monofun_cfun)
done

(* FIXME: long proof! *)
lemma finite_deflation_convex_map:
  assumes "finite_deflation d" shows "finite_deflation (convex_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (convex_map\<cdot>d)" by (rule deflation_convex_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence *: "finite (convex_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite (range (\<lambda>xs. convex_map\<cdot>d\<cdot>xs))"
    apply (rule rev_finite_subset)
    apply clarsimp
    apply (induct_tac xs rule: convex_pd.principal_induct)
    apply (simp add: adm_mem_finite *)
    apply (rename_tac t, induct_tac t rule: pd_basis_induct)
    apply (simp only: convex_unit_Rep_compact_basis [symmetric] convex_map_unit)
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
    apply (simp only: convex_plus_principal [symmetric] convex_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  thus "finite {xs. convex_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

subsection {* Convex powerdomain is bifinite *}

lemma approx_chain_convex_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. convex_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP convex_map_ID finite_deflation_convex_map)

instance convex_pd :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> 'a convex_pd \<rightarrow> 'a convex_pd). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_convex_map)
qed

subsection {* Join *}

definition
  convex_join :: "'a convex_pd convex_pd \<rightarrow> 'a convex_pd" where
  "convex_join = (\<Lambda> xss. convex_bind\<cdot>xss\<cdot>(\<Lambda> xs. xs))"

lemma convex_join_unit [simp]:
  "convex_join\<cdot>{xs}\<natural> = xs"
unfolding convex_join_def by simp

lemma convex_join_plus [simp]:
  "convex_join\<cdot>(xss \<union>\<natural> yss) = convex_join\<cdot>xss \<union>\<natural> convex_join\<cdot>yss"
unfolding convex_join_def by simp

lemma convex_join_bottom [simp]: "convex_join\<cdot>\<bottom> = \<bottom>"
unfolding convex_join_def by simp

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


subsection {* Conversions to other powerdomains *}

text {* Convex to upper *}

lemma convex_le_imp_upper_le: "t \<le>\<natural> u \<Longrightarrow> t \<le>\<sharp> u"
unfolding convex_le_def by simp

definition
  convex_to_upper :: "'a convex_pd \<rightarrow> 'a upper_pd" where
  "convex_to_upper = convex_pd.extension upper_principal"

lemma convex_to_upper_principal [simp]:
  "convex_to_upper\<cdot>(convex_principal t) = upper_principal t"
unfolding convex_to_upper_def
apply (rule convex_pd.extension_principal)
apply (rule upper_pd.principal_mono)
apply (erule convex_le_imp_upper_le)
done

lemma convex_to_upper_unit [simp]:
  "convex_to_upper\<cdot>{x}\<natural> = {x}\<sharp>"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_to_upper_plus [simp]:
  "convex_to_upper\<cdot>(xs \<union>\<natural> ys) = convex_to_upper\<cdot>xs \<union>\<sharp> convex_to_upper\<cdot>ys"
by (induct xs rule: convex_pd.principal_induct, simp,
    induct ys rule: convex_pd.principal_induct, simp, simp)

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
  "convex_to_lower = convex_pd.extension lower_principal"

lemma convex_to_lower_principal [simp]:
  "convex_to_lower\<cdot>(convex_principal t) = lower_principal t"
unfolding convex_to_lower_def
apply (rule convex_pd.extension_principal)
apply (rule lower_pd.principal_mono)
apply (erule convex_le_imp_lower_le)
done

lemma convex_to_lower_unit [simp]:
  "convex_to_lower\<cdot>{x}\<natural> = {x}\<flat>"
by (induct x rule: compact_basis.principal_induct, simp, simp)

lemma convex_to_lower_plus [simp]:
  "convex_to_lower\<cdot>(xs \<union>\<natural> ys) = convex_to_lower\<cdot>xs \<union>\<flat> convex_to_lower\<cdot>ys"
by (induct xs rule: convex_pd.principal_induct, simp,
    induct ys rule: convex_pd.principal_induct, simp, simp)

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
apply (induct xs rule: convex_pd.principal_induct, simp)
apply (induct ys rule: convex_pd.principal_induct, simp)
apply (simp add: convex_le_def)
done

lemmas convex_plus_below_plus_iff =
  convex_pd_below_iff [where xs="xs \<union>\<natural> ys" and ys="zs \<union>\<natural> ws"]
  for xs ys zs ws

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
