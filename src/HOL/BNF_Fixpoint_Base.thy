(*  Title:      HOL/BNF_Fixpoint_Base.thy
    Author:     Lorenz Panny, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013, 2014

Shared fixpoint operations on bounded natural functors.
*)

header {* Shared Fixpoint Operations on Bounded Natural Functors *}

theory BNF_Fixpoint_Base
imports BNF_Composition Basic_BNFs
begin

lemma False_imp_eq_True: "(False \<Longrightarrow> Q) \<equiv> Trueprop True"
  by default simp_all

lemma conj_imp_eq_imp_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)"
  by default simp_all

lemma mp_conj: "(P \<longrightarrow> Q) \<and> R \<Longrightarrow> P \<Longrightarrow> R \<and> Q"
  by auto

lemma predicate2D_conj: "P \<le> Q \<and> R \<Longrightarrow> P x y \<Longrightarrow> R \<and> Q x y"
  by auto

lemma eq_sym_Unity_conv: "(x = (() = ())) = x"
  by blast

lemma case_unit_Unity: "(case u of () \<Rightarrow> f) = f"
  by (cases u) (hypsubst, rule unit.case)

lemma case_prod_Pair_iden: "(case p of (x, y) \<Rightarrow> (x, y)) = p"
  by simp

lemma unit_all_impI: "(P () \<Longrightarrow> Q ()) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
  by simp

lemma pointfree_idE: "f \<circ> g = id \<Longrightarrow> f (g x) = x"
  unfolding comp_def fun_eq_iff by simp

lemma o_bij:
  assumes gf: "g \<circ> f = id" and fg: "f \<circ> g = id"
  shows "bij f"
unfolding bij_def inj_on_def surj_def proof safe
  fix a1 a2 assume "f a1 = f a2"
  hence "g ( f a1) = g (f a2)" by simp
  thus "a1 = a2" using gf unfolding fun_eq_iff by simp
next
  fix b
  have "b = f (g b)"
  using fg unfolding fun_eq_iff by simp
  thus "EX a. b = f a" by blast
qed

lemma ssubst_mem: "\<lbrakk>t = s; s \<in> X\<rbrakk> \<Longrightarrow> t \<in> X"
  by simp

lemma case_sum_step:
  "case_sum (case_sum f' g') g (Inl p) = case_sum f' g' p"
  "case_sum f (case_sum f' g') (Inr p) = case_sum f' g' p"
  by auto

lemma obj_one_pointE: "\<forall>x. s = x \<longrightarrow> P \<Longrightarrow> P"
  by blast

lemma type_copy_obj_one_point_absE:
  assumes "type_definition Rep Abs UNIV" "\<forall>x. s = Abs x \<longrightarrow> P" shows P
  using type_definition.Rep_inverse[OF assms(1)]
  by (intro mp[OF spec[OF assms(2), of "Rep s"]]) simp

lemma obj_sumE_f:
  assumes "\<forall>x. s = f (Inl x) \<longrightarrow> P" "\<forall>x. s = f (Inr x) \<longrightarrow> P"
  shows "\<forall>x. s = f x \<longrightarrow> P"
proof
  fix x from assms show "s = f x \<longrightarrow> P" by (cases x) auto
qed

lemma case_sum_if:
  "case_sum f g (if p then Inl x else Inr y) = (if p then f x else g y)"
  by simp

lemma prod_set_simps:
  "fsts (x, y) = {x}"
  "snds (x, y) = {y}"
  unfolding fsts_def snds_def by simp+

lemma sum_set_simps:
  "setl (Inl x) = {x}"
  "setl (Inr x) = {}"
  "setr (Inl x) = {}"
  "setr (Inr x) = {x}"
  unfolding sum_set_defs by simp+

lemma Inl_Inr_False: "(Inl x = Inr y) = False"
  by simp

lemma Inr_Inl_False: "(Inr x = Inl y) = False"
  by simp

lemma spec2: "\<forall>x y. P x y \<Longrightarrow> P x y"
  by blast

lemma rewriteR_comp_comp: "\<lbrakk>g \<circ> h = r\<rbrakk> \<Longrightarrow> f \<circ> g \<circ> h = f \<circ> r"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteR_comp_comp2: "\<lbrakk>g \<circ> h = r1 \<circ> r2; f \<circ> r1 = l\<rbrakk> \<Longrightarrow> f \<circ> g \<circ> h = l \<circ> r2"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteL_comp_comp: "\<lbrakk>f \<circ> g = l\<rbrakk> \<Longrightarrow> f \<circ> (g \<circ> h) = l \<circ> h"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteL_comp_comp2: "\<lbrakk>f \<circ> g = l1 \<circ> l2; l2 \<circ> h = r\<rbrakk> \<Longrightarrow> f \<circ> (g \<circ> h) = l1 \<circ> r"
  unfolding comp_def fun_eq_iff by auto

lemma convol_o: "\<langle>f, g\<rangle> \<circ> h = \<langle>f \<circ> h, g \<circ> h\<rangle>"
  unfolding convol_def by auto

lemma map_prod_o_convol: "map_prod h1 h2 \<circ> \<langle>f, g\<rangle> = \<langle>h1 \<circ> f, h2 \<circ> g\<rangle>"
  unfolding convol_def by auto

lemma map_prod_o_convol_id: "(map_prod f id \<circ> \<langle>id, g\<rangle>) x = \<langle>id \<circ> f, g\<rangle> x"
  unfolding map_prod_o_convol id_comp comp_id ..

lemma o_case_sum: "h \<circ> case_sum f g = case_sum (h \<circ> f) (h \<circ> g)"
  unfolding comp_def by (auto split: sum.splits)

lemma case_sum_o_map_sum: "case_sum f g \<circ> map_sum h1 h2 = case_sum (f \<circ> h1) (g \<circ> h2)"
  unfolding comp_def by (auto split: sum.splits)

lemma case_sum_o_map_sum_id: "(case_sum id g \<circ> map_sum f id) x = case_sum (f \<circ> id) g x"
  unfolding case_sum_o_map_sum id_comp comp_id ..

lemma rel_fun_def_butlast:
  "rel_fun R (rel_fun S T) f g = (\<forall>x y. R x y \<longrightarrow> (rel_fun S T) (f x) (g y))"
  unfolding rel_fun_def ..

lemma subst_eq_imp: "(\<forall>a b. a = b \<longrightarrow> P a b) \<equiv> (\<forall>a. P a a)"
  by auto

lemma eq_subset: "op = \<le> (\<lambda>a b. P a b \<or> a = b)"
  by auto

lemma eq_le_Grp_id_iff: "(op = \<le> Grp (Collect R) id) = (All R)"
  unfolding Grp_def id_apply by blast

lemma Grp_id_mono_subst: "(\<And>x y. Grp P id x y \<Longrightarrow> Grp Q id (f x) (f y)) \<equiv>
   (\<And>x. x \<in> P \<Longrightarrow> f x \<in> Q)"
  unfolding Grp_def by rule auto

lemma vimage2p_mono: "vimage2p f g R x y \<Longrightarrow> R \<le> S \<Longrightarrow> vimage2p f g S x y"
  unfolding vimage2p_def by blast

lemma vimage2p_refl: "(\<And>x. R x x) \<Longrightarrow> vimage2p f f R x x"
  unfolding vimage2p_def by auto

lemma
  assumes "type_definition Rep Abs UNIV"
  shows type_copy_Rep_o_Abs: "Rep \<circ> Abs = id" and type_copy_Abs_o_Rep: "Abs \<circ> Rep = id"
  unfolding fun_eq_iff comp_apply id_apply
    type_definition.Abs_inverse[OF assms UNIV_I] type_definition.Rep_inverse[OF assms] by simp_all

lemma type_copy_map_comp0_undo:
  assumes "type_definition Rep Abs UNIV"
          "type_definition Rep' Abs' UNIV"
          "type_definition Rep'' Abs'' UNIV"
  shows "Abs' \<circ> M \<circ> Rep'' = (Abs' \<circ> M1 \<circ> Rep) \<circ> (Abs \<circ> M2 \<circ> Rep'') \<Longrightarrow> M1 \<circ> M2 = M"
  by (rule sym) (auto simp: fun_eq_iff type_definition.Abs_inject[OF assms(2) UNIV_I UNIV_I]
    type_definition.Abs_inverse[OF assms(1) UNIV_I]
    type_definition.Abs_inverse[OF assms(3) UNIV_I] dest: spec[of _ "Abs'' x" for x])

lemma vimage2p_id: "vimage2p id id R = R"
  unfolding vimage2p_def by auto

lemma vimage2p_comp: "vimage2p (f1 \<circ> f2) (g1 \<circ> g2) = vimage2p f2 g2 \<circ> vimage2p f1 g1"
  unfolding fun_eq_iff vimage2p_def o_apply by simp

lemma vimage2p_rel_fun: "rel_fun (vimage2p f g R) R f g"
  unfolding rel_fun_def vimage2p_def by auto

lemma fun_cong_unused_0: "f = (\<lambda>x. g) \<Longrightarrow> f (\<lambda>x. 0) = g"
  by (erule arg_cong)

lemma inj_on_convol_ident: "inj_on (\<lambda>x. (x, f x)) X"
  unfolding inj_on_def by simp

lemma case_prod_app: "case_prod f x y = case_prod (\<lambda>l r. f l r y) x"
  by (case_tac x) simp

lemma case_sum_map_sum: "case_sum l r (map_sum f g x) = case_sum (l \<circ> f) (r \<circ> g) x"
  by (case_tac x) simp+

lemma case_sum_transfer:
  "rel_fun (rel_fun R T) (rel_fun (rel_fun S T) (rel_fun (rel_sum R S) T)) case_sum case_sum"
  unfolding rel_fun_def rel_sum_def by (auto split: sum.splits)

lemma case_prod_map_prod: "case_prod h (map_prod f g x) = case_prod (\<lambda>l r. h (f l) (g r)) x"
  by (case_tac x) simp+

lemma case_prod_transfer:
  "(rel_fun (rel_fun A (rel_fun B C)) (rel_fun (rel_prod A B) C)) case_prod case_prod"
  unfolding rel_fun_def rel_prod_def by simp

lemma prod_inj_map: "inj f \<Longrightarrow> inj g \<Longrightarrow> inj (map_prod f g)"
  by (simp add: inj_on_def)

lemma eq_ifI: "(P \<longrightarrow> t = u1) \<Longrightarrow> (\<not> P \<longrightarrow> t = u2) \<Longrightarrow> t = (if P then u1 else u2)"
  by simp

lemma comp_transfer:
  "rel_fun (rel_fun B C) (rel_fun (rel_fun A B) (rel_fun A C)) (op \<circ>) (op \<circ>)"
  unfolding rel_fun_def by simp

lemma If_transfer: "rel_fun (op =) (rel_fun A (rel_fun A A)) If If"
  unfolding rel_fun_def by simp

lemma Abs_transfer:
  assumes type_copy1: "type_definition Rep1 Abs1 UNIV"
  assumes type_copy2: "type_definition Rep2 Abs2 UNIV"
  shows "rel_fun R (vimage2p Rep1 Rep2 R) Abs1 Abs2"
  unfolding vimage2p_def rel_fun_def
    type_definition.Abs_inverse[OF type_copy1 UNIV_I]
    type_definition.Abs_inverse[OF type_copy2 UNIV_I] by simp

lemma Inl_transfer:
  "rel_fun S (rel_sum S T) Inl Inl"
  by auto

lemma Inr_transfer:
  "rel_fun T (rel_sum S T) Inr Inr"
  by auto

lemma Pair_transfer: "rel_fun A (rel_fun B (rel_prod A B)) Pair Pair"
  unfolding rel_fun_def rel_prod_def by simp

ML_file "Tools/BNF/bnf_fp_util.ML"
ML_file "Tools/BNF/bnf_fp_def_sugar_tactics.ML"
ML_file "Tools/BNF/bnf_fp_def_sugar.ML"
ML_file "Tools/BNF/bnf_fp_n2m_tactics.ML"
ML_file "Tools/BNF/bnf_fp_n2m.ML"
ML_file "Tools/BNF/bnf_fp_n2m_sugar.ML"

end
