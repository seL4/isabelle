(*  Title:      HOL/BNF_FP_Base.thy
    Author:     Lorenz Panny, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Shared fixed point operations on bounded natural functors.
*)

header {* Shared Fixed Point Operations on Bounded Natural Functors *}

theory BNF_FP_Base
imports BNF_Comp
begin

lemma mp_conj: "(P \<longrightarrow> Q) \<and> R \<Longrightarrow> P \<Longrightarrow> R \<and> Q"
by auto

lemma eq_sym_Unity_conv: "(x = (() = ())) = x"
by blast

lemma case_unit_Unity: "(case u of () \<Rightarrow> f) = f"
by (cases u) (hypsubst, rule unit.case)

lemma case_prod_Pair_iden: "(case p of (x, y) \<Rightarrow> (x, y)) = p"
by simp

lemma unit_all_impI: "(P () \<Longrightarrow> Q ()) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by simp

lemma prod_all_impI: "(\<And>x y. P (x, y) \<Longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by clarify

lemma prod_all_impI_step: "(\<And>x. \<forall>y. P (x, y) \<longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by auto

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

lemma ssubst_mem: "\<lbrakk>t = s; s \<in> X\<rbrakk> \<Longrightarrow> t \<in> X" by simp

lemma case_sum_step:
"case_sum (case_sum f' g') g (Inl p) = case_sum f' g' p"
"case_sum f (case_sum f' g') (Inr p) = case_sum f' g' p"
by auto

lemma one_pointE: "\<lbrakk>\<And>x. s = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by simp

lemma obj_one_pointE: "\<forall>x. s = x \<longrightarrow> P \<Longrightarrow> P"
by blast

lemma obj_sumE_f:
"\<lbrakk>\<forall>x. s = f (Inl x) \<longrightarrow> P; \<forall>x. s = f (Inr x) \<longrightarrow> P\<rbrakk> \<Longrightarrow> \<forall>x. s = f x \<longrightarrow> P"
by (rule allI) (metis sumE)

lemma obj_sumE: "\<lbrakk>\<forall>x. s = Inl x \<longrightarrow> P; \<forall>x. s = Inr x \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (cases s) auto

lemma case_sum_if:
"case_sum f g (if p then Inl x else Inr y) = (if p then f x else g y)"
by simp

lemma mem_UN_compreh_eq: "(z : \<Union>{y. \<exists>x\<in>A. y = F x}) = (\<exists>x\<in>A. z : F x)"
by blast

lemma UN_compreh_eq_eq:
"\<Union>{y. \<exists>x\<in>A. y = {}} = {}"
"\<Union>{y. \<exists>x\<in>A. y = {x}} = A"
by blast+

lemma Inl_Inr_False: "(Inl x = Inr y) = False"
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

lemma spec2: "\<forall>x y. P x y \<Longrightarrow> P x y"
by blast

lemma rewriteR_comp_comp: "\<lbrakk>g o h = r\<rbrakk> \<Longrightarrow> f o g o h = f o r"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteR_comp_comp2: "\<lbrakk>g o h = r1 o r2; f o r1 = l\<rbrakk> \<Longrightarrow> f o g o h = l o r2"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteL_comp_comp: "\<lbrakk>f o g = l\<rbrakk> \<Longrightarrow> f o (g o h) = l o h"
  unfolding comp_def fun_eq_iff by auto

lemma rewriteL_comp_comp2: "\<lbrakk>f o g = l1 o l2; l2 o h = r\<rbrakk> \<Longrightarrow> f o (g o h) = l1 o r"
  unfolding comp_def fun_eq_iff by auto

lemma convol_o: "<f, g> o h = <f o h, g o h>"
  unfolding convol_def by auto

lemma map_pair_o_convol: "map_pair h1 h2 o <f, g> = <h1 o f, h2 o g>"
  unfolding convol_def by auto

lemma map_pair_o_convol_id: "(map_pair f id \<circ> <id , g>) x = <id \<circ> f , g> x"
  unfolding map_pair_o_convol id_comp comp_id ..

lemma o_case_sum: "h o case_sum f g = case_sum (h o f) (h o g)"
  unfolding comp_def by (auto split: sum.splits)

lemma case_sum_o_sum_map: "case_sum f g o sum_map h1 h2 = case_sum (f o h1) (g o h2)"
  unfolding comp_def by (auto split: sum.splits)

lemma case_sum_o_sum_map_id: "(case_sum id g o sum_map f id) x = case_sum (f o id) g x"
  unfolding case_sum_o_sum_map id_comp comp_id ..

lemma fun_rel_def_butlast:
  "(fun_rel R (fun_rel S T)) f g = (\<forall>x y. R x y \<longrightarrow> (fun_rel S T) (f x) (g y))"
  unfolding fun_rel_def ..

lemma subst_eq_imp: "(\<forall>a b. a = b \<longrightarrow> P a b) \<equiv> (\<forall>a. P a a)"
  by auto

lemma eq_subset: "op = \<le> (\<lambda>a b. P a b \<or> a = b)"
  by auto

lemma eq_le_Grp_id_iff: "(op = \<le> Grp (Collect R) id) = (All R)"
  unfolding Grp_def id_apply by blast

lemma Grp_id_mono_subst: "(\<And>x y. Grp P id x y \<Longrightarrow> Grp Q id (f x) (f y)) \<equiv>
   (\<And>x. x \<in> P \<Longrightarrow> f x \<in> Q)"
  unfolding Grp_def by rule auto

ML_file "Tools/BNF/bnf_fp_util.ML"
ML_file "Tools/BNF/bnf_fp_def_sugar_tactics.ML"
ML_file "Tools/BNF/bnf_fp_def_sugar.ML"
ML_file "Tools/BNF/bnf_fp_n2m_tactics.ML"
ML_file "Tools/BNF/bnf_fp_n2m.ML"
ML_file "Tools/BNF/bnf_fp_n2m_sugar.ML"
 
end
