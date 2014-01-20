(*  Title:      HOL/BNF_FP_Base.thy
    Author:     Lorenz Panny, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Shared fixed point operations on bounded natural functors.
*)

header {* Shared Fixed Point Operations on Bounded Natural Functors *}

theory BNF_FP_Base
imports Nitpick BNF_Comp Ctr_Sugar
begin

lemma mp_conj: "(P \<longrightarrow> Q) \<and> R \<Longrightarrow> P \<Longrightarrow> R \<and> Q"
by auto

lemma eq_sym_Unity_conv: "(x = (() = ())) = x"
by blast

lemma unit_case_Unity: "(case u of () \<Rightarrow> f) = f"
by (cases u) (hypsubst, rule unit.cases)

lemma prod_case_Pair_iden: "(case p of (x, y) \<Rightarrow> (x, y)) = p"
by simp

lemma unit_all_impI: "(P () \<Longrightarrow> Q ()) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by simp

lemma prod_all_impI: "(\<And>x y. P (x, y) \<Longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by clarify

lemma prod_all_impI_step: "(\<And>x. \<forall>y. P (x, y) \<longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by auto

lemma pointfree_idE: "f \<circ> g = id \<Longrightarrow> f (g x) = x"
unfolding o_def fun_eq_iff by simp

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

lemma sum_case_step:
"sum_case (sum_case f' g') g (Inl p) = sum_case f' g' p"
"sum_case f (sum_case f' g') (Inr p) = sum_case f' g' p"
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

lemma sum_case_if:
"sum_case f g (if p then Inl x else Inr y) = (if p then f x else g y)"
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

lemma prod_rel_simp:
"prod_rel P Q (x, y) (x', y') \<longleftrightarrow> P x x' \<and> Q y y'"
unfolding prod_rel_def by simp

lemma sum_rel_simps:
"sum_rel P Q (Inl x) (Inl x') \<longleftrightarrow> P x x'"
"sum_rel P Q (Inr y) (Inr y') \<longleftrightarrow> Q y y'"
"sum_rel P Q (Inl x) (Inr y') \<longleftrightarrow> False"
"sum_rel P Q (Inr y) (Inl x') \<longleftrightarrow> False"
unfolding sum_rel_def by simp+

lemma spec2: "\<forall>x y. P x y \<Longrightarrow> P x y"
by blast

lemma rewriteR_comp_comp: "\<lbrakk>g o h = r\<rbrakk> \<Longrightarrow> f o g o h = f o r"
  unfolding o_def fun_eq_iff by auto

lemma rewriteR_comp_comp2: "\<lbrakk>g o h = r1 o r2; f o r1 = l\<rbrakk> \<Longrightarrow> f o g o h = l o r2"
  unfolding o_def fun_eq_iff by auto

lemma rewriteL_comp_comp: "\<lbrakk>f o g = l\<rbrakk> \<Longrightarrow> f o (g o h) = l o h"
  unfolding o_def fun_eq_iff by auto

lemma rewriteL_comp_comp2: "\<lbrakk>f o g = l1 o l2; l2 o h = r\<rbrakk> \<Longrightarrow> f o (g o h) = l1 o r"
  unfolding o_def fun_eq_iff by auto

lemma convol_o: "<f, g> o h = <f o h, g o h>"
  unfolding convol_def by auto

lemma map_pair_o_convol: "map_pair h1 h2 o <f, g> = <h1 o f, h2 o g>"
  unfolding convol_def by auto

lemma map_pair_o_convol_id: "(map_pair f id \<circ> <id , g>) x = <id \<circ> f , g> x"
  unfolding map_pair_o_convol id_o o_id ..

lemma o_sum_case: "h o sum_case f g = sum_case (h o f) (h o g)"
  unfolding o_def by (auto split: sum.splits)

lemma sum_case_o_sum_map: "sum_case f g o sum_map h1 h2 = sum_case (f o h1) (g o h2)"
  unfolding o_def by (auto split: sum.splits)

lemma sum_case_o_sum_map_id: "(sum_case id g o sum_map f id) x = sum_case (f o id) g x"
  unfolding sum_case_o_sum_map id_o o_id ..

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
ML_file "Tools/BNF/bnf_fp_rec_sugar_util.ML"

end
