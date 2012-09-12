(*  Title:      HOL/Codatatype/BNF_FP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

header {* Composition of Bounded Natural Functors *}

theory BNF_FP
imports BNF_Comp BNF_Wrap
keywords
  "defaults"
begin

lemma case_unit: "(case u of () => f) = f"
by (cases u) (hypsubst, rule unit.cases)

(* FIXME: needed? *)
lemma all_unit_eq: "(\<And>x. PROP P x) \<equiv> PROP P ()" by simp

(* FIXME: needed? *)
lemma all_prod_eq: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a, b))" by clarsimp

(* FIXME: needed? *)
lemma False_imp_eq: "(False \<Longrightarrow> P) \<equiv> Trueprop True"
by presburger

(* FIXME: needed? *)
lemma all_point_1: "(\<And>z. z = b \<Longrightarrow> phi z) \<equiv> Trueprop (phi b)"
by presburger

lemma rev_bspec: "a \<in> A \<Longrightarrow> \<forall>z \<in> A. P z \<Longrightarrow> P a"
by simp

lemma Un_cong: "\<lbrakk>A = B; C = D\<rbrakk> \<Longrightarrow> A \<union> C = B \<union> D"
by simp

definition convol ("<_ , _>") where
"<f , g> \<equiv> %a. (f a, g a)"

lemma fst_convol:
"fst o <f , g> = f"
apply(rule ext)
unfolding convol_def by simp

lemma snd_convol:
"snd o <f , g> = g"
apply(rule ext)
unfolding convol_def by simp

lemma pointfree_idE: "f o g = id \<Longrightarrow> f (g x) = x"
unfolding o_def fun_eq_iff by simp

lemma o_bij:
  assumes gf: "g o f = id" and fg: "f o g = id"
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

lemma obj_sumE_f':
"\<lbrakk>\<forall>x. s = f (Inl x) \<longrightarrow> P; \<forall>x. s = f (Inr x) \<longrightarrow> P\<rbrakk> \<Longrightarrow> s = f x \<longrightarrow> P"
by (cases x) blast+

lemma obj_sumE_f:
"\<lbrakk>\<forall>x. s = f (Inl x) \<longrightarrow> P; \<forall>x. s = f (Inr x) \<longrightarrow> P\<rbrakk> \<Longrightarrow> \<forall>x. s = f x \<longrightarrow> P"
by (rule allI) (rule obj_sumE_f')

lemma obj_sumE: "\<lbrakk>\<forall>x. s = Inl x \<longrightarrow> P; \<forall>x. s = Inr x \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (cases s) auto

lemma obj_sum_step':
"\<lbrakk>\<forall>x. s = f (Inr (Inl x)) \<longrightarrow> P; \<forall>x. s = f (Inr (Inr x)) \<longrightarrow> P\<rbrakk> \<Longrightarrow> s = f (Inr x) \<longrightarrow> P"
by (cases x) blast+

lemma obj_sum_step:
"\<lbrakk>\<forall>x. s = f (Inr (Inl x)) \<longrightarrow> P; \<forall>x. s = f (Inr (Inr x)) \<longrightarrow> P\<rbrakk> \<Longrightarrow> \<forall>x. s = f (Inr x) \<longrightarrow> P"
by (rule allI) (rule obj_sum_step')

lemma sum_case_if:
"sum_case f g (if p then Inl x else Inr y) = (if p then f x else g y)"
by simp

ML_file "Tools/bnf_fp_util.ML"
ML_file "Tools/bnf_fp_sugar_tactics.ML"
ML_file "Tools/bnf_fp_sugar.ML"

end
