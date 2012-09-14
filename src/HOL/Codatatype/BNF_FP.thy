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

lemma unit_all_impI: "(P () \<Longrightarrow> Q ()) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by simp

lemma prod_all_impI: "(\<And>x y. P (x, y) \<Longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by clarify

lemma prod_all_impI_step: "(\<And>x. \<forall>y. P (x, y) \<longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by auto

lemma all_unit_eq: "(\<And>x. PROP P x) \<equiv> PROP P ()"
by simp

lemma all_prod_eq: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a, b))"
by clarsimp

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

(* TODO: cleanup *)
lemma UN_compreh_bex:
"\<Union>{y. \<exists>x \<in> A. y = {}} = {}"
"\<Union>{y. \<exists>x \<in> A. y = {x}} = A"
"\<Union>{y. \<exists>x \<in> A. y = {f x}} = {y. \<exists>x \<in> A. y = f x}"
by blast+

lemma induct_set_step: "\<lbrakk>B \<in> A; c \<in> f B\<rbrakk> \<Longrightarrow> \<exists>C. (\<exists>a \<in> A. C = f a) \<and> c \<in> C"
apply (rule exI)
apply (rule conjI)
 apply (rule bexI)
  apply (rule refl)
 apply assumption
apply assumption
done

ML_file "Tools/bnf_fp_util.ML"
ML_file "Tools/bnf_fp_sugar_tactics.ML"
ML_file "Tools/bnf_fp_sugar.ML"

end
