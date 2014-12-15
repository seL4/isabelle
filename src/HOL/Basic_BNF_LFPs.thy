(*  Title:      HOL/Basic_BNF_LFPs.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Registration of basic types as BNF least fixpoints (datatypes).
*)

theory Basic_BNF_LFPs
imports BNF_Least_Fixpoint
begin

definition xtor :: "'a \<Rightarrow> 'a" where
  "xtor x = x"

lemma xtor_map: "f (xtor x) = xtor (f x)"
  unfolding xtor_def by (rule refl)

lemma xtor_set: "f (xtor x) = f x"
  unfolding xtor_def by (rule refl)

lemma xtor_rel: "R (xtor x) (xtor y) = R x y"
  unfolding xtor_def by (rule refl)

lemma xtor_induct: "(\<And>x. P (xtor x)) \<Longrightarrow> P z"
  unfolding xtor_def by assumption

lemma xtor_xtor: "xtor (xtor x) = x"
  unfolding xtor_def by (rule refl)

lemmas xtor_inject = xtor_rel[of "op ="]

lemma xtor_rel_induct: "(\<And>x y. vimage2p id_bnf id_bnf R x y \<Longrightarrow> IR (xtor x) (xtor y)) \<Longrightarrow> R \<le> IR"
  unfolding xtor_def vimage2p_def id_bnf_def by default

lemma Inl_def_alt: "Inl \<equiv> (\<lambda>a. xtor (id_bnf (Inl a)))"
  unfolding xtor_def id_bnf_def by (rule reflexive)

lemma Inr_def_alt: "Inr \<equiv> (\<lambda>a. xtor (id_bnf (Inr a)))"
  unfolding xtor_def id_bnf_def by (rule reflexive)

lemma Pair_def_alt: "Pair \<equiv> (\<lambda>a b. xtor (id_bnf (a, b)))"
  unfolding xtor_def id_bnf_def by (rule reflexive)

definition ctor_rec :: "'a \<Rightarrow> 'a" where
  "ctor_rec x = x"

lemma ctor_rec: "g = id \<Longrightarrow> ctor_rec f (xtor x) = f ((id_bnf \<circ> g \<circ> id_bnf) x)"
  unfolding ctor_rec_def id_bnf_def xtor_def comp_def id_def by hypsubst (rule refl)

lemma ctor_rec_def_alt: "f = ctor_rec (f \<circ> id_bnf)"
  unfolding ctor_rec_def id_bnf_def comp_def by (rule refl)

lemma ctor_rec_o_map: "ctor_rec f \<circ> g = ctor_rec (f \<circ> (id_bnf \<circ> g \<circ> id_bnf))"
  unfolding ctor_rec_def id_bnf_def comp_def by (rule refl)

lemma eq_fst_iff: "a = fst p \<longleftrightarrow> (\<exists>b. p = (a, b))"
  by (cases p) auto

lemma eq_snd_iff: "b = snd p \<longleftrightarrow> (\<exists>a. p = (a, b))"
  by (cases p) auto

lemma ex_neg_all_pos: "((\<exists>x. P x) \<Longrightarrow> Q) \<equiv> (\<And>x. P x \<Longrightarrow> Q)"
  by default blast+

lemma hypsubst_in_prems: "(\<And>x. y = x \<Longrightarrow> z = f x \<Longrightarrow> P) \<equiv> (z = f y \<Longrightarrow> P)"
  by default blast+

lemma isl_map_sum:
  "isl (map_sum f g s) = isl s"
  by (cases s) simp_all

lemma map_sum_sel:
  "isl s \<Longrightarrow> projl (map_sum f g s) = f (projl s)"
  "\<not> isl s \<Longrightarrow> projr (map_sum f g s) = g (projr s)"
  by (case_tac [!] s) simp_all

lemma set_sum_sel:
  "isl s \<Longrightarrow> projl s \<in> setl s"
  "\<not> isl s \<Longrightarrow> projr s \<in> setr s"
  by (case_tac [!] s) (auto intro: setl.intros setr.intros)

lemma rel_sum_sel: "rel_sum R1 R2 a b = (isl a = isl b \<and>
  (isl a \<longrightarrow> isl b \<longrightarrow> R1 (projl a) (projl b)) \<and>
  (\<not> isl a \<longrightarrow> \<not> isl b \<longrightarrow> R2 (projr a) (projr b)))"
  by (cases a b rule: sum.exhaust[case_product sum.exhaust]) simp_all

lemma isl_transfer: "rel_fun (rel_sum A B) (op =) isl isl"
  unfolding rel_fun_def rel_sum_sel by simp

lemma rel_prod_sel: "rel_prod R1 R2 p q = (R1 (fst p) (fst q) \<and> R2 (snd p) (snd q))"
  by (force simp: rel_prod.simps elim: rel_prod.cases)

ML_file "Tools/BNF/bnf_lfp_basic_sugar.ML"

ML_file "~~/src/HOL/Tools/Old_Datatype/old_size.ML"

lemma size_bool[code]: "size (b\<Colon>bool) = 0"
  by (cases b) auto

declare prod.size[no_atp]

lemma size_nat[simp, code]: "size (n\<Colon>nat) = n"
  by (induct n) simp_all

hide_const (open) xtor ctor_rec

hide_fact (open)
  xtor_def xtor_map xtor_set xtor_rel xtor_induct xtor_xtor xtor_inject ctor_rec_def ctor_rec
  ctor_rec_def_alt ctor_rec_o_map xtor_rel_induct Inl_def_alt Inr_def_alt Pair_def_alt

end
