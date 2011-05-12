(*  Title:      HOL/Metis_Examples/HO_Reas.thy
    Author:     Jasmin Blanchette, TU Muenchen

Testing Metis's and Sledgehammer's higher-order reasoning capabilities.
*)

theory HO_Reas
imports Main
begin

declare [[metis_new_skolemizer]]

sledgehammer_params [prover = e, blocking, timeout = 10]

text {* Extensionality and set constants *}

lemma plus_1_not_0: "n + (1\<Colon>nat) \<noteq> 0"
by simp

definition inc :: "nat \<Rightarrow> nat" where
"inc x = x + 1"

lemma "inc \<noteq> (\<lambda>y. 0)"
sledgehammer [expect = some] (inc_def plus_1_not_0)
by (metis inc_def plus_1_not_0)

lemma "inc = (\<lambda>y. y + 1)"
sledgehammer [expect = some] (inc_def)
by (metis inc_def)

lemma "(\<lambda>y. y + 1) = inc"
sledgehammer [expect = some] (inc_def)
by (metis inc_def)

definition add_swap :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add_swap = (\<lambda>x y. y + x)"

lemma "add_swap m n = n + m"
sledgehammer [expect = some] (add_swap_def)
by (metis add_swap_def)

definition "A = {xs\<Colon>'a list. True}"

lemma "xs \<in> A"
sledgehammer [expect = some]
by (metis A_def Collect_def mem_def)

definition "B (y::int) \<equiv> y \<le> 0"
definition "C (y::int) \<equiv> y \<le> 1"

lemma int_le_0_imp_le_1: "x \<le> (0::int) \<Longrightarrow> x \<le> 1"
by linarith

lemma "B \<subseteq> C"
sledgehammer [type_sys = poly_args, max_relevant = 200, expect = some]
by (metis B_def C_def int_le_0_imp_le_1 predicate1I)


text {* Proxies for logical constants *}

lemma "id True"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "\<not> id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "x = id True \<or> x = id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id x = id True \<or> id x = id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "P True \<Longrightarrow> P False \<Longrightarrow> P x"
sledgehammer [type_sys = erased, expect = none] ()
sledgehammer [type_sys = poly_args, expect = none] ()
sledgehammer [type_sys = poly_tags!, expect = some] ()
sledgehammer [type_sys = poly_tags, expect = some] ()
sledgehammer [type_sys = poly_preds, expect = some] ()
sledgehammer [type_sys = mangled_preds!, expect = some] ()
sledgehammer [type_sys = mangled_preds?, expect = some] ()
sledgehammer [type_sys = mangled_preds, expect = some] ()
by metisFT

lemma "id (\<not> a) \<Longrightarrow> \<not> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> \<not> a) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> (id (\<not> a))) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id b"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id b \<Longrightarrow> id (a \<and> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id (a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id b \<Longrightarrow> id (a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (\<not> b) \<Longrightarrow> id (\<not> (a \<or> b))"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (a \<longrightarrow> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<longrightarrow> b) \<longleftrightarrow> id (\<not> a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags!, expect = some] (id_apply)
sledgehammer [type_sys = poly_tags, expect = some] (id_apply)
sledgehammer [type_sys = poly_preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

end
