(*  Title:      HOL/Metis_Examples/HO_Reas.thy
    Author:     Jasmin Blanchette, TU Muenchen

Testing Metis's and Sledgehammer's higher-order reasoning capabilities.
*)

theory HO_Reas
imports Main
begin

declare [[metis_new_skolemizer]]

sledgehammer_params [prover = e, blocking, timeout = 10]

lemma "id True"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "\<not> id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "x = id True \<or> x = id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id x = id True \<or> id x = id False"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "P True \<Longrightarrow> P False \<Longrightarrow> P x"
sledgehammer [type_sys = erased, expect = none] ()
sledgehammer [type_sys = args, expect = none] ()
sledgehammer [type_sys = tags!, expect = some] ()
sledgehammer [type_sys = tags?, expect = some] ()
sledgehammer [type_sys = tags, expect = some] ()
sledgehammer [type_sys = preds!, expect = some] ()
sledgehammer [type_sys = preds?, expect = some] ()
sledgehammer [type_sys = preds, expect = some] ()
sledgehammer [type_sys = mangled_preds!, expect = some] ()
sledgehammer [type_sys = mangled_preds?, expect = some] ()
sledgehammer [type_sys = mangled_preds, expect = some] ()
by metisFT

lemma "id (\<not> a) \<Longrightarrow> \<not> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> \<not> a) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> (id (\<not> a))) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id a"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id b"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id b \<Longrightarrow> id (a \<and> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id (a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id b \<Longrightarrow> id (a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (\<not> b) \<Longrightarrow> id (\<not> (a \<or> b))"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (a \<longrightarrow> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<longrightarrow> b) \<longleftrightarrow> id (\<not> a \<or> b)"
sledgehammer [type_sys = erased, expect = some] (id_apply)
sledgehammer [type_sys = tags!, expect = some] (id_apply)
sledgehammer [type_sys = tags?, expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [type_sys = preds!, expect = some] (id_apply)
sledgehammer [type_sys = preds?, expect = some] (id_apply)
sledgehammer [type_sys = preds, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds!, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds?, expect = some] (id_apply)
sledgehammer [type_sys = mangled_preds, expect = some] (id_apply)
by (metis id_apply)

end
