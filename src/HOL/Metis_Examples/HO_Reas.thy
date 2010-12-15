(*  Title:      HOL/Metis_Examples/HO_Reas.thy
    Author:     Jasmin Blanchette, TU Muenchen

Testing Metis's and Sledgehammer's higher-order reasoning capabilities.
*)

theory HO_Reas
imports Main
begin

sledgehammer_params [prover = e, blocking, isar_proof, timeout = 10]

hide_const id
definition id where "id (x::bool) = x"

lemma "id True"
sledgehammer [expect = some] (add: id_def)
by (metis id_def)

lemma "\<not> id False"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "x = id True \<or> x = id False"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id x = id True \<or> id x = id False"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "P True \<Longrightarrow> P False \<Longrightarrow> P x"
sledgehammer [expect = none] ()
sledgehammer [full_types, expect = some] ()
by metisFT

lemma "id (\<not> a) \<Longrightarrow> \<not> id a"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (\<not> \<not> a) \<Longrightarrow> id a"
sledgehammer [expect = some] ()
by metis

lemma "id (\<not> (id (\<not> a))) \<Longrightarrow> id a"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (a \<and> b) \<Longrightarrow> id a"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (a \<and> b) \<Longrightarrow> id b"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id a \<Longrightarrow> id b \<Longrightarrow> id (a \<and> b)"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id a \<Longrightarrow> id (a \<or> b)"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id b \<Longrightarrow> id (a \<or> b)"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (\<not> a) \<Longrightarrow> id (\<not> b) \<Longrightarrow> id (\<not> (a \<or> b))"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (\<not> a) \<Longrightarrow> id (a \<longrightarrow> b)"
sledgehammer [expect = some] (id_def)
by (metis id_def)

lemma "id (a \<longrightarrow> b) \<longleftrightarrow> id (\<not> a \<or> b)"
sledgehammer [expect = some] (id_def)
by (metis id_def)

end
