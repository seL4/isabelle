(*  Title:      HOL/Metis_Examples/HO_Reas.thy
    Author:     Jasmin Blanchette, TU Muenchen

Testing Metis's and Sledgehammer's higher-order reasoning capabilities.
*)

theory HO_Reas
imports Main
begin

sledgehammer_params [prover = e, blocking, isar_proof, timeout = 10]

lemma "id True"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "\<not> id False"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "x = id True \<or> x = id False"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id x = id True \<or> id x = id False"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "P True \<Longrightarrow> P False \<Longrightarrow> P x"
sledgehammer [expect = none] ()
sledgehammer [type_sys = tags, expect = some] ()
sledgehammer [full_types, type_sys = tags, expect = some] ()
by metisFT

lemma "id (\<not> a) \<Longrightarrow> \<not> id a"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> \<not> a) \<Longrightarrow> id a"
sledgehammer [expect = some] ()
sledgehammer [type_sys = tags, expect = some] ()
sledgehammer [full_types, type_sys = tags, expect = some] ()
by metis

lemma "id (\<not> (id (\<not> a))) \<Longrightarrow> id a"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id a"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<and> b) \<Longrightarrow> id b"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id b \<Longrightarrow> id (a \<and> b)"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id a \<Longrightarrow> id (a \<or> b)"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id b \<Longrightarrow> id (a \<or> b)"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (\<not> b) \<Longrightarrow> id (\<not> (a \<or> b))"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (\<not> a) \<Longrightarrow> id (a \<longrightarrow> b)"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

lemma "id (a \<longrightarrow> b) \<longleftrightarrow> id (\<not> a \<or> b)"
sledgehammer [expect = some] (id_apply)
sledgehammer [type_sys = tags, expect = some] (id_apply)
sledgehammer [full_types, type_sys = tags, expect = some] (id_apply)
by (metis id_apply)

end
