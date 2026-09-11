(*  Title:      src/HOL/Metis_Example/Sledgehammer_Isar_Proofs.thy
    Author:     Martin Desharnais, LMU Muenchen

Tests of proof reconstruction (a.k.a. preplay) in Sledgehammer.
*)
theory Sledgehammer_Isar_Proofs
  imports Main
begin

external_file \<open>Sledgehammer_Isar_Proofs.certs\<close>
declare [[smt_certificates = "Sledgehammer_Isar_Proofs.certs"]]
declare [[smt_read_only_certificates = true]]

sledgehammer_params [expect = some_preplayed, minimize = false, slices = 1, compress = 1]

lemma
  assumes "A \<or> B" and "A \<Longrightarrow> C" and "B \<Longrightarrow> C"
  shows "C"
  sledgehammer [cvc5] (assms)
  sledgehammer [e, type_enc = mono_native] (assms)
  sledgehammer [spass] (assms)
  sledgehammer [vampire, type_enc = mono_native] (assms)
  sledgehammer [verit] (assms)
  sledgehammer [zipperposition, type_enc = mono_native] (assms)
  sledgehammer [z3] (assms)
  using assms by satx

lemma "(if P then a else b) = (if \<not> P then b else a)"
  sledgehammer [cvc5] ()
  sledgehammer [e, type_enc = mono_native_fool] ()
  sledgehammer [spass] ()
  sledgehammer [vampire, type_enc = mono_native_fool] ()
  sledgehammer [verit] ()
  sledgehammer [zipperposition, type_enc = mono_native_fool] ()
  sledgehammer [z3] ()
  by metis

end
