(*  Title:      src/HOL/Metis_Example/Sledgehammer_Isar_Proofs.thy
    Author:     Martin Desharnais, MPI-INF Saarbruecken

Tests of proof reconstruction (a.k.a. preplay) in Sledgehammer.
*)
theory Sledgehammer_Isar_Proofs
  imports Main
begin

external_file \<open>Sledgehammer_Isar_Proofs.certs\<close>
declare [[smt_certificates = "Sledgehammer_Isar_Proofs.certs"]]
declare [[smt_read_only_certificates = true]]

sledgehammer_params [verit, isar_proof, minimize = false, slices = 1, compress = 1]

lemma
  fixes a b c :: int
  shows "a + b = c \<Longrightarrow> c - b = a"
  sledgehammer [expect = some_preplayed] ()
proof -
  assume a1: "a + b = c"
  have "c - b \<le> a \<or> c \<noteq> a + b"
    by force
  then have f2: "c - b \<le> a"
    using a1 by force
  have "a \<le> c - b \<or> c \<noteq> a + b"
    by force
  then have "a \<le> c - b"
    using a1 by force
  then have f3: "c - b \<le> a \<and> a \<le> c - b"
    using f2 by fastforce
  have "c - b = a \<or> \<not> c - b \<le> a \<or> \<not> a \<le> c - b"
    by auto
  then show ?thesis
    using f3 by meson
qed

end
