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

end
