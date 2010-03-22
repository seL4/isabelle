(*  Title:      HOL/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

structure Sledgehammer_Isar : sig end =
struct

open ATP_Manager
open ATP_Minimal

structure K = OuterKeyword and P = OuterParse

val _ =
  OuterSyntax.improper_command "atp_kill" "kill all managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill));

val _ =
  OuterSyntax.improper_command "atp_info" "print information about managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative info));

val _ =
  OuterSyntax.improper_command "atp_messages" "print recent messages issued by managed provers" K.diag
    (Scan.option (P.$$$ "(" |-- P.nat --| P.$$$ ")") >>
      (fn limit => Toplevel.no_timing o Toplevel.imperative (fn () => messages limit)));

val _ =
  OuterSyntax.improper_command "print_atps" "print external provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (print_provers o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "sledgehammer"
    "search for first-order proof using automatic theorem provers" K.diag
    (Scan.repeat P.xname >> (fn names => Toplevel.no_timing o Toplevel.unknown_proof o
      Toplevel.keep (sledgehammer names o Toplevel.proof_of)));

val default_minimize_prover = "remote_vampire"
val default_minimize_time_limit = 5

fun atp_minimize_command args thm_names state =
  let
    fun theorems_from_names ctxt =
      map (fn (name, interval) =>
              let
                val thmref = Facts.Named ((name, Position.none), interval)
                val ths = ProofContext.get_fact ctxt thmref
                val name' = Facts.string_of_ref thmref
              in (name', ths) end)
    fun get_time_limit_arg time_string =
      (case Int.fromString time_string of
        SOME t => t
      | NONE => error ("Invalid time limit: " ^ quote time_string))
    fun get_opt (name, a) (p, t) =
      (case name of
        "time" => (p, get_time_limit_arg a)
      | "atp" => (a, t)
      | n => error ("Invalid argument: " ^ n))
    fun get_options args =
      fold get_opt args (default_minimize_prover, default_minimize_time_limit)
    val (prover_name, time_limit) = get_options args
    val prover =
      (case ATP_Manager.get_prover (Proof.theory_of state) prover_name of
        SOME prover => prover
      | NONE => error ("Unknown prover: " ^ quote prover_name))
    val name_thms_pairs = theorems_from_names (Proof.context_of state) thm_names
  in
    writeln (#2 (minimize_theorems linear_minimize prover prover_name time_limit
                                   state name_thms_pairs))
  end

local structure K = OuterKeyword and P = OuterParse in

val parse_args =
  Scan.optional (Args.bracks (P.list (P.xname --| P.$$$ "=" -- P.xname))) []
val parse_thm_names = Scan.repeat (P.xname -- Scan.option Attrib.thm_sel)

val _ =
  OuterSyntax.improper_command "atp_minimize" "minimize theorem list with external prover" K.diag
    (parse_args -- parse_thm_names >> (fn (args, thm_names) =>
      Toplevel.no_timing o Toplevel.unknown_proof o
        Toplevel.keep (atp_minimize_command args thm_names o Toplevel.proof_of)))

end

end;
