(*  Title:      HOL/Tools/ATP_Manager/atp_manager.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Central manager component for ATP threads.
*)

signature ATP_MANAGER =
sig
  type cnf_thm = Clausifier.cnf_thm
  type name_pool = Metis_Clauses.name_pool
  type relevance_override = Sledgehammer_Fact_Filter.relevance_override
  type minimize_command = Sledgehammer_Proof_Reconstruct.minimize_command
  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     atps: string list,
     full_types: bool,
     explicit_apply: bool,
     relevance_threshold: real,
     relevance_convergence: real,
     theory_relevant: bool option,
     defs_relevant: bool,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time,
     minimize_timeout: Time.time}
  type problem =
    {subgoal: int,
     goal: Proof.context * (thm list * thm),
     relevance_override: relevance_override,
     axiom_clauses: cnf_thm list option,
     filtered_clauses: cnf_thm list option}
  datatype failure =
    Unprovable | IncompleteUnprovable | TimedOut | OutOfResources | OldSpass |
    MalformedInput | MalformedOutput | UnknownError
  type prover_result =
    {outcome: failure option,
     message: string,
     pool: name_pool option,
     relevant_thm_names: string list,
     atp_run_time_in_msecs: int,
     output: string,
     proof: string,
     internal_thm_names: string Vector.vector,
     conjecture_shape: int list list,
     filtered_clauses: cnf_thm list}
  type prover =
    params -> minimize_command -> Time.time -> problem -> prover_result

  val kill_atps: unit -> unit
  val running_atps: unit -> unit
  val messages: int option -> unit
  val add_prover: string * prover -> theory -> theory
  val get_prover: theory -> string -> prover
  val available_atps: theory -> unit
  val start_prover_thread :
    params -> int -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> string -> unit
end;

structure ATP_Manager : ATP_MANAGER =
struct

open Metis_Clauses
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct

(** The Sledgehammer **)

fun kill_atps () = Async_Manager.kill_threads "ATPs"
fun running_atps () = Async_Manager.running_threads "ATPs"
val messages = Async_Manager.thread_messages "ATP"

(** problems, results, provers, etc. **)

type params =
  {debug: bool,
   verbose: bool,
   overlord: bool,
   atps: string list,
   full_types: bool,
   explicit_apply: bool,
   relevance_threshold: real,
   relevance_convergence: real,
   theory_relevant: bool option,
   defs_relevant: bool,
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time,
   minimize_timeout: Time.time}

type problem =
  {subgoal: int,
   goal: Proof.context * (thm list * thm),
   relevance_override: relevance_override,
   axiom_clauses: cnf_thm list option,
   filtered_clauses: cnf_thm list option}

datatype failure =
  Unprovable | IncompleteUnprovable | TimedOut | OutOfResources | OldSpass |
  MalformedInput | MalformedOutput | UnknownError

type prover_result =
  {outcome: failure option,
   message: string,
   pool: name_pool option,
   relevant_thm_names: string list,
   atp_run_time_in_msecs: int,
   output: string,
   proof: string,
   internal_thm_names: string Vector.vector,
   conjecture_shape: int list list,
   filtered_clauses: cnf_thm list}

type prover =
  params -> minimize_command -> Time.time -> problem -> prover_result

(* named provers *)

structure Data = Theory_Data
(
  type T = (prover * stamp) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
);

fun add_prover (name, prover) thy =
  Data.map (Symtab.update_new (name, (prover, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")

fun get_prover thy name =
  the (Symtab.lookup (Data.get thy) name) |> fst
  handle Option.Option => error ("Unknown ATP: " ^ name ^ ".")

fun available_atps thy =
  priority ("Available ATPs: " ^
            commas (sort_strings (Symtab.keys (Data.get thy))) ^ ".")


(* start prover thread *)

fun start_prover_thread (params as {verbose, full_types, timeout, ...}) i n
                        relevance_override minimize_command proof_state name =
  let
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val prover = get_prover (Proof.theory_of proof_state) name
    val {context = ctxt, facts, goal} = Proof.goal proof_state;
    val desc =
      "ATP " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
      Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));
  in
    Async_Manager.launch "Sledgehammer" verbose birth_time death_time desc
        (fn () =>
            let
              val problem =
                {subgoal = i, goal = (ctxt, (facts, goal)),
                 relevance_override = relevance_override, axiom_clauses = NONE,
                 filtered_clauses = NONE}
            in
              prover params (minimize_command name) timeout problem |> #message
              handle TRIVIAL () => metis_line full_types i n []
                   | ERROR message => "Error: " ^ message ^ "\n"
            end)
  end

end;
