(*  Title:      HOL/Tools/ATP_Manager/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  datatype failure =
    Unprovable | IncompleteUnprovable | CantConnect | TimedOut |
    OutOfResources | OldSpass | MalformedInput | MalformedOutput | UnknownError

  type prover_config =
    {executable: string * string,
     required_executables: (string * string) list,
     arguments: bool -> Time.time -> string,
     proof_delims: (string * string) list,
     known_failures: (failure * string) list,
     max_new_relevant_facts_per_iter: int,
     prefers_theory_relevant: bool,
     explicit_forall: bool}

  val add_prover: string * prover_config -> theory -> theory
  val get_prover: theory -> string -> prover_config
  val available_atps: theory -> unit
  val refresh_systems_on_tptp : unit -> unit
  val default_atps_param_value : unit -> string
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

(* prover configuration *)

datatype failure =
  Unprovable | IncompleteUnprovable | CantConnect | TimedOut | OutOfResources |
  OldSpass | MalformedInput | MalformedOutput | UnknownError

type prover_config =
  {executable: string * string,
   required_executables: (string * string) list,
   arguments: bool -> Time.time -> string,
   proof_delims: (string * string) list,
   known_failures: (failure * string) list,
   max_new_relevant_facts_per_iter: int,
   prefers_theory_relevant: bool,
   explicit_forall: bool}


(* named provers *)

structure Data = Theory_Data
(
  type T = (prover_config * stamp) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
)

fun add_prover (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")

fun get_prover thy name =
  the (Symtab.lookup (Data.get thy) name) |> fst
  handle Option.Option => error ("Unknown ATP: " ^ name ^ ".")

fun available_atps thy =
  priority ("Available ATPs: " ^
            commas (sort_strings (Symtab.keys (Data.get thy))) ^ ".")

fun available_atps thy =
  priority ("Available ATPs: " ^
            commas (sort_strings (Symtab.keys (Data.get thy))) ^ ".")

fun to_generous_secs time = (Time.toMilliseconds time + 999) div 1000

(* E prover *)

val tstp_proof_delims =
  ("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation")

val e_config : prover_config =
  {executable = ("E_HOME", "eproof"),
   required_executables = [],
   arguments = fn _ => fn timeout =>
     "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent --cpu-limit=" ^
     string_of_int (to_generous_secs timeout),
   proof_delims = [tstp_proof_delims],
   known_failures =
     [(Unprovable, "SZS status: CounterSatisfiable"),
      (Unprovable, "SZS status CounterSatisfiable"),
      (TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded"),
      (OutOfResources,
       "# Cannot determine problem status within resource limit"),
      (OutOfResources, "SZS status: ResourceOut"),
      (OutOfResources, "SZS status ResourceOut")],
   max_new_relevant_facts_per_iter = 80 (* FIXME *),
   prefers_theory_relevant = false,
   explicit_forall = false}
val e = ("e", e_config)


(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : prover_config =
  {executable = ("ISABELLE_ATP_MANAGER", "scripts/spass"),
   required_executables = [("SPASS_HOME", "SPASS")],
   (* "div 2" accounts for the fact that SPASS is often run twice. *)
   arguments = fn complete => fn timeout =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^
      string_of_int (to_generous_secs timeout div 2))
     |> not complete ? prefix "-SOS=1 ",
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     [(IncompleteUnprovable, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (OldSpass, "tptp2dfg")],
   max_new_relevant_facts_per_iter = 26 (* FIXME *),
   prefers_theory_relevant = true,
   explicit_forall = true}
val spass = ("spass", spass_config)

(* Vampire *)

val vampire_config : prover_config =
  {executable = ("VAMPIRE_HOME", "vampire"),
   required_executables = [],
   arguments = fn _ => fn timeout =>
     "--mode casc -t " ^ string_of_int (to_generous_secs timeout) ^
     " --input_file ",
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation"),
      ("% SZS output start Proof", "% SZS output end Proof")],
   known_failures =
     [(Unprovable, "UNPROVABLE"),
      (IncompleteUnprovable, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (OutOfResources, "Refutation not found")],
   max_new_relevant_facts_per_iter = 40 (* FIXME *),
   prefers_theory_relevant = false,
   explicit_forall = false}
val vampire = ("vampire", vampire_config)

(* Remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([]: string list)

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP_MANAGER/scripts/remote_atp\" -w" of
    (answer, 0) => split_lines answer
  | (answer, _) =>
    error ("Failed to get available systems at SystemOnTPTP:\n" ^
           perhaps (try (unsuffix "\n")) answer)

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  (if null systems then get_systems () else systems)
  |> `(find_first (String.isPrefix prefix)));

fun the_system prefix =
  (case get_system prefix of
    NONE => error ("System " ^ quote prefix ^ " not available at SystemOnTPTP.")
  | SOME sys => sys);

val remote_known_failures =
  [(CantConnect, "HTTP-Error"),
   (TimedOut, "says Timeout"),
   (MalformedOutput, "Remote script could not extract proof")]

fun remote_config atp_prefix
        ({proof_delims, known_failures, max_new_relevant_facts_per_iter,
          prefers_theory_relevant, explicit_forall, ...} : prover_config)
        : prover_config =
  {executable = ("ISABELLE_ATP_MANAGER", "scripts/remote_atp"),
   required_executables = [],
   arguments = fn _ => fn timeout =>
     " -t " ^ string_of_int (to_generous_secs timeout) ^ " -s " ^
     the_system atp_prefix,
   proof_delims = insert (op =) tstp_proof_delims proof_delims,
   known_failures = remote_known_failures @ known_failures,
   max_new_relevant_facts_per_iter = max_new_relevant_facts_per_iter,
   prefers_theory_relevant = prefers_theory_relevant,
   explicit_forall = explicit_forall}

val remote_name = prefix "remote_"

fun remote_prover (name, config) atp_prefix =
  (remote_name name, remote_config atp_prefix config)

val remote_e = remote_prover e "EP---"
val remote_vampire = remote_prover vampire "Vampire---9"

fun is_installed ({executable, required_executables, ...} : prover_config) =
  forall (curry (op <>) "" o getenv o fst) (executable :: required_executables)
fun maybe_remote (name, config) =
  name |> not (is_installed config) ? remote_name

fun default_atps_param_value () =
  space_implode " " ([maybe_remote e] @
                     (if is_installed (snd spass) then [fst spass] else []) @
                     [remote_name (fst vampire)])

val provers = [e, spass, vampire, remote_e, remote_vampire]
val setup = fold add_prover provers

end;
