(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  type failure = ATP_Proof.failure

  type atp_config =
    {exec: string * string,
     required_execs: (string * string) list,
     arguments: bool -> Time.time -> (unit -> (string * real) list) -> string,
     has_incomplete_mode: bool,
     proof_delims: (string * string) list,
     known_failures: (failure * string) list,
     default_max_relevant: int,
     explicit_forall: bool,
     use_conjecture_for_hypotheses: bool}

  (* for experimentation purposes -- do not use in production code *)
  val e_generate_weights : bool Unsynchronized.ref
  val e_weight_factor : real Unsynchronized.ref
  val e_default_weight : real Unsynchronized.ref

  val eN : string
  val spassN : string
  val vampireN : string
  val sine_eN : string
  val snarkN : string
  val remote_prefix : string
  val add_atp : string * atp_config -> theory -> theory
  val get_atp : theory -> string -> atp_config
  val available_atps : theory -> string list
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

open ATP_Proof

(* ATP configuration *)

type atp_config =
  {exec: string * string,
   required_execs: (string * string) list,
   arguments: bool -> Time.time -> (unit -> (string * real) list) -> string,
   has_incomplete_mode: bool,
   proof_delims: (string * string) list,
   known_failures: (failure * string) list,
   default_max_relevant: int,
   explicit_forall: bool,
   use_conjecture_for_hypotheses: bool}

val known_perl_failures =
  [(CantConnect, "HTTP error"),
   (NoPerl, "env: perl"),
   (NoLibwwwPerl, "Can't locate HTTP")]

(* named ATPs *)

val eN = "e"
val spassN = "spass"
val vampireN = "vampire"
val sine_eN = "sine_e"
val snarkN = "snark"
val remote_prefix = "remote_"

structure Data = Theory_Data
(
  type T = (atp_config * stamp) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
)

fun to_secs bonus time = (Time.toMilliseconds time + bonus + 999) div 1000


(* E *)

(* Give E an extra second to reconstruct the proof. Older versions even get two
   seconds, because the "eproof" script wrongly subtracted an entire second to
   account for the overhead of the script itself, which is in fact much
   lower. *)
fun e_bonus () =
  if string_ord (getenv "E_VERSION", "1.1") = LESS then 2000 else 1000

val tstp_proof_delims =
  ("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation")

val e_generate_weights = Unsynchronized.ref true
val e_weight_factor = Unsynchronized.ref 40.0
val e_default_weight = Unsynchronized.ref 0.5

fun e_weights weights =
  if !e_generate_weights andalso
     string_ord (getenv "E_VERSION", "1.2B") <> LESS then
    "--split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr \
    \--destructive-er-aggressive --destructive-er --presat-simplify \
    \--prefer-initial-clauses -tKBO6 -winvfreqrank -c1 -Ginvfreqconjmax -F1 \
    \--delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred \
    \-H'(4*FunWeight(SimulateSOS, " ^
    string_of_int (Real.ceil (!e_default_weight * !e_weight_factor)) ^
    ",20,1.5,1.5,1" ^
    (weights ()
     |> map (fn (s, w) => "," ^ s ^ ":" ^
                          string_of_int (Real.ceil (w * !e_weight_factor)))
     |> implode) ^
    "),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,\
    \1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*\
    \FIFOWeight(PreferProcessed))'"
  else
    "-xAutoDev"

val e_config : atp_config =
  {exec = ("E_HOME", "eproof"),
   required_execs = [],
   arguments = fn _ => fn timeout => fn weights =>
     "--tstp-in --tstp-out -l5 " ^ e_weights weights ^ " -tAutoDev \
     \--silent --cpu-limit=" ^ string_of_int (to_secs (e_bonus ()) timeout),
   has_incomplete_mode = false,
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
   default_max_relevant = 500 (* FUDGE *),
   explicit_forall = false,
   use_conjecture_for_hypotheses = true}

val e = (eN, e_config)


(* SPASS *)

(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/spass"),
   required_execs = [("SPASS_HOME", "SPASS"), ("SPASS_HOME", "tptp2dfg")],
   arguments = fn complete => fn timeout => fn _ =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^ string_of_int (to_secs 0 timeout))
     |> not complete ? prefix "-SOS=1 ",
   has_incomplete_mode = true,
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     known_perl_failures @
     [(IncompleteUnprovable, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (SpassTooOld, "tptp2dfg"),
      (InternalError, "Please report this error")],
   default_max_relevant = 350 (* FUDGE *),
   explicit_forall = true,
   use_conjecture_for_hypotheses = true}

val spass = (spassN, spass_config)


(* Vampire *)

val vampire_config : atp_config =
  {exec = ("VAMPIRE_HOME", "vampire"),
   required_execs = [],
   arguments = fn complete => fn timeout => fn _ =>
     (* This would work too but it's less tested: "--proof tptp " ^ *)
     "--mode casc -t " ^ string_of_int (to_secs 0 timeout) ^
     " --thanks \"Andrei and Krystof\" --input_file"
     |> not complete ? prefix "--sos on ",
   has_incomplete_mode = true,
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation"),
      ("% SZS output start Proof", "% SZS output end Proof")],
   known_failures =
     [(Unprovable, "UNPROVABLE"),
      (IncompleteUnprovable, "CANNOT PROVE"),
      (TimedOut, "SZS status Timeout"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (VampireTooOld, "not a valid option"),
      (Interrupted, "Aborted by signal SIGINT")],
   default_max_relevant = 400 (* FUDGE *),
   explicit_forall = false,
   use_conjecture_for_hypotheses = true}

val vampire = (vampireN, vampire_config)


(* Remote ATP invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([] : string list)

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP/scripts/remote_atp\" -w 2>&1" of
    (output, 0) => split_lines output
  | (output, _) =>
    error (case extract_known_failure known_perl_failures output of
             SOME failure => string_for_failure "ATP" failure
           | NONE => perhaps (try (unsuffix "\n")) output ^ ".")

fun find_system name [] systems = find_first (String.isPrefix name) systems
  | find_system name (version :: versions) systems =
    case find_first (String.isPrefix (name ^ "---" ^ version)) systems of
      NONE => find_system name versions systems
    | res => res

fun get_system name versions =
  Synchronized.change_result systems
      (fn systems => (if null systems then get_systems () else systems)
                     |> `(find_system name versions))

fun the_system name versions =
  case get_system name versions of
    SOME sys => sys
  | NONE => error ("System " ^ quote name ^
                   " is not available at SystemOnTPTP.")

val max_remote_secs = 240 (* give Geoff Sutcliffe's servers a break *)

fun remote_config system_name system_versions proof_delims known_failures
                  default_max_relevant use_conjecture_for_hypotheses
                  : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/remote_atp"),
   required_execs = [],
   arguments = fn _ => fn timeout => fn _ =>
     " -t " ^ string_of_int (Int.min (max_remote_secs, (to_secs 0 timeout)))
     ^ " -s " ^ the_system system_name system_versions,
   has_incomplete_mode = false,
   proof_delims = insert (op =) tstp_proof_delims proof_delims,
   known_failures =
     known_failures @ known_perl_failures @
     [(TimedOut, "says Timeout")],
   default_max_relevant = default_max_relevant,
   explicit_forall = true,
   use_conjecture_for_hypotheses = use_conjecture_for_hypotheses}

fun remotify_config system_name system_versions
        ({proof_delims, known_failures, default_max_relevant,
          use_conjecture_for_hypotheses, ...} : atp_config) : atp_config =
  remote_config system_name system_versions proof_delims known_failures
                default_max_relevant use_conjecture_for_hypotheses

fun remote_atp name system_name system_versions proof_delims known_failures
               default_max_relevant use_conjecture_for_hypotheses =
  (remote_prefix ^ name,
   remote_config system_name system_versions proof_delims known_failures
                 default_max_relevant use_conjecture_for_hypotheses)
fun remotify_atp (name, config) system_name system_versions =
  (remote_prefix ^ name, remotify_config system_name system_versions config)

val remote_e = remotify_atp e "EP" ["1.0", "1.1", "1.2"]
val remote_vampire = remotify_atp vampire "Vampire" ["0.6", "9.0", "1.0"]
val remote_sine_e =
  remote_atp sine_eN "SInE" [] [] [(IncompleteUnprovable, "says Unknown")]
                600 (* FUDGE *) true
val remote_snark =
  remote_atp snarkN "SNARK---" [] [("refutation.", "end_refutation.")] []
             250 (* FUDGE *) true

(* Setup *)

fun add_atp (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")

fun get_atp thy name =
  the (Symtab.lookup (Data.get thy) name) |> fst
  handle Option.Option => error ("Unknown ATP: " ^ name ^ ".")

val available_atps = Symtab.keys o Data.get

fun is_atp_installed thy name =
  let val {exec, required_execs, ...} = get_atp thy name in
    forall (curry (op <>) "" o getenv o fst) (exec :: required_execs)
  end

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

val atps = [e, spass, vampire, remote_e, remote_vampire, remote_sine_e,
            remote_snark]
val setup = fold add_atp atps

end;
