(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  datatype failure =
    Unprovable | IncompleteUnprovable | CantConnect | TimedOut |
    OutOfResources | SpassTooOld | VampireTooOld | NoPerl | NoLibwwwPerl |
    MalformedInput | MalformedOutput | Interrupted | InternalError |
    UnknownError

  type prover_config =
    {exec: string * string,
     required_execs: (string * string) list,
     arguments: bool -> Time.time -> string,
     has_incomplete_mode: bool,
     proof_delims: (string * string) list,
     known_failures: (failure * string) list,
     default_max_relevant: int,
     explicit_forall: bool,
     use_conjecture_for_hypotheses: bool}

  val string_for_failure : failure -> string
  val known_failure_in_output :
    string -> (failure * string) list -> failure option
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
  SpassTooOld | VampireTooOld | NoPerl | NoLibwwwPerl | MalformedInput |
  MalformedOutput | Interrupted | InternalError | UnknownError

type prover_config =
  {exec: string * string,
   required_execs: (string * string) list,
   arguments: bool -> Time.time -> string,
   has_incomplete_mode: bool,
   proof_delims: (string * string) list,
   known_failures: (failure * string) list,
   default_max_relevant: int,
   explicit_forall: bool,
   use_conjecture_for_hypotheses: bool}

val missing_message_tail =
  " appears to be missing. You will need to install it if you want to run \
  \ATPs remotely."

fun string_for_failure Unprovable = "The ATP problem is unprovable."
  | string_for_failure IncompleteUnprovable =
    "The ATP cannot prove the problem."
  | string_for_failure CantConnect = "Can't connect to remote server."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure OutOfResources = "The ATP ran out of resources."
  | string_for_failure SpassTooOld =
    "Isabelle requires a more recent version of SPASS with support for the \
    \TPTP syntax. To install it, download and extract the package \
    \\"http://isabelle.in.tum.de/dist/contrib/spass-3.7.tar.gz\" and add the \
    \\"spass-3.7\" directory's absolute path to " ^
    quote (Path.implode (Path.expand (Path.appends
               (Path.variable "ISABELLE_HOME_USER" ::
                map Path.basic ["etc", "components"])))) ^
    " on a line of its own."
  | string_for_failure VampireTooOld =
    "Isabelle requires a more recent version of Vampire. To install it, follow \
    \the instructions from the Sledgehammer manual (\"isabelle doc\
    \ sledgehammer\")."
  | string_for_failure NoPerl = "Perl" ^ missing_message_tail
  | string_for_failure NoLibwwwPerl =
    "The Perl module \"libwww-perl\"" ^ missing_message_tail
  | string_for_failure MalformedInput =
    "The ATP problem is malformed. Please report this to the Isabelle \
    \developers."
  | string_for_failure MalformedOutput = "The ATP output is malformed."
  | string_for_failure Interrupted = "The ATP was interrupted."
  | string_for_failure InternalError = "An internal ATP error occurred."
  | string_for_failure UnknownError = "An unknown ATP error occurred."

fun known_failure_in_output output =
  find_first (fn (_, pattern) => String.isSubstring pattern output)
  #> Option.map fst

val known_perl_failures =
  [(CantConnect, "HTTP error"),
   (NoPerl, "env: perl"),
   (NoLibwwwPerl, "Can't locate HTTP")]

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

fun to_secs bonus time = (Time.toMilliseconds time + bonus + 999) div 1000

(* E prover *)

(* Give older versions of E an extra second, because the "eproof" script wrongly
   subtracted an entire second to account for the overhead of the script
   itself, which is in fact much lower. *)
fun e_bonus () =
  case getenv "E_VERSION" of
    "" => 1000
  | version =>
    if exists (fn s => String.isPrefix s version) ["0.9", "1.0"] then 1000
    else 0

val tstp_proof_delims =
  ("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation")

val e_config : prover_config =
  {exec = ("E_HOME", "eproof"),
   required_execs = [],
   arguments = fn _ => fn timeout =>
     "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent \
     \--cpu-limit=" ^ string_of_int (to_secs (e_bonus ()) timeout),
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

val e = ("e", e_config)


(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : prover_config =
  {exec = ("ISABELLE_ATP", "scripts/spass"),
   required_execs = [("SPASS_HOME", "SPASS"), ("SPASS_HOME", "tptp2dfg")],
   arguments = fn complete => fn timeout =>
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

val spass = ("spass", spass_config)


(* Vampire *)

val vampire_config : prover_config =
  {exec = ("VAMPIRE_HOME", "vampire"),
   required_execs = [],
   arguments = fn complete => fn timeout =>
     ("--mode casc -t " ^ string_of_int (to_secs 0 timeout) ^
      " --thanks Andrei --input_file")
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

val vampire = ("vampire", vampire_config)


(* Remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([] : string list)

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP/scripts/remote_atp\" -w 2>&1" of
    (answer, 0) => split_lines answer
  | (answer, _) =>
    error (case known_failure_in_output answer known_perl_failures of
             SOME failure => string_for_failure failure
           | NONE => perhaps (try (unsuffix "\n")) answer ^ ".")

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

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
  | NONE => error ("System " ^ quote name ^ " not available at SystemOnTPTP.")

fun remote_config system_name system_versions proof_delims known_failures
                  default_max_relevant use_conjecture_for_hypotheses
                  : prover_config =
  {exec = ("ISABELLE_ATP", "scripts/remote_atp"),
   required_execs = [],
   arguments = fn _ => fn timeout =>
     " -t " ^ string_of_int (to_secs 0 timeout) ^ " -s " ^
     the_system system_name system_versions,
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
          use_conjecture_for_hypotheses, ...} : prover_config) : prover_config =
  remote_config system_name system_versions proof_delims known_failures
                default_max_relevant use_conjecture_for_hypotheses

val remotify_name = prefix "remote_"
fun remote_prover name system_name system_versions proof_delims known_failures
                  default_max_relevant use_conjecture_for_hypotheses =
  (remotify_name name,
   remote_config system_name system_versions proof_delims known_failures
                 default_max_relevant use_conjecture_for_hypotheses)
fun remotify_prover (name, config) system_name system_versions =
  (remotify_name name, remotify_config system_name system_versions config)

val remote_e = remotify_prover e "EP" ["1.0", "1.1", "1.2"]
val remote_vampire = remotify_prover vampire "Vampire" ["9.0", "1.0", "0.6"]
val remote_sine_e =
  remote_prover "sine_e" "SInE" [] [] [(IncompleteUnprovable, "says Unknown")]
                800 (* FUDGE *) true
val remote_snark =
  remote_prover "snark" "SNARK---" [] [("refutation.", "end_refutation.")] []
                250 (* FUDGE *) true

(* Setup *)

fun is_installed ({exec, required_execs, ...} : prover_config) =
  forall (curry (op <>) "" o getenv o fst) (exec :: required_execs)
fun maybe_remote (name, config) =
  name |> not (is_installed config) ? remotify_name

(* The first prover of the list is used by Auto Sledgehammer. Because of the low
   timeout, it makes sense to put SPASS first. *)
fun default_atps_param_value () =
  space_implode " " ((if is_installed (snd spass) then [fst spass] else []) @
                     [maybe_remote e] @
                     [if forall (is_installed o snd) [e, spass] then
                        remotify_name (fst vampire)
                      else
                        maybe_remote vampire,
                      fst remote_sine_e])

val provers = [e, spass, vampire, remote_e, remote_vampire, remote_sine_e,
               remote_snark]
val setup = fold add_prover provers

end;
