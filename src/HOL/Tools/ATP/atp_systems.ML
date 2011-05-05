(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  type format = ATP_Problem.format
  type formula_kind = ATP_Problem.formula_kind
  type failure = ATP_Proof.failure

  type atp_config =
    {exec : string * string,
     required_execs : (string * string) list,
     arguments :
       Proof.context -> int -> Time.time -> (unit -> (string * real) list)
       -> string,
     proof_delims : (string * string) list,
     known_failures : (failure * string) list,
     hypothesis_kind : formula_kind,
     formats : format list,
     best_slices : Proof.context -> (real * (bool * int)) list,
     best_type_systems : string list}

  val e_weight_method : string Config.T
  val e_default_fun_weight : real Config.T
  val e_fun_weight_base : real Config.T
  val e_fun_weight_span : real Config.T
  val e_default_sym_offs_weight : real Config.T
  val e_sym_offs_weight_base : real Config.T
  val e_sym_offs_weight_span : real Config.T
  val eN : string
  val spassN : string
  val vampireN : string
  val tofof_eN : string
  val sine_eN : string
  val snarkN : string
  val z3_atpN : string
  val remote_prefix : string
  val remote_atp :
    string -> string -> string list -> (string * string) list
    -> (failure * string) list -> formula_kind -> format list
    -> (Proof.context -> int) -> string list -> string * atp_config
  val add_atp : string * atp_config -> theory -> theory
  val get_atp : theory -> string -> atp_config
  val supported_atps : theory -> string list
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

open ATP_Problem
open ATP_Proof

(* ATP configuration *)

type atp_config =
  {exec : string * string,
   required_execs : (string * string) list,
   arguments :
     Proof.context -> int -> Time.time -> (unit -> (string * real) list)
     -> string,
   proof_delims : (string * string) list,
   known_failures : (failure * string) list,
   hypothesis_kind : formula_kind,
   formats : format list,
   best_slices : Proof.context -> (real * (bool * int)) list,
   best_type_systems : string list}

val known_perl_failures =
  [(CantConnect, "HTTP error"),
   (NoPerl, "env: perl"),
   (NoLibwwwPerl, "Can't locate HTTP")]

(* named ATPs *)

val eN = "e"
val spassN = "spass"
val vampireN = "vampire"
val z3_atpN = "z3_atp"
val tofof_eN = "tofof_e"
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

val e_slicesN = "slices"
val e_autoN = "auto"
val e_fun_weightN = "fun_weight"
val e_sym_offset_weightN = "sym_offset_weight"

val e_weight_method =
  Attrib.setup_config_string @{binding atp_e_weight_method} (K e_slicesN)
(* FUDGE *)
val e_default_fun_weight =
  Attrib.setup_config_real @{binding atp_e_default_fun_weight} (K 20.0)
val e_fun_weight_base =
  Attrib.setup_config_real @{binding atp_e_fun_weight_base} (K 0.0)
val e_fun_weight_span =
  Attrib.setup_config_real @{binding atp_e_fun_weight_span} (K 40.0)
val e_default_sym_offs_weight =
  Attrib.setup_config_real @{binding atp_e_default_sym_offs_weight} (K 1.0)
val e_sym_offs_weight_base =
  Attrib.setup_config_real @{binding atp_e_sym_offs_weight_base} (K ~20.0)
val e_sym_offs_weight_span =
  Attrib.setup_config_real @{binding atp_e_sym_offs_weight_span} (K 60.0)

fun e_weight_method_case method fw sow =
  if method = e_fun_weightN then fw
  else if method = e_sym_offset_weightN then sow
  else raise Fail ("unexpected" ^ quote method)

fun scaled_e_weight ctxt method w =
  w * Config.get ctxt
          (e_weight_method_case method e_fun_weight_span e_sym_offs_weight_span)
  + Config.get ctxt
        (e_weight_method_case method e_fun_weight_base e_sym_offs_weight_base)
  |> Real.ceil |> signed_string_of_int

fun e_weight_arguments ctxt method weights =
  if method = e_autoN then
    "-xAutoDev"
  else
    "--split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr \
    \--destructive-er-aggressive --destructive-er --presat-simplify \
    \--prefer-initial-clauses -tKBO6 -winvfreqrank -c1 -Ginvfreqconjmax -F1 \
    \--delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred \
    \-H'(4*" ^ e_weight_method_case method "FunWeight" "SymOffsetWeight" ^
    "(SimulateSOS, " ^
    (e_weight_method_case method e_default_fun_weight e_default_sym_offs_weight
     |> Config.get ctxt |> Real.ceil |> signed_string_of_int) ^
    ",20,1.5,1.5,1" ^
    (weights ()
     |> map (fn (s, w) => "," ^ s ^ ":" ^ scaled_e_weight ctxt method w)
     |> implode) ^
    "),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,\
    \1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*\
    \FIFOWeight(PreferProcessed))'"

fun is_old_e_version () = (string_ord (getenv "E_VERSION", "1.2w") = LESS)

fun effective_e_weight_method ctxt =
  if is_old_e_version () then e_autoN else Config.get ctxt e_weight_method

(* The order here must correspond to the order in "e_config" below. *)
fun method_for_slice ctxt slice =
  let val method = effective_e_weight_method ctxt in
    if method = e_slicesN then
      case slice of
        0 => e_sym_offset_weightN
      | 1 => e_autoN
      | 2 => e_fun_weightN
      | _ => raise Fail "no such slice"
    else
      method
  end

val e_config : atp_config =
  {exec = ("E_HOME", "eproof"),
   required_execs = [],
   arguments = fn ctxt => fn slice => fn timeout => fn weights =>
     "--tstp-in --tstp-out -l5 " ^
     e_weight_arguments ctxt (method_for_slice ctxt slice) weights ^
     " -tAutoDev --silent --cpu-limit=" ^
     string_of_int (to_secs (e_bonus ()) timeout),
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
   hypothesis_kind = Conjecture,
   formats = [Fof],
   best_slices = fn ctxt =>
     if effective_e_weight_method ctxt = e_slicesN then
       [(0.33333, (true, 100 (* FUDGE *))) (* sym_offset_weight *),
        (0.33333, (true, 1000 (* FUDGE *))) (* auto *),
        (0.33334, (true, 200 (* FUDGE *))) (* fun_weight *)]
     else
       [(1.0, (true, 250 (* FUDGE *)))],
   best_type_systems =
     [ "args", "mangled_preds!", "mangled_preds?", "mangled_preds"]}

val e = (eN, e_config)


(* SPASS *)

(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/spass"),
   required_execs = [("SPASS_HOME", "SPASS"), ("SPASS_HOME", "tptp2dfg")],
   arguments = fn _ => fn slice => fn timeout => fn _ =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^ string_of_int (to_secs 0 timeout))
     |> slice = 0 ? prefix "-SOS=1 ",
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
   hypothesis_kind = Conjecture,
   formats = [Fof],
   best_slices =
     K [(0.66667, (false, 150 (* FUDGE *))) (* with SOS *),
        (0.33333, (true, 150 (* FUDGE *))) (* without SOS *)],
   best_type_systems =
     ["mangled_preds!", "mangled_preds?", "args", "mangled_preds"]}

val spass = (spassN, spass_config)


(* Vampire *)

val vampire_config : atp_config =
  {exec = ("VAMPIRE_HOME", "vampire"),
   required_execs = [],
   arguments = fn _ => fn slice => fn timeout => fn _ =>
     (* This would work too but it's less tested: "--proof tptp " ^ *)
     "--mode casc -t " ^ string_of_int (to_secs 0 timeout) ^
     " --thanks \"Andrei and Krystof\" --input_file"
     |> slice = 0 ? prefix "--sos on ",
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation"),
      ("% SZS output start Proof", "% SZS output end Proof")],
   known_failures =
     [(Unprovable, "UNPROVABLE"),
      (IncompleteUnprovable, "CANNOT PROVE"),
      (IncompleteUnprovable, "SZS status GaveUp"),
      (ProofMissing, "[predicate definition introduction]"),
      (ProofMissing, "predicate_definition_introduction,[]"), (* TSTP *)
      (TimedOut, "SZS status Timeout"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (VampireTooOld, "not a valid option"),
      (Interrupted, "Aborted by signal SIGINT")],
   hypothesis_kind = Conjecture,
   formats = [Fof],
   best_slices =
     K [(0.66667, (false, 450 (* FUDGE *))) (* with SOS *),
        (0.33333, (true, 450 (* FUDGE *))) (* without SOS *)],
   best_type_systems =
     ["mangled_preds?", "mangled_preds!", "args", "mangled_preds"]}

val vampire = (vampireN, vampire_config)


(* Z3 with TPTP syntax *)

val z3_atp_config : atp_config =
  {exec = ("Z3_HOME", "z3"),
   required_execs = [],
   arguments = fn _ => fn _ => fn timeout => fn _ =>
     "MBQI=true -p -t:" ^ string_of_int (to_secs 0 timeout),
   proof_delims = [],
   known_failures =
     [(Unprovable, "\nsat"),
      (IncompleteUnprovable, "\nunknown"),
      (IncompleteUnprovable, "SZS status Satisfiable"),
      (ProofMissing, "\nunsat"),
      (ProofMissing, "SZS status Unsatisfiable")],
   hypothesis_kind = Hypothesis,
   formats = [Fof],
   best_slices = K [(1.0, (false, 250 (* FUDGE *)))],
   best_type_systems = [] (* FIXME *)}

val z3_atp = (z3_atpN, z3_atp_config)


(* Remote ATP invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([] : string list)

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP/scripts/remote_atp\" -w 2>&1" of
    (output, 0) => split_lines output
  | (output, _) =>
    error (case extract_known_failure known_perl_failures output of
             SOME failure => string_for_failure failure
           | NONE => perhaps (try (unsuffix "\n")) output ^ ".")

fun find_system name [] systems =
    find_first (String.isPrefix (name ^ "---")) systems
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
                  hypothesis_kind formats best_max_relevant best_type_systems
                  : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/remote_atp"),
   required_execs = [],
   arguments = fn _ => fn _ => fn timeout => fn _ =>
     " -t " ^ string_of_int (Int.min (max_remote_secs, (to_secs 0 timeout)))
     ^ " -s " ^ the_system system_name system_versions,
   proof_delims = insert (op =) tstp_proof_delims proof_delims,
   known_failures =
     known_failures @ known_perl_failures @
     [(IncompleteUnprovable, "says Unknown"),
      (IncompleteUnprovable, "says GaveUp"),
      (TimedOut, "says Timeout")],
   hypothesis_kind = hypothesis_kind,
   formats = formats,
   best_slices = fn ctxt => [(1.0, (false, best_max_relevant ctxt))],
   best_type_systems = best_type_systems}

fun int_average f xs = fold (Integer.add o f) xs 0 div length xs

fun remotify_config system_name system_versions
                    ({proof_delims, known_failures, hypothesis_kind, formats,
                      best_slices, best_type_systems, ...} : atp_config)
                    : atp_config =
  remote_config system_name system_versions proof_delims known_failures
                hypothesis_kind formats (int_average (snd o snd) o best_slices)
                best_type_systems

fun remote_atp name system_name system_versions proof_delims known_failures
               hypothesis_kind formats best_max_relevant best_type_systems =
  (remote_prefix ^ name,
   remote_config system_name system_versions proof_delims known_failures
                 hypothesis_kind formats best_max_relevant best_type_systems)
fun remotify_atp (name, config) system_name system_versions =
  (remote_prefix ^ name, remotify_config system_name system_versions config)

val remote_e = remotify_atp e "EP" ["1.0", "1.1", "1.2"]
val remote_vampire = remotify_atp vampire "Vampire" ["0.6", "9.0", "1.0"]
val remote_z3_atp = remotify_atp z3_atp "Z3" ["2.18"]
val remote_tofof_e =
  remote_atp tofof_eN "ToFoF" ["0.1"] [] (#known_failures e_config)
             Conjecture [Tff] (K 200 (* FUDGE *)) ["simple"]
val remote_sine_e =
  remote_atp sine_eN "SInE" ["0.4"] [] [] Conjecture [Fof] (K 500 (* FUDGE *))
                     ["args", "preds", "tags"]
val remote_snark =
  remote_atp snarkN "SNARK" ["20080805r024"]
             [("refutation.", "end_refutation.")] [] Conjecture [Tff, Fof]
             (K 250 (* FUDGE *)) ["simple"]

(* Setup *)

fun add_atp (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")

fun get_atp thy name =
  the (Symtab.lookup (Data.get thy) name) |> fst
  handle Option.Option => error ("Unknown ATP: " ^ name ^ ".")

val supported_atps = Symtab.keys o Data.get

fun is_atp_installed thy name =
  let val {exec, required_execs, ...} = get_atp thy name in
    forall (curry (op <>) "" o getenv o fst) (exec :: required_execs)
  end

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

val atps = [e, spass, vampire, z3_atp, remote_e, remote_vampire, remote_z3_atp,
            remote_tofof_e, remote_sine_e, remote_snark]
val setup = fold add_atp atps

end;
