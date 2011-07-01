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
       Proof.context -> bool -> string -> Time.time
       -> (unit -> (string * real) list) -> string,
     proof_delims : (string * string) list,
     known_failures : (failure * string) list,
     conj_sym_kind : formula_kind,
     prem_kind : formula_kind,
     formats : format list,
     best_slices :
       Proof.context -> (real * (bool * (int * string * string))) list}

  val e_smartN : string
  val e_autoN : string
  val e_fun_weightN : string
  val e_sym_offset_weightN : string
  val e_weight_method : string Config.T
  val e_default_fun_weight : real Config.T
  val e_fun_weight_base : real Config.T
  val e_fun_weight_span : real Config.T
  val e_default_sym_offs_weight : real Config.T
  val e_sym_offs_weight_base : real Config.T
  val e_sym_offs_weight_span : real Config.T
  val spass_force_sos : bool Config.T
  val vampire_force_sos : bool Config.T
  val eN : string
  val spassN : string
  val vampireN : string
  val leo2N : string
  val satallaxN : string
  val sine_eN : string
  val snarkN : string
  val tofof_eN : string
  val waldmeisterN : string
  val z3_atpN : string
  val remote_prefix : string
  val remote_atp :
    string -> string -> string list -> (string * string) list
    -> (failure * string) list -> formula_kind -> formula_kind -> format list
    -> (Proof.context -> int * string) -> string * atp_config
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
     Proof.context -> bool -> string -> Time.time
     -> (unit -> (string * real) list) -> string,
   proof_delims : (string * string) list,
   known_failures : (failure * string) list,
   conj_sym_kind : formula_kind,
   prem_kind : formula_kind,
   formats : format list,
   best_slices :
     Proof.context -> (real * (bool * (int * string * string))) list}

(* "best_slices" must be found empirically, taking a wholistic approach since
   the ATPs are run in parallel. The "real" components give the faction of the
   time available given to the slice and should add up to 1.0. The "bool"
   component indicates whether the slice's strategy is complete; the "int", the
   preferred number of facts to pass; the first "string", the preferred type
   system (which should be sound or quasi-sound); the second "string", extra
   information to the prover (e.g., SOS or no SOS).

   The last slice should be the most "normal" one, because it will get all the
   time available if the other slices fail early and also because it is used if
   slicing is disabled (e.g., by the minimizer). *)

val known_perl_failures =
  [(CantConnect, "HTTP error"),
   (NoPerl, "env: perl"),
   (NoLibwwwPerl, "Can't locate HTTP")]

(* named ATPs *)

val eN = "e"
val spassN = "spass"
val vampireN = "vampire"
val z3_atpN = "z3_atp"
val leo2N = "leo2"
val satallaxN = "satallax"
val sine_eN = "sine_e"
val snarkN = "snark"
val tofof_eN = "tofof_e"
val waldmeisterN = "waldmeister"
val remote_prefix = "remote_"

structure Data = Theory_Data
(
  type T = (atp_config * stamp) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
)

fun to_secs time = (Time.toMilliseconds time + 999) div 1000

val sosN = "sos"
val no_sosN = "no_sos"


(* E *)

val tstp_proof_delims =
  [("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation"),
   ("% SZS output start CNFRefutation", "% SZS output end CNFRefutation")]

val e_smartN = "smart"
val e_autoN = "auto"
val e_fun_weightN = "fun_weight"
val e_sym_offset_weightN = "sym_offset_weight"

val e_weight_method =
  Attrib.setup_config_string @{binding atp_e_weight_method} (K e_smartN)
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
  else raise Fail ("unexpected " ^ quote method)

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
    (* supplied by Stephan Schulz *)
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

val e_config : atp_config =
  {exec = ("E_HOME", "eproof"),
   required_execs = [],
   arguments =
     fn ctxt => fn _ => fn method => fn timeout => fn weights =>
        "--tstp-in --tstp-out -l5 " ^ e_weight_arguments ctxt method weights ^
        " -tAutoDev --silent --cpu-limit=" ^ string_of_int (to_secs timeout),
   proof_delims = tstp_proof_delims,
   known_failures =
     [(Unprovable, "SZS status: CounterSatisfiable"),
      (Unprovable, "SZS status CounterSatisfiable"),
      (ProofMissing, "SZS status Theorem"),
      (TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded"),
      (OutOfResources, "# Cannot determine problem status"),
      (OutOfResources, "SZS status: ResourceOut"),
      (OutOfResources, "SZS status ResourceOut")],
   conj_sym_kind = Hypothesis,
   prem_kind = Conjecture,
   formats = [FOF],
   best_slices = fn ctxt =>
     let val method = effective_e_weight_method ctxt in
       (* FUDGE *)
       if method = e_smartN then
         [(0.333, (true, (500, "mangled_tags?", e_fun_weightN))),
          (0.334, (true, (50, "mangled_preds?", e_fun_weightN))),
          (0.333, (true, (1000, "mangled_tags?", e_sym_offset_weightN)))]
       else
         [(1.0, (true, (500, "mangled_tags?", method)))]
     end}

val e = (eN, e_config)


(* SPASS *)

val spass_force_sos =
  Attrib.setup_config_bool @{binding atp_spass_force_sos} (K false)

(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/spass"),
   required_execs = [("SPASS_HOME", "SPASS"), ("SPASS_HOME", "tptp2dfg")],
   arguments = fn _ => fn _ => fn sos => fn timeout => fn _ =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^ string_of_int (to_secs timeout))
     |> sos = sosN ? prefix "-SOS=1 ",
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     known_perl_failures @
     [(GaveUp, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (SpassTooOld, "tptp2dfg"),
      (InternalError, "Please report this error")],
   conj_sym_kind = Hypothesis,
   prem_kind = Conjecture,
   formats = [FOF],
   best_slices = fn ctxt =>
     (* FUDGE *)
     [(0.333, (false, (150, "mangled_tags", sosN))),
      (0.333, (false, (300, "poly_tags?", sosN))),
      (0.334, (true, (50, "mangled_tags?", no_sosN)))]
     |> (if Config.get ctxt spass_force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val spass = (spassN, spass_config)


(* Vampire *)

val vampire_force_sos =
  Attrib.setup_config_bool @{binding atp_vampire_force_sos} (K false)

val vampire_config : atp_config =
  {exec = ("VAMPIRE_HOME", "vampire"),
   required_execs = [],
   arguments = fn _ => fn _ => fn sos => fn timeout => fn _ =>
     "--proof tptp --mode casc -t " ^ string_of_int (to_secs timeout) ^
     " --thanks \"Andrei and Krystof\" --input_file"
     |> sos = sosN ? prefix "--sos on ",
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation"),
      ("% SZS output start Proof", "% SZS output end Proof")],
   known_failures =
     [(GaveUp, "UNPROVABLE"),
      (GaveUp, "CANNOT PROVE"),
      (GaveUp, "SZS status GaveUp"),
      (ProofIncomplete, "predicate_definition_introduction,[]"),
      (TimedOut, "SZS status Timeout"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (VampireTooOld, "not a valid option"),
      (Interrupted, "Aborted by signal SIGINT")],
   conj_sym_kind = Conjecture,
   prem_kind = Conjecture,
   formats = [FOF],
   best_slices = fn ctxt =>
     (* FUDGE *)
     [(0.333, (false, (150, "poly_preds", sosN))),
      (0.334, (true, (50, "mangled_preds?", no_sosN))),
      (0.333, (false, (500, "mangled_tags?", sosN)))]
     |> (if Config.get ctxt vampire_force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val vampire = (vampireN, vampire_config)


(* Z3 with TPTP syntax *)

val z3_atp_config : atp_config =
  {exec = ("Z3_HOME", "z3"),
   required_execs = [],
   arguments = fn _ => fn _ => fn _ => fn timeout => fn _ =>
     "MBQI=true -p -t:" ^ string_of_int (to_secs timeout),
   proof_delims = [],
   known_failures =
     [(Unprovable, "\nsat"),
      (GaveUp, "\nunknown"),
      (GaveUp, "SZS status Satisfiable"),
      (ProofMissing, "\nunsat"),
      (ProofMissing, "SZS status Unsatisfiable")],
   conj_sym_kind = Hypothesis,
   prem_kind = Hypothesis,
   formats = [FOF],
   best_slices =
     (* FUDGE (FIXME) *)
     K [(1.0, (false, (250, "mangled_preds?", "")))]}

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
                     |> `(`(find_system name versions)))

fun the_system name versions =
  case get_system name versions of
    (SOME sys, _) => sys
  | (NONE, []) => error ("SystemOnTPTP is currently not available.")
  | (NONE, syss) =>
    error ("System " ^ quote name ^ " is not available at SystemOnTPTP.\n" ^
           "(Available systems: " ^ commas_quote syss ^ ".)")

val max_remote_secs = 240 (* give Geoff Sutcliffe's servers a break *)

fun remote_config system_name system_versions proof_delims known_failures
                  conj_sym_kind prem_kind formats best_slice : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/remote_atp"),
   required_execs = [],
   arguments = fn _ => fn _ => fn _ => fn timeout => fn _ =>
     "-t " ^ string_of_int (Int.min (max_remote_secs, to_secs timeout))
     ^ " -s " ^ the_system system_name system_versions,
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_perl_failures @
     [(Unprovable, "says Satisfiable"),
      (Unprovable, "says CounterSatisfiable"),
      (GaveUp, "says Unknown"),
      (GaveUp, "says GaveUp"),
      (ProofMissing, "says Theorem"),
      (ProofMissing, "says Unsatisfiable"),
      (TimedOut, "says Timeout"),
      (Inappropriate, "says Inappropriate")],
   conj_sym_kind = conj_sym_kind,
   prem_kind = prem_kind,
   formats = formats,
   best_slices = fn ctxt =>
     let val (max_relevant, type_enc) = best_slice ctxt in
       [(1.0, (false, (max_relevant, type_enc, "")))]
     end}

fun remotify_config system_name system_versions best_slice
        ({proof_delims, known_failures, conj_sym_kind, prem_kind, formats, ...}
         : atp_config) : atp_config =
  remote_config system_name system_versions proof_delims known_failures
                conj_sym_kind prem_kind formats best_slice

fun remote_atp name system_name system_versions proof_delims known_failures
        conj_sym_kind prem_kind formats best_slice =
  (remote_prefix ^ name,
   remote_config system_name system_versions proof_delims known_failures
                 conj_sym_kind prem_kind formats best_slice)
fun remotify_atp (name, config) system_name system_versions best_slice =
  (remote_prefix ^ name,
   remotify_config system_name system_versions best_slice config)

val remote_e =
  remotify_atp e "EP" ["1.0", "1.1", "1.2"]
               (K (750, "mangled_tags?") (* FUDGE *))
val remote_vampire =
  remotify_atp vampire "Vampire" ["0.6", "9.0", "1.0"]
               (K (200, "mangled_preds?") (* FUDGE *))
val remote_z3_atp =
  remotify_atp z3_atp "Z3" ["2.18"] (K (250, "mangled_preds?") (* FUDGE *))
val remote_leo2 =
  remote_atp leo2N "LEO-II" ["1.2.6"] [] [] Axiom Hypothesis [THF]
             (K (100, "simple_higher") (* FUDGE *))
val remote_satallax =
  remote_atp satallaxN "Satallax" ["2.0"] [] [] Axiom Hypothesis [THF]
             (K (64, "simple_higher") (* FUDGE *))
val remote_sine_e =
  remote_atp sine_eN "SInE" ["0.4"] [] (#known_failures e_config) Axiom
             Conjecture [FOF] (K (500, "mangled_preds?") (* FUDGE *))
val remote_snark =
  remote_atp snarkN "SNARK" ["20080805r029", "20080805r024"]
             [("refutation.", "end_refutation.")] [] Hypothesis Hypothesis
             [TFF, FOF] (K (100, "simple") (* FUDGE *))
val remote_tofof_e =
  remote_atp tofof_eN "ToFoF" ["0.1"] [] (#known_failures e_config)
             Axiom Hypothesis [TFF] (K (150, "simple") (* FUDGE *))
val remote_waldmeister =
  remote_atp waldmeisterN "Waldmeister" ["710"]
             [("#START OF PROOF", "Proved Goals:")]
             [(OutOfResources, "Too many function symbols"),
              (Crashed, "Unrecoverable Segmentation Fault")]
             Hypothesis Hypothesis [CNF_UEQ]
             (K (50, "mangled_tags?") (* FUDGE *))

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

val atps =
  [e, spass, vampire, z3_atp, remote_e, remote_vampire, remote_z3_atp,
   remote_leo2, remote_satallax, remote_sine_e, remote_snark, remote_tofof_e,
   remote_waldmeister]
val setup = fold add_atp atps

end;
