(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  type atp_format = ATP_Problem.atp_format
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
     best_slices :
       Proof.context
       -> (real * (bool * (int * atp_format * string * string))) list}

  val force_sos : bool Config.T
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
  val eN : string
  val e_sineN : string
  val e_tofofN : string
  val iproverN : string
  val iprover_eqN : string
  val leo2N : string
  val pffN : string
  val phfN : string
  val satallaxN : string
  val snarkN : string
  val spassN : string
  val spass_newN : string
  val vampireN : string
  val waldmeisterN : string
  val z3_tptpN : string
  val remote_prefix : string
  val remote_atp :
    string -> string -> string list -> (string * string) list
    -> (failure * string) list -> formula_kind -> formula_kind
    -> (Proof.context -> int * atp_format * string) -> string * atp_config
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
   best_slices :
     Proof.context
     -> (real * (bool * (int * atp_format * string * string))) list}

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

fun known_szs_failures wrap =
  [(Unprovable, wrap "CounterSatisfiable"),
   (Unprovable, wrap "Satisfiable"),
   (GaveUp, wrap "GaveUp"),
   (GaveUp, wrap "Unknown"),
   (GaveUp, wrap "Incomplete"),
   (ProofMissing, wrap "Theorem"),
   (ProofMissing, wrap "Unsatisfiable"),
   (TimedOut, wrap "Timeout"),
   (Inappropriate, wrap "Inappropriate"),
   (OutOfResources, wrap "ResourceOut"),
   (OutOfResources, wrap "MemoryOut"),
   (Interrupted, wrap "Forced"),
   (Interrupted, wrap "User")]

val known_szs_status_failures = known_szs_failures (prefix "SZS status ")
val known_says_failures = known_szs_failures (prefix " says ")

(* named ATPs *)

val eN = "e"
val e_sineN = "e_sine"
val e_tofofN = "e_tofof"
val iproverN = "iprover"
val iprover_eqN = "iprover_eq"
val leo2N = "leo2"
val pffN = "pff"
val phfN = "phf"
val satallaxN = "satallax"
val snarkN = "snark"
val spassN = "spass"
val spass_newN = "spass_new"
val vampireN = "vampire"
val waldmeisterN = "waldmeister"
val z3_tptpN = "z3_tptp"
val remote_prefix = "remote_"

structure Data = Theory_Data
(
  type T = (atp_config * stamp) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
)

fun to_secs min time = Int.max (min, (Time.toMilliseconds time + 999) div 1000)

val sosN = "sos"
val no_sosN = "no_sos"

val force_sos = Attrib.setup_config_bool @{binding atp_force_sos} (K false)


(* E *)

fun is_old_e_version () = (string_ord (getenv "E_VERSION", "1.2w") = LESS)

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

fun effective_e_weight_method ctxt =
  if is_old_e_version () then e_autoN else Config.get ctxt e_weight_method

val e_config : atp_config =
  {exec = ("E_HOME", "eproof"),
   required_execs = [],
   arguments =
     fn ctxt => fn _ => fn method => fn timeout => fn weights =>
        "--tstp-in --tstp-out -l5 " ^ e_weight_arguments ctxt method weights ^
        " -tAutoDev --silent --cpu-limit=" ^ string_of_int (to_secs 2 timeout),
   proof_delims = tstp_proof_delims,
   known_failures =
     known_szs_status_failures @
     [(TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded"),
      (OutOfResources, "# Cannot determine problem status")],
   conj_sym_kind = Hypothesis,
   prem_kind = Conjecture,
   best_slices = fn ctxt =>
     let val method = effective_e_weight_method ctxt in
       (* FUDGE *)
       if method = e_smartN then
         [(0.333, (true, (500, FOF, "mono_tags??", e_fun_weightN))),
          (0.334, (true, (50, FOF, "mono_guards??", e_fun_weightN))),
          (0.333, (true, (1000, FOF, "mono_tags??", e_sym_offset_weightN)))]
       else
         [(1.0, (true, (500, FOF, "mono_tags??", method)))]
     end}

val e = (eN, e_config)


(* LEO-II *)

val leo2_thf0 = THF (TPTP_Monomorphic, TPTP_Explicit, THF_Without_Choice)

val leo2_config : atp_config =
  {exec = ("LEO2_HOME", "leo"),
   required_execs = [],
   arguments =
     fn _ => fn _ => fn sos => fn timeout => fn _ =>
        "--proofoutput 1 --timeout " ^ string_of_int (to_secs 1 timeout)
        |> sos = sosN ? prefix "--sos ",
   proof_delims = tstp_proof_delims,
   known_failures =
     known_szs_status_failures @
     [(TimedOut, "CPU time limit exceeded, terminating")],
   conj_sym_kind = Axiom,
   prem_kind = Hypothesis,
   best_slices = fn ctxt =>
     (* FUDGE *)
     [(0.667, (false, (150, leo2_thf0, "mono_simple_higher", sosN))),
      (0.333, (true, (50, leo2_thf0, "mono_simple_higher", no_sosN)))]
     |> (if Config.get ctxt force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val leo2 = (leo2N, leo2_config)


(* Satallax *)

val satallax_thf0 = THF (TPTP_Monomorphic, TPTP_Explicit, THF_With_Choice)

val satallax_config : atp_config =
  {exec = ("SATALLAX_HOME", "satallax"),
   required_execs = [],
   arguments =
     fn _ => fn _ => fn _ => fn timeout => fn _ =>
        "-p hocore -t " ^ string_of_int (to_secs 1 timeout),
   proof_delims =
     [("% Higher-Order Unsat Core BEGIN", "% Higher-Order Unsat Core END")],
   known_failures = known_szs_status_failures,
   conj_sym_kind = Axiom,
   prem_kind = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (true, (100, satallax_thf0, "mono_simple_higher", "")))]}

val satallax = (satallaxN, satallax_config)


(* SPASS *)

(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of explicit application operators. *)
val spass_config : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/spass"),
   required_execs = [("SPASS_HOME", "SPASS"), ("SPASS_HOME", "tptp2dfg")],
   arguments = fn _ => fn _ => fn sos => fn timeout => fn _ =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^ string_of_int (to_secs 1 timeout))
     |> sos = sosN ? prefix "-SOS=1 ",
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     known_perl_failures @
     [(GaveUp, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (Unprovable, "No formulae and clauses found in input file"),
      (InternalError, "Please report this error")],
   conj_sym_kind = Hypothesis,
   prem_kind = Conjecture,
   best_slices = fn ctxt =>
     (* FUDGE *)
     [(0.333, (false, (150, DFG DFG_Unsorted, "mono_tags??", sosN))),
      (0.333, (false, (300, DFG DFG_Unsorted, "poly_tags??", sosN))),
      (0.334, (true, (50, DFG DFG_Unsorted, "mono_tags??", no_sosN)))]
     |> (if Config.get ctxt force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val spass = (spassN, spass_config)

(* Experimental *)
val spass_new_config : atp_config =
  {exec = ("SPASS_HOME", "SPASS"),
   required_execs = [],
   arguments = #arguments spass_config,
   proof_delims = #proof_delims spass_config,
   known_failures = #known_failures spass_config,
   conj_sym_kind = #conj_sym_kind spass_config,
   prem_kind = #prem_kind spass_config,
   best_slices = fn ctxt =>
     (* FUDGE *)
     [(0.333, (false, (150, DFG DFG_Sorted, "mono_simple", sosN))) (*,
      (0.333, (false, (300, DFG DFG_Sorted, "poly_tags??", sosN))),
      (0.334, (true, (50, DFG DFG_Sorted, "mono_simple", no_sosN)))*)]
     |> (if Config.get ctxt force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val spass_new = (spass_newN, spass_new_config)


(* Vampire *)

(* Vampire 1.8 has TFF support, but it's buggy and therefore disabled on
   SystemOnTPTP. *)
fun is_old_vampire_version () =
  string_ord (getenv "VAMPIRE_VERSION", "1.8") <> GREATER

val vampire_tff0 = TFF (TPTP_Monomorphic, TPTP_Implicit)

val vampire_config : atp_config =
  {exec = ("VAMPIRE_HOME", "vampire"),
   required_execs = [],
   arguments = fn _ => fn _ => fn sos => fn timeout => fn _ =>
     "--mode casc -t " ^ string_of_int (to_secs 1 timeout) ^
     " --proof tptp --output_axiom_names on\
     \ --forced_options propositional_to_bdd=off\
     \ --thanks \"Andrei and Krystof\" --input_file"
     |> sos = sosN ? prefix "--sos on ",
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation"),
      ("% SZS output start Proof", "% SZS output end Proof")],
   known_failures =
     known_szs_status_failures @
     [(GaveUp, "UNPROVABLE"),
      (GaveUp, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (Interrupted, "Aborted by signal SIGINT")],
   conj_sym_kind = Conjecture,
   prem_kind = Conjecture,
   best_slices = fn ctxt =>
     (* FUDGE *)
     (if is_old_vampire_version () then
        [(0.333, (false, (150, FOF, "poly_guards??", sosN))),
         (0.333, (false, (500, FOF, "mono_tags??", sosN))),
         (0.334, (true, (50, FOF, "mono_guards??", no_sosN)))]
      else
        [(0.333, (false, (150, vampire_tff0, "poly_guards??", sosN))),
         (0.333, (false, (500, vampire_tff0, "mono_simple", sosN))),
         (0.334, (true, (50, vampire_tff0, "mono_simple", no_sosN)))])
     |> (if Config.get ctxt force_sos then hd #> apfst (K 1.0) #> single
         else I)}

val vampire = (vampireN, vampire_config)


(* Z3 with TPTP syntax *)

val z3_tff0 = TFF (TPTP_Monomorphic, TPTP_Implicit)

val z3_tptp_config : atp_config =
  {exec = ("Z3_HOME", "z3"),
   required_execs = [],
   arguments = fn _ => fn _ => fn _ => fn timeout => fn _ =>
     "MBQI=true -tptp -t:" ^ string_of_int (to_secs 1 timeout),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   conj_sym_kind = Hypothesis,
   prem_kind = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(0.5, (false, (250, z3_tff0, "mono_simple", ""))),
        (0.25, (false, (125, z3_tff0, "mono_simple", ""))),
        (0.125, (false, (62, z3_tff0, "mono_simple", ""))),
        (0.125, (false, (31, z3_tff0, "mono_simple", "")))]}

val z3_tptp = (z3_tptpN, z3_tptp_config)


(* Not really a prover: Experimental Polymorphic TFF and THF output *)

fun dummy_config format type_enc : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/dummy_atp"),
   required_execs = [],
   arguments = K (K (K (K (K "")))),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   conj_sym_kind = Hypothesis,
   prem_kind = Hypothesis,
   best_slices = K [(1.0, (false, (200, format, type_enc, "")))]}

val pff_format = TFF (TPTP_Polymorphic, TPTP_Explicit)
val pff_config = dummy_config pff_format "poly_simple"
val pff = (pffN, pff_config)

val phf_format = THF (TPTP_Polymorphic, TPTP_Explicit, THF_With_Choice)
val phf_config = dummy_config phf_format "poly_simple_higher"
val phf = (phfN, phf_config)


(* Remote ATP invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([] : string list)

fun get_systems () =
  case Isabelle_System.bash_output
           "\"$ISABELLE_ATP/scripts/remote_atp\" -w 2>&1" of
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
                  conj_sym_kind prem_kind best_slice : atp_config =
  {exec = ("ISABELLE_ATP", "scripts/remote_atp"),
   required_execs = [],
   arguments = fn _ => fn _ => fn _ => fn timeout => fn _ =>
     "-t " ^ string_of_int (Int.min (max_remote_secs, to_secs 1 timeout))
     ^ " -s " ^ the_system system_name system_versions,
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_perl_failures @ known_says_failures,
   conj_sym_kind = conj_sym_kind,
   prem_kind = prem_kind,
   best_slices = fn ctxt =>
     let val (max_relevant, format, type_enc) = best_slice ctxt in
       [(1.0, (false, (max_relevant, format, type_enc, "")))]
     end}

fun remotify_config system_name system_versions best_slice
        ({proof_delims, known_failures, conj_sym_kind, prem_kind, ...}
         : atp_config) : atp_config =
  remote_config system_name system_versions proof_delims known_failures
                conj_sym_kind prem_kind best_slice

fun remote_atp name system_name system_versions proof_delims known_failures
               conj_sym_kind prem_kind best_slice =
  (remote_prefix ^ name,
   remote_config system_name system_versions proof_delims known_failures
                 conj_sym_kind prem_kind best_slice)
fun remotify_atp (name, config) system_name system_versions best_slice =
  (remote_prefix ^ name,
   remotify_config system_name system_versions best_slice config)

val explicit_tff0 = TFF (TPTP_Monomorphic, TPTP_Explicit)

val remote_e =
  remotify_atp e "EP" ["1.0", "1.1", "1.2"]
               (K (750, FOF, "mono_tags??") (* FUDGE *))
val remote_leo2 =
  remotify_atp leo2 "LEO-II" ["1.2.8", "1.2.6"]
               (K (100, leo2_thf0, "mono_simple_higher") (* FUDGE *))
val remote_satallax =
  remotify_atp satallax "Satallax" ["2.1", "2.0", "2"]
               (K (100, satallax_thf0, "mono_simple_higher") (* FUDGE *))
val remote_vampire =
  remotify_atp vampire "Vampire" ["1.8"]
               (K (250, FOF, "mono_guards??") (* FUDGE *))
val remote_z3_tptp =
  remotify_atp z3_tptp "Z3" ["3.0"]
               (K (250, z3_tff0, "mono_simple") (* FUDGE *))
val remote_e_sine =
  remote_atp e_sineN "SInE" ["0.4"] [] (#known_failures e_config) Axiom
             Conjecture (K (500, FOF, "mono_guards??") (* FUDGE *))
val remote_iprover =
  remote_atp iproverN "iProver" [] [] [] Axiom Conjecture
             (K (150, FOF, "mono_guards??") (* FUDGE *))
val remote_iprover_eq =
  remote_atp iprover_eqN "iProver-Eq" [] [] [] Axiom Conjecture
             (K (150, FOF, "mono_guards??") (* FUDGE *))
val remote_snark =
  remote_atp snarkN "SNARK" ["20080805r029", "20080805r024"]
             [("refutation.", "end_refutation.")] [] Hypothesis Hypothesis
             (K (100, explicit_tff0, "mono_simple") (* FUDGE *))
val remote_e_tofof =
  remote_atp e_tofofN "ToFoF" ["0.1"] [] (#known_failures e_config) Axiom
             Hypothesis (K (150, explicit_tff0, "mono_simple") (* FUDGE *))
val remote_waldmeister =
  remote_atp waldmeisterN "Waldmeister" ["710"]
             [("#START OF PROOF", "Proved Goals:")]
             [(OutOfResources, "Too many function symbols"),
              (Crashed, "Unrecoverable Segmentation Fault")]
             Hypothesis Hypothesis
             (K (50, CNF_UEQ, "mono_tags??") (* FUDGE *))

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
  [e, leo2, pff, phf, satallax, spass, spass_new, vampire, z3_tptp, remote_e,
   remote_e_sine, remote_iprover, remote_iprover_eq, remote_leo2,
   remote_satallax, remote_vampire, remote_z3_tptp, remote_snark,
   remote_e_tofof, remote_waldmeister]
val setup = fold add_atp atps

end;
