(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  type term_order = ATP_Problem.term_order
  type atp_format = ATP_Problem.atp_format
  type formula_role = ATP_Problem.formula_role
  type failure = ATP_Proof.failure

  type slice_spec = int * atp_format * string * string * bool
  type atp_config =
    {exec : string list * string,
     required_vars : string list list,
     arguments :
       Proof.context -> bool -> string -> Time.time
       -> term_order * (unit -> (string * int) list)
          * (unit -> (string * real) list) -> string,
     proof_delims : (string * string) list,
     known_failures : (failure * string) list,
     prem_role : formula_role,
     best_slices :
       Proof.context -> (real * (bool * (slice_spec * string))) list,
     best_max_mono_iters : int,
     best_max_new_mono_instances : int}

  val default_max_mono_iters : int
  val default_max_new_mono_instances : int
  val force_sos : bool Config.T
  val term_order : string Config.T
  val e_smartN : string
  val e_autoN : string
  val e_fun_weightN : string
  val e_sym_offset_weightN : string
  val e_selection_heuristic : string Config.T
  val e_default_fun_weight : real Config.T
  val e_fun_weight_base : real Config.T
  val e_fun_weight_span : real Config.T
  val e_default_sym_offs_weight : real Config.T
  val e_sym_offs_weight_base : real Config.T
  val e_sym_offs_weight_span : real Config.T
  val alt_ergoN : string
  val dummy_thfN : string
  val eN : string
  val e_sineN : string
  val e_tofofN : string
  val iproverN : string
  val iprover_eqN : string
  val leo2N : string
  val satallaxN : string
  val snarkN : string
  val spassN : string
  val spass_polyN : string
  val vampireN : string
  val waldmeisterN : string
  val z3_tptpN : string
  val remote_prefix : string
  val remote_atp :
    string -> string -> string list -> (string * string) list
    -> (failure * string) list -> formula_role
    -> (Proof.context -> slice_spec * string) -> string * (unit -> atp_config)
  val add_atp : string * (unit -> atp_config) -> theory -> theory
  val get_atp : theory -> string -> (unit -> atp_config)
  val supported_atps : theory -> string list
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val effective_term_order : Proof.context -> string -> term_order
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate

(* ATP configuration *)

val default_max_mono_iters = 3 (* FUDGE *)
val default_max_new_mono_instances = 200 (* FUDGE *)

type slice_spec = int * atp_format * string * string * bool

type atp_config =
  {exec : string list * string,
   required_vars : string list list,
   arguments :
     Proof.context -> bool -> string -> Time.time
     -> term_order * (unit -> (string * int) list)
        * (unit -> (string * real) list) -> string,
   proof_delims : (string * string) list,
   known_failures : (failure * string) list,
   prem_role : formula_role,
   best_slices : Proof.context -> (real * (bool * (slice_spec * string))) list,
   best_max_mono_iters : int,
   best_max_new_mono_instances : int}

(* "best_slices" must be found empirically, taking a wholistic approach since
   the ATPs are run in parallel. The "real" component gives the faction of the
   time available given to the slice and should add up to 1.0. The first "bool"
   component indicates whether the slice's strategy is complete; the "int", the
   preferred number of facts to pass; the first "string", the preferred type
   system (which should be sound or quasi-sound); the second "string", the
   preferred lambda translation scheme; the second "bool", whether uncurried
   aliased should be generated; the third "string", extra information to
   the prover (e.g., SOS or no SOS).

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

val alt_ergoN = "alt_ergo"
val dummy_thfN = "dummy_thf" (* for experiments *)
val eN = "e"
val e_sineN = "e_sine"
val e_tofofN = "e_tofof"
val iproverN = "iprover"
val iprover_eqN = "iprover_eq"
val leo2N = "leo2"
val satallaxN = "satallax"
val snarkN = "snark"
val spassN = "spass"
val spass_polyN = "spass_poly"
val vampireN = "vampire"
val waldmeisterN = "waldmeister"
val z3_tptpN = "z3_tptp"
val remote_prefix = "remote_"

structure Data = Theory_Data
(
  type T = ((unit -> atp_config) * stamp) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T =
    Symtab.merge (eq_snd (op =)) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")
)

fun to_secs min time = Int.max (min, (Time.toMilliseconds time + 999) div 1000)

val sosN = "sos"
val no_sosN = "no_sos"

val force_sos = Attrib.setup_config_bool @{binding atp_force_sos} (K false)

val smartN = "smart"
(* val kboN = "kbo" *)
val lpoN = "lpo"
val xweightsN = "_weights"
val xprecN = "_prec"
val xsimpN = "_simp" (* SPASS-specific *)

(* Possible values for "atp_term_order":
   "smart", "(kbo|lpo)(_weights)?(_prec|_simp)?" *)
val term_order =
  Attrib.setup_config_string @{binding atp_term_order} (K smartN)

(* Alt-Ergo *)

val alt_ergo_tff1 = TFF (Polymorphic, TPTP_Explicit)

val alt_ergo_config : atp_config =
  {exec = (["WHY3_HOME"], "why3"),
   required_vars = [],
   arguments =
     fn _ => fn _ => fn _ => fn timeout => fn _ =>
        "--format tff1 --prover alt-ergo --timelimit " ^
        string_of_int (to_secs 1 timeout),
   proof_delims = [],
   known_failures =
     [(ProofMissing, ": Valid"),
      (TimedOut, ": Timeout"),
      (GaveUp, ": Unknown")],
   prem_role = Hypothesis,
   best_slices = fn _ =>
     (* FUDGE *)
     [(1.0, (false, ((100, alt_ergo_tff1, "poly_native", liftingN, false), "")))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val alt_ergo = (alt_ergoN, fn () => alt_ergo_config)


(* E *)

fun is_recent_e_version () = (string_ord (getenv "E_VERSION", "1.3") <> LESS)
fun is_new_e_version () = (string_ord (getenv "E_VERSION", "1.6") <> LESS)

val tstp_proof_delims =
  [("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation"),
   ("% SZS output start CNFRefutation", "% SZS output end CNFRefutation")]

val e_smartN = "smart"
val e_autoN = "auto"
val e_fun_weightN = "fun_weight"
val e_sym_offset_weightN = "sym_offset_weight"

val e_selection_heuristic =
  Attrib.setup_config_string @{binding atp_e_selection_heuristic} (K e_smartN)
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

fun e_selection_heuristic_case heuristic fw sow =
  if heuristic = e_fun_weightN then fw
  else if heuristic = e_sym_offset_weightN then sow
  else raise Fail ("unexpected " ^ quote heuristic)

fun scaled_e_selection_weight ctxt heuristic w =
  w * Config.get ctxt (e_selection_heuristic_case heuristic
                           e_fun_weight_span e_sym_offs_weight_span)
  + Config.get ctxt (e_selection_heuristic_case heuristic
                         e_fun_weight_base e_sym_offs_weight_base)
  |> Real.ceil |> signed_string_of_int

fun e_selection_weight_arguments ctxt heuristic sel_weights =
  if heuristic = e_autoN then
    "-xAuto"
  else
    (* supplied by Stephan Schulz *)
    "--split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr \
    \--destructive-er-aggressive --destructive-er --presat-simplify \
    \--prefer-initial-clauses -winvfreqrank -c1 -Ginvfreqconjmax -F1 \
    \--delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H'(4*" ^
    e_selection_heuristic_case heuristic "FunWeight" "SymOffsetWeight" ^
    "(SimulateSOS, " ^
    (e_selection_heuristic_case heuristic
         e_default_fun_weight e_default_sym_offs_weight
     |> Config.get ctxt |> Real.ceil |> signed_string_of_int) ^
    ",20,1.5,1.5,1" ^
    (sel_weights ()
     |> map (fn (s, w) => "," ^ s ^ ":" ^
                          scaled_e_selection_weight ctxt heuristic w)
     |> implode) ^
    "),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,\
    \1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*\
    \FIFOWeight(PreferProcessed))'"

val e_ord_weights =
  map (fn (s, w) => s ^ ":" ^ string_of_int w) #> space_implode ","
fun e_ord_precedence [_] = ""
  | e_ord_precedence info = info |> map fst |> space_implode "<"

fun e_term_order_info_arguments false false _ = ""
  | e_term_order_info_arguments gen_weights gen_prec ord_info =
    let val ord_info = ord_info () in
      (if gen_weights then "--order-weights='" ^ e_ord_weights ord_info ^ "' "
       else "") ^
      (if gen_prec then "--precedence='" ^ e_ord_precedence ord_info ^ "' "
       else "")
    end

fun e_shell_level_argument full_proof =
  if is_new_e_version () then
    " --pcl-shell-level=" ^ (if full_proof then "0" else "2")
  else
    ""

fun effective_e_selection_heuristic ctxt =
  if is_recent_e_version () then Config.get ctxt e_selection_heuristic
  else e_autoN

fun e_kbo () = if is_recent_e_version () then "KBO6" else "KBO"

val e_config : atp_config =
  {exec = (["E_HOME"], "eproof"),
   required_vars = [],
   arguments =
     fn ctxt => fn full_proof => fn heuristic => fn timeout =>
        fn ({is_lpo, gen_weights, gen_prec, ...}, ord_info, sel_weights) =>
        "--tstp-in --tstp-out --output-level=5 --silent " ^
        e_selection_weight_arguments ctxt heuristic sel_weights ^ " " ^
        e_term_order_info_arguments gen_weights gen_prec ord_info ^ " " ^
        "--term-ordering=" ^ (if is_lpo then "LPO4" else e_kbo ()) ^ " " ^
        "--cpu-limit=" ^ string_of_int (to_secs 2 timeout) ^
        e_shell_level_argument full_proof,
   proof_delims =
     (* work-around for bug in "epclextract" version 1.6 *)
     ("# SZS status Theorem\n# SZS output start Saturation.",
      "# SZS output end Saturation.") ::
     tstp_proof_delims,
   known_failures =
     [(TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded")] @
     known_szs_status_failures,
   prem_role = Conjecture,
   best_slices = fn ctxt =>
     let val heuristic = effective_e_selection_heuristic ctxt in
       (* FUDGE *)
       if heuristic = e_smartN then
         [(0.333, (true, ((500, FOF, "mono_tags??", combsN, false), e_fun_weightN))),
          (0.334, (true, ((50, FOF, "mono_guards??", combsN, false), e_fun_weightN))),
          (0.333, (true, ((1000, FOF, "mono_tags??", combsN, false), e_sym_offset_weightN)))]
       else
         [(1.0, (true, ((500, FOF, "mono_tags??", combsN, false), heuristic)))]
     end,
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val e = (eN, fn () => e_config)


(* LEO-II *)

(* LEO-II supports definitions, but it performs significantly better on our
   benchmarks when they are not used. *)
val leo2_thf0 =
  THF (Monomorphic, TPTP_Explicit, THF_Without_Choice, THF_Without_Defs)

val leo2_config : atp_config =
  {exec = (["LEO2_HOME"], "leo"),
   required_vars = [],
   arguments =
     fn _ => fn _ => fn _ => fn timeout => fn _ =>
        "--foatp e --atp e=\"$E_HOME\"/eprover \
        \--atp epclextract=\"$E_HOME\"/epclextract \
        \--proofoutput 1 --timeout " ^
        string_of_int (to_secs 1 timeout),
   proof_delims = tstp_proof_delims,
   known_failures =
     [(TimedOut, "CPU time limit exceeded, terminating"),
      (GaveUp, "No.of.Axioms")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (true, ((40, leo2_thf0, "mono_native_higher", keep_lamsN, false), "")))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances div 2 (* FUDGE *)}

val leo2 = (leo2N, fn () => leo2_config)


(* Satallax *)

val satallax_thf0 =
  THF (Monomorphic, TPTP_Explicit, THF_With_Choice, THF_With_Defs)

val satallax_config : atp_config =
  {exec = (["SATALLAX_HOME"], "satallax"),
   required_vars = [],
   arguments =
     fn _ => fn _ => fn _ => fn timeout => fn _ =>
        "-p hocore -t " ^ string_of_int (to_secs 1 timeout),
   proof_delims =
     [("% Higher-Order Unsat Core BEGIN", "% Higher-Order Unsat Core END")],
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (true, ((60, satallax_thf0, "mono_native_higher", keep_lamsN, false), "")))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances div 2 (* FUDGE *)}

val satallax = (satallaxN, fn () => satallax_config)


(* SPASS *)

val spass_H1SOS = "-Heuristic=1 -SOS"
val spass_H2LR0LT0 = "-Heuristic=2 -LR=0 -LT=0"
val spass_H2SOS = "-Heuristic=2 -SOS"
val spass_H2NuVS0 = "-Heuristic=2 -RNuV=1 -Sorts=0"
val spass_H2NuVS0Red2 = "-Heuristic=2 -RNuV=1 -Sorts=0 -RFRew=2 -RBRew=2 -RTaut=2"

(* FIXME: Make "SPASS_NEW_HOME" legacy. *)
val spass_config : atp_config =
  {exec = (["SPASS_NEW_HOME", "SPASS_HOME"], "SPASS"),
   required_vars = [],
   arguments = fn _ => fn _ => fn extra_options => fn timeout => fn _ =>
     ("-Isabelle=1 -TimeLimit=" ^ string_of_int (to_secs 1 timeout))
     |> extra_options <> "" ? prefix (extra_options ^ " "),
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     [(OldSPASS, "Unrecognized option Isabelle"),
      (GaveUp, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (Unprovable, "No formulae and clauses found in input file"),
      (InternalError, "Please report this error")] @
      known_perl_failures,
   prem_role = Conjecture,
   best_slices = fn _ =>
     (* FUDGE *)
     [(0.1667, (false, ((150, DFG Monomorphic, "mono_native", combsN, true), ""))),
      (0.1667, (false, ((500, DFG Monomorphic, "mono_native", liftingN, true), spass_H2SOS))),
      (0.1666, (false, ((50, DFG Monomorphic,  "mono_native", liftingN, true), spass_H2LR0LT0))),
      (0.1000, (false, ((250, DFG Monomorphic, "mono_native", combsN, true), spass_H2NuVS0))),
      (0.1000, (false, ((1000, DFG Monomorphic, "mono_native", liftingN, true), spass_H1SOS))),
      (0.1000, (false, ((150, DFG Monomorphic, "poly_guards??", liftingN, false), spass_H2NuVS0Red2))),
      (0.1000, (false, ((300, DFG Monomorphic, "mono_native", combsN, true), spass_H2SOS))),
      (0.1000, (false, ((100, DFG Monomorphic, "mono_native", combs_and_liftingN, true), spass_H2NuVS0)))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val spass = (spassN, fn () => spass_config)

(* Vampire *)

(* Vampire 1.8 has TFF support, but the support was buggy until revision
   1435 (or shortly before). *)
fun is_new_vampire_version () =
  string_ord (getenv "VAMPIRE_VERSION", "1.8") = GREATER

val vampire_tff0 = TFF (Monomorphic, TPTP_Implicit)

val vampire_config : atp_config =
  {exec = (["VAMPIRE_HOME"], "vampire"),
   required_vars = [],
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
     [(GaveUp, "UNPROVABLE"),
      (GaveUp, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (Interrupted, "Aborted by signal SIGINT")] @
     known_szs_status_failures,
   prem_role = Conjecture,
   best_slices = fn ctxt =>
     (* FUDGE *)
     (if is_new_vampire_version () then
        [(0.333, (false, ((500, vampire_tff0, "mono_native", combs_or_liftingN, false), sosN))),
         (0.333, (false, ((150, vampire_tff0, "poly_guards??", combs_or_liftingN, false), sosN))),
         (0.334, (true, ((50, vampire_tff0, "mono_native", combs_or_liftingN, false), no_sosN)))]
      else
        [(0.333, (false, ((150, FOF, "poly_guards??", combs_or_liftingN, false), sosN))),
         (0.333, (false, ((500, FOF, "mono_tags??", combs_or_liftingN, false), sosN))),
         (0.334, (true, ((50, FOF, "mono_guards??", combs_or_liftingN, false), no_sosN)))])
     |> (if Config.get ctxt force_sos then hd #> apfst (K 1.0) #> single
         else I),
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val vampire = (vampireN, fn () => vampire_config)


(* Z3 with TPTP syntax *)

val z3_tff0 = TFF (Monomorphic, TPTP_Implicit)

val z3_tptp_config : atp_config =
  {exec = (["Z3_HOME"], "z3"),
   required_vars = [],
   arguments = fn _ => fn _ => fn _ => fn timeout => fn _ =>
     "MBQI=true -tptp -t:" ^ string_of_int (to_secs 1 timeout),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(0.5, (false, ((250, z3_tff0, "mono_native", combsN, false), ""))),
        (0.25, (false, ((125, z3_tff0, "mono_native", combsN, false), ""))),
        (0.125, (false, ((62, z3_tff0, "mono_native", combsN, false), ""))),
        (0.125, (false, ((31, z3_tff0, "mono_native", combsN, false), "")))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val z3_tptp = (z3_tptpN, fn () => z3_tptp_config)


(* Not really a prover: Experimental Polymorphic THF and DFG output *)

fun dummy_config format type_enc : atp_config =
  {exec = (["ISABELLE_ATP"], "scripts/dummy_atp"),
   required_vars = [],
   arguments = K (K (K (K (K "")))),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     K [(1.0, (false, ((200, format, type_enc,
                        if is_format_higher_order format then keep_lamsN
                        else combsN, false), "")))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val dummy_thf_format =
  THF (Polymorphic, TPTP_Explicit, THF_With_Choice, THF_With_Defs)
val dummy_thf_config = dummy_config dummy_thf_format "poly_native_higher"
val dummy_thf = (dummy_thfN, fn () => dummy_thf_config)

val spass_poly_format = DFG Polymorphic
val spass_poly_config = dummy_config spass_poly_format "tc_native"
val spass_poly = (spass_polyN, fn () => spass_poly_config)

(* Remote ATP invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([] : string list)

fun get_systems () =
  case Isabelle_System.bash_output
           "\"$ISABELLE_ATP/scripts/remote_atp\" -w 2>&1" of
    (output, 0) => split_lines output
  | (output, _) =>
    error (case extract_known_failure known_perl_failures output of
             SOME failure => string_for_failure failure
           | NONE => trim_line output ^ ".")

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
  | (NONE, []) => error ("SystemOnTPTP is not available.")
  | (NONE, syss) =>
    case syss |> filter_out (String.isPrefix "%")
              |> filter_out (curry (op =) "") of
      [] => error ("SystemOnTPTP is not available.")
    | [msg] => error ("SystemOnTPTP is not available: " ^ msg ^ ".")
    | syss =>
      error ("System " ^ quote name ^ " is not available at SystemOnTPTP.\n" ^
             "(Available systems: " ^ commas_quote syss ^ ".)")

val max_remote_secs = 240 (* give Geoff Sutcliffe's servers a break *)

fun remote_config system_name system_versions proof_delims known_failures
                  prem_role best_slice : atp_config =
  {exec = (["ISABELLE_ATP"], "scripts/remote_atp"),
   required_vars = [],
   arguments = fn _ => fn _ => fn command => fn timeout => fn _ =>
     (if command <> "" then "-c " ^ quote command ^ " " else "") ^
     "-s " ^ the_system system_name system_versions ^ " " ^
     "-t " ^ string_of_int (Int.min (max_remote_secs, to_secs 1 timeout)),
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_perl_failures @ known_says_failures,
   prem_role = prem_role,
   best_slices = fn ctxt => [(1.0, (false, best_slice ctxt))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

fun remotify_config system_name system_versions best_slice
        ({proof_delims, known_failures, prem_role, ...} : atp_config)
        : atp_config =
  remote_config system_name system_versions proof_delims known_failures
                prem_role best_slice

fun remote_atp name system_name system_versions proof_delims known_failures
               prem_role best_slice =
  (remote_prefix ^ name,
   fn () => remote_config system_name system_versions proof_delims
                          known_failures prem_role best_slice)
fun remotify_atp (name, config) system_name system_versions best_slice =
  (remote_prefix ^ name,
   remotify_config system_name system_versions best_slice o config)

val explicit_tff0 = TFF (Monomorphic, TPTP_Explicit)

val remote_e =
  remotify_atp e "EP" ["1.0", "1.1", "1.2"]
      (K ((750, FOF, "mono_tags??", combsN, false), "") (* FUDGE *))
val remote_leo2 =
  remotify_atp leo2 "LEO-II" ["1.2.8", "1.2.6"]
      (K ((100, leo2_thf0, "mono_native_higher", liftingN, false), "") (* FUDGE *))
val remote_satallax =
  remotify_atp satallax "Satallax" ["2.3", "2.2", "2"]
      (K ((100, satallax_thf0, "mono_native_higher", keep_lamsN, false), "") (* FUDGE *))
val remote_vampire =
  remotify_atp vampire "Vampire" ["2.6", "2.5", "1.8"]
      (K ((250, vampire_tff0, "mono_native", combs_or_liftingN, false), "") (* FUDGE *))
val remote_z3_tptp =
  remotify_atp z3_tptp "Z3" ["3.0"]
      (K ((250, z3_tff0, "mono_native", combsN, false), "") (* FUDGE *))
val remote_e_sine =
  remote_atp e_sineN "SInE" ["0.4"] [] (#known_failures e_config) Conjecture
      (K ((500, FOF, "mono_guards??", combsN, false), "") (* FUDGE *))
val remote_iprover =
  remote_atp iproverN "iProver" [] [] [] Conjecture
      (K ((150, FOF, "mono_guards??", liftingN, false), "") (* FUDGE *))
val remote_iprover_eq =
  remote_atp iprover_eqN "iProver-Eq" [] [] [] Conjecture
      (K ((150, FOF, "mono_guards??", liftingN, false), "") (* FUDGE *))
val remote_snark =
  remote_atp snarkN "SNARK" ["20080805r029", "20080805r024"]
      [("refutation.", "end_refutation.")] [] Hypothesis
      (K ((100, explicit_tff0, "mono_native", liftingN, false), "") (* FUDGE *))
val remote_e_tofof =
  remote_atp e_tofofN "ToFoF" ["0.1"] [] (#known_failures e_config) Hypothesis
      (K ((150, explicit_tff0, "mono_native", liftingN, false), "") (* FUDGE *))
val remote_waldmeister =
  remote_atp waldmeisterN "Waldmeister" ["710"]
      [("#START OF PROOF", "Proved Goals:")]
      [(OutOfResources, "Too many function symbols"),
       (Inappropriate, "****  Unexpected end of file."),
       (Crashed, "Unrecoverable Segmentation Fault")]
      Hypothesis
      (K ((50, CNF_UEQ, "raw_mono_tags??", combsN, false), "") (* FUDGE *))

(* Setup *)

fun add_atp (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name ^ ".")

fun get_atp thy name =
  the (Symtab.lookup (Data.get thy) name) |> fst
  handle Option.Option => error ("Unknown ATP: " ^ name ^ ".")

val supported_atps = Symtab.keys o Data.get

fun is_atp_installed thy name =
  let val {exec, required_vars, ...} = get_atp thy name () in
    forall (exists (fn var => getenv var <> "")) (fst exec :: required_vars)
  end

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

fun effective_term_order ctxt atp =
  let val ord = Config.get ctxt term_order in
    if ord = smartN then
      if atp = spassN then
        {is_lpo = false, gen_weights = true, gen_prec = true, gen_simp = false}
      else
        {is_lpo = false, gen_weights = false, gen_prec = false,
         gen_simp = false}
    else
      let val is_lpo = String.isSubstring lpoN ord in
        {is_lpo = is_lpo,
         gen_weights = not is_lpo andalso String.isSubstring xweightsN ord,
         gen_prec = String.isSubstring xprecN ord,
         gen_simp = String.isSubstring xsimpN ord}
      end
  end

val atps=
  [alt_ergo, e, leo2, satallax, spass, spass_poly, vampire, z3_tptp, dummy_thf,
   remote_e, remote_e_sine, remote_e_tofof, remote_iprover, remote_iprover_eq,
   remote_leo2, remote_satallax, remote_vampire, remote_z3_tptp, remote_snark,
   remote_waldmeister]

val setup = fold add_atp atps

end;
