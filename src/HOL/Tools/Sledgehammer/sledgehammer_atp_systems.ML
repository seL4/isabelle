(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, MPI-INF Saarbruecken

Setup for supported ATPs.
*)

signature SLEDGEHAMMER_ATP_SYSTEMS =
sig
  type atp_format = ATP_Problem.atp_format
  type atp_formula_role = ATP_Problem.atp_formula_role
  type atp_failure = ATP_Proof.atp_failure

  type base_slice = int * bool * bool * int * string
  type atp_slice = atp_format * string * string * bool * string
  type atp_config =
    {exec : string list * string list,
     arguments : bool -> bool -> string -> Time.time -> Path.T -> string list,
     proof_delims : (string * string) list,
     known_failures : (atp_failure * string) list,
     prem_role : atp_formula_role,
     generate_isabelle_info : bool,
     good_slices : Proof.context -> (base_slice * atp_slice) list,
     good_max_mono_iters : int,
     good_max_new_mono_instances : int}

  val default_max_mono_iters : int
  val default_max_new_mono_instances : int
  val spass_H1SOS : string
  val spass_H2 : string
  val spass_H2LR0LT0 : string
  val spass_H2NuVS0 : string
  val spass_H2NuVS0Red2 : string
  val spass_H2SOS : string
  val isabelle_scala_function: string list * string list
  val remote_atp : string -> string -> string list -> (string * string) list ->
    (atp_failure * string) list -> atp_formula_role -> bool ->
    (Proof.context -> base_slice * atp_slice) -> string * (unit -> atp_config)
  val add_atp : string * (unit -> atp_config) -> theory -> theory
  val get_atp : theory -> string -> (unit -> atp_config)
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val local_atps : string list
  val remote_atps : string list
  val dummy_atps : string list
  val non_dummy_atps : string list
  val all_atps : string list
end;

structure Sledgehammer_ATP_Systems : SLEDGEHAMMER_ATP_SYSTEMS =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate


(* ATP configuration *)

val TF0 = TFF (Monomorphic, Without_FOOL)
val TF1 = TFF (Polymorphic, Without_FOOL)
val TX0 = TFF (Monomorphic, With_FOOL {with_ite = true, with_let = true})
val TX0_MINUS = TFF (Monomorphic, With_FOOL {with_ite = false, with_let = false})
val TX1 = TFF (Polymorphic, With_FOOL {with_ite = true, with_let = true})
val TH0 = THF (Monomorphic, {with_ite = true, with_let = true}, THF_With_Choice)
val TH0_MINUS = THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice)
val TH1 = THF (Polymorphic, {with_ite = true, with_let = true}, THF_With_Choice)
val TH1_MINUS = THF (Polymorphic, {with_ite = false, with_let = false}, THF_Without_Choice)

val default_max_mono_iters = 3 (* FUDGE *)
val default_max_new_mono_instances = 100 (* FUDGE *)

(* desired slice size, abduce, falsify, desired number of facts, fact filter *)
type base_slice = int * bool * bool * int * string

(* problem file format, type encoding, lambda translation scheme, uncurried aliases?,
   prover-specific extra information *)
type atp_slice = atp_format * string * string * bool * string

type atp_config =
  {exec : string list * string list,
   arguments : bool -> bool -> string -> Time.time -> Path.T -> string list,
   proof_delims : (string * string) list,
   known_failures : (atp_failure * string) list,
   prem_role : atp_formula_role,
   generate_isabelle_info : bool,
   good_slices : Proof.context -> (base_slice * atp_slice) list,
   good_max_mono_iters : int,
   good_max_new_mono_instances : int}

(* "good_slices" must be found empirically, ideally taking a holistic approach since the ATPs are
   run in parallel. *)

val mepoN = "mepo"
val mashN = "mash"
val meshN = "mesh"

val tstp_proof_delims =
  [("% SZS output start CNFRefutation", "% SZS output end CNFRefutation"),
   ("% SZS output start Refutation", "% SZS output end Refutation"),
   ("% SZS output start Proof", "% SZS output end Proof")]

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

structure Data = Theory_Data
(
  type T = ((unit -> atp_config) * stamp) Symtab.table
  val empty = Symtab.empty
  fun merge data : T =
    Symtab.merge (eq_snd (op =)) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name)
)

fun to_secs min time = Int.max (min, (Time.toMilliseconds time + 999) div 1000)

val sosN = "sos"
val no_sosN = "no_sos"


(* agsyHOL *)

val agsyhol_config : atp_config =
  {exec = (["AGSYHOL_HOME"], ["agsyHOL"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem =>
     ["--proof --time-out " ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((2, false, false, 60, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
   good_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   good_max_new_mono_instances = default_max_new_mono_instances}

val agsyhol = (agsyholN, fn () => agsyhol_config)


(* Alt-Ergo *)

val alt_ergo_config : atp_config =
  {exec = (["WHY3_HOME"], ["why3"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem =>
     ["--format tptp --prover 'Alt-Ergo,0.95.2,' --timelimit " ^ string_of_int (to_secs 1 timeout) ^
      " " ^ File.bash_path problem],
   proof_delims = [],
   known_failures =
     [(ProofMissing, ": Valid"),
      (TimedOut, ": Timeout"),
      (GaveUp, ": Unknown")],
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((1000 (* infinity *), false, false, 100, meshN), (TF1, "poly_native", liftingN, false, ""))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val alt_ergo = (alt_ergoN, fn () => alt_ergo_config)


(* E *)

local

fun make_e_config max_new_mono_insts good_slices : atp_config =
  {exec = (["E_HOME"], ["eprover-ho", "eprover"]),
   arguments = fn abduce => fn _ => fn extra_options => fn timeout => fn problem =>
     ["--tstp-in --tstp-out --silent " ^
      (if abduce then
         "--auto --print-saturated=ieIE --print-sat-info --soft-cpu-limit="
       else
         extra_options ^ " --cpu-limit=") ^
      string_of_int (to_secs 2 timeout) ^ " --proof-object=1 " ^ File.bash_path problem],
   proof_delims =
     [("# SZS output start CNFRefutation", "# SZS output end CNFRefutation")] @
     tstp_proof_delims,
   known_failures =
     [(TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded")] @
     known_szs_status_failures,
   prem_role = Conjecture,
   generate_isabelle_info = false,
   good_slices = K good_slices,
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = max_new_mono_insts}

val e_config : atp_config =
  (* FUDGE: this solved 950/1500 (63.33 %) using MePo when testing *)
  let
    val extra_options = "--auto-schedule"
    val good_slices =
      [(((2, false, false,  128, meshN), (TX0_MINUS, "mono_native_fool", liftingN, false, extra_options))),
       (((2, false, false, 1024, meshN), (TH0, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  128, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false, 2048, meshN), (TF0, "mono_native", combsN, false, extra_options))),
       (((2, false, false,  512, meshN), (TF0, "mono_native", liftingN, false, extra_options))),
       (((2, false, false, 1024, meshN), (TX0_MINUS, "mono_native_fool", liftingN, false, extra_options))),
       (((2, false, false,   64, meshN), (TH0, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  512, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,   32, meshN), (TF0, "mono_native", liftingN, false, extra_options))),
       (((2, false, false, 2048, meshN), (TH0, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  256, meshN), (TH0, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  512, meshN), (TF0, "mono_native", combsN, false, extra_options))),
       (((2, false, false, 1024, meshN), (TF0, "mono_native", liftingN, false, extra_options))),
       (((2, false, false,   16, meshN), (TH0, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  512, meshN), (TX0_MINUS, "mono_native_fool", liftingN, false, extra_options))),
       (((2, false, false,   64, meshN), (TF0, "mono_native", liftingN, false, extra_options))),
       (((2, false, false,  128, meshN), (TF0, "mono_native", combsN, false, extra_options))),
       (((2, false, false, 2048, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, extra_options))),
       (((2, false, false,  128, meshN), (TX0_MINUS, "mono_native_fool", combsN, false, extra_options))),
       (((2, false, false, 2048, meshN), (TX0_MINUS, "mono_native_fool", liftingN, false, extra_options)))]
    in
      make_e_config 128 good_slices
    end

in

val e = (eN, fn () => e_config)

end


(* iProver *)

val iprover_config : atp_config =
  {exec = (["IPROVER_HOME"], ["iproveropt", "iprover"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem =>
     ["--clausifier \"$VAMPIRE_HOME\"/vampire " ^
      "--clausifier_options \"--mode clausify\" " ^
      "--time_out_real " ^ string_of_real (Time.toReal timeout) ^ " " ^ File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures =
     [(ProofIncomplete, "% SZS output start CNFRefutation")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((2, false, false, 32, meshN), (TF0, "mono_native", liftingN, false, "")),
       ((2, false, false, 512, meshN), (TX0, "mono_native", liftingN, false, "")),
       ((2, false, false, 128, mashN), (TF0, "mono_native", combsN, false, "")),
       ((2, false, false, 1024, meshN), (TF0, "mono_native", liftingN, false, "")),
       ((2, false, true, 256, mepoN), (TF0, "mono_native", combsN, false, ""))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val iprover = (iproverN, fn () => iprover_config)


(* LEO-II *)

val leo2_config : atp_config =
  {exec = (["LEO2_HOME"], ["leo.opt", "leo"]),
   arguments = fn _ => fn full_proofs => fn _ => fn timeout => fn problem =>
     ["--foatp e --atp e=\"$E_HOME\"/eprover \
      \--atp epclextract=\"$E_HOME\"/epclextract \
      \--proofoutput 1 --timeout " ^ string_of_int (to_secs 1 timeout) ^ " " ^
      (if full_proofs then "--notReplLeibnizEQ --notReplAndrewsEQ --notUseExtCnfCmbd " else "") ^
      File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures =
     [(TimedOut, "CPU time limit exceeded, terminating"),
      (GaveUp, "No.of.Axioms")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((2, false, false, 40, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
   good_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   good_max_new_mono_instances = default_max_new_mono_instances}

val leo2 = (leo2N, fn () => leo2_config)


(* Leo-III *)

(* Include choice? Disabled now since it's disabled for Satallax as well. *)
val leo3_config : atp_config =
  {exec = (["LEO3_HOME"], ["leo3"]),
   arguments = fn _ => fn full_proofs => fn _ => fn timeout => fn problem =>
     [File.bash_path problem ^ " " ^ "--atp cvc=\"$CVC5_SOLVER\" --atp e=\"$E_HOME\"/eprover \
      \-p -t " ^ string_of_int (to_secs 1 timeout) ^ " " ^
      (if full_proofs then "--nleq --naeq " else "")],
   proof_delims = tstp_proof_delims,
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((6, false, false, 512, meshN), (TH0, "mono_native_higher", keep_lamsN, false, "")),
       ((6, false, false, 512, meshN), (TF0, "mono_native", liftingN, false, ""))],
   good_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   good_max_new_mono_instances = default_max_new_mono_instances}

val leo3 = (leo3N, fn () => leo3_config)


(* Satallax *)

(* Choice is disabled until there is proper reconstruction for it. *)
val satallax_config : atp_config =
  {exec = (["SATALLAX_HOME"], ["satallax.opt", "satallax"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem =>
     [(case getenv "E_HOME" of
        "" => ""
      | home => "-E " ^ home ^ "/eprover ") ^
      "-p tstp -t " ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem],
   proof_delims =
     [("% SZS output start Proof", "% SZS output end Proof")],
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices =
     (* FUDGE *)
     K [((12, false, false, 256, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
   good_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   good_max_new_mono_instances = default_max_new_mono_instances}

val satallax = (satallaxN, fn () => satallax_config)


(* SPASS *)

val spass_H1SOS = "-Heuristic=1 -SOS"
val spass_H2 = "-Heuristic=2"
val spass_H2LR0LT0 = "-Heuristic=2 -LR=0 -LT=0"
val spass_H2NuVS0 = "-Heuristic=2 -RNuV=1 -Sorts=0"
val spass_H2NuVS0Red2 = "-Heuristic=2 -RNuV=1 -Sorts=0 -RFRew=2 -RBRew=2 -RTaut=2"
val spass_H2SOS = "-Heuristic=2 -SOS"

val spass_config : atp_config =
  {exec = (["SPASS_HOME"], ["SPASS"]),
   arguments = fn _ => fn full_proofs => fn extra_options => fn timeout => fn problem =>
     ["-Isabelle=1 " ^ (if full_proofs then "-CNFRenaming=0 -Splits=0 " else "") ^
      "-TimeLimit=" ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem
      |> extra_options <> "" ? prefix (extra_options ^ " ")],
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     [(GaveUp, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (Unprovable, "No formulae and clauses found in input file"),
      (InternalError, "Please report this error")],
   prem_role = Conjecture,
   generate_isabelle_info = true,
   good_slices =
     (* FUDGE *)
     K [((2, false, false, 150, meshN), (DFG Monomorphic, "mono_native", combsN, true, "")),
      ((2, false, false, 500, meshN), (DFG Monomorphic, "mono_native", liftingN, true, spass_H2SOS)),
      ((2, false, false, 50, meshN), (DFG Monomorphic,  "mono_native", liftingN, true, spass_H2LR0LT0)),
      ((2, false, false, 250, meshN), (DFG Monomorphic, "mono_native", combsN, true, spass_H2NuVS0)),
      ((2, false, false, 1000, mepoN), (DFG Monomorphic, "mono_native", liftingN, true, spass_H1SOS)),
      ((2, false, true, 150, meshN), (DFG Monomorphic, "poly_guards??", liftingN, false, spass_H2NuVS0Red2)),
      ((2, false, false,  300, meshN), (DFG Monomorphic, "mono_native", combsN, true, spass_H2SOS)),
      ((2, false, false, 100, meshN), (DFG Monomorphic, "mono_native", combs_and_liftingN, true, spass_H2))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val spass = (spassN, fn () => spass_config)


(* Vampire *)

local

val new_vampire_basic_options =
  ["--input_syntax tptp",
   "--proof tptp",
   "--output_axiom_names on"] @
  (if ML_System.platform_is_windows
   then []  (*time slicing is not support in the Windows version of Vampire*)
   else ["--mode portfolio", "--schedule snake_slh"])

val vampire_full_proof_options =
  ["--proof_extra free",
   "--forced_options avatar=off:equality_proxy=off:general_splitting=off:inequality_splitting=0:naming=0"]

fun make_vampire_config vampire_basic_options good_max_new_mono_instances good_slices : atp_config =
  {exec = (["VAMPIRE_HOME"], ["vampire"]),
   arguments = fn _ => fn full_proofs => fn extra_options => fn timeout => fn problem =>
     vampire_basic_options @
     (if full_proofs then vampire_full_proof_options else []) @
     (if extra_options <> "" then [extra_options] else []) @
     ["-t " ^ string_of_int (to_secs 1 timeout),
      "--input_file " ^ File.bash_path problem],
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation =======")] @
     tstp_proof_delims,
   known_failures =
     [(GaveUp, "UNPROVABLE"),
      (GaveUp, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (Unprovable, "Termination reason: Satisfiable"),
      (Interrupted, "Aborted by signal SIGINT")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   generate_isabelle_info = false,
   good_slices = K good_slices,
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = good_max_new_mono_instances}

val vampire_config : atp_config =
  (* FUDGE: this solved 998/1500 (66.53 %) using MePo when testing *)
  make_vampire_config new_vampire_basic_options 256
    [(((2, false, false,  512, meshN), (TX0, "mono_native_fool", liftingN, false, ""))),
     (((2, false, false, 2048, meshN), (TX0, "mono_native_fool", combsN, false, ""))),
     (((2, false, false,  128, meshN), (TX0, "mono_native_fool", liftingN, false, ""))),
     (((2, false, false, 1024, meshN), (TF1, "poly_native", liftingN, false, ""))),
     (((2, false, false,  256, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, ""))),
     (((2, false, false, 1024, meshN), (TX0, "mono_native_fool", liftingN, false, ""))),
     (((2, false, false,  256, meshN), (TX0, "mono_native_fool", liftingN, false, ""))),
     (((2, false, false, 2048, meshN), (TF1, "poly_native", combsN, false, ""))),
     (((2, false, false,  256, meshN), (TX1, "poly_native_fool", liftingN, false, ""))),
     (((2, false, false,  512, meshN), (TF0, "mono_native", liftingN, false, ""))),
     (((2, false, false, 2048, meshN), (TF0, "mono_native", liftingN, false, ""))),
     (((2, false, false,   64, meshN), (TF1, "poly_native", combsN, false, ""))),
     (((2, false, false,  256, meshN), (TH1_MINUS, "poly_native_higher", keep_lamsN, false, ""))),
     (((2, false, false,  256, meshN), (TF0, "mono_native", combsN, false, ""))),
     (((2, false, false,  256, meshN), (TF0, "mono_native", liftingN, false, ""))),
     (((2, false, false,   32, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, ""))),
     (((2, false, false,  512, meshN), (TH0_MINUS, "mono_native_higher", keep_lamsN, false, ""))),
     (((2, false, false,  512, meshN), (TX0, "mono_native_fool", combsN, false, ""))),
     (((2, false, false, 1024, meshN), (TX1, "poly_native_fool", combsN, false, "")))]

in

val vampire = (vampireN, fn () => vampire_config)

end

(* Zipperposition *)

val zipperposition_config : atp_config =
  let
    val format =
      THF (Polymorphic, {with_ite = true, with_let = false}, THF_Without_Choice)
  in
    {exec = (["ZIPPERPOSITION_HOME"], ["zipperposition"]),
     arguments = fn _ => fn _ => fn extra_options => fn timeout => fn problem =>
       ["--input tptp", "--output tptp", "--timeout " ^ Time.toString timeout, extra_options,
        File.bash_path problem],
     proof_delims = tstp_proof_delims,
     known_failures =
       [(TimedOut, "SZS status ResourceOut")] @   (* odd way of timing out *)
       known_szs_status_failures,
     prem_role = Hypothesis,
     generate_isabelle_info = true,
     good_slices =
       K [((1, false, false, 512, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --max-inferences=1 --ho-unif-max-depth=1 --ho-max-elims=0 --ho-max-app-projections=0 --ho-max-rigid-imitations=1 --ho-max-identifications=0 --boolean-reasoning=bool-hoist --bool-hoist-simpl=true --bool-select=LI --recognize-injectivity=true --ext-rules=ext-family --ext-rules-max-depth=1 --ho-choice-inst=true --ho-prim-enum=none --ho-elim-leibniz=0 --interpret-bool-funs=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --ho-unif-level=pragmatic-framework --select=bb+e-selection2 --post-cnf-lambda-lifting=true -q \"4|prefer-sos|pnrefined(2,1,1,1,2,2,2)\" -q \"6|prefer-processed|conjecture-relative-struct(1.5,3.5,2,3)\" -q \"1|const|fifo\" -q \"4|prefer-ground|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-struct(1,5,2,3)\" --avatar=off --recognize-injectivity=true --ho-neg-ext=true --e-timeout=2 --ho-pattern-decider=true --ho-fixpoint-decider=true --e-max-derived=50 --ignore-orphans=true --e-auto=true --presaturate=true --e-call-point=0.1")),  (* sh5_sh1.sh *)
          ((1, false, false, 512, mepoN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic -nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0 --ho-unif-max-depth=3 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection7 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=7 --sine=50 --sine-tolerance=1 --sine-depth-max=2 --sine-depth-min=1 --e-max-derived=64 --sine-ignore-k-most-common-syms=2 --sine-trim-implications=true --e-encode-lambdas=lift --scan-clause-ac=false --lambdasup=0 --kbo-weight-fun=lambda-def-invfreqrank --demod-in-var-args=true --bool-demod=true --lambda-demod=true --e-call-point=0.1")),  (* sh10_c_ic.sh *)
          ((1, false, false, 1024, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=2 --ho-unif-max-depth=1 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection16 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --sine=50 --sine-tolerance=1.0 --sine-depth-max=3 --sine-depth-min=1 --sine-trim-implications=true --ho-unif-level=pragmatic-framework --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=lambda-def-invfreqrank --e-call-point=0.1")),  (* sh8_shallow_sine.sh *)
          ((1, false, false, 256, mepoN), (format, "mono_native_higher_fool", keep_lamsN, false, "-nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=off --ho-prim-enum=full --ho-prim-max=1 --avatar=off --recognize-injectivity=true --ho-elim-leibniz=4 --ho-unif-level=full-framework --no-max-vars -q \"2|prefer-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1)\" -q \"4|const|conjecture-relative-e(0.1,1,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1.5)\" -q \"4|prefer-sos|pnrefined(1,1,1,1,2,1.5,2)\" --select=ho-selection5 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=5 --e-call-point=0.25 --e-auto=true --sine=50 --sine-tolerance=2 --sine-depth-max=4 --sine-depth-min=1 --e-max-derived=96 --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=arity0 --prec-gen-fun=invfreq_conj")),  (* sh10_new_c.s3.sh *)
          ((1, false, true, 512, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-comb-complete --boolean-reasoning=simpl-only --ext-rules=off --kbo-weight-fun=lambda-def-sqarity --ho-prim-enum=none --tptp-def-as-rewrite -q \"4|prefer-sos|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-var(1,s,f)\" -q \"3|const|default\" -q \"1|prefer-processed|fifo\" --ho-elim-leibniz=1 --select=NoSelection --solve-formulas=true --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=8 --sine=60 --sine-tolerance=2 --sine-depth-max=5 --sine-depth-min=1 --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --e-max-derived=50 --e-encode-lambdas=lift --scan-clause-ac=false --presaturate=true --comb-b-penalty=3 --comb-c-penalty=3 --comb-k-penalty=1 --comb-s-penalty=5 --subvarsup=false --e-call-point=0.15")),  (* sh8_b.comb.sh (modified) *)
          ((1, false, false, 1024, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --boolean-reasoning=simpl-only --ho-unif-max-depth=0 --ho-prim-enum=none -q \"2|prefer-ho-steps|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"2|prefer-ground|default\" -q \"2|prefer-empty-trail|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" --select=bb+e-selection7 --ho-pattern-decider=false --ho-fixpoint-decider=true --ho-solid-decider=false --sine=150 --sine-tolerance=2 --sine-depth-max=3 --sine-depth-min=1 --prec-gen-fun=invfreqhack --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=2 --fluid-log-hoist=false --tptp-def-as-rewrite --rewrite-before-cnf=true --ho-prim-enum=eq --ho-prim-enum-add-var=true --ho-prim-max=1 --ho-prim-enum-early-bird=true --avatar=eager --split-only-ground=true")),  (* sh5_add_var_l_av.sh *)
          ((1, false, false, 256, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0 --ho-unif-max-depth=2 --max-inferences=3 --boolean-reasoning=bool-hoist --bool-select=LO --ext-rules=off --kbo-weight-fun=lambda-def-invfreqrank --ho-prim-enum=none --ho-unif-level=pragmatic-framework -q \"1|prefer-sos|conjecture-relative-var(1.01,s,f)\" -q \"4|const|conjecture-relative-var(1.05,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1.02,l,f)\" -q \"4|prefer-sos|pnrefined(3,2,3,2,2,1.5,2)\" --ho-elim-leibniz=1 --ho-fixpoint-decider=true --ho-pattern-decider=true --ho-solid-decider=true --select=e-selection2 --solve-formulas=true --lambdasup=0 --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-max-derived=48 --e-encode-lambdas=lift --presaturate=true --prec-gen-fun=invfreq --e-call-point=0.2 --e-auto=true --sine-trim-implications=true")),  (* sh10_e_lift.sh *)
          ((1, false, false, 512, mepoN), (format, "mono_native_higher_fool", keep_lamsN, false, "-nc --tptp-def-as-rewrite --mode=ho-pragmatic --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=1 --ho-max-identifications=0 --ho-unif-max-depth=2 --boolean-reasoning=simpl-only --ext-rules=off --kbo-weight-fun=lambda-def-const --ho-prim-enum=neg --ho-prim-enum-early-bird=true --tptp-def-as-rewrite --rewrite-before-cnf=true --ho-unif-level=pragmatic-framework --ho-unif-max-depth=1 --sine=50 --sine-tolerance=1.0 --sine-depth-max=3 --sine-depth-min=1 --sine-trim-implications=true -q \"4|prefer-sos|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-var(1,s,f)\" -q \"3|const|default\" -q \"1|prefer-processed|fifo\" --ho-elim-leibniz=1 --ho-fixpoint-decider=true --ho-pattern-decider=true --ho-solid-decider=false --select=e-selection10 --solve-formulas=true --sup-at-vars=false --sup-at-var-headed=false --sup-from-var-headed=true --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=4 --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=2 --e-auto=true --e-max-derived=32 --e-encode-lambdas=lift --scan-clause-ac=false --presaturate=true --e-call-point=0.16")),  (* sh5_shallow_sine.sh *)
          ((1, false, false, 512, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "-nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=bool-hoist --ext-rules=off --recognize-injectivity=true --ho-unif-level=full-framework -q \"4|prefer-goals|pnrefined(1,1,1,2,2,2,0.5)\" -q \"1|prefer-fo|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-ho-steps|conjecture-relative-var(1.01,s,f)\" -q \"1|prefer-processed|fifo\" --select=bb+ho-selection --scan-clause-ac=false --kbo-weight-fun=invfreqrank --fluidsup=true --boolean-reasoning=bool-hoist --fluid-log-hoist=true --fluid-hoist=true --ite-axioms=true --lazy-cnf=true --ho-solid-decider=true --ho-fixpoint-decider=true --bool-select=\"sel1(pos_ctx)\" --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=2 --e-auto=true --e-call-point=0.35 --avatar=off --e-max-derived=50")),  (* sh5_e_short1.sh *)
          ((1, false, false, 1024, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --boolean-reasoning=simpl-only --select=e-selection12 --prec-gen-fun=invfreq_conj --ord=lambda_kbo --ho-unif-level=full-framework --ho-pattern-decider=true --ho-solid-decider=false --ho-fixpoint-decider=true --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=1 --sine=100 --sine-depth-min=1 --sine-depth-max=5 --sine-tolerance=1.5 -q \"1|prefer-sos|default\" -q \"8|prefer-processed|conjecture-relative-var(1,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-lambdas|explore\" -q \"1|prefer-non-goals|explore\" -q \"1|prefer-processed|conjecture-relative-var(1,s,f)\" --kbo-weight-fun=arity0")),  (* sh5_32.sh *)
          ((1, false, false, 256, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --boolean-reasoning=simpl-only --ho-unif-max-depth=2 --ho-max-app-projections=0 --ho-max-rigid-imitations=1 --ho-max-elims=0 --ho-max-identifications=1 --max-inferences=3 --ext-rules=off --recognize-injectivity=true --ho-prim-enum=none --ho-choice-inst=true -q \"3|prefer-fo|conjecture-relative-var(1.02,l,f)\" -q \"3|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"2|prefer-ground|orient-lmax(2,1,2,1,1)\" -q \"1|prefer-processed|fifo\" --select=MaxGoalNS --sine=60 --sine-tolerance=1.5 --sine-depth-max=3 --sine-depth-min=1 --prec-gen-fun=invfreqhack --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=3 --kbo-weight-fun-from-precedence=true --kbo-weight-fun-from-precedence-rank=5 --trigger-bool-inst=1 --avatar=lazy --tptp-def-as-rewrite --rewrite-before-cnf=true --sup-from-var-headed=false --sup-at-vars=false")),  (* sh5_sh4.sh *)
          ((1, false, false, 512, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "--tptp-def-as-rewrite --rewrite-before-cnf=true --mode=lambda-free-intensional --check-lambda-free=false --boolean-reasoning=simpl-only --post-cnf-lambda-lifting=true --ext-rules=off --ho-prim-enum=none --recognize-injectivity=true --no-max-vars --select=e-selection8 --prec-gen-fun=invfreq --kbo-weight-fun=invfreqrank --kbo-const-weight=2 --ord=lambdafree_kbo --ignore-orphans=true -q \"1|prefer-sos|conjecture-relative-struct(1.5,3.5,2,3)\" -q \"1|const|conj_pref_weight(0.5,100,0.2,0.2,4)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-e(0.3,0.25,100,100,100,100,1.5,1.5,1)\" -q \"1|prefer-sos|pnrefined(3,2,3,2,2,1.5,2)\" --lazy-cnf=true --lazy-cnf-renaming-threshold=2")),  (* sh5_lifting2.sh *)
          ((1, false, false, 512, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "-nc --tptp-def-as-rewrite --rewrite-before-cnf=true --tptp-rewrite-formulas-only=true --mode=ho-pragmatic --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=neg --ho-prim-max=1 --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars -q \"1|prefer-sos|conjecture-relative-var(1.02,l,f)\" -q \"4|const|conjecture-relative-var(1,s,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-sos|pnrefined(2,1,1,1,2,2,2)\" --select=e-selection7 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=2 --e-auto=true --sine=50 --sine-tolerance=10 --sine-depth-max=5 --sine-depth-min=1 --e-max-derived=64 --e-encode-lambdas=lift --scan-clause-ac=false --prec-gen-fun=invfreq_conj --ord=lambda_kbo --solid-subsumption=true --ignore-orphans=true --e-call-point=0.2")),  (* sh5_noforms.sh *)
          ((1, false, false, 1024, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --max-inferences=4 --ho-unif-max-depth=3 --ho-max-elims=0 --ho-max-app-projections=1 --ho-max-identifications=0 --ho-max-rigid-imitations=2 --ho-unif-level=pragmatic-framework --boolean-reasoning=simpl-only --kbo-weight-fun=freqrank --ext-rules=ext-family --ext-rules-max-depth=2 --ho-prim-enum=eq --ho-prim-max=2 --interpret-bool-funs=false -q \"2|prefer-goals|default\" -q \"8|prefer-sos|conjecture-relative-var(1,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-lambdas|explore\" -q \"1|prefer-non-goals|explore\" -q \"1|prefer-processed|conjecture-relative-var(1,s,f)\" --recognize-injectivity=true --ho-selection-restriction=none --select=ho-selection2 --solve-formulas=true")),  (* sh8_old_zip1.sh *)
          ((1, false, false, 256, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --boolean-reasoning=simpl-only --tptp-def-as-rewrite --rewrite-before-cnf=true --kbo-weight-fun=freqrank -q \"1|prefer-sos|default\" -q \"1|prefer-goals|conjecture-relative-var(1.03,s,f)\" -q \"1|prefer-non-goals|default\" -q \"5|const|conjecture-relative-var(1.01,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|const|conjecture-relative-var(1.05,l,f)\" -q \"1|defer-sos|conjecture-relative-var(1.1,s,f)\" --select=e-selection9 --recognize-injectivity=true --ho-choice-inst=false --ho-selection-restriction=none --sine=50 --sine-tolerance=3 --sine-depth-max=3 --sine-depth-min=1 --eq-encode=true --avatar=eager --sine-trim-implications=true"))],  (* sh5_sh.eqenc.sh *)
     good_max_mono_iters = default_max_mono_iters,
     good_max_new_mono_instances = default_max_new_mono_instances}
  end

val zipperposition = (zipperpositionN, fn () => zipperposition_config)


(* Remote ATP invocation via SystemOnTPTP *)

val no_remote_systems = {url = "", systems = [] : string list}
val remote_systems = Synchronized.var "atp_remote_systems" no_remote_systems

fun get_remote_systems () =
  Timeout.apply (seconds 10.0) SystemOnTPTP.list_systems ()
    handle ERROR msg => (warning msg; no_remote_systems)
      | Timeout.TIMEOUT _ => no_remote_systems

fun find_remote_system name [] systems =
    find_first (String.isPrefix (name ^ "---")) systems
  | find_remote_system name (version :: versions) systems =
    case find_first (String.isPrefix (name ^ "---" ^ version)) systems of
      NONE => find_remote_system name versions systems
    | res => res

fun get_remote_system name versions =
  Synchronized.change_result remote_systems (fn remote =>
    (if #url remote <> SystemOnTPTP.get_url () orelse null (#systems remote)
      then get_remote_systems () else remote) |> ` #systems)
  |> `(find_remote_system name versions)

fun the_remote_system name versions =
  (case get_remote_system name versions of
    (SOME sys, _) => sys
  | (NONE, []) => error "SystemOnTPTP is currently not available"
  | (NONE, syss) =>
    (case syss |> filter_out (String.isPrefix "%") |> filter_out (curry (op =) "") of
      [] => error "SystemOnTPTP is currently not available"
    | [msg] => error ("SystemOnTPTP is currently not available: " ^ msg)
    | syss =>
      error ("System " ^ quote name ^ " is not available at SystemOnTPTP.\n(Available systems: " ^
        commas_quote syss ^ ".)")))

val max_remote_secs = 1000   (* give Geoff Sutcliffe's servers a break *)

val isabelle_scala_function = (["SCALA_HOME"], ["bin/scala"])

fun remote_config system_name system_versions proof_delims known_failures prem_role
    generate_isabelle_info good_slice =
  {exec = isabelle_scala_function,
   arguments = fn _ => fn _ => fn command => fn timeout => fn problem =>
     [the_remote_system system_name system_versions,
      Isabelle_System.absolute_path problem,
      command, string_of_int (Int.min (max_remote_secs, to_secs 1 timeout) * 1000)],
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_says_failures,
   prem_role = prem_role,
   generate_isabelle_info = generate_isabelle_info,
   good_slices = fn ctxt => [good_slice ctxt],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances} : atp_config

fun remotify_config system_name system_versions good_slice
    ({proof_delims, known_failures, prem_role, generate_isabelle_info, ...} : atp_config) =
  remote_config system_name system_versions proof_delims known_failures prem_role
    generate_isabelle_info good_slice

fun remote_atp name system_name system_versions proof_delims known_failures prem_role
    generate_isabelle_info good_slice =
  (remote_prefix ^ name, fn () =>
     remote_config system_name system_versions proof_delims known_failures prem_role
       generate_isabelle_info good_slice)
fun remotify_atp (name, config) system_name system_versions good_slice =
  (remote_prefix ^ name, remotify_config system_name system_versions good_slice o config)

fun gen_remote_waldmeister name type_enc =
  remote_atp name "Waldmeister" ["710"] tstp_proof_delims
    ([(OutOfResources, "Too many function symbols"),
      (Inappropriate, "****  Unexpected end of file."),
      (Crashed, "Unrecoverable Segmentation Fault")]
     @ known_szs_status_failures)
    Hypothesis false
    (K ((1000 (* infinity *), false, false, 50, meshN), (CNF_UEQ, type_enc, combsN, false, "")) (* FUDGE *))

val remote_agsyhol =
  remotify_atp agsyhol "agsyHOL" ["1.0", "1"]
    (K ((1000 (* infinity *), false, false, 60, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, "")) (* FUDGE *))
val remote_alt_ergo =
  remotify_atp alt_ergo "Alt-Ergo" ["0.95.2"]
    (K ((1000 (* infinity *), false, false, 250, meshN), (TF1, "poly_native", keep_lamsN, false, "")) (* FUDGE *))
val remote_e =
  remotify_atp e "E" ["2.0", "1.9.1", "1.8"]
    (K ((1000 (* infinity *), false, false, 750, meshN), (TF0, "mono_native", combsN, false, "")) (* FUDGE *))
val remote_iprover =
  remotify_atp iprover "iProver" ["0.99"]
    (K ((1000 (* infinity *), false, false, 150, meshN), (FOF, "mono_guards??", liftingN, false, "")) (* FUDGE *))
val remote_leo2 =
  remotify_atp leo2 "LEO-II" ["1.5.0", "1.4", "1.3", "1.2", "1"]
    (K ((1000 (* infinity *), false, false, 40, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", liftingN, false, "")) (* FUDGE *))
val remote_leo3 =
  remotify_atp leo3 "Leo-III" ["1.1"]
    (K ((1000 (* infinity *), false, false, 150, meshN), (THF (Polymorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "poly_native_higher", keep_lamsN, false, "")) (* FUDGE *))
val remote_waldmeister = gen_remote_waldmeister waldmeisterN "raw_mono_tags??"
val remote_zipperposition =
  remotify_atp zipperposition "Zipperpin" ["2.1", "2.0"]
    (K ((1000 (* infinity *), false, false, 512, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, "")) (* FUDGE *))


(* Dummy prover *)

fun dummy_config prem_role format type_enc uncurried_aliases : atp_config =
  {exec = (["ISABELLE_ATP"], ["scripts/dummy_atp"]),
   arguments = K (K (K (K (K [])))),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   prem_role = prem_role,
   generate_isabelle_info = false,
   good_slices =
     K [((2, false, false, 256, "mepo"), (format, type_enc,
      if is_format_higher_order format then keep_lamsN else combsN, uncurried_aliases, ""))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val dummy_fof =
  (dummy_fofN, fn () => dummy_config Hypothesis FOF "mono_guards??" false)

val dummy_tfx =
  (dummy_tfxN, fn () => dummy_config Hypothesis TX1 "poly_native_fool" false)

val dummy_thf =
  (dummy_thfN, fn () => dummy_config Hypothesis TH1 "poly_native_higher" false)

val dummy_thf_reduced =
  let
    val format = THF (Polymorphic, {with_ite = false, with_let = false}, THF_Without_Choice)
    val config = dummy_config Hypothesis format "poly_native_higher" false
  in (dummy_thfN ^ "_reduced", fn () => config) end

(* Setup *)

fun add_atp (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name)

fun get_atp thy name =
  fst (the (Symtab.lookup (Data.get thy) name))
  handle Option.Option => error ("Unknown ATP: " ^ name)

fun is_atp_installed thy name =
  let val {exec, ...} = get_atp thy name () in
    exists (fn var => getenv var <> "") (fst exec)
  end

fun refresh_systems_on_tptp () =
  Synchronized.change remote_systems (fn _ => get_remote_systems ())

val local_atps =
  [agsyhol, alt_ergo, e, iprover, leo2, leo3, satallax, spass, vampire, zipperposition]
val remote_atps =
  [remote_agsyhol, remote_alt_ergo, remote_e, remote_iprover, remote_leo2, remote_leo3,
   remote_waldmeister, remote_zipperposition]
val dummy_atps =
  [dummy_fof, dummy_tfx, dummy_thf, dummy_thf_reduced]
val non_dummy_atps = local_atps @ remote_atps
val all_atps = non_dummy_atps @ dummy_atps

val _ = Theory.setup (fold add_atp all_atps)

val local_atps = map fst local_atps
val remote_atps = map fst remote_atps
val dummy_atps = map fst dummy_atps
val non_dummy_atps = map fst non_dummy_atps
val all_atps = map fst all_atps

end;
