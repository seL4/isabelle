(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature SLEDGEHAMMER_ATP_SYSTEMS =
sig
  type atp_format = ATP_Problem.atp_format
  type atp_formula_role = ATP_Problem.atp_formula_role
  type atp_failure = ATP_Proof.atp_failure

  type base_slice = int * int * string
  type atp_slice = atp_format * string * string * bool * string
  type atp_config =
    {exec : string list * string list,
     arguments : Proof.context -> bool -> string -> Time.time -> Path.T -> string list,
     proof_delims : (string * string) list,
     known_failures : (atp_failure * string) list,
     prem_role : atp_formula_role,
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
    (atp_failure * string) list -> atp_formula_role -> (Proof.context -> base_slice * atp_slice) ->
    string * (unit -> atp_config)
  val add_atp : string * (unit -> atp_config) -> theory -> theory
  val get_atp : theory -> string -> (unit -> atp_config)
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val local_atps : string list
  val remote_atps : string list
  val atps : string list
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
val TX1 = TFF (Polymorphic, With_FOOL {with_ite = true, with_let = true})
val TH0 = THF (Monomorphic, {with_ite = true, with_let = true}, THF_With_Choice)
val TH1 = THF (Polymorphic, {with_ite = true, with_let = true}, THF_With_Choice)

val default_max_mono_iters = 3 (* FUDGE *)
val default_max_new_mono_instances = 100 (* FUDGE *)

(* desired slice size, desired number of facts, fact filter *)
type base_slice = int * int * string

(* problem file format, type encoding, lambda translation scheme, uncurried aliases?,
   prover-specific extra information *)
type atp_slice = atp_format * string * string * bool * string

type atp_config =
  {exec : string list * string list,
   arguments : Proof.context -> bool -> string -> Time.time -> Path.T -> string list,
   proof_delims : (string * string) list,
   known_failures : (atp_failure * string) list,
   prem_role : atp_formula_role,
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
   good_slices =
     (* FUDGE *)
     K [((1, 60, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
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
   good_slices =
     (* FUDGE *)
     K [((1000 (* infinity *), 100, meshN), (TF1, "poly_native", liftingN, false, ""))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val alt_ergo = (alt_ergoN, fn () => alt_ergo_config)


(* E *)

val e_config : atp_config =
  {exec = (["E_HOME"], ["eprover-ho", "eprover"]),
   arguments = fn _ => fn _ => fn extra_options => fn timeout => fn problem =>
     ["--tstp-in --tstp-out --silent " ^ extra_options ^
      " --demod-under-lambda=true --cpu-limit=" ^ string_of_int (to_secs 2 timeout) ^
      " --proof-object=1 " ^ File.bash_path problem],
   proof_delims =
     [("# SZS output start CNFRefutation", "# SZS output end CNFRefutation")] @
     tstp_proof_delims,
   known_failures =
     [(TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded")] @
     known_szs_status_failures,
   prem_role = Conjecture,
   good_slices =
     let
       val (format, type_enc, lam_trans, extra_options) =
         if string_ord (getenv "E_VERSION", "2.7") <> LESS then
           (THF (Monomorphic, {with_ite = true, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, "--auto-schedule=4 --serialize-schedule=true")
         else if string_ord (getenv "E_VERSION", "2.6") <> LESS then
           (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, "--auto-schedule")
         else
           (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Lambda_Free), "mono_native_higher", combsN, "--auto-schedule")
     in
       (* FUDGE *)
       K [((1000 (* infinity *), 512, meshN), (format, type_enc, lam_trans, false, extra_options)),
         ((1000 (* infinity *), 1024, meshN), (format, type_enc, lam_trans, false, extra_options)),
         ((1000 (* infinity *), 128, mepoN), (format, type_enc, lam_trans, false, extra_options)),
         ((1000 (* infinity *), 724, meshN), (TF0, "poly_guards??", lam_trans, false, extra_options)),
         ((1000 (* infinity *), 256, mepoN), (format, type_enc, liftingN, false, extra_options)),
         ((1000 (* infinity *), 64, mashN), (format, type_enc, combsN, false, extra_options))]
     end,
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances}

val e = (eN, fn () => e_config)


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
   good_slices =
     (* FUDGE *)
     K [((1, 32, meshN), (TF0, "mono_native", liftingN, false, "")),
       ((1, 512, meshN), (TX0, "mono_native", liftingN, false, "")),
       ((1, 128, mashN), (TF0, "mono_native", combsN, false, "")),
       ((1, 1024, meshN), (TF0, "mono_native", liftingN, false, "")),
       ((1, 256, mepoN), (TF0, "mono_native", combsN, false, ""))],
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
   good_slices =
     (* FUDGE *)
     K [((1, 40, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
   good_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   good_max_new_mono_instances = default_max_new_mono_instances}

val leo2 = (leo2N, fn () => leo2_config)


(* Leo-III *)

(* Include choice? Disabled now since it's disabled for Satallax as well. *)
val leo3_config : atp_config =
  {exec = (["LEO3_HOME"], ["leo3"]),
   arguments = fn _ => fn full_proofs => fn _ => fn timeout => fn problem =>
     [File.bash_path problem ^ " " ^ "--atp cvc=\"$CVC4_SOLVER\" --atp e=\"$E_HOME\"/eprover \
      \-p -t " ^ string_of_int (to_secs 1 timeout) ^ " " ^
      (if full_proofs then "--nleq --naeq " else "")],
   proof_delims = tstp_proof_delims,
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   good_slices =
     (* FUDGE *)
     K [((3, 512, meshN), (TH0, "mono_native_higher", keep_lamsN, false, "")),
       ((3, 512, meshN), (TF0, "mono_native", liftingN, false, ""))],
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
   good_slices =
     (* FUDGE *)
     K [((6, 256, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, ""))],
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
  let
    val format = DFG Monomorphic
  in
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
     good_slices =
       (* FUDGE *)
       K [((1, 150, meshN), (format, "mono_native", combsN, true, "")),
        ((1, 500, meshN), (format, "mono_native", liftingN, true, spass_H2SOS)),
        ((1, 50, meshN), (format,  "mono_native", liftingN, true, spass_H2LR0LT0)),
        ((1, 250, meshN), (format, "mono_native", combsN, true, spass_H2NuVS0)),
        ((1, 1000, mepoN), (format, "mono_native", liftingN, true, spass_H1SOS)),
        ((1, 150, meshN), (format, "poly_guards??", liftingN, false, spass_H2NuVS0Red2)),
        ((1, 300, meshN), (format, "mono_native", combsN, true, spass_H2SOS)),
        ((1, 100, meshN), (format, "mono_native", combs_and_liftingN, true, spass_H2))],
     good_max_mono_iters = default_max_mono_iters,
     good_max_new_mono_instances = default_max_new_mono_instances}
  end

val spass = (spassN, fn () => spass_config)


(* Vampire *)

val vampire_basic_options =
  "--proof tptp --output_axiom_names on" ^
  (if ML_System.platform_is_windows
   then ""  (*time slicing is not support in the Windows version of Vampire*)
   else " --mode casc")

val vampire_full_proof_options =
  " --proof_extra free --forced_options avatar=off:equality_proxy=off:general_splitting=off:inequality_splitting=0:naming=0"

val vampire_config : atp_config =
  {exec = (["VAMPIRE_HOME"], ["vampire"]),
   arguments = fn _ => fn full_proofs => fn sos => fn timeout => fn problem =>
     [vampire_basic_options ^ (if full_proofs then " " ^ vampire_full_proof_options else "") ^
       " -t " ^ string_of_int (to_secs 1 timeout) ^ " --input_file " ^ File.bash_path problem
       |> sos = sosN ? prefix "--sos on "],
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
   good_slices =
     (* FUDGE *)
     K [((1, 512, meshN), (TX1, "mono_native_fool", combsN, false, sosN)),
      ((1, 1024, meshN), (TX1, "mono_native_fool", liftingN, false, sosN)),
      ((1, 256, mashN), (TX1, "mono_native_fool", liftingN, false, no_sosN)),
      ((1, 512, mepoN), (TF1, "poly_native", liftingN, false, no_sosN)),
      ((1, 16, meshN), (TX1, "mono_native_fool", liftingN, false, no_sosN)),
      ((1, 32, meshN), (TX1, "mono_native_fool", combsN, false, no_sosN)),
      ((1, 64, meshN), (TX1, "mono_native_fool", combs_or_liftingN, false, no_sosN)),
      ((1, 128, meshN), (TX1, "mono_native_fool", liftingN, false, no_sosN))],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = 2 * default_max_new_mono_instances (* FUDGE *)}

val vampire = (vampireN, fn () => vampire_config)


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
     good_slices =
       K [((1, 1024, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --max-inferences=1 --ho-unif-max-depth=1 --ho-max-elims=0 --ho-max-app-projections=0 --ho-max-rigid-imitations=1 --ho-max-identifications=0 --boolean-reasoning=bool-hoist --bool-hoist-simpl=true --bool-select=LI --recognize-injectivity=true --ext-rules=ext-family --ext-rules-max-depth=1 --ho-choice-inst=true --ho-prim-enum=none --ho-elim-leibniz=0 --interpret-bool-funs=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --ho-unif-level=pragmatic-framework --select=bb+e-selection2 --post-cnf-lambda-lifting=true -q \"4|prefer-sos|pnrefined(2,1,1,1,2,2,2)\" -q \"6|prefer-processed|conjecture-relative-struct(1.5,3.5,2,3)\" -q \"1|const|fifo\" -q \"4|prefer-ground|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-struct(1,5,2,3)\" --avatar=off --recognize-injectivity=true --ho-neg-ext=true --e-timeout=2 --ho-pattern-decider=true --ho-fixpoint-decider=true --e-max-derived=50 --ignore-orphans=true --e-auto=true --presaturate=true --e-call-point=0.1")),
         ((1, 128, mepoN), (format, "mono_native_higher_fool", keep_lamsN, false, "-nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=off --ho-prim-enum=full --ho-prim-max=1 --avatar=off --recognize-injectivity=true --ho-elim-leibniz=4 --ho-unif-level=full-framework --no-max-vars -q \"2|prefer-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1)\" -q \"4|const|conjecture-relative-e(0.1,1,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1.5)\" -q \"4|prefer-sos|pnrefined(1,1,1,1,2,1.5,2)\" --select=ho-selection5 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=5 --e-call-point=0.25 --e-auto=true --sine=50 --sine-tolerance=2 --sine-depth-max=4 --sine-depth-min=1 --e-max-derived=96 --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=arity0 --prec-gen-fun=invfreq_conj")),
         ((1, 512, mashN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=2 --ho-unif-max-depth=1 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection16 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --sine=50 --sine-tolerance=1.0 --sine-depth-max=3 --sine-depth-min=1 --sine-trim-implications=true --ho-unif-level=pragmatic-framework --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=lambda-def-invfreqrank --e-call-point=0.1")),
         ((1, 32, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic -nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0 --ho-unif-max-depth=3 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection7 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=7 --sine=50 --sine-tolerance=1 --sine-depth-max=2 --sine-depth-min=1 --e-max-derived=64 --sine-ignore-k-most-common-syms=2 --sine-trim-implications=true --e-encode-lambdas=lift --scan-clause-ac=false --lambdasup=0 --kbo-weight-fun=lambda-def-invfreqrank --demod-in-var-args=true --bool-demod=true --lambda-demod=true --e-call-point=0.1 --lazy-cnf-kind=simp")),
         ((1, 64, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-comb-complete --boolean-reasoning=simpl-only --ext-rules=off --kbo-weight-fun=lambda-def-sqarity --ho-prim-enum=none --tptp-def-as-rewrite -q \"4|prefer-sos|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-var(1,s,f)\" -q \"3|const|default\" -q \"1|prefer-processed|fifo\" --ho-elim-leibniz=1 --select=NoSelection --solve-formulas=true --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=8 --sine=60 --sine-tolerance=2 --sine-depth-max=5 --sine-depth-min=1 --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --e-max-derived=50 --e-encode-lambdas=ignore --scan-clause-ac=false --presaturate=true --comb-b-penalty=3 --comb-c-penalty=3 --comb-k-penalty=1 --comb-s-penalty=5 --subvarsup=false --e-call-point=0.15 --lazy-cnf-kind=simp --trigger-bool-ind=1")),
         ((1, 256, meshN), (format, "mono_native_higher_fool", keep_lamsN, false, "--mode=ho-pragmatic --boolean-reasoning=simpl-only --ho-unif-max-depth=0 --ho-prim-enum=none -q \"2|prefer-ho-steps|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"2|prefer-ground|default\" -q \"2|prefer-empty-trail|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" --select=bb+e-selection7 --ho-pattern-decider=false --ho-fixpoint-decider=true --ho-solid-decider=false --sine=150 --sine-tolerance=2 --sine-depth-max=3 --sine-depth-min=1 --prec-gen-fun=invfreqhack --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=2 --fluid-log-hoist=false --tptp-def-as-rewrite --rewrite-before-cnf=true --ho-prim-enum=eq --ho-prim-enum-add-var=true --ho-prim-max=1 --ho-prim-enum-early-bird=true -o tptp --avatar=eager --split-only-ground=true"))],
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

fun remote_config system_name system_versions proof_delims known_failures prem_role good_slice =
  {exec = isabelle_scala_function,
   arguments = fn _ => fn _ => fn command => fn timeout => fn problem =>
     [the_remote_system system_name system_versions,
      Isabelle_System.absolute_path problem,
      command, string_of_int (Int.min (max_remote_secs, to_secs 1 timeout) * 1000)],
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_says_failures,
   prem_role = prem_role,
   good_slices = fn ctxt => [good_slice ctxt],
   good_max_mono_iters = default_max_mono_iters,
   good_max_new_mono_instances = default_max_new_mono_instances} : atp_config

fun remotify_config system_name system_versions good_slice
    ({proof_delims, known_failures, prem_role, ...} : atp_config) =
  remote_config system_name system_versions proof_delims known_failures prem_role good_slice

fun remote_atp name system_name system_versions proof_delims known_failures prem_role good_slice =
  (remote_prefix ^ name, fn () =>
     remote_config system_name system_versions proof_delims known_failures prem_role good_slice)
fun remotify_atp (name, config) system_name system_versions good_slice =
  (remote_prefix ^ name, remotify_config system_name system_versions good_slice o config)

fun gen_remote_waldmeister name type_enc =
  remote_atp name "Waldmeister" ["710"] tstp_proof_delims
    ([(OutOfResources, "Too many function symbols"),
      (Inappropriate, "****  Unexpected end of file."),
      (Crashed, "Unrecoverable Segmentation Fault")]
     @ known_szs_status_failures)
    Hypothesis
    (K ((1000 (* infinity *), 50, meshN), (CNF_UEQ, type_enc, combsN, false, "")) (* FUDGE *))

val remote_agsyhol =
  remotify_atp agsyhol "agsyHOL" ["1.0", "1"]
    (K ((1000 (* infinity *), 60, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, "")) (* FUDGE *))
val remote_alt_ergo =
  remotify_atp alt_ergo "Alt-Ergo" ["0.95.2"]
    (K ((1000 (* infinity *), 250, meshN), (TF1, "poly_native", keep_lamsN, false, "")) (* FUDGE *))
val remote_e =
  remotify_atp e "E" ["2.0", "1.9.1", "1.8"]
    (K ((1000 (* infinity *), 750, meshN), (TF0, "mono_native", combsN, false, "")) (* FUDGE *))
val remote_iprover =
  remotify_atp iprover "iProver" ["0.99"]
    (K ((1000 (* infinity *), 150, meshN), (FOF, "mono_guards??", liftingN, false, "")) (* FUDGE *))
val remote_leo2 =
  remotify_atp leo2 "LEO-II" ["1.5.0", "1.4", "1.3", "1.2", "1"]
    (K ((1000 (* infinity *), 40, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", liftingN, false, "")) (* FUDGE *))
val remote_leo3 =
  remotify_atp leo3 "Leo-III" ["1.1"]
    (K ((1000 (* infinity *), 150, meshN), (THF (Polymorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "poly_native_higher", keep_lamsN, false, "")) (* FUDGE *))
val remote_waldmeister = gen_remote_waldmeister waldmeisterN "raw_mono_tags??"
val remote_zipperposition =
  remotify_atp zipperposition "Zipperpin" ["2.1", "2.0"]
    (K ((1000 (* infinity *), 512, meshN), (THF (Monomorphic, {with_ite = false, with_let = false}, THF_Without_Choice), "mono_native_higher", keep_lamsN, false, "")) (* FUDGE *))


(* Dummy prover *)

fun dummy_config prem_role format type_enc uncurried_aliases : atp_config =
  {exec = (["ISABELLE_ATP"], ["scripts/dummy_atp"]),
   arguments = K (K (K (K (K [])))),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   prem_role = prem_role,
   good_slices =
     K [((1, 256, "mepo"), (format, type_enc,
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
   remote_waldmeister, remote_zipperposition, dummy_fof, dummy_tfx, dummy_thf, dummy_thf_reduced]
val atps = local_atps @ remote_atps

val _ = Theory.setup (fold add_atp atps)

val local_atps = map fst local_atps
val remote_atps = map fst remote_atps
val atps = map fst atps

end;
