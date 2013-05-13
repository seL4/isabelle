(*  Title:      Pure/ProofGeneral/preferences.ML
    Author:     David Aspinall and Markus Wenzel

User preferences for Isabelle which are maintained by the interface.
*)

signature PREFERENCES =
sig
  val category_display: string
  val category_advanced_display: string
  val category_tracing: string
  val category_proof: string
  type preference =
   {name: string,
    descr: string,
    default: string,
    pgiptype: PgipTypes.pgiptype,
    get: unit -> string,
    set: string -> unit}
  val options_pref: string -> string -> string -> preference
  val string_pref: string Unsynchronized.ref -> string -> string -> preference
  val real_pref: real Unsynchronized.ref -> string -> string -> preference
  val int_pref: int Unsynchronized.ref -> string -> string -> preference
  val bool_pref: bool Unsynchronized.ref -> string -> string -> preference
  type T = (string * preference list) list
  val thm_depsN: string
  val pure_preferences: T
  val add: string -> preference -> T -> T
end

structure Preferences: PREFERENCES =
struct

(* categories *)

val category_display = "Display";
val category_advanced_display = "Advanced Display";
val category_tracing = "Tracing";
val category_proof = "Proof"


(* preferences and preference tables *)

type preference =
 {name: string,
  descr: string,
  default: string,
  pgiptype: PgipTypes.pgiptype,
  get: unit -> string,
  set: string -> unit};


(* options as preferences *)

fun options_pref option_name pgip_name descr : preference =
  let
    val typ = Options.default_typ option_name;
    val pgiptype =
      if typ = Options.boolT then PgipTypes.Pgipbool
      else if typ = Options.intT then PgipTypes.Pgipint (NONE, NONE)
      else if typ = Options.realT then PgipTypes.Pgipreal
      else PgipTypes.Pgipstring;
  in
   {name = pgip_name,
    descr = descr,
    default = Options.get_default option_name,
    pgiptype = pgiptype,
    get = fn () => Options.get_default option_name,
    set = Options.put_default option_name}
  end;


(* generic preferences *)

fun mkpref raw_get raw_set typ name descr : preference =
  let
    fun get () = CRITICAL raw_get;
    fun set x = CRITICAL (fn () => raw_set x);
  in {name = name, descr = descr, pgiptype = typ, get = get, set = set, default = get ()} end;

fun generic_pref read write typ r =
  mkpref (fn () => read (! r)) (fn x => r := write x) typ;

val string_pref = generic_pref I I PgipTypes.Pgipstring;

val real_pref =
  generic_pref PgipTypes.real_to_pgstring PgipTypes.read_pgipreal PgipTypes.Pgipreal;

val int_pref =
  generic_pref PgipTypes.int_to_pgstring (PgipTypes.read_pgipint (NONE, NONE))
    (PgipTypes.Pgipint (NONE, NONE));

val bool_pref =
  generic_pref PgipTypes.bool_to_pgstring PgipTypes.read_pgipbool PgipTypes.Pgipbool;


(* preferences of Pure *)

val proof_pref = Unsynchronized.setmp Proofterm.proofs 1 (fn () =>
  let
    fun get () = PgipTypes.bool_to_pgstring (Proofterm.proofs_enabled ());
    fun set s = Proofterm.proofs := (if PgipTypes.read_pgipbool s then 2 else 1);
  in mkpref get set PgipTypes.Pgipbool "full-proofs" "Record full proof objects internally" end) ();

val parallel_proof_pref =
  let
    fun get () = PgipTypes.bool_to_pgstring (! Goal.parallel_proofs >= 1);
    fun set s = Goal.parallel_proofs := (if PgipTypes.read_pgipbool s then 1 else 0);
  in mkpref get set PgipTypes.Pgipbool "parallel-proofs" "Check proofs in parallel" end;

val thm_depsN = "thm_deps";
val thm_deps_pref =
  let
    fun get () = PgipTypes.bool_to_pgstring (print_mode_active thm_depsN);
    fun set s =
      if PgipTypes.read_pgipbool s
      then Unsynchronized.change print_mode (insert (op =) thm_depsN)
      else Unsynchronized.change print_mode (remove (op =) thm_depsN);
  in
    mkpref get set PgipTypes.Pgipbool "theorem-dependencies"
      "Track theorem dependencies within Proof General"
  end;

val print_depth_pref =
  let
    fun get () = PgipTypes.int_to_pgstring (get_print_depth ());
    val set = print_depth o PgipTypes.read_pgipnat;
  in mkpref get set PgipTypes.Pgipnat "print-depth" "Setting for the ML print depth" end;


val display_preferences =
 [bool_pref Printer.show_types_default
    "show-types"
    "Include types in display of Isabelle terms",
  bool_pref Printer.show_sorts_default
    "show-sorts"
    "Include sorts in display of Isabelle terms",
  bool_pref Goal_Display.show_consts_default
    "show-consts"
    "Show types of consts in Isabelle goal display",
  options_pref "names_long"
    "long-names"
    "Show fully qualified names in Isabelle terms",
  bool_pref Printer.show_brackets_default
    "show-brackets"
    "Show full bracketing in Isabelle terms",
  bool_pref Goal_Display.show_main_goal_default
    "show-main-goal"
    "Show main goal in proof state display",
  bool_pref Syntax_Trans.eta_contract_default
    "eta-contract"
    "Print terms eta-contracted"];

val advanced_display_preferences =
 [options_pref "goals_limit"
    "goals-limit"
    "Setting for maximum number of subgoals to be printed",
  print_depth_pref,
  options_pref "show_question_marks"
    "show-question-marks"
    "Show leading question mark of variable name"];

val tracing_preferences =
 [bool_pref Raw_Simplifier.simp_trace_default
    "trace-simplifier"
    "Trace simplification rules.",
  int_pref Raw_Simplifier.simp_trace_depth_limit_default
    "trace-simplifier-depth"
    "Trace simplifier depth limit.",
  bool_pref Pattern.trace_unify_fail
    "trace-unification"
    "Output error diagnostics during unification",
  bool_pref Toplevel.timing
    "global-timing"
    "Whether to enable timing in Isabelle.",
  bool_pref Toplevel.debug
    "debugging"
    "Whether to enable debugging.",
  thm_deps_pref];

val proof_preferences =
 [Unsynchronized.setmp quick_and_dirty true (fn () =>
    bool_pref quick_and_dirty
      "quick-and-dirty"
      "Take a few short cuts") (),
  bool_pref Goal.skip_proofs
    "skip-proofs"
    "Skip over proofs",
  proof_pref,
  int_pref Multithreading.max_threads
    "max-threads"
    "Maximum number of threads",
  parallel_proof_pref];

val pure_preferences =
 [(category_display, display_preferences),
  (category_advanced_display, advanced_display_preferences),
  (category_tracing, tracing_preferences),
  (category_proof, proof_preferences)];


(* table of categories and preferences; names must be unique *)

type T = (string * preference list) list;

fun add cname (pref: preference) (tab: T) = tab |> map
  (fn (cat, prefs) =>
    if cat <> cname then (cat, prefs)
    else
      if exists (fn {name, ...} => name = #name pref) prefs
      then (warning ("Preference already exists: " ^ quote (#name pref)); (cat, prefs))
      else (cat, prefs @ [pref]));

end;
