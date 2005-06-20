(*  Title:      Pure/Isar/isar_cmd.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Non-logical toplevel commands.
*)

signature ISAR_CMD =
sig
  val welcome: Toplevel.transition -> Toplevel.transition
  val init_toplevel: Toplevel.transition -> Toplevel.transition
  val exit: Toplevel.transition -> Toplevel.transition
  val quit: Toplevel.transition -> Toplevel.transition
  val touch_child_thys: string -> Toplevel.transition -> Toplevel.transition
  val touch_all_thys: Toplevel.transition -> Toplevel.transition
  val touch_thy: string -> Toplevel.transition -> Toplevel.transition
  val remove_thy: string -> Toplevel.transition -> Toplevel.transition
  val kill_thy: string -> Toplevel.transition -> Toplevel.transition
  val pr: string list * (int option * int option) -> Toplevel.transition -> Toplevel.transition
  val disable_pr: Toplevel.transition -> Toplevel.transition
  val enable_pr: Toplevel.transition -> Toplevel.transition
  val cannot_undo: string -> Toplevel.transition -> Toplevel.transition
  val clear_undos_theory: int -> Toplevel.transition -> Toplevel.transition
  val redo: Toplevel.transition -> Toplevel.transition
  val undos_proof: int -> Toplevel.transition -> Toplevel.transition
  val kill_proof_notify: (unit -> unit) -> Toplevel.transition -> Toplevel.transition
  val kill_proof: Toplevel.transition -> Toplevel.transition
  val undo_theory: Toplevel.transition -> Toplevel.transition
  val undo: Toplevel.transition -> Toplevel.transition
  val kill: Toplevel.transition -> Toplevel.transition
  val back: bool -> Toplevel.transition -> Toplevel.transition
  val use: Path.T -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext: bool -> string -> Toplevel.transition -> Toplevel.transition
  val use_commit: Toplevel.transition -> Toplevel.transition
  val cd: Path.T -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val use_thy: string -> Toplevel.transition -> Toplevel.transition
  val use_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val update_thy: string -> Toplevel.transition -> Toplevel.transition
  val update_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val display_drafts: Path.T list -> Toplevel.transition -> Toplevel.transition
  val print_drafts: Path.T list -> Toplevel.transition -> Toplevel.transition
  val pretty_setmargin: int -> Toplevel.transition -> Toplevel.transition
  val print_context: Toplevel.transition -> Toplevel.transition
  val print_theory: Toplevel.transition -> Toplevel.transition
  val print_syntax: Toplevel.transition -> Toplevel.transition
  val print_theorems: Toplevel.transition -> Toplevel.transition
  val print_locales: Toplevel.transition -> Toplevel.transition
  val print_locale: Locale.expr * Locale.element list
    -> Toplevel.transition -> Toplevel.transition
  val print_registrations: string -> Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_simpset: Toplevel.transition -> Toplevel.transition
  val print_rules: Toplevel.transition -> Toplevel.transition
  val print_induct_rules: Toplevel.transition -> Toplevel.transition
  val print_trans_rules: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_antiquotations: Toplevel.transition -> Toplevel.transition
  val thm_deps: (thmref * Attrib.src list) list ->
    Toplevel.transition -> Toplevel.transition
  val find_theorems: int option * (bool * string FindTheorems.criterion) list
    -> Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_lthms: Toplevel.transition -> Toplevel.transition
  val print_cases: Toplevel.transition -> Toplevel.transition
  val print_thms: string list * (thmref * Attrib.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_prfs: bool -> string list * (thmref * Attrib.src list) list option
    -> Toplevel.transition -> Toplevel.transition
  val print_prop: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_term: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_type: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val add_header: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_chapter: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_section: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsection: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsubsection: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_text: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_text_raw: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_sect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsubsect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_txt: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_txt_raw: string * Position.T -> Toplevel.transition -> Toplevel.transition
end;

structure IsarCmd: ISAR_CMD =
struct


(* variations on init / exit *)

val init_toplevel = Toplevel.imperative (fn () => raise Toplevel.RESTART);
val welcome = Toplevel.imperative (writeln o Session.welcome);

val exit = Toplevel.keep (fn state =>
  (Context.set_context (try Toplevel.theory_of state);
    writeln "Leaving the Isar loop.  Invoke 'loop();' to restart.";
    raise Toplevel.TERMINATE));

val quit = Toplevel.imperative quit;


(* touch theories *)

fun touch_child_thys name = Toplevel.imperative (fn () => ThyInfo.touch_child_thys name);
val touch_all_thys = Toplevel.imperative ThyInfo.touch_all_thys;
fun touch_thy name = Toplevel.imperative (fn () => ThyInfo.touch_thy name);
fun remove_thy name = Toplevel.imperative (fn () => ThyInfo.remove_thy name);
fun kill_thy name = Toplevel.imperative (fn () => IsarThy.kill_theory name);


(* print state *)

fun with_modes modes e =
  Library.setmp print_mode (modes @ ! print_mode) e ();

fun set_limit _ NONE = ()
  | set_limit r (SOME n) = r := n;

fun pr (ms, (lim1, lim2)) = Toplevel.keep (fn state =>
  (set_limit goals_limit lim1; set_limit ProofContext.prems_limit lim2; Toplevel.quiet := false;
    with_modes ms (fn () => Toplevel.print_state true state)));

val disable_pr = Toplevel.imperative (fn () => Toplevel.quiet := true);
val enable_pr = Toplevel.imperative (fn () => Toplevel.quiet := false);


(* history commands *)

fun cannot_undo txt = Toplevel.imperative (fn () => error ("Cannot undo " ^ quote txt));
val clear_undos_theory = Toplevel.history o History.clear;
val redo = Toplevel.history History.redo o Toplevel.proof'' ProofHistory.redo o
  Toplevel.skip_proof History.redo;

fun undos_proof n = Toplevel.proof'' (fn prf =>
    if ProofHistory.is_initial prf then raise Toplevel.UNDEF else funpow n ProofHistory.undo prf) o
  Toplevel.skip_proof (fn h =>
    if History.is_initial h then raise Toplevel.UNDEF else funpow n History.undo h);

fun kill_proof_notify (f: unit -> unit) = Toplevel.history (fn hist =>
  (case History.current hist of
    Toplevel.Theory _ => raise Toplevel.UNDEF
  | _ => (f (); History.undo hist)));

val kill_proof = kill_proof_notify (K ());

val undo_theory = Toplevel.history (fn hist =>
  if History.is_initial hist then raise Toplevel.UNDEF else History.undo hist);

val undo = Toplevel.kill o undo_theory o undos_proof 1;
val kill = Toplevel.kill o kill_proof;
val back = Toplevel.proof o ProofHistory.back;


(* use ML text *)

fun use path = Toplevel.keep (fn state =>
  Context.setmp (try Toplevel.theory_of state) (ThyInfo.load_file false) path);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory' o Context.use_mltext_theory;

(*ignore result theory context*)
fun use_mltext v txt = Toplevel.keep' (fn verb => fn state =>
  (Context.use_mltext txt (v andalso verb) (try Toplevel.theory_of state)));

(*commit is dynamically bound!*)
val use_commit = use_mltext false "commit();";


(* current working directory *)

fun cd path = Toplevel.imperative (fn () => (File.cd path));
val pwd = Toplevel.imperative (fn () => writeln (Path.pack (File.pwd ())));


(* load theory files *)

fun use_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy name);
fun use_thy_only name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy_only name);
fun update_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.update_thy name);
fun update_thy_only name =
  Toplevel.imperative (fn () => Context.save ThyInfo.update_thy_only name);


(* present draft files *)

fun display_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts (getenv "ISABELLE_DOC_FORMAT") files)
  in File.isatool ("display -c " ^ outfile ^ " &"); () end);

fun print_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts "ps" files)
  in File.isatool ("print -c " ^ outfile); () end);


(* pretty_setmargin *)

fun pretty_setmargin n = Toplevel.imperative (fn () => Pretty.setmargin n);


(* print parts of theory and proof context *)

val print_context = Toplevel.keep Toplevel.print_state_context;

val print_theory = Toplevel.unknown_theory o
  Toplevel.keep (PureThy.print_theory o Toplevel.theory_of);

val print_syntax = Toplevel.unknown_theory o
  Toplevel.keep (Display.print_syntax o Toplevel.theory_of) o
  Toplevel.keep (ProofContext.print_syntax o Proof.context_of o Toplevel.proof_of);

val print_theorems = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  (case History.previous (Toplevel.node_history_of state) of
    SOME (Toplevel.Theory prev_thy) => PureThy.print_theorems_diff prev_thy
  | _ => PureThy.print_theorems) (Toplevel.theory_of state));

val print_locales = Toplevel.unknown_theory o
  Toplevel.keep (Locale.print_locales o Toplevel.theory_of);

fun print_locale (import, body) = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  Locale.print_locale (Toplevel.theory_of state) import body);

fun print_registrations name = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case (Locale.print_global_registrations name)
    (Locale.print_local_registrations name o Proof.context_of));

val print_attributes = Toplevel.unknown_theory o
  Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);

val print_simpset = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case Simplifier.print_simpset
    (Simplifier.print_local_simpset o Proof.context_of));

val print_rules = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case ContextRules.print_global_rules
    (ContextRules.print_local_rules o Proof.context_of));

val print_induct_rules = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case InductAttrib.print_global_rules
    (InductAttrib.print_local_rules o Proof.context_of));

val print_trans_rules = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case Calculation.print_global_rules
    (Calculation.print_local_rules o Proof.context_of));

val print_methods = Toplevel.unknown_theory o
  Toplevel.keep (Method.print_methods o Toplevel.theory_of);

val print_antiquotations = Toplevel.imperative IsarOutput.print_antiquotations;


(* retrieve theorems *)

fun thm_deps args = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  ThmDeps.thm_deps (IsarThy.get_thmss args (Toplevel.enter_forward_proof state)));

fun find_theorems (opt_lim, spec) = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  let
    val proof_state = Toplevel.enter_forward_proof state;
    val ctxt = Proof.context_of proof_state;
    val opt_goal = try Proof.get_goal proof_state |> Option.map (Thm.prop_of o #2 o #2);
  in FindTheorems.print_theorems ctxt opt_goal opt_lim spec end);


(* print proof context contents *)

val print_binds = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose
    ProofContext.print_binds (Proof.context_of (Toplevel.proof_of state)));

val print_lthms = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose
    ProofContext.print_lthms (Proof.context_of (Toplevel.proof_of state)));

val print_cases = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose
    ProofContext.print_cases (Proof.context_of (Toplevel.proof_of state)));


(* print theorems / types / terms / props *)

fun string_of_thms state ms args = with_modes ms (fn () =>
  Pretty.string_of (ProofContext.pretty_thms (Proof.context_of state)
    (IsarThy.get_thmss args state)));

fun string_of_prfs full state ms arg = with_modes ms (fn () =>
  Pretty.string_of (case arg of    (* FIXME context syntax!? *)
      NONE =>
        let
          val (_, (_, thm)) = Proof.get_goal state;
          val {sign, prop, der = (_, prf), ...} = rep_thm thm;
          val prf' = Proofterm.rewrite_proof_notypes ([], []) prf
        in
          ProofSyntax.pretty_proof sign
            (if full then Reconstruct.reconstruct_proof sign prop prf' else prf')
        end
    | SOME args => Pretty.chunks
        (map (ProofSyntax.pretty_proof_of full) (IsarThy.get_thmss args state))));

fun string_of_prop state ms s =
  let
    val ctxt = Proof.context_of state;
    val prop = ProofContext.read_prop ctxt s;
  in
    with_modes ms (fn () => Pretty.string_of (Pretty.quote (ProofContext.pretty_term ctxt prop)))
  end;

fun string_of_term state ms s =
  let
    val ctxt = Proof.context_of state;
    val t = ProofContext.read_term ctxt s;
    val T = Term.type_of t;
  in
    with_modes ms (fn () => Pretty.string_of
      (Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt T)]))
  end;

fun string_of_type state ms s =
  let
    val ctxt = Proof.context_of state;
    val T = ProofContext.read_typ ctxt s;
  in with_modes ms (fn () => Pretty.string_of (Pretty.quote (ProofContext.pretty_typ ctxt T))) end;

fun print_item string_of (x, y) = Toplevel.keep (fn state =>
  writeln (string_of (Toplevel.enter_forward_proof state) x y));

val print_thms = print_item string_of_thms;
fun print_prfs full = print_item (string_of_prfs full);
val print_prop = print_item string_of_prop;
val print_term = print_item string_of_term;
val print_type = print_item string_of_type;


(* markup commands *)

fun add_header s = Toplevel.keep' (fn int => fn state =>
  (if Toplevel.is_toplevel state then () else raise Toplevel.UNDEF;
    OuterSyntax.check_text s int state));

local

fun present_text assert_proof present (s, pos) = Toplevel.keep' (fn int => fn state =>
  (if can Toplevel.proof_of state = assert_proof then () else raise Toplevel.UNDEF;
    Context.setmp (SOME (Toplevel.theory_of state)) present s;
    OuterSyntax.check_text (s, pos) int state;
    raise Toplevel.UNDEF));

fun theory f x = Toplevel.theory I o present_text false f x;
fun proof f x = Toplevel.print o Toplevel.proof (ProofHistory.apply I) o present_text true f x;

in

val add_chapter = theory Present.section;
val add_section = theory Present.section;
val add_subsection = theory Present.subsection;
val add_subsubsection = theory Present.subsubsection;
val add_text = theory (K ());
val add_text_raw = add_text;
val add_txt = proof (K ());
val add_txt_raw = add_txt;
val add_sect = add_txt;
val add_subsect = add_txt;
val add_subsubsect = add_txt;

end;

end;
