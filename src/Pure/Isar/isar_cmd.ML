(*  Title:      Pure/Isar/isar_cmd.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

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
  val pr: string list * int option -> Toplevel.transition -> Toplevel.transition
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
  val back: bool * Comment.text -> Toplevel.transition -> Toplevel.transition
  val use: string * Comment.text -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string * Comment.text -> Toplevel.transition -> Toplevel.transition
  val use_mltext: bool -> string * Comment.text -> Toplevel.transition -> Toplevel.transition
  val use_setup: string * Comment.text -> theory -> theory
  val use_commit: Toplevel.transition -> Toplevel.transition
  val cd: string -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val use_thy: string -> Toplevel.transition -> Toplevel.transition
  val use_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val update_thy: string -> Toplevel.transition -> Toplevel.transition
  val update_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val pretty_setmargin: int -> Toplevel.transition -> Toplevel.transition
  val print_context: Toplevel.transition -> Toplevel.transition
  val print_theory: Toplevel.transition -> Toplevel.transition
  val print_syntax: Toplevel.transition -> Toplevel.transition
  val print_theorems: Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_trans_rules: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_antiquotations: Toplevel.transition -> Toplevel.transition
  val print_thms_containing: xstring list -> Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_lthms: Toplevel.transition -> Toplevel.transition
  val print_cases: Toplevel.transition -> Toplevel.transition
  val print_thms: string list * (string * Args.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_prop: string list * string -> Toplevel.transition -> Toplevel.transition
  val print_term: string list * string -> Toplevel.transition -> Toplevel.transition
  val print_type: string list * string -> Toplevel.transition -> Toplevel.transition
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

fun pr (ms, limit) = Toplevel.keep (fn state =>
  ((case limit of Some n => goals_limit := n | None => ()); Toplevel.quiet := false;
    with_modes ms (fn () => Toplevel.print_state true state)));

val disable_pr = Toplevel.imperative (fn () => Toplevel.quiet := true);
val enable_pr = Toplevel.imperative (fn () => Toplevel.quiet := false);


(* history commands *)

fun cannot_undo txt = Toplevel.imperative (fn () => error ("Cannot undo " ^ quote txt));
val clear_undos_theory = Toplevel.history o History.clear;
val redo = Toplevel.history History.redo o Toplevel.proof ProofHistory.redo;

fun undos_proof n = Toplevel.proof (fn prf =>
  if ProofHistory.is_initial prf then raise Toplevel.UNDEF else funpow n ProofHistory.undo prf);

fun kill_proof_notify (f: unit -> unit) = Toplevel.history (fn hist =>
  (case History.current hist of
    Toplevel.Theory _ => raise Toplevel.UNDEF
  | Toplevel.Proof _ => (f (); History.undo hist)));

val kill_proof = kill_proof_notify (K ());

val undo_theory = Toplevel.history (fn hist =>
  if History.is_initial hist then raise Toplevel.UNDEF else History.undo hist);

val undo = Toplevel.kill o undo_theory o undos_proof 1;
val kill = Toplevel.kill o kill_proof;

val back = Toplevel.proof o ProofHistory.back o Comment.ignore;


(* use ML text *)

fun use (name, comment_ignore) = Toplevel.keep (fn state =>
  Context.setmp (try Toplevel.theory_of state) ThyInfo.use name);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory' o Context.use_mltext_theory o Comment.ignore;

(*ignore result theory context*)
fun use_mltext v (txt, comment_ignore) = Toplevel.keep' (fn verb => fn state =>
  (Context.use_mltext txt (v andalso verb) (try Toplevel.theory_of state)));

val use_setup = Context.use_setup o Comment.ignore;

(*Note: commit is dynamically bound*)
val use_commit = use_mltext false ("commit();", Comment.none);


(* current working directory *)

fun cd dir = Toplevel.imperative (fn () => (File.cd (Path.unpack dir)));
val pwd = Toplevel.imperative (fn () => writeln (Path.pack (File.pwd ())));


(* load theory files *)

fun use_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy name);
fun use_thy_only name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy_only name);
fun update_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.update_thy name);
fun update_thy_only name =
  Toplevel.imperative (fn () => Context.save ThyInfo.update_thy_only name);


(* pretty_setmargin *)

fun pretty_setmargin n = Toplevel.imperative (fn () => Pretty.setmargin n);


(* print theory *)

val print_context = Toplevel.keep Toplevel.print_state_context;
val print_theory = Toplevel.keep (PureThy.print_theory o Toplevel.theory_of);
val print_syntax = Toplevel.keep (Display.print_syntax o Toplevel.theory_of);
val print_theorems = Toplevel.keep (PureThy.print_theorems o Toplevel.theory_of);
val print_attributes = Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);
val print_trans_rules = Toplevel.keep (Toplevel.node_case Calculation.print_global_rules
  (Calculation.print_local_rules o Proof.context_of));
val print_methods = Toplevel.keep (Method.print_methods o Toplevel.theory_of);
val print_antiquotations = Toplevel.imperative IsarOutput.print_antiquotations;

fun print_thms_containing cs = Toplevel.keep (fn state =>
  ThmDatabase.print_thms_containing (Toplevel.theory_of state) cs);


(* print proof context contents *)

val print_binds = Toplevel.keep (ProofContext.print_binds o Proof.context_of o Toplevel.proof_of);
val print_lthms = Toplevel.keep (ProofContext.print_thms o Proof.context_of o Toplevel.proof_of);
val print_cases = Toplevel.keep (ProofContext.print_cases o Proof.context_of o Toplevel.proof_of);


(* print theorems / types / terms / props *)

fun string_of_thms state ms args = with_modes ms (fn () =>
  Pretty.string_of (Proof.pretty_thms (IsarThy.get_thmss args state)));

fun string_of_prop state ms s =
  let
    val sign = Proof.sign_of state;
    val prop = ProofContext.read_prop (Proof.context_of state) s;
  in with_modes ms (fn () => Pretty.string_of (Pretty.quote (Sign.pretty_term sign prop))) end;

fun string_of_term state ms s =
  let
    val sign = Proof.sign_of state;
    val t = ProofContext.read_term (Proof.context_of state) s;
    val T = Term.type_of t;
  in
    with_modes ms (fn () => Pretty.string_of
      (Pretty.block [Pretty.quote (Sign.pretty_term sign t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ sign T)]))
  end;

fun string_of_type state ms s =
  let
    val sign = Proof.sign_of state;
    val T = ProofContext.read_typ (Proof.context_of state) s;
  in with_modes ms (fn () => Pretty.string_of (Pretty.quote (Sign.pretty_typ sign T))) end;

fun print_item string_of (x, y) = Toplevel.keep (fn state =>
  writeln (string_of (Toplevel.node_case Proof.init_state Proof.enter_forward state) x y));

val print_thms = print_item string_of_thms;
val print_prop = print_item string_of_prop;
val print_term = print_item string_of_term;
val print_type = print_item string_of_type;


end;
