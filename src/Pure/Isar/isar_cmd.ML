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
  val cannot_undo: string -> Toplevel.transition -> Toplevel.transition
  val clear_undos_theory: int -> Toplevel.transition -> Toplevel.transition
  val redo: Toplevel.transition -> Toplevel.transition
  val undos_proof: int -> Toplevel.transition -> Toplevel.transition
  val kill_proof_notify: (unit -> unit) -> Toplevel.transition -> Toplevel.transition
  val kill_proof: Toplevel.transition -> Toplevel.transition
  val undo_theory: Toplevel.transition -> Toplevel.transition
  val undo: Toplevel.transition -> Toplevel.transition
  val use: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext: bool -> string -> Toplevel.transition -> Toplevel.transition
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
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_thms_containing: xstring list -> Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_lthms: Toplevel.transition -> Toplevel.transition
  val print_cases: Toplevel.transition -> Toplevel.transition
  val print_thms: (string * Args.src list) list -> Toplevel.transition -> Toplevel.transition
  val print_prop: string -> Toplevel.transition -> Toplevel.transition
  val print_term: string -> Toplevel.transition -> Toplevel.transition
  val print_type: string -> Toplevel.transition -> Toplevel.transition
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


(* use ML text *)

fun use name = Toplevel.keep (fn state =>
  Context.setmp (try Toplevel.theory_of state) ThyInfo.use name);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory' o Context.use_mltext_theory;

(*ignore result theory context*)
fun use_mltext v txt = Toplevel.keep' (fn verb => fn state =>
  (Context.use_mltext txt (v andalso verb) (try Toplevel.theory_of state)));

(*Note: commit is dynamically bound*)
val use_commit = use_mltext false "commit();";


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
val print_methods = Toplevel.keep (Method.print_methods o Toplevel.theory_of);

fun print_thms_containing cs = Toplevel.keep (fn state =>
  ThmDatabase.print_thms_containing (Toplevel.theory_of state) cs);


(* print proof context contents *)

val print_binds = Toplevel.keep (ProofContext.print_binds o Proof.context_of o Toplevel.proof_of);
val print_lthms = Toplevel.keep (ProofContext.print_thms o Proof.context_of o Toplevel.proof_of);
val print_cases = Toplevel.keep (ProofContext.print_cases o Proof.context_of o Toplevel.proof_of);


(* print theorems / types / terms / props *)

fun print_thms args = Toplevel.keep (fn state =>
  let val st = Toplevel.node_case Proof.init_state Proof.enter_forward state
  in Pretty.writeln (Proof.pretty_thms (IsarThy.get_thmss args st)) end);

fun print_type s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val T = ProofContext.read_typ (Toplevel.context_of state) s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_typ sign T)) end);

fun print_term s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val t = ProofContext.read_term (Toplevel.context_of state) s;
    val T = Term.type_of t;
  in
    Pretty.writeln (Pretty.block [Pretty.quote (Sign.pretty_term sign t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ sign T)])
  end);

fun print_prop s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val prop = ProofContext.read_prop (Toplevel.context_of state) s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_term sign prop)) end);


end;
