(*  Title:      Pure/Isar/isar_cmd.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Non-logical toplevel commands.
*)

signature ISAR_CMD =
sig
  val exit: Toplevel.transition -> Toplevel.transition
  val quit: Toplevel.transition -> Toplevel.transition
  val init_toplevel: Toplevel.transition -> Toplevel.transition
  val touch_all_thys: Toplevel.transition -> Toplevel.transition
  val touch_thy: string -> Toplevel.transition -> Toplevel.transition
  val remove_thy: string -> Toplevel.transition -> Toplevel.transition
  val kill_theory: Toplevel.transition -> Toplevel.transition
  val cannot_undo: string -> Toplevel.transition -> Toplevel.transition
  val clear_undo: Toplevel.transition -> Toplevel.transition
  val redo: Toplevel.transition -> Toplevel.transition
  val undos_proof: int -> Toplevel.transition -> Toplevel.transition
  val kill_proof: Toplevel.transition -> Toplevel.transition
  val undo_theory: Toplevel.transition -> Toplevel.transition
  val undo: Toplevel.transition -> Toplevel.transition
  val use: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext: string -> Toplevel.transition -> Toplevel.transition
  val use_commit: Toplevel.transition -> Toplevel.transition
  val cd: string -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val use_thy: string -> Toplevel.transition -> Toplevel.transition
  val use_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val update_thy: string -> Toplevel.transition -> Toplevel.transition
  val update_thy_only: string -> Toplevel.transition -> Toplevel.transition
  val print_theory: Toplevel.transition -> Toplevel.transition
  val print_syntax: Toplevel.transition -> Toplevel.transition
  val print_theorems: Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_lthms: Toplevel.transition -> Toplevel.transition
  val print_thms: (string * Args.src list) list -> Toplevel.transition -> Toplevel.transition
  val print_prop: string -> Toplevel.transition -> Toplevel.transition
  val print_term: string -> Toplevel.transition -> Toplevel.transition
  val print_type: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarCmd: ISAR_CMD =
struct


(* variations on exit *)

val exit = Toplevel.keep (fn state =>
  (Context.set_context (try Toplevel.theory_of state);
    writeln "Leaving the Isar loop.  Invoke 'loop();' to restart.";
    raise Toplevel.TERMINATE));

val quit = Toplevel.imperative quit;

val init_toplevel = Toplevel.imperative (fn () => raise Toplevel.RESTART);


(* touch theories *)

val touch_all_thys = Toplevel.imperative ThyInfo.touch_all_thys;
fun touch_thy name = Toplevel.imperative (fn () => ThyInfo.touch_thy name);
fun remove_thy name = Toplevel.imperative (fn () => ThyInfo.remove_thy name);
val kill_theory = Toplevel.imperative (fn () => warning "Nothing to kill.") o Toplevel.kill;


(* history commands *)

fun cannot_undo txt = Toplevel.imperative (fn () => error ("Cannot undo " ^ quote txt));
val clear_undo = Toplevel.history History.clear o Toplevel.proof ProofHistory.clear;
val redo = Toplevel.history History.redo o Toplevel.proof ProofHistory.redo;

fun undos_proof n = Toplevel.proof (fn prf =>
  if ProofHistory.is_initial prf then raise Toplevel.UNDEF else funpow n ProofHistory.undo prf);

val kill_proof = Toplevel.history (fn hist =>
  (case History.current hist of
    Toplevel.Theory _ => raise Toplevel.UNDEF
  | Toplevel.Proof _ => History.undo hist));

val undo_theory = Toplevel.history (fn hist =>
  if History.is_initial hist then raise Toplevel.UNDEF else History.undo hist);

val undo = kill_theory o undo_theory o undos_proof 1;


(* use ML text *)

fun use name = Toplevel.keep (fn state =>
  Context.setmp (try Toplevel.theory_of state) ThyInfo.use name);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory o IsarThy.use_mltext_theory;

(*ignore result theory context*)
fun use_mltext txt = Toplevel.keep (fn state =>
  (IsarThy.use_mltext txt (try Toplevel.theory_of state); ()));

(*Note: commit is dynamically bound*)
val use_commit = use_mltext "commit();";


(* current working directory *)

fun print_cd _ = writeln (Path.pack (File.pwd ()));

fun cd dir = Toplevel.imperative (fn () => (File.cd (Path.unpack dir); print_cd ()));
val pwd = Toplevel.imperative print_cd;


(* load theory files *)

fun use_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy name);
fun use_thy_only name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy_only name);
fun update_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.update_thy name);
fun update_thy_only name = Toplevel.imperative (fn () => Context.save ThyInfo.update_thy_only name);


(* print theory contents *)

val print_theory = Toplevel.keep (PureThy.print_theory o Toplevel.theory_of);
val print_syntax = Toplevel.keep (Display.print_syntax o Toplevel.theory_of);
val print_theorems = Toplevel.keep (PureThy.print_theorems o Toplevel.theory_of);
val print_attributes = Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);
val print_methods = Toplevel.keep (Method.print_methods o Toplevel.theory_of);


(* print proof context contents *)

val print_binds = Toplevel.keep (ProofContext.print_binds o Proof.context_of o Toplevel.proof_of);
val print_lthms = Toplevel.keep (ProofContext.print_thms o Proof.context_of o Toplevel.proof_of);


(* print theorems / types / terms / props *)

fun print_thms args = Toplevel.keep (fn state =>
  let val st = Toplevel.node_case Proof.init_state Proof.enter_forward state
  in Display.print_thms (IsarThy.get_thmss args st) end);


fun read_typ thy = Sign.read_typ (Theory.sign_of thy, K None);

fun read_term T thy s =
  Thm.term_of (#1 (Thm.read_def_cterm (Theory.sign_of thy, K None, K None) [] true (s, T)));


fun print_type s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val T = Toplevel.node_case read_typ (ProofContext.read_typ o Proof.context_of) state s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_typ sign T)) end);

fun print_term s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val t = Toplevel.node_case (read_term (TVar (("'z", 0), logicS)))
      (ProofContext.read_term o Proof.context_of) state s;
    val T = Term.type_of t;
  in
    Pretty.writeln (Pretty.block [Pretty.quote (Sign.pretty_term sign t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ sign T)])
  end);

fun print_prop s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val prop =
      Toplevel.node_case (read_term propT) (ProofContext.read_prop o Proof.context_of) state s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_term sign prop)) end);


end;
