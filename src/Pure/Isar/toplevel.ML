(*  Title:      Pure/Isar/toplevel.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle/Isar toplevel.

TODO:
  - cleanup this file:
      . more internal locality;
      . clearer structure of control flow (exceptions, interrupts);
      . clear division with outer_syntax.ML (!?);
  - improve transactions; only in interactive mode!
  - init / exit proof;
  - display stack size in prompt (prompt: state -> string (hook));
  - excursion: more robust checking of begin / end theory match (including correct name);
*)

signature TOPLEVEL =
sig
  datatype node = Theory of theory | Proof of ProofHistory.T
  type state
  exception UNDEF
  val toplevel: state
  val print_state_default: state -> unit
  val print_state_fn: (state -> unit) ref
  val print_state: state -> unit
  val node_of: state -> node
  val node_cases: (theory -> 'a) -> (Proof.state -> 'a) -> state -> 'a
  val theory_of: state -> theory
  val sign_of: state -> Sign.sg
  val proof_of: state -> Proof.state
  type transition
  exception TERMINATE
  exception RESTART
  exception BREAK of state
  val empty: transition
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val interactive: bool -> transition -> transition
  val print: transition -> transition
  val reset: transition -> transition
  val init: (state -> node) -> (node -> unit) -> transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val exit: transition -> transition
  val imperative: (unit -> unit) -> transition -> transition
  val init_theory: (unit -> theory) -> (theory -> unit) -> transition -> transition
(* FIXME
  val init_proof: (theory -> ProofHistory.T) -> transition -> transition
  val exit_proof: (ProofHistory.T -> unit) -> transition -> transition
*)
  val theory: (theory -> theory) -> transition -> transition
  val proof: (ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val theory_to_proof: (theory -> ProofHistory.T) -> transition -> transition
  val proof_to_theory: (ProofHistory.T -> theory) -> transition -> transition
  type isar
  val trace: bool ref
  val exn_message: exn -> string
  val apply: bool -> transition -> state -> (state * (exn * string) option) option
  val excursion: transition list -> unit
  val set_state: state -> unit
  val get_state: unit -> state
  val exn: unit -> (exn * string) option
  val >> : transition -> bool
  val loop: isar -> unit
end;

structure Toplevel: TOPLEVEL =
struct


(** toplevel state **)

(* datatype node *)

datatype node =
  Theory of theory |
  Proof of ProofHistory.T;

fun print_node (Theory thy) = Pretty.writeln (Pretty.block
      [Pretty.str "Theory:", Pretty.brk 1, Pretty.str (PureThy.get_name thy),
        Pretty.str " =", Pretty.brk 1, Display.pretty_theory thy])
  | print_node (Proof prf) =
      (writeln ("Proof: step #" ^ string_of_int (ProofHistory.position prf));
        Proof.print_state (ProofHistory.current prf));


(* datatype state *)

datatype state = State of (node * (node -> unit)) list;

exception UNDEF;

val toplevel = State [];
fun append_states (State ns) (State ms) = State (ns @ ms);

fun str_of_state (State []) = "at top level"
  | str_of_state (State ((Theory _, _) :: _)) = "in theory mode"
  | str_of_state (State ((Proof _, _) :: _)) = "in proof mode";


(* print_state hook *)

fun print_topnode (State []) = ()
  | print_topnode (State [(node, _)]) = print_node node
  | print_topnode (State ((node, _) :: nodes)) =
      (writeln ("Stack size: " ^ string_of_int (length nodes)); print_node node);

fun print_state_default state =
  let val ref (begin_state, end_state, _) = Goals.current_goals_markers in
    if begin_state = "" then () else writeln begin_state;
    print_topnode state;
    if end_state = "" then () else writeln end_state
  end;

val print_state_fn = ref print_state_default;
fun print_state state = ! print_state_fn state;


(* top node *)

fun node_of (State []) = raise UNDEF
  | node_of (State ((node, _) :: _)) = node;

fun node_cases f g state =
  (case node_of state of
    Theory thy => f thy
  | Proof prf => g (ProofHistory.current prf));

val theory_of = node_cases I Proof.theory_of;
val sign_of = Theory.sign_of o theory_of;
val proof_of = node_cases (fn _ => raise UNDEF) I;



(** toplevel transitions **)

exception TERMINATE;
exception RESTART;
exception BREAK of state;
exception FAIL of exn * string;


(* datatype trans *)

datatype trans =
  Reset |
  Init of (state -> node) * (node -> unit) |
  Keep of (state -> unit) |
  Exit |
  MapCurrent of node -> node;

fun apply_trans Reset _ = State []
  | apply_trans (Init (f, g)) (state as State nodes) = State ((f state, g) :: nodes)
  | apply_trans (Keep f) state = (f state; state)
  | apply_trans Exit (State []) = raise UNDEF
  | apply_trans Exit (State ((node, g) :: nodes)) = (g node; State nodes)
  | apply_trans (MapCurrent _) (State []) = raise UNDEF
  | apply_trans (MapCurrent f) (State ((node, g) :: nodes)) = State ((f node, g) :: nodes);

fun apply_union [] _ = raise UNDEF
  | apply_union (tr :: trs) state =
      apply_trans tr state handle UNDEF => apply_union trs state;


(* datatype transition *)

datatype transition = Transition of
 {name: string,
  pos: Position.T,
  int_only: bool,
  print: bool,
  trans: trans list};

fun make_transition (name, pos, int_only, print, trans) =
  Transition {name = name, pos = pos, int_only = int_only, print = print, trans = trans};

fun map_transition f (Transition {name, pos, int_only, print, trans}) =
  make_transition (f (name, pos, int_only, print, trans));

val empty = make_transition ("<unknown>", Position.none, false, false, []);


(* diagnostics *)

fun str_of_transition (Transition {name, pos, ...}) = quote name ^ Position.str_of pos;

fun command_msg msg tr = msg ^ "command " ^ str_of_transition tr;
fun at_command tr = command_msg "At " tr ^ ".";

fun type_error tr state =
  error (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name nm = map_transition
  (fn (_, pos, int_only, print, trans) => (nm, pos, int_only, print, trans));

fun position pos = map_transition
  (fn (name, _, int_only, print, trans) => (name, pos, int_only, print, trans));

fun interactive int_only = map_transition
  (fn (name, pos, _, print, trans) => (name, pos, int_only, print, trans));

val print = map_transition
  (fn (name, pos, int_only, _, trans) => (name, pos, int_only, true, trans));

fun add_trans tr = map_transition
  (fn (name, pos, int_only, print, trans) => (name, pos, int_only, print, trans @ [tr]));


(* build transitions *)

val reset = add_trans Reset;
fun init f g = add_trans (Init (f, g));
val keep = add_trans o Keep;
val exit = add_trans Exit;
val map_current = add_trans o MapCurrent;

fun imperative f = keep (fn _ => f ());

fun init_theory f g =
  init (fn _ => Theory (f ())) (fn Theory thy => g thy | _ => raise UNDEF);

fun theory f = map_current
  (fn Theory thy => Theory (PureThy.transaction f thy) | _ => raise UNDEF);
fun proof f = map_current (fn Proof prf => Proof (f prf) | _ => raise UNDEF);

fun theory_to_proof f = map_current (fn Theory thy => Proof (f thy) | _ => raise UNDEF);
fun proof_to_theory f = map_current (fn Proof prf => Theory (f prf) | _ => raise UNDEF);


(* the Isar source of transitions *)

type isar =
  (transition, (transition option,
    (OuterLex.token, (OuterLex.token,
      Position.T * (Symbol.symbol, (string, unit) Source.source) Source.source)
          Source.source) Source.source) Source.source) Source.source;



(** toplevel transactions **)

val trace = ref false;


(* print exceptions *)

fun raised name = "exception " ^ name ^ " raised";
fun raised_msg name msg = raised name ^ ": " ^ msg;

fun exn_message TERMINATE = "Exit."
  | exn_message RESTART = "Restart."
  | exn_message (BREAK _) = "Break."
  | exn_message (FAIL (exn, msg)) = cat_lines [exn_message exn, msg]
  | exn_message Interrupt = "Interrupt (exec)."
  | exn_message ERROR = "ERROR."
  | exn_message (ERROR_MESSAGE msg) = msg
  | exn_message (THEORY (msg, _)) = msg
  | exn_message (ProofContext.CONTEXT (msg, _)) = msg
  | exn_message (Proof.STATE (msg, _)) = msg
  | exn_message (ProofHistory.FAIL msg) = msg
  | exn_message (Attrib.ATTRIB_FAIL info) = fail_message "attribute" info
  | exn_message (Method.METHOD_FAIL info) = fail_message "method" info
  | exn_message (Syntax.AST (msg, _)) = raised_msg "AST" msg
  | exn_message (TYPE (msg, _, _)) = raised_msg "TYPE" msg
  | exn_message (TERM (msg, _)) = raised_msg "TERM" msg
  | exn_message (THM (msg, _, _)) = raised_msg "THM" msg
  | exn_message Library.OPTION = raised "Library.OPTION"
  | exn_message (Library.LIST msg) = raised_msg "Library.LIST" msg
  | exn_message exn = General.exnMessage exn
and fail_message kind ((name, pos), exn) =
  "Error in " ^ kind ^ " " ^ name ^ Position.str_of pos ^ ":\n" ^ exn_message exn;

fun print_exn None = ()
  | print_exn (Some (exn, s)) = error_msg (cat_lines [exn_message exn, s]);


(* transform interrupt (non-polymorphic) *)

fun transform_interrupt_state f x =
  let val y = ref (None: state option);
  in exhibit_interrupt (fn () => y := Some (f x)) (); the (! y) end;

fun transform_interrupt_isar f x =
  let val y = ref (None: (transition * isar) option option);
  in exhibit_interrupt (fn () => y := Some (f x)) (); the (! y) end;


(* the dreaded stale signatures *)

fun check_stale state =
  (case try theory_of state of
    None => ()
  | Some thy =>
      if Sign.is_stale (Theory.sign_of thy) then
        warning "Stale signature encountered!  Should redo current theory from start."
      else ());


(* apply transitions *)

fun app int (tr as Transition {trans, int_only, print, ...}) state =
  let
    val _ =
      if int orelse not int_only then ()
      else warning (command_msg "Executing interactive-only " tr);
    val state' =
      (if ! trace then (writeln (command_msg "" tr); timeap (apply_union trans) state)
        else apply_union trans state)
      handle UNDEF => type_error tr state;
    val _ = if int andalso print then print_state state' else ();
  in state' end;

fun rollback tr copy_thy (State ((Theory _, g) :: nodes)) =
      (warning (command_msg "Rollback after " tr); State ((Theory copy_thy, g) :: nodes))
  | rollback tr _ state =
      (warning (command_msg "Ignoring rollback theory copy from " tr); state);

fun apply int tr state =
  Some (transform_interrupt_state (transform_error (app int tr)) state, None)
    handle
      TERMINATE => None
    | RESTART => Some (toplevel, None)
    | FAIL (exn_info as (BREAK break_state, _)) =>
        Some (append_states break_state state, Some exn_info)
    | FAIL exn_info => Some (state, Some exn_info)
    | PureThy.ROLLBACK (copy_thy, opt_exn) =>
        Some (rollback tr copy_thy state, apsome (fn exn => (exn, at_command tr)) opt_exn)
    | exn => Some (state, Some (exn, at_command tr));


(* excursion: toplevel -- apply transformers -- toplevel *)

fun excur [] x = x
  | excur (tr :: trs) x =
      (case apply false tr x of
        Some (x', None) => excur trs x'
      | Some (x', Some exn_info) => raise FAIL exn_info
      | None => raise FAIL (TERMINATE, at_command tr));

fun excursion trs =
  (case excur trs (State []) of
    State [] => ()
  | _ => raise ERROR_MESSAGE "Open block(s) pending at end of input");



(** interactive transformations **)

(* the global state reference *)

val global_state = ref (State [], None: (exn * string) option);

fun set_state state = global_state := (state, None);
fun get_state () = fst (! global_state);
fun exn () = snd (! global_state);


(* apply transformers to global state *)

nonfix >>;

fun >> tr =
  (case apply true tr (get_state ()) of
    None => false
  | Some (state', exn_info) =>
      (global_state := (state', exn_info);
        check_stale state'; print_exn exn_info;
        true));

fun get_interruptible src =
  Some (transform_interrupt_isar Source.get_single src)
    handle Interrupt => None;

fun raw_loop src =
  (case get_interruptible src of
    None => (writeln "\nInterrupt (read)."; raw_loop src)
  | Some None => ()
  | Some (Some (tr, src')) => if >> tr then raw_loop src' else ());


fun loop src = mask_interrupt raw_loop src;


end;
