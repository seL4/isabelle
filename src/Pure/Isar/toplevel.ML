(*  Title:      Pure/Isar/toplevel.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The Isabelle/Isar toplevel.
*)

signature TOPLEVEL =
sig
  datatype node = Theory of theory | Proof of ProofHistory.T
  type state
  val toplevel: state
  val is_toplevel: state -> bool
  val prompt_state_default: state -> string
  val prompt_state_fn: (state -> string) ref
  val print_state_context: state -> unit
  val print_state_default: bool -> state -> unit
  val print_state_fn: (bool -> state -> unit) ref
  val print_state: bool -> state -> unit
  exception UNDEF
  val node_history_of: state -> node History.T
  val node_of: state -> node
  val node_case: (theory -> 'a) -> (Proof.state -> 'a) -> state -> 'a
  val theory_of: state -> theory
  val sign_of: state -> Sign.sg
  val context_of: state -> Proof.context
  val proof_of: state -> Proof.state
  val enter_forward_proof: state -> Proof.state
  type transition
  exception TERMINATE
  exception RESTART
  val undo_limit: bool -> int option
  val empty: transition
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val interactive: bool -> transition -> transition
  val print: transition -> transition
  val no_timing: transition -> transition
  val reset: transition -> transition
  val init: (bool -> node) -> (node -> unit) -> (node -> unit) -> transition -> transition
  val exit: transition -> transition
  val kill: transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val keep': (bool -> state -> unit) -> transition -> transition
  val history: (node History.T -> node History.T) -> transition -> transition
  val imperative: (unit -> unit) -> transition -> transition
  val init_theory: (bool -> theory) -> (theory -> unit) -> (theory -> unit)
    -> transition -> transition
  val theory: (theory -> theory) -> transition -> transition
  val theory': (bool -> theory -> theory) -> transition -> transition
  val theory_to_proof: (bool -> theory -> ProofHistory.T) -> transition -> transition
  val proof: (ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val proof': (bool -> ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val proof_to_theory: (ProofHistory.T -> theory) -> transition -> transition
  val quiet: bool ref
  val exn_message: exn -> string
  val apply: bool -> transition -> state -> (state * (exn * string) option) option
  val excursion_result: ((transition * (state -> 'a -> 'a)) list * 'a) -> 'a
  val excursion: transition list -> unit
  val set_state: state -> unit
  val get_state: unit -> state
  val exn: unit -> (exn * string) option
  val >> : transition -> bool
  type isar
  val loop: isar -> unit
end;

structure Toplevel: TOPLEVEL =
struct


(** toplevel state **)

(* datatype node *)

datatype node =
  Theory of theory |
  Proof of ProofHistory.T;

fun str_of_node (Theory _) = "in theory mode"
  | str_of_node (Proof _) = "in proof mode";

fun print_ctxt thy = Pretty.writeln (Pretty.block
  [Pretty.str "theory", Pretty.brk 1, Pretty.str (PureThy.get_name thy),
    Pretty.str " =", Pretty.brk 1, Display.pretty_theory thy]);

fun print_prf prf = Proof.print_state (ProofHistory.position prf) (ProofHistory.current prf);

fun print_node_ctxt (Theory thy) = print_ctxt thy
  | print_node_ctxt (Proof prf) = print_ctxt (Proof.theory_of (ProofHistory.current prf));

fun print_node prf_only (Theory thy) = if prf_only then () else print_ctxt thy
  | print_node _ (Proof prf) = print_prf prf;


(* datatype state *)

datatype state = State of (node History.T * ((node -> unit) * (node -> unit))) option;

val toplevel = State None;

fun is_toplevel (State None) = true
  | is_toplevel _ = false;

fun str_of_state (State None) = "at top level"
  | str_of_state (State (Some (node, _))) = str_of_node (History.current node);


(* prompt_state hook *)

fun prompt_state_default (State _) = Source.default_prompt;

val prompt_state_fn = ref prompt_state_default;
fun prompt_state state = ! prompt_state_fn state;


(* print state *)

fun print_current_node _ (State None) = ()
  | print_current_node prt (State (Some (node, _))) = prt (History.current node);

val print_state_context = print_current_node print_node_ctxt;

fun print_state_default prf_only state =
  let val ref (begin_state, end_state, _) = Goals.current_goals_markers in
    if begin_state = "" then () else writeln begin_state;
    print_current_node (print_node prf_only) state;
    if end_state = "" then () else writeln end_state
  end;

val print_state_fn = ref print_state_default;
fun print_state state = ! print_state_fn state;


(* top node *)

exception UNDEF;

fun node_history_of (State None) = raise UNDEF
  | node_history_of (State (Some (node, _))) = node;

val node_of = History.current o node_history_of;

fun node_case f g state =
  (case node_of state of
    Theory thy => f thy
  | Proof prf => g (ProofHistory.current prf));

val theory_of = node_case I Proof.theory_of;
val context_of = node_case ProofContext.init Proof.context_of;
val sign_of = Theory.sign_of o theory_of;
val proof_of = node_case (fn _ => raise UNDEF) I;

val enter_forward_proof = node_case Proof.init_state Proof.enter_forward;


(** toplevel transitions **)

exception TERMINATE;
exception RESTART;
exception EXCURSION_FAIL of exn * string;
exception FAILURE of state * exn;


(* recovery from stale signatures *)

(*note: proof commands should be non-destructive!*)

local

fun is_stale state = Sign.is_stale (sign_of state) handle UNDEF => false;

fun checkpoint_node true (Theory thy) = Theory (PureThy.checkpoint thy)
  | checkpoint_node _ node = node;

fun copy_node true (Theory thy) = Theory (Theory.copy thy)
  | copy_node _ node = node;

fun interruptible f x =
  let val y = ref (None: node History.T option);
  in exhibit_interrupt (fn () => y := Some (f x)) (); the (! y) end;

val rollback = ERROR_MESSAGE "Stale signature encountered after succesful execution!";

fun return (result, None) = result
  | return (result, Some exn) = raise FAILURE (result, exn);

in

fun node_trans _ _ _ (State None) = raise UNDEF
  | node_trans int hist f (State (Some (node, term))) =
      let
        fun mk_state nd = State (Some (nd, term));

        val cont_node = History.map (checkpoint_node int) node;
        val back_node = History.map (copy_node int) cont_node;

        val trans = if hist then History.apply_copy (copy_node int) else History.map;
        val (result, opt_exn) =
          (mk_state (transform_error (interruptible (trans (f int))) cont_node), None)
            handle exn => (mk_state cont_node, Some exn);
      in
        if is_stale result then return (mk_state back_node, Some (if_none opt_exn rollback))
        else return (result, opt_exn)
      end;

fun check_stale state =
  if not (is_stale state) then ()
  else warning "Stale signature encountered!  Should restart current theory.";

end;


(* primitive transitions *)

(*Important note: recovery from stale signatures is provided only for
  theory-level operations via MapCurrent and AppCurrent.  Other node
  or state operations should not touch signatures at all.

  Also note that interrupts are enabled for Keep, MapCurrent, and
  AppCurrent only.*)

datatype trans =
  Reset |                                       (*empty toplevel*)
  Init of (bool -> node) * ((node -> unit) * (node -> unit)) |
    (*init node; provide exit/kill operation*)
  Exit |                                        (*conclude node*)
  Kill |                                        (*abort node*)
  Keep of bool -> state -> unit |               (*peek at state*)
  History of node History.T -> node History.T | (*history operation (undo etc.)*)
  MapCurrent of bool -> node -> node |          (*change node, bypassing history*)
  AppCurrent of bool -> node -> node;           (*change node, recording history*)

fun undo_limit int = if int then None else Some 0;

local

fun apply_tr _ Reset _ = toplevel
  | apply_tr int (Init (f, term)) (State None) =
      State (Some (History.init (undo_limit int) (f int), term))
  | apply_tr _ (Init _ ) (State (Some _)) = raise UNDEF
  | apply_tr _ Exit (State None) = raise UNDEF
  | apply_tr _ Exit (State (Some (node, (exit, _)))) =
      (exit (History.current node); State None)
  | apply_tr _ Kill (State None) = raise UNDEF
  | apply_tr _ Kill (State (Some (node, (_, kill)))) =
      (kill (History.current node); State None)
  | apply_tr int (Keep f) state = (exhibit_interrupt (f int) state; state)
  | apply_tr _ (History _) (State None) = raise UNDEF
  | apply_tr _ (History f) (State (Some (node, term))) = State (Some (f node, term))
  | apply_tr int (MapCurrent f) state = node_trans int false f state
  | apply_tr int (AppCurrent f) state = node_trans int true f state;

fun apply_union _ [] state = raise FAILURE (state, UNDEF)
  | apply_union int (tr :: trs) state =
      transform_error (apply_tr int tr) state
        handle UNDEF => apply_union int trs state
          | FAILURE (alt_state, UNDEF) => apply_union int trs alt_state
          | exn as FAILURE _ => raise exn
          | exn => raise FAILURE (state, exn);

in

fun apply_trans int trs state = (apply_union int trs state, None)
  handle FAILURE (alt_state, exn) => (alt_state, Some exn) | exn => (state, Some exn);

end;


(* datatype transition *)

datatype transition = Transition of
 {name: string,
  pos: Position.T,
  int_only: bool,
  print: bool,
  no_timing: bool,
  trans: trans list};

fun make_transition (name, pos, int_only, print, no_timing, trans) =
  Transition {name = name, pos = pos, int_only = int_only, print = print,
    no_timing = no_timing, trans = trans};

fun map_transition f (Transition {name, pos, int_only, print, no_timing, trans}) =
  make_transition (f (name, pos, int_only, print, no_timing, trans));

val empty = make_transition ("<unknown>", Position.none, false, false, false, []);


(* diagnostics *)

fun str_of_transition (Transition {name, pos, ...}) = quote name ^ Position.str_of pos;

fun command_msg msg tr = msg ^ "command " ^ str_of_transition tr;
fun at_command tr = command_msg "At " tr ^ ".";

fun type_error tr state =
  ERROR_MESSAGE (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name nm = map_transition (fn (_, pos, int_only, print, no_timing, trans) =>
  (nm, pos, int_only, print, no_timing, trans));

fun position pos = map_transition (fn (name, _, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

fun interactive int_only = map_transition (fn (name, pos, _, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

val print = map_transition (fn (name, pos, int_only, _, no_timing, trans) =>
  (name, pos, int_only, true, no_timing, trans));

val no_timing = map_transition (fn (name, pos, int_only, print, _, trans) =>
  (name, pos, int_only, print, true, trans));

fun add_trans tr = map_transition (fn (name, pos, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans @ [tr]));


(* build transitions *)

val reset = add_trans Reset;
fun init f exit kill = add_trans (Init (f, (exit, kill)));
val exit = add_trans Exit;
val kill = add_trans Kill;
val keep' = add_trans o Keep;
val history = add_trans o History;
val map_current = add_trans o MapCurrent;
val app_current = add_trans o AppCurrent;

fun keep f = add_trans (Keep (fn _ => f));
fun imperative f = keep (fn _ => f ());

fun init_theory f exit kill =
  init (fn int => Theory (f int))
    (fn Theory thy => exit thy | _ => raise UNDEF)
    (fn Theory thy => kill thy | _ => raise UNDEF);

fun theory f = app_current (fn _ => (fn Theory thy => Theory (f thy) | _ => raise UNDEF));
fun theory' f = app_current (fn int => (fn Theory thy => Theory (f int thy) | _ => raise UNDEF));
fun theory_to_proof f =
  app_current (fn int => (fn Theory thy => Proof (f int thy) | _ => raise UNDEF));
fun proof' f = map_current (fn int => (fn Proof prf => Proof (f int prf) | _ => raise UNDEF));
val proof = proof' o K;
fun proof_to_theory f = map_current (fn _ => (fn Proof prf => Theory (f prf) | _ => raise UNDEF));



(** toplevel transactions **)

val quiet = ref false;


(* print exceptions *)

fun raised name = "exception " ^ name ^ " raised";
fun raised_msg name msg = raised name ^ ": " ^ msg;

fun exn_message TERMINATE = "Exit."
  | exn_message RESTART = "Restart."
  | exn_message (EXCURSION_FAIL (exn, msg)) = cat_lines [exn_message exn, msg]
  | exn_message Interrupt = "Interrupt."
  | exn_message ERROR = "ERROR."
  | exn_message (ERROR_MESSAGE msg) = msg
  | exn_message (THEORY (msg, _)) = msg
  | exn_message (ProofContext.CONTEXT (msg, _)) = msg
  | exn_message (Proof.STATE (msg, _)) = msg
  | exn_message (ProofHistory.FAIL msg) = msg
  | exn_message (Attrib.ATTRIB_FAIL info) = fail_message "attribute" info
  | exn_message (Method.METHOD_FAIL info) = fail_message "method" info
  | exn_message (Comment.OUTPUT_FAIL info) = fail_message "antiquotation" info
  | exn_message (Syntax.AST (msg, _)) = raised_msg "AST" msg
  | exn_message (TYPE (msg, _, _)) = raised_msg "TYPE" msg
  | exn_message (TERM (msg, _)) = raised_msg "TERM" msg
  | exn_message (THM (msg, _, _)) = raised_msg "THM" msg
  | exn_message Library.OPTION = raised "Library.OPTION"
  | exn_message (Library.LIST msg) = raised_msg "Library.LIST" msg
  | exn_message exn = General.exnMessage exn
and fail_message kind ((name, pos), exn) =
  "Error in " ^ kind ^ " " ^ quote name ^ Position.str_of pos ^ ":\n" ^ exn_message exn;

fun print_exn None = ()
  | print_exn (Some (exn, s)) = error_msg (cat_lines [exn_message exn, s]);


(* apply transitions *)

local

fun app int (tr as Transition {trans, int_only, print, no_timing, ...}) state =
  let
    val _ =
      if int orelse not int_only then ()
      else warning (command_msg "Interactive-only " tr);
    val (result, opt_exn) =
      (if ! Library.timing andalso not no_timing then (warning (command_msg "" tr); timeap) else I)
        (apply_trans int trans) state;
    val _ = if int andalso print andalso not (! quiet) then print_state false result else ();
  in (result, apsome (fn UNDEF => type_error tr state | exn => exn) opt_exn) end;

in

fun apply int tr st =
  (case app int tr st of
    (_, Some TERMINATE) => None
  | (_, Some RESTART) => Some (toplevel, None)
  | (state', Some (EXCURSION_FAIL exn_info)) => Some (state', Some exn_info)
  | (state', Some exn) => Some (state', Some (exn, at_command tr))
  | (state', None) => Some (state', None));

end;


(* excursion: toplevel -- apply transformers -- toplevel *)

local

fun excur [] x = x
  | excur ((tr, f) :: trs) (st, res) =
      (case apply false tr st of
        Some (st', None) =>
          excur trs (st', transform_error (fn () => f st' res) () handle exn =>
            raise EXCURSION_FAIL (exn, "Presentation failed.\n" ^ at_command tr))
      | Some (st', Some exn_info) => raise EXCURSION_FAIL exn_info
      | None => raise EXCURSION_FAIL (TERMINATE, at_command tr));

in

fun excursion_result (trs, res) =
  (case excur trs (State None, res) of
    (State None, res') => res'
  | _ => raise ERROR_MESSAGE "Unfinished development at end of input")
  handle exn => error (exn_message exn);

fun excursion trs =
  excursion_result (map (fn tr => (tr, fn _ => fn _ => ())) trs, ());

end;



(** interactive transformations **)

(* the global state reference *)

val global_state = ref (toplevel, None: (exn * string) option);

fun set_state state = global_state := (state, None);
fun get_state () = fst (! global_state);
fun exn () = snd (! global_state);


(* the Isar source of transitions *)

type isar =
  (transition, (transition option,
    (OuterLex.token, (OuterLex.token,
      Position.T * (Symbol.symbol, (string, unit) Source.source) Source.source)
          Source.source) Source.source) Source.source) Source.source;


(* apply transformers to global state *)

nonfix >>;

fun >> tr =
  (case apply true tr (get_state ()) of
    None => false
  | Some (state', exn_info) =>
      (global_state := (state', exn_info);
        check_stale state'; print_exn exn_info;
        true));

(*Note: this is for Poly/ML only, we really do not intend to exhibit
  interrupts here*)
fun get_interrupt src = Some (Source.get_single src) handle Interrupt => None;

fun raw_loop src =
  (case get_interrupt (Source.set_prompt (prompt_state (get_state ())) src) of
    None => (writeln "\nInterrupt."; raw_loop src)
  | Some None => ()
  | Some (Some (tr, src')) => if >> tr then raw_loop src' else ());


fun loop src = mask_interrupt raw_loop src;


end;
