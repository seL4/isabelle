(*  Title:      Pure/Isar/toplevel.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle/Isar toplevel.
*)

signature TOPLEVEL =
sig
  datatype node =
    Theory of theory * Proof.context option |
    Proof of ProofHistory.T |
    SkipProof of int History.T * theory
  type state
  val toplevel: state
  val is_toplevel: state -> bool
  val level: state -> int
  exception UNDEF
  val assert: bool -> unit
  val node_history_of: state -> node History.T
  val node_of: state -> node
  val node_case: (theory -> 'a) -> (Proof.state -> 'a) -> state -> 'a
  val theory_of: state -> theory
  val sign_of: state -> theory    (*obsolete*)
  val body_context_of: state -> Proof.context
  val no_body_context: state -> state
  val proof_of: state -> Proof.state
  val is_proof: state -> bool
  val enter_forward_proof: state -> Proof.state
  val prompt_state_default: state -> string
  val prompt_state_fn: (state -> string) ref
  val print_state_context: state -> unit
  val print_state_default: bool -> state -> unit
  val print_state_hook: (bool -> state -> unit) -> unit
  val print_state_fn: (bool -> state -> unit) ref
  val print_state: bool -> state -> unit
  val pretty_state: bool -> state -> Pretty.T list
  val quiet: bool ref
  val debug: bool ref
  val interact: bool ref
  val timing: bool ref
  val profiling: int ref
  val skip_proofs: bool ref
  exception TERMINATE
  exception RESTART
  type transition
  val undo_limit: bool -> int option
  val empty: transition
  val name_of: transition -> string
  val source_of: transition -> OuterLex.token list option
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val source: OuterLex.token list -> transition -> transition
  val interactive: bool -> transition -> transition
  val print: transition -> transition
  val print': string -> transition -> transition
  val three_buffersN: string
  val print3: transition -> transition
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
  val theory_context: (theory -> theory * Proof.context) -> transition -> transition
  val theory_to_proof: (theory -> Proof.state) -> transition -> transition
  val proof: (ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val proof': (bool -> ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val actual_proof: (ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val skip_proof: (int History.T -> int History.T) -> transition -> transition
  val proof_to_theory: (ProofHistory.T -> theory) -> transition -> transition
  val proof_to_theory': (bool -> ProofHistory.T -> theory) -> transition -> transition
  val proof_to_theory_context: (bool -> ProofHistory.T -> theory * Proof.context)
    -> transition -> transition
  val skip_proof_to_theory: (int History.T -> bool) -> transition -> transition
  val unknown_theory: transition -> transition
  val unknown_proof: transition -> transition
  val unknown_context: transition -> transition
  val exn_message: exn -> string
  val apply: bool -> transition -> state -> (state * (exn * string) option) option
  val command: transition -> state -> state
  val present_excursion: (transition * (state -> state -> 'a -> 'a)) list -> 'a -> 'a
  val excursion: transition list -> unit
  val set_state: state -> unit
  val get_state: unit -> state
  val exn: unit -> (exn * string) option
  val >> : transition -> bool
  val >>> : transition list -> unit
  type 'a isar
  val loop: 'a isar -> unit
end;

structure Toplevel: TOPLEVEL =
struct


(** toplevel state **)

(* datatype state *)

datatype node =
  Theory of theory * Proof.context option |  (*theory with optional body context*)
  Proof of ProofHistory.T |                  (*history of proof states*)
  SkipProof of int History.T * theory;       (*history of proof depths*)

datatype state = State of (node History.T * ((node -> unit) * (node -> unit))) option;

val toplevel = State NONE;

fun is_toplevel (State NONE) = true
  | is_toplevel _ = false;

fun level (State NONE) = 0
  | level (State (SOME (node, _))) =
      (case History.current node of
        Theory _ => 0
      | Proof prf => Proof.level (ProofHistory.current prf)
      | SkipProof (h, _) => History.current h + 1);    (*different notion of proof depth!*)

fun str_of_state (State NONE) = "at top level"
  | str_of_state (State (SOME (node, _))) =
      (case History.current node of
        Theory _ => "in theory mode"
      | Proof _ => "in proof mode"
      | SkipProof _ => "in skipped proof mode");


(* top node *)

exception UNDEF;

fun assert true = ()
  | assert false = raise UNDEF;

fun node_history_of (State NONE) = raise UNDEF
  | node_history_of (State (SOME (node, _))) = node;

val node_of = History.current o node_history_of;

fun node_case f g state =
  (case node_of state of
    Theory (thy, _) => f thy
  | Proof prf => g (ProofHistory.current prf)
  | SkipProof (_, thy) => f thy);

val theory_of = node_case I Proof.theory_of;
val sign_of = theory_of;

fun body_context_of state =
  (case node_of state of
    Theory (_, SOME ctxt) => ctxt
  | _ => node_case ProofContext.init Proof.context_of state);

fun no_body_context (State NONE) = State NONE
  | no_body_context (State (SOME (node, x))) =
      State (SOME (History.apply (fn Theory (thy, _) => Theory (thy, NONE) | nd => nd) node, x));

val proof_of = node_case (fn _ => raise UNDEF) I;
val is_proof = can proof_of;

val enter_forward_proof = node_case (Proof.init o ProofContext.init) Proof.enter_forward;


(* prompt state *)

fun prompt_state_default (State _) = Source.default_prompt;

val prompt_state_fn = ref prompt_state_default;
fun prompt_state state = ! prompt_state_fn state;


(* print state *)

fun pretty_context thy = [Pretty.block
  [Pretty.str "theory", Pretty.brk 1, Pretty.str (Context.theory_name thy),
    Pretty.str " =", Pretty.brk 1, ThyInfo.pretty_theory thy]];

fun pretty_state_context state =
  (case try theory_of state of NONE => []
  | SOME thy => pretty_context thy);

fun pretty_node prf_only (Theory (thy, _)) = if prf_only then [] else pretty_context thy
  | pretty_node _ (Proof prf) =
      Proof.pretty_state (ProofHistory.position prf) (ProofHistory.current prf)
  | pretty_node _ (SkipProof (h, _)) =
      [Pretty.str ("skipped proof: depth " ^ string_of_int (History.current h))];

fun pretty_state prf_only state =
  let val ref (begin_state, end_state, _) = Display.current_goals_markers in
    (case try node_of state of NONE => []
    | SOME node =>
        (if begin_state = "" then [] else [Pretty.str begin_state]) @
        pretty_node prf_only node @
        (if end_state = "" then [] else [Pretty.str end_state]))
  end;

val print_state_context = Pretty.writelns o pretty_state_context;
fun print_state_default prf_only state = Pretty.writelns (pretty_state prf_only state);

val print_state_hooks = ref ([]: (bool -> state -> unit) list);
fun print_state_hook f = change print_state_hooks (cons f);
val print_state_fn = ref print_state_default;

fun print_state prf_only state =
 (List.app (fn f => (try (fn () => f prf_only state) (); ())) (! print_state_hooks);
  ! print_state_fn prf_only state);



(** toplevel transitions **)

val quiet = ref false;
val debug = ref false;
val interact = ref false;
val timing = Output.timing;
val profiling = ref 0;
val skip_proofs = ref false;

exception TERMINATE;
exception RESTART;
exception EXCURSION_FAIL of exn * string;
exception FAILURE of state * exn;


(* node transactions and recovery from stale theories *)

(*NB: proof commands should be non-destructive!*)

local

fun is_stale state = Context.is_stale (theory_of state) handle UNDEF => false;

val stale_theory = ERROR_MESSAGE "Stale theory encountered after succesful execution!";

fun checkpoint_node true (Theory (thy, ctxt)) = Theory (Theory.checkpoint thy, ctxt)
  | checkpoint_node _ node = node;

fun copy_node true (Theory (thy, ctxt)) = Theory (Theory.copy thy, ctxt)
  | copy_node _ node = node;

fun return (result, NONE) = result
  | return (result, SOME exn) = raise FAILURE (result, exn);

fun debug_trans f x =
  if ! debug then
    setmp Output.transform_exceptions false
      exception_trace (fn () => f x)
  else f x;

fun interruptible f x =
  let val y = ref x
  in raise_interrupt (fn () => y := f x) (); ! y end;

in

fun transaction _ _ _ (State NONE) = raise UNDEF
  | transaction int hist f (State (SOME (node, term))) =
      let
        val cont_node = History.map (checkpoint_node int) node;
        val back_node = History.map (copy_node int) cont_node;
        fun state nd = State (SOME (nd, term));
        fun normal_state nd = (state nd, NONE);
        fun error_state nd exn = (state nd, SOME exn);

        val (result, err) =
          cont_node
          |> ((fn nd => f int nd)
              |> (if hist then History.apply_copy (copy_node int) else History.map)
              |> debug_trans
              |> interruptible
              |> transform_error)
          |> normal_state
          handle exn => error_state cont_node exn;
      in
        if is_stale result
        then return (error_state back_node (if_none err stale_theory))
        else return (result, err)
      end;

end;


(* primitive transitions *)

(*NB: recovery from stale theories is provided only for theory-level
  operations via MapCurrent and AppCurrent.  Other node or state
  operations should not touch theories at all.

  Interrupts are enabled only for Keep, MapCurrent, and AppCurrent.*)

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

fun undo_limit int = if int then NONE else SOME 0;

local

fun apply_tr _ Reset _ = toplevel
  | apply_tr int (Init (f, term)) (State NONE) =
      State (SOME (History.init (undo_limit int) (f int), term))
  | apply_tr _ (Init _ ) (State (SOME _)) = raise UNDEF
  | apply_tr _ Exit (State NONE) = raise UNDEF
  | apply_tr _ Exit (State (SOME (node, (exit, _)))) =
      (exit (History.current node); State NONE)
  | apply_tr _ Kill (State NONE) = raise UNDEF
  | apply_tr _ Kill (State (SOME (node, (_, kill)))) =
      (kill (History.current node); State NONE)
  | apply_tr int (Keep f) state = (raise_interrupt (f int) state; state)
  | apply_tr _ (History _) (State NONE) = raise UNDEF
  | apply_tr _ (History f) (State (SOME (node, term))) = State (SOME (f node, term))
  | apply_tr int (MapCurrent f) state = transaction int false f state
  | apply_tr int (AppCurrent f) state = transaction int true f state;

fun apply_union _ [] state = raise FAILURE (state, UNDEF)
  | apply_union int (tr :: trs) state =
      transform_error (apply_tr int tr) state
        handle UNDEF => apply_union int trs state
          | FAILURE (alt_state, UNDEF) => apply_union int trs alt_state
          | exn as FAILURE _ => raise exn
          | exn => raise FAILURE (state, exn);

in

fun apply_trans int trs state = (apply_union int trs state, NONE)
  handle FAILURE (alt_state, exn) => (alt_state, SOME exn) | exn => (state, SOME exn);

end;


(* datatype transition *)

datatype transition = Transition of
 {name: string,                        (*command name*)
  pos: Position.T,                     (*source position*)
  source: OuterLex.token list option,  (*source text*)
  int_only: bool,                      (*interactive-only*)
  print: string list,                  (*print modes (union)*)
  no_timing: bool,                     (*suppress timing*)
  trans: trans list};                  (*primitive transitions (union)*)

fun make_transition (name, pos, source, int_only, print, no_timing, trans) =
  Transition {name = name, pos = pos, source = source,
    int_only = int_only, print = print, no_timing = no_timing, trans = trans};

fun map_transition f (Transition {name, pos, source, int_only, print, no_timing, trans}) =
  make_transition (f (name, pos, source, int_only, print, no_timing, trans));

val empty = make_transition ("<unknown>", Position.none, NONE, false, [], false, []);

fun name_of (Transition {name, ...}) = name;
fun source_of (Transition {source, ...}) = source;


(* diagnostics *)

fun str_of_transition (Transition {name, pos, ...}) = quote name ^ Position.str_of pos;

fun command_msg msg tr = msg ^ "command " ^ str_of_transition tr;
fun at_command tr = command_msg "At " tr ^ ".";

fun type_error tr state =
  ERROR_MESSAGE (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name nm = map_transition (fn (_, pos, source, int_only, print, no_timing, trans) =>
  (nm, pos, source, int_only, print, no_timing, trans));

fun position pos = map_transition (fn (name, _, source, int_only, print, no_timing, trans) =>
  (name, pos, source, int_only, print, no_timing, trans));

fun source src = map_transition (fn (name, pos, _, int_only, print, no_timing, trans) =>
  (name, pos, SOME src, int_only, print, no_timing, trans));

fun interactive int_only = map_transition (fn (name, pos, source, _, print, no_timing, trans) =>
  (name, pos, source, int_only, print, no_timing, trans));

val no_timing = map_transition (fn (name, pos, source, int_only, print, _, trans) =>
  (name, pos, source, int_only, print, true, trans));

fun add_trans tr = map_transition (fn (name, pos, source, int_only, print, no_timing, trans) =>
  (name, pos, source, int_only, print, no_timing, trans @ [tr]));

fun print' mode = map_transition (fn (name, pos, source, int_only, print, no_timing, trans) =>
  (name, pos, source, int_only, insert (op =) mode print, no_timing, trans));

val print = print' "";

val three_buffersN = "three_buffers";
val print3 = print' three_buffersN;


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
  init (fn int => Theory (f int, NONE))
    (fn Theory (thy, _) => exit thy | _ => raise UNDEF)
    (fn Theory (thy, _) => kill thy | _ => raise UNDEF);


(* typed transitions *)

fun theory f = app_current (K (fn Theory (thy, _) => Theory (f thy, NONE) | _ => raise UNDEF));
fun theory' f = app_current (fn int =>
  (fn Theory (thy, _) => Theory (f int thy, NONE) | _ => raise UNDEF));

fun theory_context f =
  app_current (K (fn Theory (thy, _) => Theory (apsnd SOME (f thy)) | _ => raise UNDEF));

fun theory_to_proof f = app_current (fn int =>
  (fn Theory (thy, _) =>
      let val st = f thy in
        if Theory.eq_thy (thy, Proof.theory_of st) then ()
        else error "Theory changed at start of proof";
        if ! skip_proofs then
          SkipProof (History.init (undo_limit int) 0, #1 (Proof.global_skip_proof int st))
        else Proof (ProofHistory.init (undo_limit int) st)
      end
    | _ => raise UNDEF));

fun proof' f = map_current (fn int =>
  (fn Proof prf => Proof (f int prf)
    | SkipProof (h, thy) => SkipProof (History.apply I h, thy)   (*approximate f*)
    | _ => raise UNDEF));

val proof = proof' o K;

fun actual_proof f = map_current (fn _ =>
  (fn Proof prf => Proof (f prf) | _ => raise UNDEF));

fun skip_proof f = map_current (fn _ =>
  (fn SkipProof (h, thy) => SkipProof (f h, thy) | _ => raise UNDEF));

fun end_proof f =
  map_current (fn int => (fn Proof prf => Theory (f int prf)
    | SkipProof (h, thy) => if History.current h = 0 then Theory (thy, NONE) else raise UNDEF
    | _ => raise UNDEF));

fun proof_to_theory' f = end_proof (rpair NONE oo f);
fun proof_to_theory f = proof_to_theory' (K f);
fun proof_to_theory_context f = end_proof (apsnd SOME oo f);

fun skip_proof_to_theory p = map_current (fn _ =>
  (fn SkipProof (h, thy) => if p h then Theory (thy, NONE) else raise UNDEF | _ => raise UNDEF));

val unknown_theory = imperative (fn () => warning "Unknown theory context");
val unknown_proof = imperative (fn () => warning "Unknown proof context");
val unknown_context = imperative (fn () => warning "Unknown context");



(** toplevel transactions **)

(* print exceptions *)

local

fun with_context f xs =
  (case Context.get_context () of NONE => []
  | SOME thy => map (f thy) xs);

fun raised name [] = "exception " ^ name ^ " raised"
  | raised name [msg] = "exception " ^ name ^ " raised: " ^ msg
  | raised name msgs = cat_lines (("exception " ^ name ^ " raised:") :: msgs);

fun exn_msg _ TERMINATE = "Exit."
  | exn_msg _ RESTART = "Restart."
  | exn_msg _ Interrupt = "Interrupt."
  | exn_msg _ ERROR = "ERROR."
  | exn_msg _ (ERROR_MESSAGE msg) = msg
  | exn_msg detailed (EXCEPTION (exn, msg)) = cat_lines [exn_msg detailed exn, msg]
  | exn_msg detailed (EXCURSION_FAIL (exn, msg)) = cat_lines [exn_msg detailed exn, msg]
  | exn_msg false (THEORY (msg, _)) = msg
  | exn_msg true (THEORY (msg, thys)) = raised "THEORY" (msg :: map Context.str_of_thy thys)
  | exn_msg _ (ProofContext.CONTEXT (msg, _)) = msg
  | exn_msg _ (Proof.STATE (msg, _)) = msg
  | exn_msg _ (ProofHistory.FAIL msg) = msg
  | exn_msg detailed (MetaSimplifier.SIMPROC_FAIL (name, exn)) =
      fail_msg detailed "simproc" ((name, Position.none), exn)
  | exn_msg detailed (Attrib.ATTRIB_FAIL info) = fail_msg detailed "attribute" info
  | exn_msg detailed (Method.METHOD_FAIL info) = fail_msg detailed "method" info
  | exn_msg detailed (Antiquote.ANTIQUOTE_FAIL info) = fail_msg detailed "antiquotation" info
  | exn_msg false (Syntax.AST (msg, _)) = raised "AST" [msg]
  | exn_msg true (Syntax.AST (msg, asts)) =
      raised "AST" (msg :: map (Pretty.string_of o Syntax.pretty_ast) asts)
  | exn_msg false (TYPE (msg, _, _)) = raised "TYPE" [msg]
  | exn_msg true (TYPE (msg, Ts, ts)) = raised "TYPE" (msg ::
        with_context Sign.string_of_typ Ts @ with_context Sign.string_of_term ts)
  | exn_msg false (TERM (msg, _)) = raised "TERM" [msg]
  | exn_msg true (TERM (msg, ts)) = raised "TERM" (msg :: with_context Sign.string_of_term ts)
  | exn_msg false (THM (msg, _, _)) = raised "THM" [msg]
  | exn_msg true (THM (msg, i, thms)) =
      raised ("THM " ^ string_of_int i) (msg :: map Display.string_of_thm thms)
  | exn_msg _ Option = raised "Option" []
  | exn_msg _ UnequalLengths = raised "UnequalLengths" []
  | exn_msg _ Empty = raised "Empty" []
  | exn_msg _ Subscript = raised "Subscript" []
  | exn_msg _ (Fail msg) = raised "Fail" [msg]
  | exn_msg _ exn = General.exnMessage exn
and fail_msg detailed kind ((name, pos), exn) =
  "Error in " ^ kind ^ " " ^ quote name ^ Position.str_of pos ^ ":\n" ^ exn_msg detailed exn;

in

fun exn_message exn = exn_msg (! debug) exn;

fun print_exn NONE = ()
  | print_exn (SOME (exn, s)) = error_msg (cat_lines [exn_message exn, s]);

end;


(* apply transitions *)

local

fun app int (tr as Transition {trans, int_only, print, no_timing, ...}) state =
  let
    val _ = conditional (not int andalso int_only) (fn () =>
      warning (command_msg "Interactive-only " tr));

    fun do_timing f x = (info (command_msg "" tr); timeap f x);
    fun do_profiling f x = profile (! profiling) f x;

    val (result, opt_exn) =
       state |> (apply_trans int trans
        |> (if ! profiling > 0 then do_profiling else I)
        |> (if ! profiling > 0 orelse ! timing andalso not no_timing then do_timing else I));
    val _ = conditional (int andalso not (! quiet) andalso
        exists (fn m => m mem_string print) ("" :: ! print_mode))
      (fn () => print_state false result);
  in (result, Option.map (fn UNDEF => type_error tr state | exn => exn) opt_exn) end;

in

fun apply int tr st =
  (case app int tr st of
    (_, SOME TERMINATE) => NONE
  | (_, SOME RESTART) => SOME (toplevel, NONE)
  | (state', SOME (EXCURSION_FAIL exn_info)) => SOME (state', SOME exn_info)
  | (state', SOME exn) => SOME (state', SOME (exn, at_command tr))
  | (state', NONE) => SOME (state', NONE));

fun command tr st =
  (case apply false tr st of
    SOME (st', NONE) => st'
  | SOME (st', SOME exn_info) => raise EXCURSION_FAIL exn_info
  | NONE => raise EXCURSION_FAIL (TERMINATE, at_command tr));

end;


(* excursion: toplevel -- apply transformers/presentation -- toplevel *)

local

fun excur [] x = x
  | excur ((tr, pr) :: trs) (st, res) =
      (case apply (! interact) tr st of
        SOME (st', NONE) =>
          excur trs (st', transform_error (fn () => pr st st' res) () handle exn =>
            raise EXCURSION_FAIL (exn, "Presentation failed\n" ^ at_command tr))
      | SOME (st', SOME exn_info) => raise EXCURSION_FAIL exn_info
      | NONE => raise EXCURSION_FAIL (TERMINATE, at_command tr));

fun no_pr _ _ _ = ();

in

fun present_excursion trs res =
  (case excur trs (State NONE, res) of
    (State NONE, res') => res'
  | _ => raise ERROR_MESSAGE "Unfinished development at end of input")
  handle exn => error (exn_message exn);

fun excursion trs = present_excursion (map (rpair no_pr) trs) ();

end;



(** interactive transformations **)

(* the global state reference *)

val global_state = ref (toplevel, NONE: (exn * string) option);

fun set_state state = global_state := (state, NONE);
fun get_state () = fst (! global_state);
fun exn () = snd (! global_state);


(* the Isar source of transitions *)

type 'a isar =
  (transition, (transition option,
    (OuterLex.token, (OuterLex.token option, (OuterLex.token, (OuterLex.token,
      Position.T * (Symbol.symbol, (string, 'a) Source.source) Source.source)
          Source.source) Source.source) Source.source) Source.source) Source.source) Source.source;


(* apply transformers to global state *)

nonfix >> >>>;

fun >> tr =
  (case apply true tr (get_state ()) of
    NONE => false
  | SOME (state', exn_info) =>
      (global_state := (state', exn_info);
        print_exn exn_info;
        true));

fun >>> [] = ()
  | >>> (tr :: trs) = if >> tr then >>> trs else ();

(*Note: we really do not intend to exhibit interrupts here.
  Poly/ML needs exception Interrupt to be handled. SML/NJ needs IO to be handled.*)
fun get_interrupt src = SOME (Source.get_single src) 
                        handle Interrupt => NONE
                             | IO.Io _ => get_interrupt src;

fun raw_loop src =
  (case get_interrupt (Source.set_prompt (prompt_state (get_state ())) src) of
    NONE => (writeln "\nInterrupt."; raw_loop src)
  | SOME NONE => ()
  | SOME (SOME (tr, src')) => if >> tr then raw_loop src' else ());

fun loop src = ignore_interrupt raw_loop src;

end;
