(*  Title:      Pure/Isar/toplevel.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle/Isar toplevel.
*)

signature TOPLEVEL =
sig
  exception UNDEF
  type generic_theory
  type node
  val theory_node: node -> generic_theory option
  val proof_node: node -> ProofHistory.T option
  val cases_node: (generic_theory -> 'a) -> (Proof.state -> 'a) -> node -> 'a
  val presentation_context: node option -> xstring option -> Proof.context
  type state
  val is_toplevel: state -> bool
  val is_theory: state -> bool
  val is_proof: state -> bool
  val level: state -> int
  val node_history_of: state -> node History.T
  val node_of: state -> node
  val node_case: (generic_theory -> 'a) -> (Proof.state -> 'a) -> state -> 'a
  val context_of: state -> Proof.context
  val generic_theory_of: state -> generic_theory
  val theory_of: state -> theory
  val proof_of: state -> Proof.state
  val proof_position_of: state -> int
  val enter_proof_body: state -> Proof.state
  val print_state_context: state -> unit
  val print_state: bool -> state -> unit
  val quiet: bool ref
  val debug: bool ref
  val interact: bool ref
  val timing: bool ref
  val profiling: int ref
  val skip_proofs: bool ref
  val crashes: exn list ref
  exception TERMINATE
  exception RESTART
  exception TOPLEVEL_ERROR
  val exn_message: exn -> string
  val program: (unit -> 'a) -> 'a
  type transition
  val undo_limit: bool -> int option
  val empty: transition
  val name_of: transition -> string
  val properties_of: transition -> Markup.property list
  val source_of: transition -> OuterLex.token list option
  val name: string -> transition -> transition
  val properties: Markup.property list -> transition -> transition
  val position: Position.T -> transition -> transition
  val source: OuterLex.token list -> transition -> transition
  val interactive: bool -> transition -> transition
  val print: transition -> transition
  val print': string -> transition -> transition
  val three_buffersN: string
  val print3: transition -> transition
  val no_timing: transition -> transition
  val init_theory: (bool -> theory) -> (theory -> unit) -> (theory -> unit) ->
    transition -> transition
  val init_empty: (state -> bool) -> (unit -> unit) -> transition -> transition
  val exit: transition -> transition
  val undo_exit: transition -> transition
  val kill: transition -> transition
  val history: (node History.T -> node History.T) -> transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val keep': (bool -> state -> unit) -> transition -> transition
  val imperative: (unit -> unit) -> transition -> transition
  val theory: (theory -> theory) -> transition -> transition
  val theory': (bool -> theory -> theory) -> transition -> transition
  val begin_local_theory: bool -> (theory -> local_theory) -> transition -> transition
  val end_local_theory: transition -> transition
  val local_theory: xstring option -> (local_theory -> local_theory) -> transition -> transition
  val present_local_theory: xstring option -> (bool -> node -> unit) -> transition -> transition
  val local_theory_to_proof': xstring option -> (bool -> local_theory -> Proof.state) ->
    transition -> transition
  val local_theory_to_proof: xstring option -> (local_theory -> Proof.state) ->
    transition -> transition
  val theory_to_proof: (theory -> Proof.state) -> transition -> transition
  val end_proof: (bool -> Proof.state -> Proof.context) -> transition -> transition
  val forget_proof: transition -> transition
  val present_proof: (bool -> node -> unit) -> transition -> transition
  val proofs': (bool -> Proof.state -> Proof.state Seq.seq) -> transition -> transition
  val proof': (bool -> Proof.state -> Proof.state) -> transition -> transition
  val proofs: (Proof.state -> Proof.state Seq.seq) -> transition -> transition
  val proof: (Proof.state -> Proof.state) -> transition -> transition
  val actual_proof: (ProofHistory.T -> ProofHistory.T) -> transition -> transition
  val skip_proof: (int History.T -> int History.T) -> transition -> transition
  val skip_proof_to_theory: (int -> bool) -> transition -> transition
  val unknown_theory: transition -> transition
  val unknown_proof: transition -> transition
  val unknown_context: transition -> transition
  val present_excursion: (transition * (state -> state -> 'a -> 'a)) list -> 'a -> 'a
  val excursion: transition list -> unit
  val set_state: state -> unit
  val get_state: unit -> state
  val exn: unit -> (exn * string) option
  val >> : transition -> bool
  val >>> : transition list -> unit
  val init_state: unit -> unit
  type 'a isar
  val loop: bool -> 'a isar -> unit
end;

structure Toplevel: TOPLEVEL =
struct


(** toplevel state **)

exception UNDEF;


(* local theory wrappers *)

type generic_theory = Context.generic;    (*theory or local_theory*)

val loc_init = TheoryTarget.context;
val loc_exit = ProofContext.theory_of o LocalTheory.exit;

fun loc_begin loc (Context.Theory thy) = loc_init (the_default "-" loc) thy
  | loc_begin NONE (Context.Proof lthy) = lthy
  | loc_begin (SOME loc) (Context.Proof lthy) = loc_init loc (loc_exit lthy);

fun loc_finish _ (Context.Theory _) = Context.Theory o loc_exit
  | loc_finish NONE (Context.Proof _) = Context.Proof o LocalTheory.restore
  | loc_finish (SOME _) (Context.Proof lthy) = fn lthy' =>
      Context.Proof (LocalTheory.reinit (LocalTheory.raw_theory (K (loc_exit lthy')) lthy));


(* datatype node *)

datatype node =
  Theory of generic_theory * Proof.context option | (*theory with presentation context*)
  Proof of ProofHistory.T * ((Proof.context -> generic_theory) * generic_theory) |
    (*history of proof states, finish, original theory*)
  SkipProof of int History.T * (generic_theory * generic_theory);
    (*history of proof depths, resulting theory, original theory*)

val the_global_theory = fn Theory (Context.Theory thy, _) => thy | _ => raise UNDEF;
val theory_node = fn Theory (gthy, _) => SOME gthy | _ => NONE;
val proof_node = fn Proof (prf, _) => SOME prf | _ => NONE;

fun cases_node f _ (Theory (gthy, _)) = f gthy
  | cases_node _ g (Proof (prf, _)) = g (ProofHistory.current prf)
  | cases_node f _ (SkipProof (_, (gthy, _))) = f gthy;

fun presentation_context (SOME (Theory (_, SOME ctxt))) NONE = ctxt
  | presentation_context (SOME node) NONE = cases_node Context.proof_of Proof.context_of node
  | presentation_context (SOME node) (SOME loc) =
      loc_init loc (cases_node Context.theory_of Proof.theory_of node)
  | presentation_context NONE _ = raise UNDEF;


(* datatype state *)

type state_info = node History.T * ((theory -> unit) * (theory -> unit));

datatype state =
  Toplevel of state_info option |  (*outer toplevel, leftover end state*)
  State of state_info;

val toplevel = Toplevel NONE;

fun is_toplevel (Toplevel _) = true
  | is_toplevel _ = false;

fun level (Toplevel _) = 0
  | level (State (node, _)) =
      (case History.current node of
        Theory _ => 0
      | Proof (prf, _) => Proof.level (ProofHistory.current prf)
      | SkipProof (h, _) => History.current h + 1);   (*different notion of proof depth!*)

fun str_of_state (Toplevel _) = "at top level"
  | str_of_state (State (node, _)) =
      (case History.current node of
        Theory (Context.Theory _, _) => "in theory mode"
      | Theory (Context.Proof _, _) => "in local theory mode"
      | Proof _ => "in proof mode"
      | SkipProof _ => "in skipped proof mode");


(* top node *)

fun node_history_of (Toplevel _) = raise UNDEF
  | node_history_of (State (node, _)) = node;

val node_of = History.current o node_history_of;

fun is_theory state = not (is_toplevel state) andalso is_some (theory_node (node_of state));
fun is_proof state = not (is_toplevel state) andalso is_some (proof_node (node_of state));

fun node_case f g state = cases_node f g (node_of state);

val context_of = node_case Context.proof_of Proof.context_of;
val generic_theory_of = node_case I (Context.Proof o Proof.context_of);
val theory_of = node_case Context.theory_of Proof.theory_of;
val proof_of = node_case (fn _ => raise UNDEF) I;

fun proof_position_of state =
  (case node_of state of
    Proof (prf, _) => ProofHistory.position prf
  | _ => raise UNDEF);

val enter_proof_body = node_case (Proof.init o Context.proof_of) Proof.enter_forward;


(* print state *)

val pretty_context = LocalTheory.pretty o Context.cases (TheoryTarget.init NONE) I;

fun print_state_context state =
  (case try node_of state of
    NONE => []
  | SOME (Theory (gthy, _)) => pretty_context gthy
  | SOME (Proof (_, (_, gthy))) => pretty_context gthy
  | SOME (SkipProof (_, (gthy, _))) => pretty_context gthy)
  |> Pretty.chunks |> Pretty.writeln;

fun print_state prf_only state =
  (case try node_of state of
    NONE => []
  | SOME (Theory (gthy, _)) => if prf_only then [] else pretty_context gthy
  | SOME (Proof (prf, _)) =>
      Proof.pretty_state (ProofHistory.position prf) (ProofHistory.current prf)
  | SOME (SkipProof (h, _)) =>
      [Pretty.str ("skipped proof: depth " ^ string_of_int (History.current h))])
  |> Pretty.markup_chunks Markup.state |> Pretty.writeln;



(** toplevel transitions **)

val quiet = ref false;
val debug = Output.debugging;
val interact = ref false;
val timing = Output.timing;
val profiling = ref 0;
val skip_proofs = ref false;
val crashes = ref ([]: exn list);

exception TERMINATE;
exception RESTART;
exception EXCURSION_FAIL of exn * string;
exception FAILURE of state * exn;
exception TOPLEVEL_ERROR;


(* print exceptions *)

local

fun with_context f xs =
  (case ML_Context.get_context () of NONE => []
  | SOME context => map (f (Context.proof_of context)) xs);

fun raised name [] = "exception " ^ name ^ " raised"
  | raised name [msg] = "exception " ^ name ^ " raised: " ^ msg
  | raised name msgs = cat_lines (("exception " ^ name ^ " raised:") :: msgs);

fun exn_msg _ TERMINATE = "Exit."
  | exn_msg _ RESTART = "Restart."
  | exn_msg _ Interrupt = "Interrupt."
  | exn_msg _ TOPLEVEL_ERROR = "Error."
  | exn_msg _ (SYS_ERROR msg) = "## SYSTEM ERROR ##\n" ^ msg
  | exn_msg _ (ERROR msg) = msg
  | exn_msg detailed (Exn.EXCEPTIONS (exns, "")) = cat_lines (map (exn_msg detailed) exns)
  | exn_msg detailed (Exn.EXCEPTIONS (exns, msg)) = cat_lines (map (exn_msg detailed) exns @ [msg])
  | exn_msg detailed (EXCURSION_FAIL (exn, msg)) = cat_lines [exn_msg detailed exn, msg]
  | exn_msg false (THEORY (msg, _)) = msg
  | exn_msg true (THEORY (msg, thys)) = raised "THEORY" (msg :: map Context.str_of_thy thys)
  | exn_msg false (Syntax.AST (msg, _)) = raised "AST" [msg]
  | exn_msg true (Syntax.AST (msg, asts)) =
      raised "AST" (msg :: map (Pretty.string_of o Syntax.pretty_ast) asts)
  | exn_msg false (TYPE (msg, _, _)) = raised "TYPE" [msg]
  | exn_msg true (TYPE (msg, Ts, ts)) = raised "TYPE" (msg ::
        with_context Syntax.string_of_typ Ts @ with_context Syntax.string_of_term ts)
  | exn_msg false (TERM (msg, _)) = raised "TERM" [msg]
  | exn_msg true (TERM (msg, ts)) =
      raised "TERM" (msg :: with_context Syntax.string_of_term ts)
  | exn_msg false (THM (msg, _, _)) = raised "THM" [msg]
  | exn_msg true (THM (msg, i, thms)) =
      raised ("THM " ^ string_of_int i) (msg :: with_context ProofContext.string_of_thm thms)
  | exn_msg _ Option.Option = raised "Option" []
  | exn_msg _ Library.UnequalLengths = raised "UnequalLengths" []
  | exn_msg _ Empty = raised "Empty" []
  | exn_msg _ Subscript = raised "Subscript" []
  | exn_msg _ (Fail msg) = raised "Fail" [msg]
  | exn_msg _ exn = General.exnMessage exn;

in

fun exn_message exn = exn_msg (! debug) exn;
fun print_exn (exn, s) = Output.error_msg (cat_lines [exn_message exn, s]);

end;


(* controlled execution *)

local

fun debugging f x =
  if ! debug then exception_trace (fn () => f x)
  else f x;

fun interruptible f x =
  let val y = ref NONE
  in raise_interrupt (fn () => y := SOME (f x)) (); the (! y) end;

fun toplevel_error f x = f x
  handle exn => (Output.error_msg (exn_message exn); raise TOPLEVEL_ERROR);

in

fun controlled_execution f =
  f
  |> debugging
  |> interruptible;

fun program f =
 (f
  |> debugging
  |> toplevel_error) ();

end;


(* node transactions and recovery from stale theories *)

(*NB: proof commands should be non-destructive!*)

local

fun is_stale state = Context.is_stale (theory_of state) handle UNDEF => false;

val stale_theory = ERROR "Stale theory encountered after succesful execution!";

fun map_theory f = History.map_current
  (fn Theory (gthy, _) => Theory (Context.mapping f (LocalTheory.raw_theory f) gthy, NONE)
    | node => node);

fun context_position pos = History.map_current
  (fn Theory (gthy, ctxt) => Theory (ContextPosition.put pos gthy, ctxt)
    | Proof (prf, x) =>
        Proof (ProofHistory.map_current (Proof.map_context (ContextPosition.put_ctxt pos)) prf, x)
    | node => node);

fun return (result, NONE) = result
  | return (result, SOME exn) = raise FAILURE (result, exn);

in

fun transaction hist pos f (node, term) =
  let
    val cont_node = map_theory Theory.checkpoint node;
    val back_node = map_theory Theory.copy cont_node;
    fun state nd = State (nd, term);
    fun normal_state nd = (state nd, NONE);
    fun error_state nd exn = (state nd, SOME exn);

    val (result, err) =
      cont_node
      |> context_position pos
      |> map_theory Theory.checkpoint
      |> (f
          |> (if hist then History.apply' (History.current back_node) else History.map_current)
          |> controlled_execution)
      |> context_position Position.none
      |> normal_state
      handle exn => error_state cont_node exn;
  in
    if is_stale result
    then return (error_state back_node (the_default stale_theory err))
    else return (result, err)
  end;

end;


(* primitive transitions *)

(*Note: Recovery from stale theories is provided only for theory-level
  operations via Transaction.  Other node or state operations should
  not touch theories at all.  Interrupts are enabled only for Keep and
  Transaction.*)

datatype trans =
  Init of (bool -> theory) * ((theory -> unit) * (theory -> unit)) |
                                                    (*init node; with exit/kill operation*)
  InitEmpty of (state -> bool) * (unit -> unit) |   (*init empty toplevel*)
  Exit |                                            (*conclude node -- deferred until init*)
  UndoExit |                                        (*continue after conclusion*)
  Kill |                                            (*abort node*)
  History of node History.T -> node History.T |     (*history operation (undo etc.)*)
  Keep of bool -> state -> unit |                   (*peek at state*)
  Transaction of bool * (bool -> node -> node);     (*node transaction*)

fun undo_limit int = if int then NONE else SOME 0;

fun safe_exit (Toplevel (SOME (node, (exit, _)))) =
    (case try the_global_theory (History.current node) of
      SOME thy => controlled_execution exit thy
    | NONE => ())
  | safe_exit _ = ();

local

fun keep_state int f = controlled_execution (fn x => tap (f int) x);

fun apply_tr int _ (Init (f, term)) (state as Toplevel _) =
      let val node = Theory (Context.Theory (f int), NONE)
      in safe_exit state; State (History.init (undo_limit int) node, term) end
  | apply_tr int _ (InitEmpty (check, f)) (state as Toplevel _) =
      if check state then (safe_exit state; keep_state int (fn _ => fn _ => f ()) toplevel)
      else raise UNDEF
  | apply_tr _ _ Exit (State (node, term)) =
      (the_global_theory (History.current node); Toplevel (SOME (node, term)))
  | apply_tr _ _ UndoExit (Toplevel (SOME state_info)) = State state_info
  | apply_tr _ _ Kill (State (node, (_, kill))) =
      (kill (the_global_theory (History.current node)); toplevel)
  | apply_tr _ _ (History f) (State (node, term)) = State (f node, term)
  | apply_tr int _ (Keep f) state = keep_state int f state
  | apply_tr int pos (Transaction (hist, f)) (State state) =
      transaction hist pos (fn x => f int x) state
  | apply_tr _ _ _ _ = raise UNDEF;

fun apply_union _ _ [] state = raise FAILURE (state, UNDEF)
  | apply_union int pos (tr :: trs) state =
      apply_tr int pos tr state
        handle UNDEF => apply_union int pos trs state
          | FAILURE (alt_state, UNDEF) => apply_union int pos trs alt_state
          | exn as FAILURE _ => raise exn
          | exn => raise FAILURE (state, exn);

in

fun apply_trans int pos trs state = (apply_union int pos trs state, NONE)
  handle FAILURE (alt_state, exn) => (alt_state, SOME exn) | exn => (state, SOME exn);

end;


(* datatype transition *)

datatype transition = Transition of
 {name: string,                        (*command name*)
  props: Markup.property list,         (*properties*)
  pos: Position.T,                     (*source position*)
  source: OuterLex.token list option,  (*source text*)
  int_only: bool,                      (*interactive-only*)
  print: string list,                  (*print modes (union)*)
  no_timing: bool,                     (*suppress timing*)
  trans: trans list};                  (*primitive transitions (union)*)

fun make_transition (name, props, pos, source, int_only, print, no_timing, trans) =
  Transition {name = name, props = props, pos = pos, source = source,
    int_only = int_only, print = print, no_timing = no_timing, trans = trans};

fun map_transition f (Transition {name, props, pos, source, int_only, print, no_timing, trans}) =
  make_transition (f (name, props, pos, source, int_only, print, no_timing, trans));

val empty = make_transition ("<unknown>", [], Position.none, NONE, false, [], false, []);

fun name_of (Transition {name, ...}) = name;
fun properties_of (Transition {props, ...}) = props;
fun source_of (Transition {source, ...}) = source;


(* diagnostics *)

fun str_of_transition (Transition {name, pos, ...}) = quote name ^ Position.str_of pos;

fun command_msg msg tr = msg ^ "command " ^ str_of_transition tr;
fun at_command tr = command_msg "At " tr ^ ".";

fun type_error tr state =
  ERROR (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name nm =
  map_transition (fn (_, props, pos, source, int_only, print, no_timing, trans) =>
    (nm, props, pos, source, int_only, print, no_timing, trans));

fun properties props =
  map_transition (fn (name, _, pos, source, int_only, print, no_timing, trans) =>
    (name, props, pos, source, int_only, print, no_timing, trans));

fun position pos =
  map_transition (fn (name, props, _, source, int_only, print, no_timing, trans) =>
    (name, props, pos, source, int_only, print, no_timing, trans));

fun source src =
  map_transition (fn (name, props, pos, _, int_only, print, no_timing, trans) =>
    (name, props, pos, SOME src, int_only, print, no_timing, trans));

fun interactive int_only =
  map_transition (fn (name, props, pos, source, _, print, no_timing, trans) =>
    (name, props, pos, source, int_only, print, no_timing, trans));

val no_timing =
  map_transition (fn (name, props, pos, source, int_only, print, _, trans) =>
    (name, props, pos, source, int_only, print, true, trans));

fun add_trans tr =
  map_transition (fn (name, props, pos, source, int_only, print, no_timing, trans) =>
    (name, props, pos, source, int_only, print, no_timing, trans @ [tr]));

fun print' mode =
  map_transition (fn (name, props, pos, source, int_only, print, no_timing, trans) =>
    (name, props, pos, source, int_only, insert (op =) mode print, no_timing, trans));

val print = print' "";

val three_buffersN = "three_buffers";
val print3 = print' three_buffersN;


(* basic transitions *)

fun init_theory f exit kill = add_trans (Init (f, (exit, kill)));
fun init_empty check f = add_trans (InitEmpty (check, f));
val exit = add_trans Exit;
val undo_exit = add_trans UndoExit;
val kill = add_trans Kill;
val history = add_trans o History;
val keep' = add_trans o Keep;
fun map_current f = add_trans (Transaction (false, f));
fun app_current f = add_trans (Transaction (true, f));

fun keep f = add_trans (Keep (fn _ => f));
fun imperative f = keep (fn _ => f ());

val unknown_theory = imperative (fn () => warning "Unknown theory context");
val unknown_proof = imperative (fn () => warning "Unknown proof context");
val unknown_context = imperative (fn () => warning "Unknown context");


(* theory transitions *)

fun theory' f = app_current (fn int =>
  (fn Theory (Context.Theory thy, _) => Theory (Context.Theory (f int thy), NONE)
    | _ => raise UNDEF));

fun theory f = theory' (K f);

fun begin_local_theory begin f = app_current (fn _ =>
  (fn Theory (Context.Theory thy, _) =>
        let
          val lthy = f thy;
          val gthy = if begin then Context.Proof lthy else Context.Theory (loc_exit lthy);
        in Theory (gthy, SOME lthy) end
    | _ => raise UNDEF));

val end_local_theory = app_current (fn _ =>
  (fn Theory (Context.Proof lthy, _) => Theory (Context.Theory (loc_exit lthy), SOME lthy)
    | _ => raise UNDEF));

local

fun local_theory_presentation loc f g = app_current (fn int =>
  (fn Theory (gthy, _) =>
        let
          val pos = ContextPosition.get (Context.proof_of gthy);
          val finish = loc_finish loc gthy;
          val lthy' = f (ContextPosition.put_ctxt pos (loc_begin loc gthy));
        in Theory (finish lthy', SOME lthy') end
    | _ => raise UNDEF) #> tap (g int));

in

fun local_theory loc f = local_theory_presentation loc f (K I);
fun present_local_theory loc g = local_theory_presentation loc I g;

end;


(* proof transitions *)

fun end_proof f = map_current (fn int =>
  (fn Proof (prf, (finish, _)) =>
        let val state = ProofHistory.current prf in
          if can (Proof.assert_bottom true) state then
            let
              val ctxt' = f int state;
              val gthy' = finish ctxt';
            in Theory (gthy', SOME ctxt') end
          else raise UNDEF
        end
    | SkipProof (h, (gthy, _)) =>
        if History.current h = 0 then Theory (gthy, NONE) else raise UNDEF
    | _ => raise UNDEF));

local

fun begin_proof init finish = app_current (fn int =>
  (fn Theory (gthy, _) =>
    let
      val prf = init int gthy;
      val schematic = Proof.schematic_goal prf;
    in
      if ! skip_proofs andalso schematic then
        warning "Cannot skip proof of schematic goal statement"
      else ();
      if ! skip_proofs andalso not schematic then
        SkipProof
          (History.init (undo_limit int) 0, (finish gthy (Proof.global_skip_proof int prf), gthy))
      else Proof (ProofHistory.init (undo_limit int) prf, (finish gthy, gthy))
    end
  | _ => raise UNDEF));

in

fun local_theory_to_proof' loc f = begin_proof
  (fn int => fn gthy =>
    f int (ContextPosition.put_ctxt (ContextPosition.get (Context.proof_of gthy))
      (loc_begin loc gthy)))
  (loc_finish loc);

fun local_theory_to_proof loc f = local_theory_to_proof' loc (K f);

fun theory_to_proof f = begin_proof
  (K (fn Context.Theory thy => f thy | _ => raise UNDEF))
  (K (Context.Theory o ProofContext.theory_of));

end;

val forget_proof = map_current (fn _ =>
  (fn Proof (_, (_, orig_gthy)) => Theory (orig_gthy, NONE)
    | SkipProof (_, (_, orig_gthy)) => Theory (orig_gthy, NONE)
    | _ => raise UNDEF));

fun present_proof f = map_current (fn int =>
  (fn Proof (prf, x) => Proof (ProofHistory.apply I prf, x)
    | SkipProof (h, x) => SkipProof (History.apply I h, x)
    | _ => raise UNDEF) #> tap (f int));

fun proofs' f = map_current (fn int =>
  (fn Proof (prf, x) => Proof (ProofHistory.applys (f int) prf, x)
    | SkipProof (h, x) => SkipProof (History.apply I h, x)
    | _ => raise UNDEF));

fun proof' f = proofs' (Seq.single oo f);
val proofs = proofs' o K;
val proof = proof' o K;

fun actual_proof f = map_current (fn _ =>
  (fn Proof (prf, x) => Proof (f prf, x)
    | _ => raise UNDEF));

fun skip_proof f = map_current (fn _ =>
  (fn SkipProof (h, x) => SkipProof (f h, x)
    | _ => raise UNDEF));

fun skip_proof_to_theory p = map_current (fn _ =>
  (fn SkipProof (h, (gthy, _)) =>
    if p (History.current h) then Theory (gthy, NONE)
    else raise UNDEF
  | _ => raise UNDEF));



(** toplevel transactions **)

(* thread transition properties *)

fun setmp_thread_position (Transition {props, pos, ...}) f x =
  Position.setmp_thread_data pos f x;


(* apply transitions *)

local

fun app int (tr as Transition {trans, pos, int_only, print, no_timing, ...}) =
  setmp_thread_position tr (fn state =>
    let
      val _ =
        if not int andalso int_only then warning (command_msg "Interactive-only " tr)
        else ();

      fun do_timing f x = (warning (command_msg "" tr); timeap f x);
      fun do_profiling f x = profile (! profiling) f x;

      val (result, opt_exn) =
         state |> (apply_trans int pos trans
          |> (if ! profiling > 0 andalso not no_timing then do_profiling else I)
          |> (if ! profiling > 0 orelse ! timing andalso not no_timing then do_timing else I));
      val _ =
        if int andalso not (! quiet) andalso exists (member (op =) print) ("" :: print_mode_value ())
        then print_state false result else ();
    in (result, Option.map (fn UNDEF => type_error tr state | exn => exn) opt_exn) end);

in

fun apply int tr st =
  (case app int tr st of
    (_, SOME TERMINATE) => NONE
  | (_, SOME RESTART) => SOME (toplevel, NONE)
  | (state', SOME (EXCURSION_FAIL exn_info)) => SOME (state', SOME exn_info)
  | (state', SOME exn) => SOME (state', SOME (exn, at_command tr))
  | (state', NONE) => SOME (state', NONE));

end;


(* excursion: toplevel -- apply transformers/presentation -- toplevel *)

local

fun excur [] x = x
  | excur ((tr, pr) :: trs) (st, res) =
      (case apply (! interact) tr st of
        SOME (st', NONE) =>
          excur trs (st', pr st st' res handle exn =>
            raise EXCURSION_FAIL (exn, "Presentation failed\n" ^ at_command tr))
      | SOME (st', SOME exn_info) => raise EXCURSION_FAIL exn_info
      | NONE => raise EXCURSION_FAIL (TERMINATE, at_command tr));

fun no_pr _ _ _ = ();

in

fun present_excursion trs res =
  (case excur trs (toplevel, res) of
    (state as Toplevel _, res') => (safe_exit state; res')
  | _ => error "Unfinished development at end of input")
  handle exn => error (exn_message exn);

fun excursion trs = present_excursion (map (rpair no_pr) trs) ();

end;



(** interactive transformations **)

(* the global state reference *)

val global_state = ref (toplevel, NONE: (exn * string) option);

fun set_state state = global_state := (state, NONE);
fun get_state () = fst (! global_state);
fun exn () = snd (! global_state);


(* apply transformers to global state --- NOT THREAD-SAFE! *)

nonfix >> >>>;

fun >> tr =
  (case apply true tr (get_state ()) of
    NONE => false
  | SOME (state', exn_info) =>
      (global_state := (state', exn_info);
        (case exn_info of
          NONE => ()
        | SOME err => setmp_thread_position tr print_exn err);
        true));

fun >>> [] = ()
  | >>> (tr :: trs) = if >> tr then >>> trs else ();

fun init_state () = (>> (init_empty (K true) (K ()) empty); ());


(* the Isar source of transitions *)

type 'a isar =
  (transition, (transition option,
    (OuterLex.token, (OuterLex.token option, (OuterLex.token, (OuterLex.token,
      Position.T * (Symbol.symbol, (string, 'a) Source.source) Source.source)
          Source.source) Source.source) Source.source) Source.source) Source.source) Source.source;

local

(*Spurious interrupts ahead!  Race condition?*)
fun get_interrupt src = SOME (Source.get_single src) handle Interrupt => NONE;

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
  in
    (case get_interrupt (Source.set_prompt Source.default_prompt src) of
      NONE => (writeln "\nInterrupt."; raw_loop secure src)
    | SOME NONE => if secure then quit () else ()
    | SOME (SOME (tr, src')) => if >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn => (CRITICAL (fn () => change crashes (cons exn));
      warning "Recovering after Isar toplevel crash -- see also Toplevel.crashes";
      raw_loop secure src)
  end;

in

fun loop secure src = ignore_interrupt (raw_loop secure) src;

end;

end;
