(*  Title:      Pure/Isar/toplevel.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar toplevel transactions.
*)

signature TOPLEVEL =
sig
  exception UNDEF
  type generic_theory
  type node
  val theory_node: node -> generic_theory option
  val proof_node: node -> ProofNode.T option
  val cases_node: (generic_theory -> 'a) -> (Proof.state -> 'a) -> node -> 'a
  val presentation_context: node option -> xstring option -> Proof.context
  type state
  val toplevel: state
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
  exception TERMINATE
  exception RESTART
  exception CONTEXT of Proof.context * exn
  exception TOPLEVEL_ERROR
  val exn_message: exn -> string
  val program: (unit -> 'a) -> 'a
  type transition
  val undo_limit: bool -> int option
  val empty: transition
  val init_of: transition -> string option
  val name_of: transition -> string
  val str_of: transition -> string
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val interactive: bool -> transition -> transition
  val print: transition -> transition
  val no_timing: transition -> transition
  val init_theory: string -> (bool -> theory) -> (theory -> unit) -> (theory -> unit) ->
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
  val generic_theory: (generic_theory -> generic_theory) -> transition -> transition
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
  val actual_proof: (ProofNode.T -> ProofNode.T) -> transition -> transition
  val skip_proof: (int -> int) -> transition -> transition
  val skip_proof_to_theory: (int -> bool) -> transition -> transition
  val get_id: transition -> string option
  val put_id: string -> transition -> transition
  val unknown_theory: transition -> transition
  val unknown_proof: transition -> transition
  val unknown_context: transition -> transition
  val error_msg: transition -> exn * string -> unit
  val transition: bool -> transition -> state -> (state * (exn * string) option) option
  val present_excursion: (transition * (state -> state -> 'a -> 'a)) list -> 'a -> 'a
  val excursion: transition list -> unit
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
  Proof of ProofNode.T * ((Proof.context -> generic_theory) * generic_theory) |
    (*proof node, finish, original theory*)
  SkipProof of int * (generic_theory * generic_theory);
    (*proof depth, resulting theory, original theory*)

val the_global_theory = fn Theory (Context.Theory thy, _) => thy | _ => raise UNDEF;
val theory_node = fn Theory (gthy, _) => SOME gthy | _ => NONE;
val proof_node = fn Proof (prf, _) => SOME prf | _ => NONE;

fun cases_node f _ (Theory (gthy, _)) = f gthy
  | cases_node _ g (Proof (prf, _)) = g (ProofNode.current prf)
  | cases_node f _ (SkipProof (_, (gthy, _))) = f gthy;

fun presentation_context (SOME (Theory (_, SOME ctxt))) NONE = ctxt
  | presentation_context (SOME node) NONE = cases_node Context.proof_of Proof.context_of node
  | presentation_context (SOME node) (SOME loc) =
      loc_init loc (cases_node Context.theory_of Proof.theory_of node)
  | presentation_context NONE _ = raise UNDEF;

fun reset_presentation (Theory (gthy, _)) = Theory (gthy, NONE)
  | reset_presentation node = node;


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
      | Proof (prf, _) => Proof.level (ProofNode.current prf)
      | SkipProof (d, _) => d + 1);   (*different notion of proof depth!*)

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
    Proof (prf, _) => ProofNode.position prf
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
      Proof.pretty_state (ProofNode.position prf) (ProofNode.current prf)
  | SOME (SkipProof (d, _)) => [Pretty.str ("skipped proof: depth " ^ string_of_int d)])
  |> Pretty.markup_chunks Markup.state |> Pretty.writeln;



(** toplevel transitions **)

val quiet = ref false;
val debug = Output.debugging;
val interact = ref false;
val timing = Output.timing;
val profiling = ref 0;
val skip_proofs = ref false;

exception TERMINATE;
exception RESTART;
exception EXCURSION_FAIL of exn * string;
exception FAILURE of state * exn;
exception TOPLEVEL_ERROR;


(* print exceptions *)

exception CONTEXT of Proof.context * exn;

fun exn_context NONE exn = exn
  | exn_context (SOME ctxt) exn = CONTEXT (ctxt, exn);

local

fun if_context NONE _ _ = []
  | if_context (SOME ctxt) f xs = map (f ctxt) xs;

fun raised name [] = "exception " ^ name ^ " raised"
  | raised name [msg] = "exception " ^ name ^ " raised: " ^ msg
  | raised name msgs = cat_lines (("exception " ^ name ^ " raised:") :: msgs);

in

fun exn_message e =
  let
    val detailed = ! debug;

    fun exn_msg _ (CONTEXT (ctxt, exn)) = exn_msg (SOME ctxt) exn
      | exn_msg ctxt (Exn.EXCEPTIONS (exns, "")) = cat_lines (map (exn_msg ctxt) exns)
      | exn_msg ctxt (Exn.EXCEPTIONS (exns, msg)) = cat_lines (map (exn_msg ctxt) exns @ [msg])
      | exn_msg ctxt (EXCURSION_FAIL (exn, loc)) =
          exn_msg ctxt exn ^ Markup.markup Markup.location ("\n" ^ loc)
      | exn_msg _ TERMINATE = "Exit."
      | exn_msg _ RESTART = "Restart."
      | exn_msg _ Interrupt = "Interrupt."
      | exn_msg _ TimeLimit.TimeOut = "Timeout."
      | exn_msg _ TOPLEVEL_ERROR = "Error."
      | exn_msg _ (SYS_ERROR msg) = "## SYSTEM ERROR ##\n" ^ msg
      | exn_msg _ (ERROR msg) = msg
      | exn_msg _ (Fail msg) = raised "Fail" [msg]
      | exn_msg _ (THEORY (msg, thys)) =
          raised "THEORY" (msg :: (if detailed then map Context.str_of_thy thys else []))
      | exn_msg _ (Syntax.AST (msg, asts)) = raised "AST" (msg ::
            (if detailed then map (Pretty.string_of o Syntax.pretty_ast) asts else []))
      | exn_msg ctxt (TYPE (msg, Ts, ts)) = raised "TYPE" (msg ::
            (if detailed then
              if_context ctxt Syntax.string_of_typ Ts @ if_context ctxt Syntax.string_of_term ts
             else []))
      | exn_msg ctxt (TERM (msg, ts)) = raised "TERM" (msg ::
            (if detailed then if_context ctxt Syntax.string_of_term ts else []))
      | exn_msg ctxt (THM (msg, i, thms)) = raised ("THM " ^ string_of_int i) (msg ::
            (if detailed then if_context ctxt ProofContext.string_of_thm thms else []))
      | exn_msg _ exn = raised (General.exnMessage exn) []
  in exn_msg NONE e end;

end;


(* controlled execution *)

local

fun debugging f x =
  if ! debug then exception_trace (fn () => f x)
  else f x;

fun toplevel_error f x =
  let val ctxt = try ML_Context.the_local_context () in
    f x handle exn =>
      (Output.error_msg (exn_message (exn_context ctxt exn)); raise TOPLEVEL_ERROR)
  end;

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

fun is_draft_theory (Theory (gthy, _)) = Context.is_draft (Context.theory_of gthy)
  | is_draft_theory _ = false;

fun stale_error NONE = SOME (ERROR "Stale theory encountered after successful execution!")
  | stale_error some = some;

fun map_theory f = History.map_current
  (fn Theory (gthy, ctxt) => Theory (Context.mapping f (LocalTheory.raw_theory f) gthy, ctxt)
    | node => node);

in

fun transaction hist pos f (node, term) =
  let
    val _ = is_draft_theory (History.current node) andalso
      error "Illegal draft theory in toplevel state";
    val cont_node = node |> History.map_current reset_presentation;
    val back_node = cont_node |> map_theory Theory.copy |> map_theory Theory.checkpoint;
    fun state_error e nd = (State (nd, term), e);

    val (result, err) =
      cont_node
      |> (f
          |> (if hist then History.apply' (History.current back_node) else History.map_current)
          |> controlled_execution)
      |> map_theory Theory.checkpoint
      |> state_error NONE
      handle exn => state_error (SOME exn) cont_node;

    val (result', err') =
      if is_stale result then state_error (stale_error err) back_node
      else (result, err);
  in
    (case err' of
      NONE => result'
    | SOME exn => raise FAILURE (result', exn))
  end;

end;


(* primitive transitions *)

(*Note: Recovery from stale theories is provided only for theory-level
  operations via Transaction.  Other node or state operations should
  not touch theories at all.  Interrupts are enabled only for Keep and
  Transaction.*)

datatype trans =
  Init of string * (bool -> theory) * ((theory -> unit) * (theory -> unit)) |
                                                    (*name; init node; with exit/kill operation*)
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

fun apply_tr int _ (Init (_, f, term)) (state as Toplevel _) =
      let val node = Theory (Context.Theory (Theory.checkpoint (f int)), NONE)
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
 {name: string,              (*command name*)
  pos: Position.T,           (*source position*)
  int_only: bool,            (*interactive-only*)
  print: bool,               (*print result state*)
  no_timing: bool,           (*suppress timing*)
  trans: trans list};        (*primitive transitions (union)*)

fun make_transition (name, pos, int_only, print, no_timing, trans) =
  Transition {name = name, pos = pos, int_only = int_only, print = print, no_timing = no_timing,
    trans = trans};

fun map_transition f (Transition {name, pos, int_only, print, no_timing, trans}) =
  make_transition (f (name, pos, int_only, print, no_timing, trans));

val empty = make_transition ("", Position.none, false, false, false, []);


(* diagnostics *)

fun init_of (Transition {trans = [Init (name, _, _)], ...}) = SOME name
  | init_of _ = NONE;

fun name_of (Transition {name, ...}) = name;
fun str_of (Transition {name, pos, ...}) = quote name ^ Position.str_of pos;

fun command_msg msg tr = msg ^ "command " ^ str_of tr;
fun at_command tr = command_msg "At " tr ^ ".";

fun type_error tr state =
  ERROR (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name nm = map_transition (fn (_, pos, int_only, print, no_timing, trans) =>
  (nm, pos, int_only, print, no_timing, trans));

fun position pos = map_transition (fn (name, _, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

fun interactive int_only = map_transition (fn (name, pos, _, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

val no_timing = map_transition (fn (name, pos, int_only, print, _, trans) =>
  (name, pos, int_only, print, true, trans));

fun add_trans tr = map_transition (fn (name, pos, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans @ [tr]));

val print = map_transition (fn (name, pos, int_only, _, no_timing, trans) =>
  (name, pos, int_only, true, no_timing, trans));


(* basic transitions *)

fun init_theory name f exit kill = add_trans (Init (name, f, (exit, kill)));
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

fun generic_theory f = app_current (fn _ =>
  (fn Theory (gthy, _) => Theory (f gthy, NONE)
    | _ => raise UNDEF));

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
          val finish = loc_finish loc gthy;
          val lthy' = f (loc_begin loc gthy);
        in Theory (finish lthy', SOME lthy') end
    | _ => raise UNDEF) #> tap (g int));

in

fun local_theory loc f = local_theory_presentation loc f (K I);
fun present_local_theory loc g = local_theory_presentation loc I g;

end;


(* proof transitions *)

fun end_proof f = map_current (fn int =>
  (fn Proof (prf, (finish, _)) =>
        let val state = ProofNode.current prf in
          if can (Proof.assert_bottom true) state then
            let
              val ctxt' = f int state;
              val gthy' = finish ctxt';
            in Theory (gthy', SOME ctxt') end
          else raise UNDEF
        end
    | SkipProof (0, (gthy, _)) => Theory (gthy, NONE)
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
        SkipProof (0, (finish gthy (Proof.global_skip_proof int prf), gthy))
      else Proof (ProofNode.init prf, (finish gthy, gthy))
    end
  | _ => raise UNDEF));

in

fun local_theory_to_proof' loc f = begin_proof
  (fn int => fn gthy => f int (loc_begin loc gthy))
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
  (fn Proof (prf, x) => Proof (ProofNode.apply I prf, x)
    | skip as SkipProof _ => skip
    | _ => raise UNDEF) #> tap (f int));

fun proofs' f = map_current (fn int =>
  (fn Proof (prf, x) => Proof (ProofNode.applys (f int) prf, x)
    | skip as SkipProof _ => skip
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

fun skip_proof_to_theory pred = map_current (fn _ =>
  (fn SkipProof (d, (gthy, _)) => if pred d then Theory (gthy, NONE) else raise UNDEF
  | _ => raise UNDEF));



(** toplevel transactions **)

(* identification *)

fun get_id (Transition {pos, ...}) = Position.get_id pos;
fun put_id id (tr as Transition {pos, ...}) = position (Position.put_id id pos) tr;


(* thread position *)

fun setmp_thread_position (Transition {pos, ...}) f x =
  Position.setmp_thread_data pos f x;

fun error_msg tr exn_info =
  setmp_thread_position tr (fn () => Output.error_msg (exn_message (EXCURSION_FAIL exn_info))) ();


(* apply transitions *)

local

fun app int (tr as Transition {trans, pos, int_only, print, no_timing, ...}) =
  setmp_thread_position tr (fn state =>
    let
      val _ = if not int andalso int_only then warning (command_msg "Interactive-only " tr) else ();

      fun do_timing f x = (warning (command_msg "" tr); timeap f x);
      fun do_profiling f x = profile (! profiling) f x;

      val (result, status) =
         state |> (apply_trans int pos trans
          |> (if ! profiling > 0 andalso not no_timing then do_profiling else I)
          |> (if ! profiling > 0 orelse ! timing andalso not no_timing then do_timing else I));

      val _ = if int andalso not (! quiet) andalso print then print_state false result else ();
    in (result, Option.map (fn UNDEF => type_error tr state | exn => exn) status) end);

in

fun transition int tr st =
  let val ctxt = try context_of st in
    (case app int tr st of
      (_, SOME TERMINATE) => NONE
    | (_, SOME RESTART) => SOME (toplevel, NONE)
    | (state', SOME (EXCURSION_FAIL exn_info)) => SOME (state', SOME exn_info)
    | (state', SOME exn) => SOME (state', SOME (exn_context ctxt exn, at_command tr))
    | (state', NONE) => SOME (state', NONE))
  end;

end;


(* excursion: toplevel -- apply transformers/presentation -- toplevel *)

local

fun excur [] x = x
  | excur ((tr, pr) :: trs) (st, res) =
      (case transition (! interact) tr st of
        SOME (st', NONE) =>
          excur trs (st', setmp_thread_position tr (fn () => pr st st' res) () handle exn =>
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

end;
