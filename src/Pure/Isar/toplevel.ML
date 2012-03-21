(*  Title:      Pure/Isar/toplevel.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar toplevel transactions.
*)

signature TOPLEVEL =
sig
  exception UNDEF
  type state
  val toplevel: state
  val is_toplevel: state -> bool
  val is_theory: state -> bool
  val is_proof: state -> bool
  val level: state -> int
  val presentation_context_of: state -> Proof.context
  val previous_context_of: state -> Proof.context option
  val context_of: state -> Proof.context
  val generic_theory_of: state -> generic_theory
  val theory_of: state -> theory
  val proof_of: state -> Proof.state
  val proof_position_of: state -> int
  val end_theory: Position.T -> state -> theory
  val print_state_context: state -> unit
  val print_state: bool -> state -> unit
  val pretty_abstract: state -> Pretty.T
  val quiet: bool Unsynchronized.ref
  val debug: bool Unsynchronized.ref
  val interact: bool Unsynchronized.ref
  val timing: bool Unsynchronized.ref
  val profiling: int Unsynchronized.ref
  val skip_proofs: bool Unsynchronized.ref
  val program: (unit -> 'a) -> 'a
  val thread: bool -> (unit -> unit) -> Thread.thread
  type transition
  val empty: transition
  val print_of: transition -> bool
  val name_of: transition -> string
  val pos_of: transition -> Position.T
  val str_of: transition -> string
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val interactive: bool -> transition -> transition
  val set_print: bool -> transition -> transition
  val print: transition -> transition
  val no_timing: transition -> transition
  val init_theory: (unit -> theory) -> transition -> transition
  val is_init: transition -> bool
  val modify_init: (unit -> theory) -> transition -> transition
  val exit: transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val keep': (bool -> state -> unit) -> transition -> transition
  val imperative: (unit -> unit) -> transition -> transition
  val ignored: Position.T -> transition
  val malformed: Position.T -> string -> transition
  val theory: (theory -> theory) -> transition -> transition
  val generic_theory: (generic_theory -> generic_theory) -> transition -> transition
  val theory': (bool -> theory -> theory) -> transition -> transition
  val begin_local_theory: bool -> (theory -> local_theory) -> transition -> transition
  val end_local_theory: transition -> transition
  val open_target: (generic_theory -> local_theory) -> transition -> transition
  val close_target: transition -> transition
  val local_theory': (xstring * Position.T) option -> (bool -> local_theory -> local_theory) ->
    transition -> transition
  val local_theory: (xstring * Position.T) option -> (local_theory -> local_theory) ->
    transition -> transition
  val present_local_theory: (xstring * Position.T) option -> (state -> unit) ->
    transition -> transition
  val local_theory_to_proof': (xstring * Position.T) option ->
    (bool -> local_theory -> Proof.state) -> transition -> transition
  val local_theory_to_proof: (xstring * Position.T) option ->
    (local_theory -> Proof.state) -> transition -> transition
  val theory_to_proof: (theory -> Proof.state) -> transition -> transition
  val end_proof: (bool -> Proof.state -> Proof.context) -> transition -> transition
  val forget_proof: transition -> transition
  val present_proof: (state -> unit) -> transition -> transition
  val proofs': (bool -> Proof.state -> Proof.state Seq.seq) -> transition -> transition
  val proof': (bool -> Proof.state -> Proof.state) -> transition -> transition
  val proofs: (Proof.state -> Proof.state Seq.seq) -> transition -> transition
  val proof: (Proof.state -> Proof.state) -> transition -> transition
  val actual_proof: (Proof_Node.T -> Proof_Node.T) -> transition -> transition
  val skip_proof: (int -> int) -> transition -> transition
  val skip_proof_to_theory: (int -> bool) -> transition -> transition
  val get_id: transition -> string option
  val put_id: string -> transition -> transition
  val unknown_theory: transition -> transition
  val unknown_proof: transition -> transition
  val unknown_context: transition -> transition
  val setmp_thread_position: transition -> ('a -> 'b) -> 'a -> 'b
  val status: transition -> Markup.T -> unit
  val error_msg: transition -> serial * string -> unit
  val add_hook: (transition -> state -> state -> unit) -> unit
  val transition: bool -> transition -> state -> (state * (exn * string) option) option
  val command: transition -> state -> state
  val proof_result: bool -> transition * transition list -> state ->
    (transition * state) list future * state
end;

structure Toplevel: TOPLEVEL =
struct

(** toplevel state **)

exception UNDEF = Runtime.UNDEF;


(* local theory wrappers *)

val loc_init = Named_Target.context_cmd;
val loc_exit = Local_Theory.assert_bottom true #> Local_Theory.exit_global;

fun loc_begin loc (Context.Theory thy) = loc_init (the_default ("-", Position.none) loc) thy
  | loc_begin NONE (Context.Proof lthy) = lthy
  | loc_begin (SOME loc) (Context.Proof lthy) = (loc_init loc o loc_exit) lthy;

fun loc_finish _ (Context.Theory _) = Context.Theory o loc_exit
  | loc_finish NONE (Context.Proof _) = Context.Proof o Local_Theory.restore
  | loc_finish (SOME _) (Context.Proof lthy) = Context.Proof o Named_Target.reinit lthy;


(* datatype node *)

datatype node =
  Theory of generic_theory * Proof.context option
    (*theory with presentation context*) |
  Proof of Proof_Node.T * ((Proof.context -> generic_theory) * generic_theory)
    (*proof node, finish, original theory*) |
  SkipProof of int * (generic_theory * generic_theory);
    (*proof depth, resulting theory, original theory*)

val theory_node = fn Theory (gthy, _) => SOME gthy | _ => NONE;
val proof_node = fn Proof (prf, _) => SOME prf | _ => NONE;

fun cases_node f _ (Theory (gthy, _)) = f gthy
  | cases_node _ g (Proof (prf, _)) = g (Proof_Node.current prf)
  | cases_node f _ (SkipProof (_, (gthy, _))) = f gthy;

val context_node = cases_node Context.proof_of Proof.context_of;


(* datatype state *)

datatype state = State of node option * node option;  (*current, previous*)

val toplevel = State (NONE, NONE);

fun is_toplevel (State (NONE, _)) = true
  | is_toplevel _ = false;

fun level (State (NONE, _)) = 0
  | level (State (SOME (Theory _), _)) = 0
  | level (State (SOME (Proof (prf, _)), _)) = Proof.level (Proof_Node.current prf)
  | level (State (SOME (SkipProof (d, _)), _)) = d + 1;   (*different notion of proof depth!*)

fun str_of_state (State (NONE, _)) = "at top level"
  | str_of_state (State (SOME (Theory (Context.Theory _, _)), _)) = "in theory mode"
  | str_of_state (State (SOME (Theory (Context.Proof _, _)), _)) = "in local theory mode"
  | str_of_state (State (SOME (Proof _), _)) = "in proof mode"
  | str_of_state (State (SOME (SkipProof _), _)) = "in skipped proof mode";


(* current node *)

fun node_of (State (NONE, _)) = raise UNDEF
  | node_of (State (SOME node, _)) = node;

fun is_theory state = not (is_toplevel state) andalso is_some (theory_node (node_of state));
fun is_proof state = not (is_toplevel state) andalso is_some (proof_node (node_of state));

fun node_case f g state = cases_node f g (node_of state);

fun presentation_context_of state =
  (case try node_of state of
    SOME (Theory (_, SOME ctxt)) => ctxt
  | SOME node => context_node node
  | NONE => raise UNDEF);

fun previous_context_of (State (_, NONE)) = NONE
  | previous_context_of (State (_, SOME prev)) = SOME (context_node prev);

val context_of = node_case Context.proof_of Proof.context_of;
val generic_theory_of = node_case I (Context.Proof o Proof.context_of);
val theory_of = node_case Context.theory_of Proof.theory_of;
val proof_of = node_case (fn _ => raise UNDEF) I;

fun proof_position_of state =
  (case node_of state of
    Proof (prf, _) => Proof_Node.position prf
  | _ => raise UNDEF);

fun end_theory _ (State (NONE, SOME (Theory (Context.Theory thy, _)))) = thy
  | end_theory pos (State (NONE, _)) = error ("Missing theory" ^ Position.str_of pos)
  | end_theory pos (State (SOME _, _)) = error ("Unfinished theory" ^ Position.str_of pos);


(* print state *)

val pretty_context = Local_Theory.pretty o Context.cases (Named_Target.theory_init) I;

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
      Proof.pretty_state (Proof_Node.position prf) (Proof_Node.current prf)
  | SOME (SkipProof (d, _)) => [Pretty.str ("skipped proof: depth " ^ string_of_int d)])
  |> Pretty.markup_chunks Isabelle_Markup.state |> Pretty.writeln;

fun pretty_abstract state = Pretty.str ("<Isar " ^ str_of_state state ^ ">");



(** toplevel transitions **)

val quiet = Unsynchronized.ref false;
val debug = Runtime.debug;
val interact = Unsynchronized.ref false;
val timing = Unsynchronized.ref false;
val profiling = Unsynchronized.ref 0;
val skip_proofs = Unsynchronized.ref false;

fun program body =
 (body
  |> Runtime.controlled_execution
  |> Runtime.toplevel_error (Output.error_msg o ML_Compiler.exn_message)) ();

fun thread interrupts body =
  Thread.fork
    (((fn () => body () handle exn => if Exn.is_interrupt exn then () else reraise exn)
        |> Runtime.debugging
        |> Runtime.toplevel_error
          (fn exn =>
            Output.urgent_message ("## INTERNAL ERROR ##\n" ^ ML_Compiler.exn_message exn))),
      Simple_Thread.attributes interrupts);


(* node transactions -- maintaining stable checkpoints *)

exception FAILURE of state * exn;

local

fun reset_presentation (Theory (gthy, _)) = Theory (gthy, NONE)
  | reset_presentation node = node;

fun is_draft_theory (Theory (gthy, _)) = Context.is_draft (Context.theory_of gthy)
  | is_draft_theory _ = false;

fun is_stale state = Context.is_stale (theory_of state) handle Runtime.UNDEF => false;

fun stale_error NONE = SOME (ERROR "Stale theory encountered after successful execution!")
  | stale_error some = some;

fun map_theory f (Theory (gthy, ctxt)) =
      Theory (Context.mapping f (Local_Theory.raw_theory f) gthy, ctxt)
  | map_theory _ node = node;

in

fun apply_transaction f g node =
  let
    val _ = is_draft_theory node andalso error "Illegal draft theory in toplevel state";
    val cont_node = reset_presentation node;
    val back_node = map_theory (Theory.checkpoint o Theory.copy) cont_node;
    fun state_error e nd = (State (SOME nd, SOME node), e);

    val (result, err) =
      cont_node
      |> Runtime.controlled_execution f
      |> map_theory Theory.checkpoint
      |> state_error NONE
      handle exn => state_error (SOME exn) cont_node;

    val (result', err') =
      if is_stale result then state_error (stale_error err) back_node
      else (result, err);
  in
    (case err' of
      NONE => tap g result'
    | SOME exn => raise FAILURE (result', exn))
  end;

val exit_transaction =
  apply_transaction
    (fn Theory (Context.Theory thy, _) => Theory (Context.Theory (Theory.end_theory thy), NONE)
      | node => node) (K ())
  #> (fn State (node', _) => State (NONE, node'));

end;


(* primitive transitions *)

datatype trans =
  Init of unit -> theory |               (*init theory*)
  Exit |                                 (*formal exit of theory*)
  Keep of bool -> state -> unit |        (*peek at state*)
  Transaction of (bool -> node -> node) * (state -> unit);  (*node transaction and presentation*)

local

fun apply_tr _ (Init f) (State (NONE, _)) =
      State (SOME (Theory (Context.Theory
          (Theory.checkpoint (Runtime.controlled_execution f ())), NONE)), NONE)
  | apply_tr _ Exit (State (SOME (state as Theory (Context.Theory _, _)), _)) =
      exit_transaction state
  | apply_tr int (Keep f) state =
      Runtime.controlled_execution (fn x => tap (f int) x) state
  | apply_tr int (Transaction (f, g)) (State (SOME state, _)) =
      apply_transaction (fn x => f int x) g state
  | apply_tr _ _ _ = raise UNDEF;

fun apply_union _ [] state = raise FAILURE (state, UNDEF)
  | apply_union int (tr :: trs) state =
      apply_union int trs state
        handle Runtime.UNDEF => apply_tr int tr state
          | FAILURE (alt_state, UNDEF) => apply_tr int tr alt_state
          | exn as FAILURE _ => raise exn
          | exn => raise FAILURE (state, exn);

in

fun apply_trans int trs state = (apply_union int trs state, NONE)
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

fun print_of (Transition {print, ...}) = print;
fun name_of (Transition {name, ...}) = name;
fun pos_of (Transition {pos, ...}) = pos;
fun str_of tr = quote (name_of tr) ^ Position.str_of (pos_of tr);

fun command_msg msg tr = msg ^ "command " ^ str_of tr;
fun at_command tr = command_msg "At " tr;

fun type_error tr state =
  ERROR (command_msg "Illegal application of " tr ^ " " ^ str_of_state state);


(* modify transitions *)

fun name name = map_transition (fn (_, pos, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

fun position pos = map_transition (fn (name, _, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

fun interactive int_only = map_transition (fn (name, pos, _, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

val no_timing = map_transition (fn (name, pos, int_only, print, _, trans) =>
  (name, pos, int_only, print, true, trans));

fun add_trans tr = map_transition (fn (name, pos, int_only, print, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, tr :: trans));

val reset_trans = map_transition (fn (name, pos, int_only, print, no_timing, _) =>
  (name, pos, int_only, print, no_timing, []));

fun set_print print = map_transition (fn (name, pos, int_only, _, no_timing, trans) =>
  (name, pos, int_only, print, no_timing, trans));

val print = set_print true;


(* basic transitions *)

fun init_theory f = add_trans (Init f);

fun is_init (Transition {trans = [Init _], ...}) = true
  | is_init _ = false;

fun modify_init f tr = if is_init tr then init_theory f (reset_trans tr) else tr;

val exit = add_trans Exit;
val keep' = add_trans o Keep;

fun present_transaction f g = add_trans (Transaction (f, g));
fun transaction f = present_transaction f (K ());

fun keep f = add_trans (Keep (fn _ => f));
fun imperative f = keep (fn _ => f ());

fun ignored pos = empty |> name "<ignored>" |> position pos |> imperative I;
fun malformed pos msg =
  empty |> name "<malformed>" |> position pos |> imperative (fn () => error msg);

val unknown_theory = imperative (fn () => warning "Unknown theory context");
val unknown_proof = imperative (fn () => warning "Unknown proof context");
val unknown_context = imperative (fn () => warning "Unknown context");


(* theory transitions *)

val global_theory_group =
  Sign.new_group #>
  Global_Theory.begin_recent_proofs #> Theory.checkpoint;

val local_theory_group =
  Local_Theory.new_group #>
  Local_Theory.raw_theory (Global_Theory.begin_recent_proofs #> Theory.checkpoint);

fun generic_theory f = transaction (fn _ =>
  (fn Theory (gthy, _) => Theory (f gthy, NONE)
    | _ => raise UNDEF));

fun theory' f = transaction (fn int =>
  (fn Theory (Context.Theory thy, _) =>
      let val thy' = thy
        |> global_theory_group
        |> f int
        |> Sign.reset_group;
      in Theory (Context.Theory thy', NONE) end
    | _ => raise UNDEF));

fun theory f = theory' (K f);

fun begin_local_theory begin f = transaction (fn _ =>
  (fn Theory (Context.Theory thy, _) =>
        let
          val lthy = f thy;
          val gthy = if begin then Context.Proof lthy else Context.Theory (loc_exit lthy);
        in Theory (gthy, SOME lthy) end
    | _ => raise UNDEF));

val end_local_theory = transaction (fn _ =>
  (fn Theory (Context.Proof lthy, _) => Theory (Context.Theory (loc_exit lthy), SOME lthy)
    | _ => raise UNDEF));

fun open_target f = transaction (fn _ =>
  (fn Theory (gthy, _) =>
        let val lthy = f gthy
        in Theory (Context.Proof lthy, SOME lthy) end
    | _ => raise UNDEF));

val close_target = transaction (fn _ =>
  (fn Theory (Context.Proof lthy, _) =>
        (case try Local_Theory.close_target lthy of
          SOME lthy' => Theory (Context.Proof lthy', SOME lthy)
        | NONE => raise UNDEF)
    | _ => raise UNDEF));


local

fun local_theory_presentation loc f = present_transaction (fn int =>
  (fn Theory (gthy, _) =>
        let
          val finish = loc_finish loc gthy;
          val lthy' = loc_begin loc gthy
            |> local_theory_group
            |> f int
            |> Local_Theory.reset_group;
        in Theory (finish lthy', SOME lthy') end
    | _ => raise UNDEF));

in

fun local_theory' loc f = local_theory_presentation loc f (K ());
fun local_theory loc f = local_theory' loc (K f);
fun present_local_theory loc = local_theory_presentation loc (K I);

end;


(* proof transitions *)

fun end_proof f = transaction (fn int =>
  (fn Proof (prf, (finish, _)) =>
        let val state = Proof_Node.current prf in
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

fun begin_proof init finish = transaction (fn int =>
  (fn Theory (gthy, _) =>
    let
      val prf = init int gthy;
      val skip = ! skip_proofs;
      val (is_goal, no_skip) =
        (true, Proof.schematic_goal prf) handle ERROR _ => (false, true);
    in
      if is_goal andalso skip andalso no_skip then
        warning "Cannot skip proof of schematic goal statement"
      else ();
      if skip andalso not no_skip then
        SkipProof (0, (finish gthy (Proof.global_skip_proof int prf), gthy))
      else Proof (Proof_Node.init prf, (finish gthy, gthy))
    end
  | _ => raise UNDEF));

in

fun local_theory_to_proof' loc f = begin_proof
  (fn int => fn gthy => f int (local_theory_group (loc_begin loc gthy)))
  (fn gthy => loc_finish loc gthy o Local_Theory.reset_group);

fun local_theory_to_proof loc f = local_theory_to_proof' loc (K f);

fun theory_to_proof f = begin_proof
  (K (fn Context.Theory thy => f (global_theory_group thy) | _ => raise UNDEF))
  (K (Context.Theory o Sign.reset_group o Proof_Context.theory_of));

end;

val forget_proof = transaction (fn _ =>
  (fn Proof (_, (_, orig_gthy)) => Theory (orig_gthy, NONE)
    | SkipProof (_, (_, orig_gthy)) => Theory (orig_gthy, NONE)
    | _ => raise UNDEF));

val present_proof = present_transaction (fn _ =>
  (fn Proof (prf, x) => Proof (Proof_Node.apply I prf, x)
    | skip as SkipProof _ => skip
    | _ => raise UNDEF));

fun proofs' f = transaction (fn int =>
  (fn Proof (prf, x) => Proof (Proof_Node.applys (f int) prf, x)
    | skip as SkipProof _ => skip
    | _ => raise UNDEF));

fun proof' f = proofs' (Seq.single oo f);
val proofs = proofs' o K;
val proof = proof' o K;

fun actual_proof f = transaction (fn _ =>
  (fn Proof (prf, x) => Proof (f prf, x)
    | _ => raise UNDEF));

fun skip_proof f = transaction (fn _ =>
  (fn SkipProof (h, x) => SkipProof (f h, x)
    | _ => raise UNDEF));

fun skip_proof_to_theory pred = transaction (fn _ =>
  (fn SkipProof (d, (gthy, _)) => if pred d then Theory (gthy, NONE) else raise UNDEF
    | _ => raise UNDEF));



(** toplevel transactions **)

(* identification *)

fun get_id (Transition {pos, ...}) = Position.get_id pos;
fun put_id id (tr as Transition {pos, ...}) = position (Position.put_id id pos) tr;


(* thread position *)

fun setmp_thread_position (Transition {pos, ...}) f x =
  Position.setmp_thread_data pos f x;

fun status tr m =
  setmp_thread_position tr (fn () => Output.status (Markup.markup_only m)) ();

fun error_msg tr msg =
  setmp_thread_position tr (fn () => Output.error_msg' msg) ();


(* post-transition hooks *)

local
  val hooks = Unsynchronized.ref ([]: (transition -> state -> state -> unit) list);
in

fun add_hook f = CRITICAL (fn () => Unsynchronized.change hooks (cons f));
fun get_hooks () = ! hooks;

end;


(* apply transitions *)

local

fun app int (tr as Transition {trans, print, no_timing, ...}) =
  setmp_thread_position tr (fn state =>
    let
      fun do_timing f x = (warning (command_msg "" tr); timeap f x);
      fun do_profiling f x = profile (! profiling) f x;

      val (result, status) =
         state |>
          (apply_trans int trans
            |> (! profiling > 0 andalso not no_timing) ? do_profiling
            |> (! profiling > 0 orelse ! timing andalso not no_timing) ? do_timing);

      val _ = if int andalso not (! quiet) andalso print then print_state false result else ();
    in (result, Option.map (fn UNDEF => type_error tr state | exn => exn) status) end);

in

fun transition int tr st =
  let
    val hooks = get_hooks ();
    fun apply_hooks st' = hooks |> List.app (fn f => (try (fn () => f tr st st') (); ()));

    val ctxt = try context_of st;
    val res =
      (case app int tr st of
        (_, SOME Runtime.TERMINATE) => NONE
      | (st', SOME (Runtime.EXCURSION_FAIL exn_info)) => SOME (st', SOME exn_info)
      | (st', SOME exn) => SOME (st', SOME (Runtime.exn_context ctxt exn, at_command tr))
      | (st', NONE) => SOME (st', NONE));
    val _ = (case res of SOME (st', NONE) => apply_hooks st' | _ => ());
  in res end;

end;


(* nested commands *)

fun command tr st =
  (case transition (! interact) tr st of
    SOME (st', NONE) => st'
  | SOME (_, SOME (exn, info)) =>
      if Exn.is_interrupt exn then reraise exn else raise Runtime.EXCURSION_FAIL (exn, info)
  | NONE => raise Runtime.EXCURSION_FAIL (Runtime.TERMINATE, at_command tr));

fun command_result tr st =
  let val st' = command tr st
  in (st', st') end;


(* scheduled proof result *)

structure States = Proof_Data
(
  type T = state list future option;
  fun init _ = NONE;
);

fun proof_result immediate (tr, proof_trs) st =
  let val st' = command tr st in
    if immediate orelse
      null proof_trs orelse
      Keyword.is_schematic_goal (name_of tr) orelse
      exists (Keyword.is_qed_global o name_of) proof_trs orelse
      not (can proof_of st') orelse
      Proof.is_relevant (proof_of st')
    then
      let val (states, st'') = fold_map command_result proof_trs st'
      in (Future.value ((tr, st') :: (proof_trs ~~ states)), st'') end
    else
      let
        val (body_trs, end_tr) = split_last proof_trs;
        val finish = Context.Theory o Proof_Context.theory_of;

        val future_proof = Proof.global_future_proof
          (fn prf =>
            Goal.fork_name "Toplevel.future_proof"
              (fn () =>
                let val (states, result_state) =
                  (case st' of State (SOME (Proof (_, (_, orig_gthy))), prev)
                    => State (SOME (Proof (Proof_Node.init prf, (finish, orig_gthy))), prev))
                  |> fold_map command_result body_trs
                  ||> command (end_tr |> set_print false);
                in (states, presentation_context_of result_state) end))
          #> (fn (states, ctxt) => States.put (SOME states) ctxt);

        val st'' = st' |> command (end_tr |> reset_trans |> end_proof (K future_proof));

        val states =
          (case States.get (presentation_context_of st'') of
            NONE => raise Fail ("No future states for " ^ name_of tr ^ Position.str_of (pos_of tr))
          | SOME states => states);
        val result = states
          |> Future.map (fn sts => (tr, st') :: (body_trs ~~ sts) @ [(end_tr, st'')]);

      in (result, st'') end
  end;

end;
