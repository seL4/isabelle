(*  Title:      Pure/Isar/toplevel.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar toplevel transactions.
*)

signature TOPLEVEL =
sig
  exception UNDEF
  type state
  val init_toplevel: unit -> state
  val theory_toplevel: theory -> state
  val is_toplevel: state -> bool
  val is_theory: state -> bool
  val is_proof: state -> bool
  val is_skipped_proof: state -> bool
  val level: state -> int
  val previous_theory_of: state -> theory option
  val context_of: state -> Proof.context
  val generic_theory_of: state -> generic_theory
  val theory_of: state -> theory
  val proof_of: state -> Proof.state
  val proof_position_of: state -> int
  val is_end_theory: state -> bool
  val end_theory: Position.T -> state -> theory
  val presentation_context: state -> Proof.context
  val presentation_state: Proof.context -> state
  val pretty_context: state -> Pretty.T list
  val pretty_state: state -> Pretty.T list
  val string_of_state: state -> string
  val pretty_abstract: state -> Pretty.T
  type transition
  val empty: transition
  val name_of: transition -> string
  val pos_of: transition -> Position.T
  val timing_of: transition -> Time.time
  val type_error: transition -> string
  val name: string -> transition -> transition
  val position: Position.T -> transition -> transition
  val markers: Input.source list -> transition -> transition
  val timing: Time.time -> transition -> transition
  val init_theory: (unit -> theory) -> transition -> transition
  val is_init: transition -> bool
  val modify_init: (unit -> theory) -> transition -> transition
  val exit: transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val keep': (bool -> state -> unit) -> transition -> transition
  val keep_proof: (state -> unit) -> transition -> transition
  val ignored: Position.T -> transition
  val is_ignored: transition -> bool
  val malformed: Position.T -> string -> transition
  val generic_theory: (generic_theory -> generic_theory) -> transition -> transition
  val theory': (bool -> theory -> theory) -> transition -> transition
  val theory: (theory -> theory) -> transition -> transition
  val begin_main_target: bool -> (theory -> local_theory) -> transition -> transition
  val end_main_target: transition -> transition
  val begin_nested_target: (local_theory -> local_theory) -> transition -> transition
  val end_nested_target: transition -> transition
  val local_theory': (bool * Position.T) option -> (xstring * Position.T) option ->
    (bool -> local_theory -> local_theory) -> transition -> transition
  val local_theory: (bool * Position.T) option -> (xstring * Position.T) option ->
    (local_theory -> local_theory) -> transition -> transition
  val present_local_theory: (xstring * Position.T) option -> (state -> unit) ->
    transition -> transition
  val local_theory_to_proof': (bool * Position.T) option -> (xstring * Position.T) option ->
    (bool -> local_theory -> Proof.state) -> transition -> transition
  val local_theory_to_proof: (bool * Position.T) option -> (xstring * Position.T) option ->
    (local_theory -> Proof.state) -> transition -> transition
  val theory_to_proof: (theory -> Proof.state) -> transition -> transition
  val end_proof: (bool -> Proof.state -> Proof.context) -> transition -> transition
  val forget_proof: transition -> transition
  val proofs': (bool -> Proof.state -> Proof.state Seq.result Seq.seq) -> transition -> transition
  val proof': (bool -> Proof.state -> Proof.state) -> transition -> transition
  val proofs: (Proof.state -> Proof.state Seq.result Seq.seq) -> transition -> transition
  val proof: (Proof.state -> Proof.state) -> transition -> transition
  val actual_proof: (Proof_Node.T -> Proof_Node.T) -> transition -> transition
  val skip_proof: (unit -> unit) -> transition -> transition
  val skip_proof_open: transition -> transition
  val skip_proof_close: transition -> transition
  val exec_id: Document_ID.exec -> transition -> transition
  val setmp_thread_position: transition -> ('a -> 'b) -> 'a -> 'b
  val add_hook: (transition -> state -> state -> unit) -> unit
  val transition: bool -> transition -> state -> state * (exn * string) option
  val command_errors: bool -> transition -> state -> Runtime.error list * state option
  val command_exception: bool -> transition -> state -> state
  val reset_theory: state -> state option
  val reset_proof: state -> state option
  val reset_notepad: state -> state option
  val fork_presentation: transition -> transition * transition
  type result
  val join_results: result -> (transition * state) list
  val element_result: Keyword.keywords -> transition Thy_Element.element -> state -> result * state
end;

structure Toplevel: TOPLEVEL =
struct

(** toplevel state **)

exception UNDEF = Runtime.UNDEF;


(* datatype node *)

datatype node =
  Toplevel
    (*toplevel outside of theory body*) |
  Theory of generic_theory
    (*global or local theory*) |
  Proof of Proof_Node.T * ((Proof.context -> generic_theory) * generic_theory)
    (*proof node, finish, original theory*) |
  Skipped_Proof of int * (generic_theory * generic_theory);
    (*proof depth, resulting theory, original theory*)

val theory_node = fn Theory gthy => SOME gthy | _ => NONE;
val proof_node = fn Proof (prf, _) => SOME prf | _ => NONE;
val skipped_proof_node = fn Skipped_Proof _ => true | _ => false;

fun cases_node f _ _ Toplevel = f ()
  | cases_node _ g _ (Theory gthy) = g gthy
  | cases_node _ _ h (Proof (prf, _)) = h (Proof_Node.current prf)
  | cases_node _ g _ (Skipped_Proof (_, (gthy, _))) = g gthy;

fun cases_proper_node g h = cases_node (fn () => raise UNDEF) g h;

val get_theory = cases_node (K NONE) (SOME o Context.theory_of) (SOME o Proof.theory_of);


(* datatype state *)

type node_presentation = node * Proof.context;

fun init_presentation () =
  Proof_Context.init_global (Theory.get_pure_bootstrap ());

fun node_presentation node =
  (node, cases_node init_presentation Context.proof_of Proof.context_of node);


datatype state =
  State of node_presentation * theory option;
    (*current node with presentation context, previous theory*)

fun node_of (State ((node, _), _)) = node;
fun previous_theory_of (State (_, prev_thy)) = prev_thy;

fun init_toplevel () = State (node_presentation Toplevel, NONE);
fun theory_toplevel thy = State (node_presentation (Theory (Context.Theory thy)), NONE);


fun level state =
  (case node_of state of
    Toplevel => 0
  | Theory _ => 0
  | Proof (prf, _) => Proof.level (Proof_Node.current prf)
  | Skipped_Proof (d, _) => d + 1);   (*different notion of proof depth!*)

fun str_of_state state =
  (case node_of state of
    Toplevel =>
      (case previous_theory_of state of
        NONE => "at top level"
      | SOME thy => "at top level, result theory " ^ quote (Context.theory_name thy))
  | Theory (Context.Theory _) => "in theory mode"
  | Theory (Context.Proof _) => "in local theory mode"
  | Proof _ => "in proof mode"
  | Skipped_Proof _ => "in skipped proof mode");


(* current node *)

fun is_toplevel state = (case node_of state of Toplevel => true | _ => false);

fun is_theory state =
  not (is_toplevel state) andalso is_some (theory_node (node_of state));

fun is_proof state =
  not (is_toplevel state) andalso is_some (proof_node (node_of state));

fun is_skipped_proof state =
  not (is_toplevel state) andalso skipped_proof_node (node_of state);

fun proper_node_of state = if is_toplevel state then raise UNDEF else node_of state;
fun proper_node_case f g state = cases_proper_node f g (proper_node_of state);

val context_of = proper_node_case Context.proof_of Proof.context_of;
val generic_theory_of = proper_node_case I (Context.Proof o Proof.context_of);
val theory_of = proper_node_case Context.theory_of Proof.theory_of;
val proof_of = proper_node_case (fn _ => error "No proof state") I;

fun proof_position_of state =
  (case proper_node_of state of
    Proof (prf, _) => Proof_Node.position prf
  | _ => ~1);

fun is_end_theory (State ((Toplevel, _), SOME _)) = true
  | is_end_theory _ = false;

fun end_theory _ (State ((Toplevel, _), SOME thy)) = thy
  | end_theory pos _ = error ("Malformed theory" ^ Position.here pos);


(* presentation context *)

structure Presentation_State = Proof_Data
(
  type T = state option;
  fun init _ = NONE;
);

fun presentation_context0 (State ((_, pr_ctxt), _)) = pr_ctxt;

fun presentation_context (state as State (current, _)) =
  presentation_context0 state
  |> Presentation_State.put (SOME (State (current, NONE)));

fun presentation_state ctxt =
  (case Presentation_State.get ctxt of
    NONE => State (node_presentation (Theory (Context.Proof ctxt)), NONE)
  | SOME state => state);


(* print state *)

fun pretty_context state =
  if is_toplevel state then []
  else
    let
      val gthy =
        (case node_of state of
          Toplevel => raise Match
        | Theory gthy => gthy
        | Proof (_, (_, gthy)) => gthy
        | Skipped_Proof (_, (_, gthy)) => gthy);
      val lthy = Context.cases Named_Target.theory_init I gthy;
    in Local_Theory.pretty lthy end;

fun pretty_state state =
  (case node_of state of
    Toplevel => []
  | Theory _ => []
  | Proof (prf, _) => Proof.pretty_state (Proof_Node.current prf)
  | Skipped_Proof (d, _) => [Pretty.str ("skipped proof: depth " ^ string_of_int d)]);

val string_of_state = pretty_state #> Pretty.chunks #> Pretty.string_of;

fun pretty_abstract state = Pretty.str ("<Isar " ^ str_of_state state ^ ">");

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_polyml o pretty_abstract);



(** toplevel transitions **)

(* primitive transitions *)

datatype trans =
  (*init theory*)
  Init of unit -> theory |
  (*formal exit of theory*)
  Exit |
  (*peek at state*)
  Keep of bool -> state -> unit |
  (*node transaction and presentation*)
  Transaction of (bool -> node -> node_presentation) * (state -> unit);

local

exception FAILURE of state * exn;

fun apply f g node =
  let
    val node_pr = node_presentation node;
    val context = cases_proper_node I (Context.Proof o Proof.context_of) node;
    fun state_error e node_pr' = (State (node_pr', get_theory node), e);

    val (result, err) =
      node
      |> Runtime.controlled_execution (SOME context) f
      |> state_error NONE
      handle exn => state_error (SOME exn) node_pr;
  in
    (case err of
      NONE => tap g result
    | SOME exn => raise FAILURE (result, exn))
  end;

fun apply_tr int trans state =
  (case (trans, node_of state) of
    (Init f, Toplevel) =>
      Runtime.controlled_execution NONE (fn () =>
        State (node_presentation (Theory (Context.Theory (f ()))), NONE)) ()
  | (Exit, node as Theory (Context.Theory thy)) =>
      let
        val State ((node', pr_ctxt), _) =
          node |> apply
            (fn _ =>
              node_presentation
                (Theory (Context.Theory (tap Thm.expose_theory (Theory.end_theory thy)))))
            (K ());
      in State ((Toplevel, pr_ctxt), get_theory node') end
  | (Keep f, node) =>
      Runtime.controlled_execution (try generic_theory_of state)
        (fn () => (f int state; State (node_presentation node, previous_theory_of state))) ()
  | (Transaction _, Toplevel) => raise UNDEF
  | (Transaction (f, g), node) => apply (fn x => f int x) g node
  | _ => raise UNDEF);

fun apply_union _ [] state = raise FAILURE (state, UNDEF)
  | apply_union int (tr :: trs) state =
      apply_union int trs state
        handle Runtime.UNDEF => apply_tr int tr state
          | FAILURE (alt_state, UNDEF) => apply_tr int tr alt_state
          | exn as FAILURE _ => raise exn
          | exn => raise FAILURE (state, exn);

fun apply_markers name markers (state as State ((node, pr_ctxt), prev_thy)) =
  let
    val state' =
      Runtime.controlled_execution (try generic_theory_of state)
        (fn () => State ((node, fold (Document_Marker.evaluate name) markers pr_ctxt), prev_thy)) ();
  in (state', NONE) end
  handle exn => (state, SOME exn);

in

fun apply_trans int name markers trans state =
  (apply_union int trans state |> apply_markers name markers)
  handle FAILURE (alt_state, exn) => (alt_state, SOME exn) | exn => (state, SOME exn);

end;


(* datatype transition *)

datatype transition = Transition of
 {name: string,               (*command name*)
  pos: Position.T,            (*source position*)
  markers: Input.source list, (*semantic document markers*)
  timing: Time.time,          (*prescient timing information*)
  trans: trans list};         (*primitive transitions (union)*)

fun make_transition (name, pos, markers, timing, trans) =
  Transition {name = name, pos = pos, markers = markers, timing = timing, trans = trans};

fun map_transition f (Transition {name, pos, markers, timing, trans}) =
  make_transition (f (name, pos, markers, timing, trans));

val empty = make_transition ("", Position.none, [], Time.zeroTime, []);


(* diagnostics *)

fun name_of (Transition {name, ...}) = name;
fun pos_of (Transition {pos, ...}) = pos;
fun timing_of (Transition {timing, ...}) = timing;

fun command_msg msg tr =
  msg ^ "command " ^ quote (Markup.markup Markup.keyword1 (name_of tr)) ^
    Position.here (pos_of tr);

fun at_command tr = command_msg "At " tr;
fun type_error tr = command_msg "Bad context for " tr;


(* modify transitions *)

fun name name = map_transition (fn (_, pos, markers, timing, trans) =>
  (name, pos, markers, timing, trans));

fun position pos = map_transition (fn (name, _, markers, timing, trans) =>
  (name, pos, markers, timing, trans));

fun markers markers = map_transition (fn (name, pos, _, timing, trans) =>
  (name, pos, markers, timing, trans));

fun timing timing = map_transition (fn (name, pos, markers, _, trans) =>
  (name, pos, markers, timing, trans));

fun add_trans tr = map_transition (fn (name, pos, markers, timing, trans) =>
  (name, pos, markers, timing, tr :: trans));

val reset_trans = map_transition (fn (name, pos, markers, timing, _) =>
  (name, pos, markers, timing, []));


(* basic transitions *)

fun init_theory f = add_trans (Init f);

fun is_init (Transition {trans = [Init _], ...}) = true
  | is_init _ = false;

fun modify_init f tr = if is_init tr then init_theory f (reset_trans tr) else tr;

val exit = add_trans Exit;
val keep' = add_trans o Keep;

fun present_transaction f g = add_trans (Transaction (f, g));
fun transaction f = present_transaction f (K ());
fun transaction0 f = present_transaction (node_presentation oo f) (K ());

fun keep f = add_trans (Keep (fn _ => f));

fun keep_proof f =
  keep (fn st =>
    if is_proof st then f st
    else if is_skipped_proof st then ()
    else warning "No proof state");

fun ignored pos = empty |> name "<ignored>" |> position pos |> keep (fn _ => ());
fun is_ignored tr = name_of tr = "<ignored>";

fun malformed pos msg =
  empty |> name "<malformed>" |> position pos |> keep (fn _ => error msg);


(* theory transitions *)

fun generic_theory f = transaction (fn _ =>
  (fn Theory gthy => node_presentation (Theory (f gthy))
    | _ => raise UNDEF));

fun theory' f = transaction (fn int =>
  (fn Theory (Context.Theory thy) =>
      let val thy' = thy
        |> Sign.new_group
        |> f int
        |> Sign.reset_group;
      in node_presentation (Theory (Context.Theory thy')) end
    | _ => raise UNDEF));

fun theory f = theory' (K f);

fun begin_main_target begin f = transaction (fn _ =>
  (fn Theory (Context.Theory thy) =>
        let
          val lthy = f thy;
          val gthy = if begin then Context.Proof lthy else Context.Theory (Named_Target.exit lthy);
          val _ =
            (case Local_Theory.pretty lthy of
              [] => ()
            | prts => Output.state (Pretty.string_of (Pretty.chunks prts)));
        in (Theory gthy, lthy) end
    | _ => raise UNDEF));

val end_main_target = transaction (fn _ =>
  (fn Theory (Context.Proof lthy) => (Theory (Context.Theory (Named_Target.exit lthy)), lthy)
    | _ => raise UNDEF));

fun begin_nested_target f = transaction0 (fn _ =>
  (fn Theory gthy =>
        let
          val lthy = Bundle.begin_nested gthy;
          val lthy' = f lthy
        in Theory (Context.Proof lthy') end
    | _ => raise UNDEF));

val end_nested_target = transaction (fn _ =>
  (fn Theory (Context.Proof lthy) =>
        (case try Local_Theory.close_target lthy of
          SOME lthy' =>
            let val gthy' = Bundle.end_nested lthy'
            in (Theory gthy', lthy) end
        | NONE => raise UNDEF)
    | _ => raise UNDEF));

fun restricted_context (SOME (strict, scope)) =
      Proof_Context.map_naming (Name_Space.restricted strict scope)
  | restricted_context NONE = I;

fun local_theory' restricted target f = present_transaction (fn int =>
  (fn Theory gthy =>
        let
          val (finish, lthy) = Named_Target.switch target gthy;
          val lthy' = lthy
            |> restricted_context restricted
            |> Local_Theory.new_group
            |> f int
            |> Local_Theory.reset_group;
        in (Theory (finish lthy'), lthy') end
    | _ => raise UNDEF))
  (K ());

fun local_theory restricted target f = local_theory' restricted target (K f);

fun present_local_theory target = present_transaction (fn _ =>
  (fn Theory gthy =>
        let val (finish, lthy) = Named_Target.switch target gthy;
        in (Theory (finish lthy), lthy) end
    | _ => raise UNDEF));


(* proof transitions *)

fun end_proof f = transaction (fn int =>
  (fn Proof (prf, (finish, _)) =>
        let val state = Proof_Node.current prf in
          if can (Proof.assert_bottom true) state then
            let
              val ctxt' = f int state;
              val gthy' = finish ctxt';
            in (Theory gthy', ctxt') end
          else raise UNDEF
        end
    | Skipped_Proof (0, (gthy, _)) => node_presentation (Theory gthy)
    | _ => raise UNDEF));

local

fun begin_proof init_proof = transaction0 (fn int =>
  (fn Theory gthy =>
    let
      val (finish, prf) = init_proof int gthy;
      val document = Options.default_string "document";
      val skip = (document = "" orelse document = "false") andalso Goal.skip_proofs_enabled ();
      val schematic_goal = try Proof.schematic_goal prf;
      val _ =
        if skip andalso schematic_goal = SOME true then
          warning "Cannot skip proof of schematic goal statement"
        else ();
    in
      if skip andalso schematic_goal = SOME false then
        Skipped_Proof (0, (finish (Proof.global_skip_proof true prf), gthy))
      else Proof (Proof_Node.init prf, (finish, gthy))
    end
  | _ => raise UNDEF));

in

fun local_theory_to_proof' restricted target f = begin_proof
  (fn int => fn gthy =>
    let
      val (finish, lthy) = Named_Target.switch target gthy;
      val prf = lthy
        |> restricted_context restricted
        |> Local_Theory.new_group
        |> f int;
    in (finish o Local_Theory.reset_group, prf) end);

fun local_theory_to_proof restricted target f =
  local_theory_to_proof' restricted target (K f);

fun theory_to_proof f = begin_proof
  (fn _ => fn gthy =>
    (Context.Theory o Sign.reset_group o Sign.change_check o Proof_Context.theory_of,
      (case gthy of
        Context.Theory thy => f (Sign.new_group thy)
      | _ => raise UNDEF)));

end;

val forget_proof = transaction0 (fn _ =>
  (fn Proof (prf, (_, orig_gthy)) =>
        if Proof.is_notepad (Proof_Node.current prf) then raise UNDEF
        else Theory orig_gthy
    | Skipped_Proof (_, (_, orig_gthy)) => Theory orig_gthy
    | _ => raise UNDEF));

fun proofs' f = transaction0 (fn int =>
  (fn Proof (prf, x) => Proof (Proof_Node.applys (f int) prf, x)
    | skip as Skipped_Proof _ => skip
    | _ => raise UNDEF));

fun proof' f = proofs' ((Seq.single o Seq.Result) oo f);
val proofs = proofs' o K;
val proof = proof' o K;


(* skipped proofs *)

fun actual_proof f = transaction0 (fn _ =>
  (fn Proof (prf, x) => Proof (f prf, x)
    | _ => raise UNDEF));

fun skip_proof f = transaction0 (fn _ =>
  (fn skip as Skipped_Proof _ => (f (); skip)
    | _ => raise UNDEF));

val skip_proof_open = transaction0 (fn _ =>
  (fn Skipped_Proof (d, x) => Skipped_Proof (d + 1, x)
    | _ => raise UNDEF));

val skip_proof_close = transaction0 (fn _ =>
  (fn Skipped_Proof (0, (gthy, _)) => Theory gthy
    | Skipped_Proof (d, x) => Skipped_Proof (d - 1, x)
    | _ => raise UNDEF));



(** toplevel transactions **)

(* runtime position *)

fun exec_id id (tr as Transition {pos, ...}) =
  position (Position.put_id (Document_ID.print id) pos) tr;

fun setmp_thread_position (Transition {pos, ...}) f x =
  Position.setmp_thread_data pos f x;


(* post-transition hooks *)

local
  val hooks =
    Synchronized.var "Toplevel.hooks" ([]: (transition -> state -> state -> unit) list);
in

fun add_hook hook = Synchronized.change hooks (cons hook);
fun get_hooks () = Synchronized.value hooks;

end;


(* apply transitions *)

local

fun app int (tr as Transition {name, markers, trans, ...}) =
  setmp_thread_position tr
    (Timing.protocol (name_of tr) (pos_of tr) (apply_trans int name markers trans)
      ##> Option.map (fn UNDEF => ERROR (type_error tr) | exn => exn));

in

fun transition int tr st =
  let
    val (st', opt_err) =
      Context.setmp_generic_context (try (Context.Proof o presentation_context0) st)
        (fn () => app int tr st) ();
    val opt_err' = opt_err |> Option.map
      (fn Runtime.EXCURSION_FAIL exn_info => exn_info
        | exn => (Runtime.exn_context (try context_of st) exn, at_command tr));
    val _ = get_hooks () |> List.app (fn f => (try (fn () => f tr st st') (); ()));
  in (st', opt_err') end;

end;


(* managed commands *)

fun command_errors int tr st =
  (case transition int tr st of
    (st', NONE) => ([], SOME st')
  | (_, SOME (exn, _)) => (Runtime.exn_messages exn, NONE));

fun command_exception int tr st =
  (case transition int tr st of
    (st', NONE) => st'
  | (_, SOME (exn, info)) =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else raise Runtime.EXCURSION_FAIL (exn, info));

val command = command_exception false;


(* reset state *)

local

fun reset_state check trans st =
  if check st then NONE
  else #2 (command_errors false (trans empty) st);

in

val reset_theory = reset_state is_theory forget_proof;

val reset_proof =
  reset_state is_proof
    (transaction0 (fn _ =>
      (fn Theory gthy => Skipped_Proof (0, (gthy, gthy))
        | _ => raise UNDEF)));

val reset_notepad =
  reset_state
    (fn st =>
      (case try proof_of st of
        SOME state => not (Proof.is_notepad state) orelse can Proof.end_notepad state
      | NONE => true))
    (proof Proof.reset_notepad);

end;


(* scheduled proof result *)

datatype result =
  Result of transition * state |
  Result_List of result list |
  Result_Future of result future;

fun join_results (Result x) = [x]
  | join_results (Result_List xs) = maps join_results xs
  | join_results (Result_Future x) = join_results (Future.join x);

local

structure Result = Proof_Data
(
  type T = result;
  fun init _ = Result_List [];
);

val get_result = Result.get o Proof.context_of;
val put_result = Proof.map_context o Result.put;

fun timing_estimate elem =
  let val trs = tl (Thy_Element.flat_element elem)
  in fold (fn tr => fn t => timing_of tr + t) trs Time.zeroTime end;

fun future_proofs_enabled estimate st =
  (case try proof_of st of
    NONE => false
  | SOME state =>
      not (Proofterm.proofs_enabled ()) andalso
      not (Proof.is_relevant state) andalso
       (if can (Proof.assert_bottom true) state
        then Future.proofs_enabled 1
        else Future.proofs_enabled 2 orelse Future.proofs_enabled_timing estimate));

val empty_markers = markers [];
val empty_trans = reset_trans #> keep (K ());

in

fun fork_presentation tr = (tr |> empty_markers, tr |> empty_trans);

fun atom_result keywords tr st =
  let
    val st' =
      if Future.proofs_enabled 1 andalso Keyword.is_diag keywords (name_of tr) then
        let
          val (tr1, tr2) = fork_presentation tr;
          val _ =
            Execution.fork {name = "Toplevel.diag", pos = pos_of tr, pri = ~1}
              (fn () => command tr1 st);
        in command tr2 st end
      else command tr st;
  in (Result (tr, st'), st') end;

fun element_result keywords (Thy_Element.Element (tr, NONE)) st = atom_result keywords tr st
  | element_result keywords (elem as Thy_Element.Element (head_tr, SOME element_rest)) st =
      let
        val (head_result, st') = atom_result keywords head_tr st;
        val (body_elems, end_tr) = element_rest;
        val estimate = timing_estimate elem;
      in
        if not (future_proofs_enabled estimate st')
        then
          let
            val proof_trs = maps Thy_Element.flat_element body_elems @ [end_tr];
            val (proof_results, st'') = fold_map (atom_result keywords) proof_trs st';
          in (Result_List (head_result :: proof_results), st'') end
        else
          let
            val (end_tr1, end_tr2) = fork_presentation end_tr;

            val finish = Context.Theory o Proof_Context.theory_of;

            val future_proof =
              Proof.future_proof (fn state =>
                Execution.fork
                  {name = "Toplevel.future_proof", pos = pos_of head_tr, pri = ~1}
                  (fn () =>
                    let
                      val State ((Proof (prf, (_, orig_gthy)), _), prev_thy) = st';
                      val node' = Proof (Proof_Node.apply (K state) prf, (finish, orig_gthy));
                      val (results, result_state) =
                        State (node_presentation node', prev_thy)
                        |> fold_map (element_result keywords) body_elems ||> command end_tr1;
                    in (Result_List results, presentation_context0 result_state) end))
              #> (fn (res, state') => state' |> put_result (Result_Future res));

            val forked_proof =
              proof (future_proof #>
                (fn state => state |> Proof.local_done_proof |> put_result (get_result state))) o
              end_proof (fn _ => future_proof #>
                (fn state => state |> Proof.global_done_proof |> Result.put (get_result state)));

            val st'' = st' |> command (head_tr |> reset_trans |> forked_proof);
            val end_st = st'' |> command end_tr2;
            val end_result = Result (end_tr, end_st);
            val result =
              Result_List [head_result, Result.get (presentation_context0 st''), end_result];
          in (result, end_st) end
      end;

end;

end;

structure Local_Theory : LOCAL_THEORY = struct open Local_Theory; end;
