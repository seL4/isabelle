(*  Title:      Pure/Isar/toplevel.ML
    Author:     Makarius

Isabelle/Isar command transactions, within a PIDE document.

Note: The name "toplevel" refers to old times, when Isabelle still had a
toplevel command loop, or read-eval-print loop (REPL). This no longer exists,
but the name remains with a quite different meaning.

See also:
  Makarius Wenzel. READ-EVAL-PRINT in parallel and asynchronous proof-checking.
  In Cezary Kaliszyk and Christoph Lüth, editors, User Interfaces for Theorem
  Provers (UITP 2012), volume 118 of EPTCS, 2013.
  https://arxiv.org/abs/1307.1944v1
*)

signature TOPLEVEL =
sig
  exception UNDEF
  type state
  val make_state: Context.generic option -> state
  val is_toplevel: state -> bool
  val is_theory: state -> bool
  val is_proof: state -> bool
  val is_skipped_proof: state -> bool
  val is_skipped: state -> bool
  val proof_level: state -> int
  val previous_theory_of: state -> theory option
  val output_of: state -> Latex.text option
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
  val pretty_abstract: state -> Pretty.T
  type presentation = state -> Latex.text
  type transition
  val make: {name: string, kind: string, is_begin: bool, pos: Position.T} -> transition
  val empty: transition
  val name_of: transition -> string
  val kind_of: transition -> string
  val pos_of: transition -> Position.T
  val timing_of: transition -> Time.time
  val is_begin: transition -> bool
  val type_error: transition -> string
  val position: Position.T -> transition -> transition
  val markers: Input.source list -> transition -> transition
  val timing: Time.time -> transition -> transition
  val is_theory_begin: transition -> bool
  val prepare_init: transition -> transition
  type init = unit -> {skipped: bool, theory: theory}
  val provide_init: init -> transition -> transition
  val present: presentation -> transition -> transition
  val keep: (state -> unit) -> transition -> transition
  val keep_proof: (state -> unit) -> transition -> transition
  val is_ignored: transition -> bool
  val is_malformed: transition -> bool
  val ignored: Position.T -> transition
  val malformed: Position.T -> string -> transition
  val generic_theory: (generic_theory -> generic_theory) -> transition -> transition
  val theory_presentation: (theory -> theory) -> presentation -> transition -> transition
  val theory: (theory -> theory) -> transition -> transition
  val begin_main_target: bool -> (theory -> local_theory) -> transition -> transition
  val begin_nested_target: (Context.generic -> local_theory) -> transition -> transition
  val local_theory_presentation: (bool * Position.T) option -> (xstring * Position.T) option ->
    (local_theory -> local_theory) -> presentation -> transition -> transition
  val local_theory: (bool * Position.T) option -> (xstring * Position.T) option ->
    (local_theory -> local_theory) -> transition -> transition
  val present_local_theory: (xstring * Position.T) option -> presentation ->
    transition -> transition
  val local_theory_to_proof: (bool * Position.T) option -> (xstring * Position.T) option ->
    (local_theory -> Proof.state) -> transition -> transition
  val theory_to_proof: (theory -> Proof.state) -> transition -> transition
  val end_proof: (Proof.state -> Proof.context) -> transition -> transition
  val forget_proof: transition -> transition
  val proofs: (Proof.state -> Proof.state Seq.result Seq.seq) -> transition -> transition
  val proof: (Proof.state -> Proof.state) -> transition -> transition
  val actual_proof: (Proof_Node.T -> Proof_Node.T) -> transition -> transition
  val skip_proof: (unit -> unit) -> transition -> transition
  val skip_proof_open: transition -> transition
  val skip_proof_close: transition -> transition
  val end_context: transition -> transition
  val exec_id: Document_ID.exec -> transition -> transition
  val setmp_thread_position: transition -> ('a -> 'b) -> 'a -> 'b
  val command_errors: transition -> state -> Runtime.error list * state option
  val command_exception: transition -> state -> state
  val reset_state: transition -> state -> state
  val fork_presentation: transition -> transition * transition
  type result
  val join_results: result -> (state * transition * state) list
  val element_result: transition Thy_Element.element -> state -> result * state
end;

structure Toplevel: TOPLEVEL =
struct

(** toplevel state **)

exception UNDEF = Runtime.UNDEF;


(* datatype node *)

type thy = {skipped: bool, level: int, gthy: generic_theory};
  (*skipped mode, target context level, global or local theory target*)

fun inherit_thy ({skipped, level, ...}: thy) =
  fn gthy' => {skipped = skipped, level = level, gthy = gthy'};

fun inc_level level = level + 1;
fun dec_level level = if level <= 0 then raise UNDEF else level - 1;

fun report_skipped () =
  Position.report_text (Position.thread_data ()) (Markup.bad ()) "Skipped";

datatype node =
  Toplevel
    (*toplevel outside of theory body*) |
  Theory of thy
    (*theory target context*) |
  Proof of Proof_Node.T * ((Proof.context -> thy) * thy)
    (*proof node, finish, original theory*) |
  Skipped_Proof of int * (thy * thy);
    (*proof depth, resulting theory, original theory*)

val theory_node = fn Theory gthy => SOME gthy | _ => NONE;
val proof_node = fn Proof (prf, _) => SOME prf | _ => NONE;
val skipped_proof_node = fn Skipped_Proof _ => true | _ => false;

fun cases_node f _ _ Toplevel = f ()
  | cases_node _ g _ (Theory {gthy, ...}) = g gthy
  | cases_node _ _ h (Proof (prf, _)) = h (Proof_Node.current prf)
  | cases_node _ g _ (Skipped_Proof (_, ({gthy, ...}, _))) = g gthy;

fun cases_proper_node g h = cases_node (fn () => raise UNDEF) g h;

val get_theory = cases_node (K NONE) (SOME o Context.theory_of) (SOME o Proof.theory_of);


(* datatype state *)

type node_presentation = node * Proof.context;

fun init_presentation () =
  Proof_Context.init_global (Theory.get_pure_bootstrap ());

fun node_presentation node =
  (node, cases_node init_presentation Context.proof_of Proof.context_of node);

datatype state =
  State of node_presentation * (theory option * Latex.text future option);
    (*current node with presentation context, previous theory, document output*)

fun node_of (State ((node, _), _)) = node;
fun previous_theory_of (State (_, (prev_thy, _))) = prev_thy;
fun output_of (State (_, (_, output))) = Option.map Future.join output;

fun reset_output (State (node_presentation, (prev_thy, _))) =
  State ((node_presentation, (prev_thy, NONE)));

fun make_state_node node = State (node_presentation node, (NONE, NONE));

fun make_state opt_gthy =
  let val node =
    (case opt_gthy of
      NONE => Toplevel
    | SOME gthy =>
        let val level = Context.cases (K 0) Local_Theory.level gthy
        in Theory {skipped = false, level = level, gthy = gthy} end)
  in make_state_node node end;

fun proof_level state =
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
      | SOME thy => "at top level, result theory " ^ quote (Context.theory_base_name thy))
  | Theory {skipped = true, ...} => "in skipped theory mode"
  | Theory {gthy = Context.Theory _, ...} => "in theory mode"
  | Theory {gthy = Context.Proof _, ...} => "in local theory mode"
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

fun is_skipped state =
  (case node_of state of
    Theory {skipped, ...} => skipped
  | Skipped_Proof _ => true
  | _ => false);

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

fun is_end_theory (State ((Toplevel, _), (SOME _, _))) = true
  | is_end_theory _ = false;

fun end_theory _ (State ((Toplevel, _), (SOME thy, _))) = thy
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
  |> Presentation_State.put (SOME (State (current, (NONE, NONE))));

fun presentation_state ctxt =
  Presentation_State.get ctxt
  |> \<^if_none>\<open>make_state (SOME (Context.Proof ctxt))\<close>;


(* print state *)

fun pretty_context state =
  if is_toplevel state then []
  else
    let
      val gthy =
        (case node_of state of
          Toplevel => raise Match
        | Theory {gthy, ...} => gthy
        | Proof (_, (_, {gthy, ...})) => gthy
        | Skipped_Proof (_, (_, {gthy, ...})) => gthy);
      val lthy = Context.cases Named_Target.theory_init I gthy;
    in Local_Theory.pretty lthy end;

fun pretty_state state =
  (case node_of state of
    Toplevel => []
  | Theory _ => []
  | Proof (prf, _) => Proof.pretty_state (Proof_Node.current prf)
  | Skipped_Proof (d, _) => [Pretty.str ("skipped proof: depth " ^ string_of_int d)]);

fun pretty_abstract state = Pretty.str ("<Isar " ^ str_of_state state ^ ">");

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o pretty_abstract);



(** toplevel transitions **)

(* primitive transitions *)

type presentation = state -> Latex.text;

type init = unit -> {skipped: bool, theory: theory};

datatype trans =
  (*init theory*)
  Init of init |
  (*formal exit of theory*)
  Exit |
  (*keep state unchanged*)
  Keep of (state -> unit) * presentation option |
  (*node transaction and presentation*)
  Transaction of (node -> node_presentation) * presentation option;

local

fun present_state fork g node_pr prev_thy =
  let
    val state = State (node_pr, (prev_thy, NONE));
    fun present pr =
      if fork andalso Future.proofs_enabled 1 then
        Execution.fork {name = "Toplevel.present_state", pos = Position.thread_data (), pri = ~1}
          (fn () => pr state)
      else Future.value (pr state);
    val output =
      if is_some prev_thy andalso is_skipped state
      then NONE else Option.map present g;
  in State (node_pr, (prev_thy, output)) end;

fun no_update f g state =
  Runtime.controlled_execution (try generic_theory_of state)
    (fn () =>
      let
        val prev_thy = previous_theory_of state;
        val () = if is_skipped state then report_skipped () else f state;
        val node_pr = node_presentation (node_of state);
      in present_state false g node_pr prev_thy end) ()

fun update f g state =
  Runtime.controlled_execution (try generic_theory_of state)
    (fn () =>
      let
        val node = node_of state;
        val prev_thy = get_theory node;
      in present_state true g (f node) prev_thy end) ();

fun apply_tr trans state =
  (case (trans, node_of state) of
    (Init f, Toplevel) =>
      Runtime.controlled_execution NONE (fn () =>
        let
          val {skipped, theory} = f ();
          val node = Theory {skipped = skipped, level = 0, gthy = Context.Theory theory};
        in make_state_node node end) ()
  | (Exit, Theory {level = 0, gthy = Context.Theory thy, ...}) =>
      let
        val State ((node', pr_ctxt), _) =
          state |> update
            (fn _ =>
              node_presentation
                (Theory {skipped = false, level = 0,
                  gthy = Context.Theory (tap Thm.expose_theory (Theory.end_theory thy))}))
            NONE;
      in State ((Toplevel, pr_ctxt), (get_theory node', NONE)) end
  | (Keep (f, g), _) => no_update (fn x => f x) g state
  | (Transaction _, Toplevel) => raise UNDEF
  | (Transaction (f, g), _) => update f g state
  | _ => raise UNDEF);

fun apply_body [] _ = raise UNDEF
  | apply_body [tr] state = apply_tr tr state
  | apply_body (tr :: trs) state =
      apply_body trs state
        handle Runtime.UNDEF => apply_tr tr state;

fun apply_markers name markers (state as State ((node, pr_ctxt), prev_thy)) =
  let
    val state' =
      Runtime.controlled_execution (try generic_theory_of state)
        (fn () => State ((node, fold (Document_Marker.evaluate name) markers pr_ctxt), prev_thy)) ();
  in (state', NONE) end;

in

fun apply_capture name markers trans state =
  (case Exn.capture_body (fn () => apply_body trans state |> apply_markers name markers) of
    Exn.Res res => res
  | Exn.Exn exn => (state, SOME exn));

end;


(* datatype transition *)

datatype transition = Transition of
 {name: string,               (*command name*)
  kind: string,               (*command kind*)
  is_begin: bool,             (*command with 'begin' keyword *)
  pos: Position.T,            (*source position*)
  markers: Input.source list, (*semantic document markers*)
  timing: Time.time,          (*prescient timing information*)
  trans: trans list};         (*primitive transitions (union)*)

fun make_transition (name, kind, is_begin, pos, markers, timing, trans) =
  Transition {name = name, kind = kind, is_begin = is_begin, pos = pos,
    markers = markers, timing = timing, trans = trans};

fun map_transition f (Transition {name, kind, is_begin, pos, markers, timing, trans}) =
  make_transition (f (name, kind, is_begin, pos, markers, timing, trans));

fun make {name, kind, is_begin, pos} =
  let
    val theory_begin = Symset.member Keyword.theory_begin_kinds kind;
    val theory_end = Symset.member Keyword.theory_end_kinds kind;
    val ok =
      if name = Thy_Header.theoryN then theory_begin
      else if name = Thy_Header.endN then theory_end
      else not (theory_begin orelse theory_end);
  in
    if ok then make_transition (name, kind, is_begin, pos, [], Time.zeroTime, [])
    else raise Fail ("Bad command classification: name " ^ quote name ^ ", kind " ^ quote kind)
  end;

val empty = make {name = "", kind = "", is_begin = false, pos = Position.none};


(* diagnostics *)

fun rep_transition (Transition args) = args;

val name_of = #name o rep_transition;
val kind_of = #kind o rep_transition;
val pos_of = #pos o rep_transition;
val timing_of = #timing o rep_transition;

val is_begin = #is_begin o rep_transition;

fun command_msg msg tr =
  msg ^ "command " ^ quote (Markup.markup Markup.keyword1 (name_of tr)) ^
    Position.here (pos_of tr);

fun at_command tr = command_msg "At " tr;
fun type_error tr = command_msg "Bad context for " tr;


(* modify transitions *)

fun position pos = map_transition (fn (name, kind, is_begin, _, markers, timing, trans) =>
  (name, kind, is_begin, pos, markers, timing, trans));

fun markers markers = map_transition (fn (name, kind, is_begin, pos, _, timing, trans) =>
  (name, kind, is_begin, pos, markers, timing, trans));

fun timing timing = map_transition (fn (name, kind, is_begin, pos, markers, _, trans) =>
  (name, kind, is_begin, pos, markers, timing, trans));

fun add_trans tr = map_transition (fn (name, kind, is_begin, pos, markers, timing, trans) =>
  (name, kind, is_begin, pos, markers, timing, tr :: trans));

val reset_trans = map_transition (fn (name, kind, is_begin, pos, markers, timing, _) =>
  (name, kind, is_begin, pos, markers, timing, []));


(* basic transitions *)

val is_theory_begin = Symset.member Keyword.theory_begin_kinds o kind_of;

fun prepare_init tr =
  if is_theory_begin tr
  then add_trans (Init (fn () => raise Fail "Missing theory initialization")) tr
  else raise Fail ("Bad theory initialization: " ^ quote (name_of tr) ^ Position.here (pos_of tr));

fun provide_init f tr =
  if is_theory_begin tr then add_trans (Init f) (reset_trans tr) else tr;

fun present_transaction f g = add_trans (Transaction (f, g));
fun transaction f = present_transaction f NONE;
fun transaction0 f = transaction (node_presentation o f);

fun present g = add_trans (Keep (fn _ => (), SOME g));
fun keep f = add_trans (Keep (f, NONE));

fun keep_proof f =
  keep (fn st =>
    if is_proof st then f st
    else if is_skipped_proof st then ()
    else warning "No proof state");

val ignoredN = "<ignored>";
val malformedN = "<malformed>";

fun is_ignored tr = name_of tr = ignoredN;
fun is_malformed tr = name_of tr = malformedN;

fun ignored pos =
  make {name = ignoredN, kind = "", is_begin = false, pos = pos};

fun malformed pos msg =
  make {name = malformedN, kind = "", is_begin = false, pos = pos} |> keep (fn _ => error msg);


(* theory transitions *)

fun generic_theory f = transaction0
  (fn node as Theory {skipped, level, gthy} =>
        if skipped then (report_skipped (); node)
        else Theory {skipped = skipped, level = level, gthy = f gthy}
    | _ => raise UNDEF);

fun theory' f = present_transaction
  (fn node as Theory {skipped, level, gthy = Context.Theory thy} =>
        let
          val node' =
            if skipped then (report_skipped (); node)
            else
              let
                val thy' = thy
                  |> Sign.new_group
                  |> f
                  |> Sign.reset_group;
              in Theory {skipped = skipped, level = level, gthy = Context.Theory thy'} end;
        in node_presentation node' end
    | _ => raise UNDEF);

fun theory_presentation f g = theory' f (SOME g);
fun theory f = theory' f NONE;

fun begin_main_target begin f = transaction
  (fn Theory {skipped, level, gthy = gthy as Context.Theory thy} =>
        let val level' = level |> begin ? inc_level in
          if skipped then
            (report_skipped ();
             node_presentation (Theory {skipped = skipped, level = level', gthy = gthy}))
          else
            let
              val lthy = f thy;
              val gthy' =
                if begin
                then Context.Proof lthy
                else Target_Context.end_named_cmd lthy;
              val _ =
                (case Local_Theory.pretty lthy of
                  [] => ()
                | prts => Pretty.writeln (Pretty.chunks prts));
            in (Theory {skipped = skipped, level = level', gthy = gthy'}, lthy) end
        end
    | _ => raise UNDEF);

val end_main_target = transaction
  (fn Theory {skipped, level, gthy} =>
        let val level' = dec_level level in
          if skipped then
            (report_skipped ();
             node_presentation (Theory {skipped = skipped, level = level', gthy = gthy}))
          else
            (case gthy of
              Context.Proof lthy =>
                (Theory {skipped = skipped, level = level', gthy = Target_Context.end_named_cmd lthy},
                  lthy)
            | _ => raise UNDEF)
        end
    | _ => raise UNDEF);

fun begin_nested_target f = transaction0
  (fn Theory {skipped, level, gthy} =>
        let
          val level' = inc_level level;
          val gthy' = if skipped then (report_skipped (); gthy) else Context.Proof (f gthy);
        in Theory {skipped = skipped, level = level', gthy = gthy'} end
    | _ => raise UNDEF);

val end_nested_target = transaction
  (fn Theory {skipped, level, gthy} =>
        let val level' = dec_level level in
          if skipped then
            (report_skipped ();
             node_presentation (Theory {skipped = skipped, level = level', gthy = gthy}))
          else
            (case gthy of
              Context.Proof lthy =>
                (case try Target_Context.end_nested_cmd lthy of
                  SOME gthy' => (Theory {skipped = skipped, level = level', gthy = gthy'}, lthy)
                | NONE => raise UNDEF)
            | _ => raise UNDEF)
        end
    | _ => raise UNDEF);

fun local_theory' restricted target f = present_transaction
  (fn node as Theory {skipped, level, gthy} =>
        if skipped then (report_skipped (); node_presentation node)
        else
          let
            val (finish, lthy) = Target_Context.switch_named_cmd target gthy;
            val lthy' = lthy
              |> Proof_Context.restricted restricted
              |> Local_Theory.new_group
              |> f
              |> Local_Theory.reset_group;
          in (Theory {skipped = skipped, level = level, gthy = finish lthy'}, lthy') end
    | _ => raise UNDEF);

fun local_theory_presentation restricted target f g = local_theory' restricted target f (SOME g);
fun local_theory restricted target f = local_theory' restricted target f NONE;

fun present_local_theory target g = present_transaction
  (fn node as Theory {skipped, level, gthy} =>
        if skipped then (report_skipped (); node_presentation node)
        else
          let val (finish, lthy) = Target_Context.switch_named_cmd target gthy;
          in (Theory {skipped = skipped, level = level, gthy = finish lthy}, lthy) end
    | _ => raise UNDEF)
  (SOME g);


(* proof transitions *)

fun end_proof f = transaction
  (fn Proof (prf, (finish, _)) =>
        let val state = Proof_Node.current prf in
          if can (Proof.assert_bottom true) state then
            let
              val ctxt' = f state;
              val thy' = finish ctxt';
            in (Theory thy', ctxt') end
          else raise UNDEF
        end
    | Skipped_Proof (0, (gthy, _)) => node_presentation (Theory gthy)
    | _ => raise UNDEF);

local

fun begin_proof init_proof = transaction0
  (fn Theory (thy as {skipped, gthy, ...}) =>
        if skipped then (report_skipped (); Skipped_Proof (0, (thy, thy)))
        else
          let
            val (finish_gthy, prf) = init_proof gthy;
            val finish = finish_gthy #> inherit_thy thy;
            val document = Options.default_string "document";
            val skip = (document = "" orelse document = "false") andalso Goal.skip_proofs_enabled ();
            val schematic_goal = try Proof.schematic_goal prf;
            val _ =
              if skip andalso schematic_goal = SOME true then
                warning "Cannot skip proof of schematic goal statement"
              else ();
          in
            if skip andalso schematic_goal = SOME false then
              Skipped_Proof (0, (finish (Interactive.setmp true Proof.global_skip_proof prf), thy))
            else Proof (Proof_Node.init prf, (finish, thy))
          end
  | _ => raise UNDEF);

in

fun local_theory_to_proof restricted target f = begin_proof
  (fn gthy =>
    let
      val (finish, lthy) = Target_Context.switch_named_cmd target gthy;
      val prf = lthy
        |> Proof_Context.restricted restricted
        |> Local_Theory.new_group
        |> f;
    in (finish o Local_Theory.reset_group, prf) end);

fun theory_to_proof f = begin_proof
  (fn gthy =>
    (Context.Theory o Sign.reset_group o Sign.change_check o Proof_Context.theory_of,
      (case gthy of
        Context.Theory thy => f (Sign.new_group thy)
      | _ => raise UNDEF)));

end;

val forget_proof = transaction0
  (fn Proof (prf, (_, orig_thy)) =>
        if Proof.is_notepad (Proof_Node.current prf) then raise UNDEF
        else Theory orig_thy
    | Skipped_Proof (_, (_, orig_gthy)) => Theory orig_gthy
    | _ => raise UNDEF);

fun proofs f = transaction0
  (fn Proof (prf, x) => Proof (Proof_Node.applys f prf, x)
    | skip as Skipped_Proof _ => skip
    | _ => raise UNDEF);

fun proof f = proofs ((Seq.single o Seq.Result) o f);


(* skipped proofs *)

fun actual_proof f = transaction0
  (fn Proof (prf, x) => Proof (f prf, x)
    | _ => raise UNDEF);

fun skip_proof f = transaction0
  (fn skip as Skipped_Proof _ => (f (); skip)
    | _ => raise UNDEF);

val skip_proof_open = transaction0
  (fn Skipped_Proof (d, x) => Skipped_Proof (d + 1, x)
    | _ => raise UNDEF);

val skip_proof_close = transaction0
  (fn Skipped_Proof (0, (gthy, _)) => Theory gthy
    | Skipped_Proof (d, x) => Skipped_Proof (d - 1, x)
    | _ => raise UNDEF);


(* end context *)

val end_context =
  add_trans Exit o end_main_target o end_nested_target o end_proof Proof.end_notepad;



(** toplevel transactions **)

(* runtime position *)

fun exec_id id (tr as Transition {pos, ...}) =
  let val put_id = Position.put_id (Document_ID.print id)
  in position (put_id pos) tr end;

fun setmp_thread_position (Transition {pos, name, ...}) f x =
  Position.setmp_thread_data (Position.label (Long_Name.qualify Markup.commandN name) pos) f x;


(* command transitions *)

local

fun show_state (st', opt_err) =
  let
    val enabled =
      is_none opt_err andalso
      Options.default_bool \<^system_option>\<open>show_states\<close>;
    val opt_err' =
      if enabled then
        (case Exn.capture (Output.state o Pretty.strings_of o Pretty.chunks o pretty_state) st' of
          Exn.Exn exn => SOME exn
        | Exn.Res _ => opt_err)
      else opt_err;
  in (st', opt_err') end;

fun app_state (tr as Transition {name, markers, trans, ...}) =
  setmp_thread_position tr
    ((apply_capture name markers trans |> Timing.command_timing (name_of tr) (pos_of tr))
      ##> Option.map (fn Runtime.UNDEF => ERROR (type_error tr) | exn => exn)
      #> show_state);

fun command_transition tr st =
  let
    val (st', opt_err) =
      if is_ignored tr then (reset_output st, NONE)
      else
        Context.setmp_generic_context (try (Context.Proof o presentation_context0) st)
          (fn () => app_state tr st) ();
    val opt_err' = opt_err |> Option.map
      (fn Runtime.EXCURSION_FAIL exn_info => exn_info
        | exn => (Runtime.exn_context (try context_of st) exn, at_command tr));
  in (st', opt_err') end;

in

fun command_errors tr st =
  (case command_transition tr st of
    (st', NONE) => ([], SOME st')
  | (_, SOME (exn, _)) => (Runtime.exn_messages exn, NONE));

fun command_exception tr st =
  (case command_transition tr st of
    (st', NONE) => st'
  | (_, SOME (exn, info)) =>
      if Exn.is_interrupt_proper exn then Exn.reraise exn
      else raise Runtime.EXCURSION_FAIL (exn, info));

end;


(* reset state *)

local

fun reset_if cond trans st =
  if cond st then NONE
  else #2 (command_errors (trans empty) st);

val reset_theory = reset_if is_theory forget_proof;

val reset_proof =
  reset_if is_proof
    (transaction0
      (fn Theory gthy => Skipped_Proof (0, (gthy, gthy))
        | _ => raise UNDEF));

val reset_notepad =
  reset_if
    (fn st =>
      (case try proof_of st of
        SOME state => not (Proof.is_notepad state) orelse can Proof.end_notepad state
      | NONE => true))
    (proof Proof.reset_notepad);

in

fun reset_state tr st = setmp_thread_position tr (fn () =>
  let
    val kind = kind_of tr;
    val res =
      if Symset.member Keyword.theory_body_kinds kind then reset_theory st
      else if Symset.member Keyword.proof_kinds kind then reset_proof st
      else if Symset.member Keyword.theory_end_kinds kind then
        (case reset_notepad st of
          NONE => reset_theory st
        | some => some)
      else NONE;
  in
    (case res of
      NONE => st
    | SOME st' => (Output.error_message (type_error tr ^ " -- using reset state"); st'))
  end) ();

end;


(* scheduled proof result *)

datatype result =
  Result of transition * state |
  Result_List of result list |
  Result_Future of result future;

fun join_results result =
  let
    fun add (tr, st') res =
      (case res of
        [] => [(make_state NONE, tr, st')]
      | (_, _, st) :: _ => (st, tr, st') :: res);
    fun acc (Result r) = add r
      | acc (Result_List rs) = fold acc rs
      | acc (Result_Future x) = acc (Future.join x);
  in rev (acc result []) end;

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
      not (Proofterm.any_proofs_enabled ()) andalso
      not (Proof.is_relevant state) andalso
       (if can (Proof.assert_bottom true) state
        then Future.proofs_enabled 1
        else Future.proofs_enabled 2 orelse Future.proofs_enabled_timing estimate));

in

fun fork_presentation tr = (markers [] tr, ignored (pos_of tr));

fun atom_result tr st =
  let
    val st' =
      if Future.proofs_enabled 1 andalso Symset.member Keyword.diag_kinds (kind_of tr) then
        let
          val (tr1, tr2) = fork_presentation tr;
          val _ =
            Execution.fork {name = "Toplevel.diag", pos = pos_of tr, pri = ~1}
              (fn () => command_exception tr1 st);
        in command_exception tr2 st end
      else command_exception tr st;
  in (Result (tr, st'), st') end;

fun element_result (Thy_Element.Element (tr, NONE)) st = atom_result tr st
  | element_result (elem as Thy_Element.Element (head_tr, SOME element_rest)) st =
      let
        val (head_result, st') = atom_result head_tr st;
        val (body_elems, end_tr) = element_rest;
        val estimate = timing_estimate elem;
      in
        if not (future_proofs_enabled estimate st')
        then
          let
            val proof_trs = maps Thy_Element.flat_element body_elems @ [end_tr];
            val (proof_results, st'') = fold_map atom_result proof_trs st';
          in (Result_List (head_result :: proof_results), st'') end
        else
          let
            val (end_tr1, end_tr2) = fork_presentation end_tr;

            val future_proof =
              Proof.future_proof (fn state =>
                Execution.fork {name = "Toplevel.future_proof", pos = pos_of head_tr, pri = ~1}
                  (fn () =>
                    let
                      val State ((Proof (prf, (_, orig_thy)), _), prev_thy) = st';
                      val finish = inherit_thy orig_thy o Context.Theory o Proof_Context.theory_of;
                      val node' = Proof (Proof_Node.apply (K state) prf, (finish, orig_thy));
                      val (results, result_state) =
                        State (node_presentation node', prev_thy)
                        |> fold_map element_result body_elems ||> command_exception end_tr1;
                    in (Result_List results, presentation_context0 result_state) end))
              #> (fn (res, state') => state' |> put_result (Result_Future res));

            val forked_proof =
              proof (future_proof #>
                (fn state => state |> Proof.local_done_proof |> put_result (get_result state))) o
              end_proof (future_proof #>
                (fn state => state |> Proof.global_done_proof |> Result.put (get_result state)));

            val st'' = st' |> command_exception (head_tr |> reset_trans |> forked_proof);
            val end_st = st'' |> command_exception end_tr2;
            val end_result = Result (end_tr, end_st);
            val result =
              Result_List [head_result, Result.get (presentation_context0 st''), end_result];
          in (result, end_st) end
      end;

end;

end;
