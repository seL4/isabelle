(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, with asynchronous read/eval/print processes.
*)

signature DOCUMENT =
sig
  type node_header = string * Thy_Header.header * string list
  datatype node_edit =
    Clear |    (* FIXME unused !? *)
    Edits of (Document_ID.command option * Document_ID.command option) list |
    Deps of node_header |
    Perspective of Document_ID.command list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_command: Document_ID.command -> string -> string -> state -> state
  val remove_versions: Document_ID.version list -> state -> state
  val discontinue_execution: state -> unit
  val cancel_execution: state -> unit
  val start_execution: state -> unit
  val timing: bool Unsynchronized.ref
  val update: Document_ID.version -> Document_ID.version -> edit list -> state ->
    (Document_ID.command * Document_ID.exec list) list * state
  val state: unit -> state
  val change_state: (state -> state) -> unit
end;

structure Document: DOCUMENT =
struct

(* command execution *)

type exec = Document_ID.exec * (Command.eval * Command.print list);  (*eval/print process*)
val no_exec: exec = (Document_ID.none, (Command.no_eval, []));

fun exec_ids_of ((exec_id, (_, prints)): exec) = exec_id :: map #exec_id prints;

fun exec_result ((_, (eval, _)): exec) = Command.memo_result eval;

fun exec_run ((_, (eval, prints)): exec) =
 (Command.memo_eval eval;
  prints |> List.app (fn {name, pri, print, ...} =>
    Command.memo_fork {name = name, group = NONE, deps = [], pri = pri, interrupts = true} print));



(** document structure **)

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ Document_ID.print id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ Document_ID.print id);

type node_header = string * Thy_Header.header * string list;
type perspective = Inttab.set * Document_ID.command option;
structure Entries = Linear_Set(type key = Document_ID.command val ord = int_ord);

abstype node = Node of
 {header: node_header,  (*master directory, theory header, errors*)
  perspective: perspective,  (*visible commands, last visible command*)
  entries: exec option Entries.T * bool,  (*command entries with excecutions, stable*)
  result: Command.eval option}  (*result of last execution*)
and version = Version of node String_Graph.T  (*development graph wrt. static imports*)
with

fun make_node (header, perspective, entries, result) =
  Node {header = header, perspective = perspective, entries = entries, result = result};

fun map_node f (Node {header, perspective, entries, result}) =
  make_node (f (header, perspective, entries, result));

fun make_perspective command_ids : perspective =
  (Inttab.make_set command_ids, try List.last command_ids);

val no_header = ("", Thy_Header.make ("", Position.none) [] [], ["Bad theory header"]);
val no_perspective = make_perspective [];

val empty_node = make_node (no_header, no_perspective, (Entries.empty, true), NONE);
val clear_node =
  map_node (fn (header, _, _, _) => (header, no_perspective, (Entries.empty, true), NONE));


(* basic components *)

fun set_header header =
  map_node (fn (_, perspective, entries, result) => (header, perspective, entries, result));

fun get_header (Node {header = (master, header, errors), ...}) =
  if null errors then (master, header)
  else error (cat_lines errors);

fun read_header node span =
  let
    val (dir, {name = (name, _), imports, keywords}) = get_header node;
    val {name = (_, pos), imports = imports', ...} = Thy_Header.read_tokens span;
  in (dir, Thy_Header.make (name, pos) (map #1 imports ~~ map #2 imports') keywords) end;

fun get_perspective (Node {perspective, ...}) = perspective;
fun set_perspective ids =
  map_node (fn (header, _, entries, result) => (header, make_perspective ids, entries, result));

val visible_commands = #1 o get_perspective;
val visible_last = #2 o get_perspective;
val visible_node = is_some o visible_last

fun map_entries f =
  map_node (fn (header, perspective, (entries, stable), result) =>
    (header, perspective, (f entries, stable), result));
fun get_entries (Node {entries = (entries, _), ...}) = entries;

fun entries_stable stable =
  map_node (fn (header, perspective, (entries, _), result) =>
    (header, perspective, (entries, stable), result));
fun stable_entries (Node {entries = (_, stable), ...}) = stable;

fun iterate_entries f = Entries.iterate NONE f o get_entries;
fun iterate_entries_after start f (Node {entries = (entries, _), ...}) =
  (case Entries.get_after entries start of
    NONE => I
  | SOME id => Entries.iterate (SOME id) f entries);

fun get_result (Node {result, ...}) = result;
fun set_result result =
  map_node (fn (header, perspective, entries, _) => (header, perspective, entries, result));

fun get_node nodes name = String_Graph.get_node nodes name
  handle String_Graph.UNDEF _ => empty_node;
fun default_node name = String_Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> String_Graph.map_node name f;


(* node edits and associated executions *)

datatype node_edit =
  Clear |
  Edits of (Document_ID.command option * Document_ID.command option) list |
  Deps of node_header |
  Perspective of Document_ID.command list;

type edit = string * node_edit;

val after_entry = Entries.get_after o get_entries;

fun lookup_entry node id =
  (case Entries.lookup (get_entries node) id of
    NONE => NONE
  | SOME (exec, _) => exec);

fun the_entry node id =
  (case Entries.lookup (get_entries node) id of
    NONE => err_undef "command entry" id
  | SOME (exec, _) => exec);

fun the_default_entry node (SOME id) = (id, the_default no_exec (the_entry node id))
  | the_default_entry _ NONE = (Document_ID.none, no_exec);

fun update_entry id exec =
  map_entries (Entries.update (id, exec));

fun reset_entry id node =
  if is_some (lookup_entry node id) then update_entry id NONE node else node;

fun reset_after id entries =
  (case Entries.get_after entries id of
    NONE => entries
  | SOME next => Entries.update (next, NONE) entries);

val edit_node = map_entries o fold
  (fn (id, SOME id2) => Entries.insert_after id (id2, NONE)
    | (id, NONE) => Entries.delete_after id #> reset_after id);


(* version operations *)

val empty_version = Version String_Graph.empty;

fun nodes_of (Version nodes) = nodes;
val node_of = get_node o nodes_of;

fun cycle_msg names = "Cyclic dependency of " ^ space_implode " via " (map quote names);

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (case node_edit of
      Clear => update_node name clear_node nodes
    | Edits edits => update_node name (edit_node edits) nodes
    | Deps (master, header, errors) =>
        let
          val imports = map fst (#imports header);
          val errors1 =
            (Thy_Header.define_keywords header; errors)
              handle ERROR msg => errors @ [msg];
          val nodes1 = nodes
            |> default_node name
            |> fold default_node imports;
          val nodes2 = nodes1
            |> String_Graph.Keys.fold
                (fn dep => String_Graph.del_edge (dep, name)) (String_Graph.imm_preds nodes1 name);
          val (nodes3, errors2) =
            (String_Graph.add_deps_acyclic (name, imports) nodes2, errors1)
              handle String_Graph.CYCLES cs => (nodes2, errors1 @ map cycle_msg cs);
        in String_Graph.map_node name (set_header (master, header, errors2)) nodes3 end
    | Perspective perspective => update_node name (set_perspective perspective) nodes);

fun put_node (name, node) (Version nodes) =
  Version (update_node name (K node) nodes);

end;



(** main state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands: (string * Token.T list lazy) Inttab.table,  (*command_id -> named span*)
  execution:
    Document_ID.version * Future.group * bool Unsynchronized.ref}  (*current execution process*)
with

fun make_state (versions, commands, execution) =
  State {versions = versions, commands = commands, execution = execution};

fun map_state f (State {versions, commands, execution}) =
  make_state (f (versions, commands, execution));

val init_state =
  make_state (Inttab.make [(Document_ID.none, empty_version)], Inttab.empty,
    (Document_ID.none, Future.new_group NONE, Unsynchronized.ref false));

fun execution_of (State {execution, ...}) = execution;


(* document versions *)

fun define_version (id: Document_ID.version) version =
  map_state (fn (versions, commands, _) =>
    let
      val versions' = Inttab.update_new (id, version) versions
        handle Inttab.DUP dup => err_dup "document version" dup;
      val execution' = (id, Future.new_group NONE, Unsynchronized.ref true);
    in (versions', commands, execution') end);

fun the_version (State {versions, ...}) (id: Document_ID.version) =
  (case Inttab.lookup versions id of
    NONE => err_undef "document version" id
  | SOME version => version);

fun delete_version (id: Document_ID.version) versions = Inttab.delete id versions
  handle Inttab.UNDEF _ => err_undef "document version" id;


(* commands *)

fun define_command (id: Document_ID.command) name text =
  map_state (fn (versions, commands, execution) =>
    let
      val id_string = Document_ID.print id;
      val span = Lazy.lazy (fn () =>
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Thy_Syntax.parse_tokens (Keyword.get_lexicons ()) (Position.id id_string) text)
            ());
      val _ =
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Output.status (Markup.markup_only Markup.accepted)) ();
      val commands' =
        Inttab.update_new (id, (name, span)) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execution) end);

fun the_command (State {commands, ...}) (id: Document_ID.command) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME command => command);

end;

fun remove_versions ids state = state |> map_state (fn (versions, _, execution) =>
  let
    val _ = member (op =) ids (#1 execution) andalso
      error ("Attempt to remove execution version " ^ Document_ID.print (#1 execution));

    val versions' = fold delete_version ids versions;
    val commands' =
      (versions', Inttab.empty) |->
        Inttab.fold (fn (_, version) => nodes_of version |>
          String_Graph.fold (fn (_, (node, _)) => node |>
            iterate_entries (fn ((_, id), _) =>
              SOME o Inttab.insert (K true) (id, the_command state id))));
  in (versions', commands', execution) end);


(* consolidated states *)

fun stable_goals exec_id =
  not (Par_Exn.is_interrupted (Future.join_results (Goal.peek_futures exec_id)));

fun stable_eval ((exec_id, (eval, _)): exec) =
  stable_goals exec_id andalso Command.memo_stable eval;

fun stable_print ({exec_id, print, ...}: Command.print) =
  stable_goals exec_id andalso Command.memo_stable print;

fun finished_theory node =
  (case Exn.capture (Command.memo_result o the) (get_result node) of
    Exn.Res {state = st, ...} => can (Toplevel.end_theory Position.none) st
  | _ => false);



(** document execution **)

val discontinue_execution = execution_of #> (fn (_, _, running) => running := false);
val cancel_execution = execution_of #> (fn (_, group, _) => Future.cancel_group group);
val terminate_execution = execution_of #> (fn (_, group, _) => Future.terminate group);

fun start_execution state =
  let
    val (version_id, group, running) = execution_of state;
    val _ =
      (singleton o Future.forks)
        {name = "Document.execution", group = SOME group, deps = [], pri = ~2, interrupts = true}
        (fn () =>
         (OS.Process.sleep (seconds 0.02);
          nodes_of (the_version state version_id) |> String_Graph.schedule
            (fn deps => fn (name, node) =>
              if not (visible_node node) andalso finished_theory node then
                Future.value ()
              else
                (singleton o Future.forks)
                  {name = "theory:" ^ name, group = SOME (Future.new_group (SOME group)),
                    deps = map (Future.task_of o #2) deps, pri = ~2, interrupts = false}
                  (fn () =>
                    iterate_entries (fn (_, opt_exec) => fn () =>
                      (case opt_exec of
                        SOME exec => if ! running then SOME (exec_run exec) else NONE
                      | NONE => NONE)) node ()))));
  in () end;



(** document update **)

val timing = Unsynchronized.ref false;
fun timeit msg e = cond_timeit (! timing) msg e;

local

fun make_required nodes =
  let
    val all_visible =
      String_Graph.fold (fn (a, (node, _)) => visible_node node ? cons a) nodes []
      |> String_Graph.all_preds nodes
      |> map (rpair ()) |> Symtab.make;

    val required =
      Symtab.fold (fn (a, ()) =>
        exists (Symtab.defined all_visible) (String_Graph.immediate_succs nodes a) ?
          Symtab.update (a, ())) all_visible Symtab.empty;
  in Symtab.defined required end;

fun init_theory deps node span =
  let
    (* FIXME provide files via Isabelle/Scala, not master_dir *)
    val (dir, header) = read_header node span;
    val master_dir =
      (case try Url.explode dir of
        SOME (Url.File path) => path
      | _ => Path.current);
    val imports = #imports header;
    val parents =
      imports |> map (fn (import, _) =>
        (case Thy_Info.lookup_theory import of
          SOME thy => thy
        | NONE =>
            Toplevel.end_theory (Position.file_only import)
              (#state
                (Command.memo_result
                  (the_default Command.no_eval
                    (get_result (snd (the (AList.lookup (op =) deps import)))))))));
    val _ = Position.reports (map #2 imports ~~ map Theory.get_markup parents);
  in Thy_Load.begin_theory master_dir header parents end;

fun check_theory full name node =
  is_some (Thy_Info.lookup_theory name) orelse
  can get_header node andalso (not full orelse is_some (get_result node));

fun last_common state last_visible node0 node =
  let
    fun update_flags prev (visible, initial) =
      let
        val visible' = visible andalso prev <> last_visible;
        val initial' = initial andalso
          (case prev of
            NONE => true
          | SOME id => not (Keyword.is_theory_begin (#1 (the_command state id))));
      in (visible', initial') end;
    fun get_common ((prev, id), opt_exec) (same, (_, flags)) =
      if same then
        let
          val flags' = update_flags prev flags;
          val same' =
            (case opt_exec of
              NONE => false
            | SOME (exec_id, exec) =>
                (case lookup_entry node0 id of
                  NONE => false
                | SOME (exec_id0, _) => exec_id = exec_id0 andalso stable_eval (exec_id, exec)));
        in SOME (same', (prev, flags')) end
      else NONE;
    val (same, (common, flags)) =
      iterate_entries get_common node (true, (NONE, (true, true)));
  in
    if same then
      let val last = Entries.get_after (get_entries node) common
      in (last, update_flags last flags) end
    else (common, flags)
  end;

fun new_exec state proper_init command_visible command_id' (execs, command_exec, init) =
  if not proper_init andalso is_none init then NONE
  else
    let
      val (command_name, span) = the_command state command_id' ||> Lazy.force;

      fun illegal_init _ = error "Illegal theory header after end of theory";
      val (modify_init, init') =
        if Keyword.is_theory_begin command_name then
          (Toplevel.modify_init (fn () => the_default illegal_init init span), NONE)
        else (I, init);

      val exec_id' = Document_ID.make ();
      val eval' =
        Command.memo (fn () =>
          let
            val eval_state = exec_result (snd command_exec);
            val tr =
              Position.setmp_thread_data (Position.id_only (Document_ID.print exec_id'))
                (fn () =>
                  Command.read span
                  |> modify_init
                  |> Toplevel.put_id exec_id') ();
          in Command.eval span tr eval_state end);
      val prints' = if command_visible then Command.print command_name eval' else [];
      val command_exec' = (command_id', (exec_id', (eval', prints')));
    in SOME (command_exec' :: execs, command_exec', init') end;

fun update_prints state node command_id =
  (case the_entry node command_id of
    SOME (exec_id, (eval, prints)) =>
      let
        val (command_name, _) = the_command state command_id;
        val new_prints = Command.print command_name eval;
        val prints' =
          new_prints |> map (fn new_print =>
            (case find_first (fn {name, ...} => name = #name new_print) prints of
              SOME print => if stable_print print then print else new_print
            | NONE => new_print));
      in
        if eq_list (op = o pairself #exec_id) (prints, prints') then NONE
        else SOME (command_id, (exec_id, (eval, prints')))
      end
  | NONE => NONE);

in

fun update (old_id: Document_ID.version) (new_id: Document_ID.version) edits state =
  let
    val old_version = the_version state old_id;
    val new_version = timeit "Document.edit_nodes" (fn () => fold edit_nodes edits old_version);

    val nodes = nodes_of new_version;
    val is_required = make_required nodes;

    val _ = timeit "Document.terminate_execution" (fn () => terminate_execution state);
    val updated = timeit "Document.update" (fn () =>
      nodes |> String_Graph.schedule
        (fn deps => fn (name, node) =>
          (singleton o Future.forks)
            {name = "Document.update", group = NONE,
              deps = map (Future.task_of o #2) deps, pri = 0, interrupts = false}
            (fn () =>
              let
                val imports = map (apsnd Future.join) deps;
                val changed_imports = exists (#4 o #1 o #2) imports;
                val node_required = is_required name;
              in
                if changed_imports orelse AList.defined (op =) edits name orelse
                  not (stable_entries node) orelse not (finished_theory node)
                then
                  let
                    val node0 = node_of old_version name;
                    val init = init_theory imports node;
                    val proper_init =
                      check_theory false name node andalso
                      forall (fn (name, (_, node)) => check_theory true name node) imports;

                    val visible_commands = visible_commands node;
                    val visible_command = Inttab.defined visible_commands;
                    val last_visible = visible_last node;

                    val (common, (still_visible, initial)) =
                      if changed_imports then (NONE, (true, true))
                      else last_common state last_visible node0 node;
                    val common_command_exec = the_default_entry node common;

                    val (new_execs, (command_id', (_, (eval', _))), _) =
                      ([], common_command_exec, if initial then SOME init else NONE) |>
                      (still_visible orelse node_required) ?
                        iterate_entries_after common
                          (fn ((prev, id), _) => fn res =>
                            if not node_required andalso prev = last_visible then NONE
                            else new_exec state proper_init (visible_command id) id res) node;

                    val updated_execs =
                      (visible_commands, new_execs) |-> Inttab.fold (fn (id, ()) =>
                        if exists (fn (_, (id', _)) => id = id') new_execs then I
                        else append (the_list (update_prints state node id)));

                    val no_execs =
                      iterate_entries_after common
                        (fn ((_, id0), exec0) => fn res =>
                          if is_none exec0 then NONE
                          else if exists (fn (_, (id, _)) => id0 = id) updated_execs
                          then SOME res
                          else SOME (id0 :: res)) node0 [];

                    val last_exec =
                      if command_id' = Document_ID.none then NONE else SOME command_id';
                    val result =
                      if is_some (after_entry node last_exec) then NONE
                      else SOME eval';

                    val node' = node
                      |> fold reset_entry no_execs
                      |> fold (fn (id, exec) => update_entry id (SOME exec)) updated_execs
                      |> entries_stable (null updated_execs)
                      |> set_result result;
                    val updated_node =
                      if null no_execs andalso null updated_execs then NONE
                      else SOME (name, node');
                    val changed_result = not (null no_execs) orelse not (null new_execs);
                  in ((no_execs, updated_execs, updated_node, changed_result), node') end
                else (([], [], NONE, false), node)
              end))
      |> Future.joins |> map #1);

    val command_execs =
      map (rpair []) (maps #1 updated) @
      map (fn (command_id, exec) => (command_id, exec_ids_of exec)) (maps #2 updated);
    val updated_nodes = map_filter #3 updated;

    val state' = state
      |> define_version new_id (fold put_node updated_nodes new_version);
  in (command_execs, state') end;

end;



(** global state **)

val global_state = Synchronized.var "Document.global_state" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;

