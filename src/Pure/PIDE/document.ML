(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, with asynchronous read/eval/print processes.
*)

signature DOCUMENT =
sig
  type id = int
  type version_id = id
  type command_id = id
  type exec_id = id
  val no_id: id
  val new_id: unit -> id
  val parse_id: string -> id
  val print_id: id -> string
  type node_header = ((string * string) * string list * (string * bool) list) Exn.result
  datatype node_edit =
    Clear |
    Edits of (command_id option * command_id option) list |
    Header of node_header |
    Perspective of command_id list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_command: command_id -> string -> string -> state -> state
  val cancel_execution: state -> Future.task list
  val update_perspective: version_id -> version_id -> string -> command_id list -> state -> state
  val update: version_id -> version_id -> edit list -> state ->
    ((command_id * exec_id option) list * (string * command_id option) list) * state
  val execute: version_id -> state -> state
  val remove_versions: version_id list -> state -> state
  val state: unit -> state
  val change_state: (state -> state) -> unit
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type id = int;
type version_id = id;
type command_id = id;
type exec_id = id;

val no_id = 0;
val new_id = Synchronized.counter ();

val parse_id = Markup.parse_int;
val print_id = Markup.print_int;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ print_id id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ print_id id);



(** document structure **)

type node_header = ((string * string) * string list * (string * bool) list) Exn.result;
type perspective = (command_id -> bool) * command_id option; (*visible commands, last*)
structure Entries = Linear_Set(type key = command_id val ord = int_ord);

type exec = exec_id * (Toplevel.state * unit lazy) lazy;  (*eval/print process*)
val no_print = Lazy.value ();
val no_exec = (no_id, Lazy.value (Toplevel.toplevel, no_print));

abstype node = Node of
 {touched: bool,
  header: node_header,
  perspective: perspective,
  entries: exec option Entries.T,  (*command entries with excecutions*)
  last_exec: command_id option,  (*last command with exec state assignment*)
  result: Toplevel.state lazy}
and version = Version of node Graph.T  (*development graph wrt. static imports*)
with

fun make_node (touched, header, perspective, entries, last_exec, result) =
  Node {touched = touched, header = header, perspective = perspective,
    entries = entries, last_exec = last_exec, result = result};

fun map_node f (Node {touched, header, perspective, entries, last_exec, result}) =
  make_node (f (touched, header, perspective, entries, last_exec, result));

fun make_perspective command_ids : perspective =
  (Inttab.defined (Inttab.make (map (rpair ()) command_ids)), try List.last command_ids);

val no_header = Exn.Exn (ERROR "Bad theory header");
val no_perspective = make_perspective [];
val no_result = Lazy.value Toplevel.toplevel;

val empty_node = make_node (false, no_header, no_perspective, Entries.empty, NONE, no_result);
val clear_node = map_node (fn (_, header, _, _, _, _) =>
  (false, header, no_perspective, Entries.empty, NONE, no_result));


(* basic components *)

fun is_touched (Node {touched, ...}) = touched;
fun set_touched touched =
  map_node (fn (_, header, perspective, entries, last_exec, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_header (Node {header, ...}) = header;
fun set_header header =
  map_node (fn (touched, _, perspective, entries, last_exec, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_perspective (Node {perspective, ...}) = perspective;
fun set_perspective ids =
  map_node (fn (touched, header, _, entries, last_exec, result) =>
    (touched, header, make_perspective ids, entries, last_exec, result));

fun map_entries f =
  map_node (fn (touched, header, perspective, entries, last_exec, result) =>
    (touched, header, perspective, f entries, last_exec, result));
fun get_entries (Node {entries, ...}) = entries;

fun iterate_entries f = Entries.iterate NONE f o get_entries;
fun iterate_entries_after start f (Node {entries, ...}) =
  (case Entries.get_after entries start of
    NONE => I
  | SOME id => Entries.iterate (SOME id) f entries);

fun get_last_exec (Node {last_exec, ...}) = last_exec;
fun set_last_exec last_exec =
  map_node (fn (touched, header, perspective, entries, _, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_theory pos (Node {result, ...}) = Toplevel.end_theory pos (Lazy.force result);
fun set_result result =
  map_node (fn (touched, header, perspective, entries, last_exec, _) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_node nodes name = Graph.get_node nodes name handle Graph.UNDEF _ => empty_node;
fun default_node name = Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> Graph.map_node name f;


(* node edits and associated executions *)

datatype node_edit =
  Clear |
  Edits of (command_id option * command_id option) list |
  Header of node_header |
  Perspective of command_id list;

type edit = string * node_edit;

fun after_entry (Node {entries, ...}) = Entries.get_after entries;

fun lookup_entry (Node {entries, ...}) id =
  (case Entries.lookup entries id of
    NONE => NONE
  | SOME (exec, _) => exec);

fun the_entry (Node {entries, ...}) id =
  (case Entries.lookup entries id of
    NONE => err_undef "command entry" id
  | SOME (exec, _) => exec);

fun the_default_entry node (SOME id) = (id, (the_default no_exec (the_entry node id)))
  | the_default_entry _ NONE = (no_id, no_exec);

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

val empty_version = Version Graph.empty;

fun nodes_of (Version nodes) = nodes;
val node_of = get_node o nodes_of;

local

fun cycle_msg names = "Cyclic dependency of " ^ space_implode " via " (map quote names);

fun touch_node name nodes =
  fold (fn desc =>
      update_node desc
        (set_touched true #>
          desc <> name ? (map_entries (reset_after NONE) #> set_result no_result)))
    (Graph.all_succs nodes [name]) nodes;

in

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (case node_edit of
      Clear =>
        nodes
        |> update_node name clear_node
        |> touch_node name
    | Edits edits =>
        nodes
        |> update_node name (edit_node edits)
        |> touch_node name
    | Header header =>
        let
          val imports = (case header of Exn.Res (_, imports, _) => imports | _ => []);
          val nodes1 = nodes
            |> default_node name
            |> fold default_node imports;
          val nodes2 = nodes1
            |> Graph.Keys.fold
                (fn dep => Graph.del_edge (dep, name)) (Graph.imm_preds nodes1 name);
          val (header', nodes3) =
            (header, Graph.add_deps_acyclic (name, imports) nodes2)
              handle Graph.CYCLES cs => (Exn.Exn (ERROR (cat_lines (map cycle_msg cs))), nodes2);
        in Graph.map_node name (set_header header') nodes3 end
        |> touch_node name
    | Perspective perspective =>
        update_node name (set_perspective perspective) nodes);

end;

fun put_node (name, node) (Version nodes) =
  Version (update_node name (K node) nodes);

end;



(** global state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands: (string * Toplevel.transition future) Inttab.table,  (*command_id -> name * transition*)
  execution: version_id * Future.group}  (*current execution process*)
with

fun make_state (versions, commands, execution) =
  State {versions = versions, commands = commands, execution = execution};

fun map_state f (State {versions, commands, execution}) =
  make_state (f (versions, commands, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)], Inttab.empty, (no_id, Future.new_group NONE));


(* document versions *)

fun define_version (id: version_id) version =
  map_state (fn (versions, commands, execution) =>
    let val versions' = Inttab.update_new (id, version) versions
      handle Inttab.DUP dup => err_dup "document version" dup
    in (versions', commands, execution) end);

fun the_version (State {versions, ...}) (id: version_id) =
  (case Inttab.lookup versions id of
    NONE => err_undef "document version" id
  | SOME version => version);

fun delete_version (id: version_id) versions = Inttab.delete id versions
  handle Inttab.UNDEF _ => err_undef "document version" id;


(* commands *)

fun define_command (id: command_id) name text =
  map_state (fn (versions, commands, execution) =>
    let
      val id_string = print_id id;
      val future =
        (singleton o Future.forks)
          {name = "Document.define_command", group = SOME (Future.new_group NONE),
            deps = [], pri = ~1, interrupts = false}
          (fn () =>
            Position.setmp_thread_data (Position.id_only id_string)
              (fn () => Outer_Syntax.read_command (Position.id id_string) text) ());
      val commands' =
        Inttab.update_new (id, (name, future)) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME command => command);


(* document execution *)

fun cancel_execution (State {execution, ...}) = Future.cancel_group (#2 execution);

end;



(* toplevel transactions *)

local

fun timing tr t =
  if Timing.is_relevant t then Toplevel.status tr (Isabelle_Markup.timing t) else ();

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => Toplevel.status tr (Proof.status_markup prf)
  | NONE => ());

fun print_state tr st =
  (Lazy.lazy o Toplevel.setmp_thread_position tr)
    (fn () => Toplevel.print_state false st);

fun run int tr st =
  (case Toplevel.transition int tr st of
    SOME (st', NONE) => ([], SOME st')
  | SOME (_, SOME (exn, _)) => (ML_Compiler.exn_messages exn, NONE)
  | NONE => ([(serial (), ML_Compiler.exn_message Runtime.TERMINATE)], NONE));

in

fun run_command tr st =
  let
    val is_init = Toplevel.is_init tr;
    val is_proof = Keyword.is_proof (Toplevel.name_of tr);

    val _ = Multithreading.interrupted ();
    val _ = Toplevel.status tr Isabelle_Markup.forked;
    val start = Timing.start ();
    val (errs, result) = run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
    val _ = timing tr (Timing.result start);
    val _ = Toplevel.status tr Isabelle_Markup.joined;
    val _ = List.app (Toplevel.error_msg tr) errs;
  in
    (case result of
      NONE =>
        let
          val _ = if null errs then Exn.interrupt () else ();
          val _ = Toplevel.status tr Isabelle_Markup.failed;
        in (st, no_print) end
    | SOME st' =>
        let
          val _ = Toplevel.status tr Isabelle_Markup.finished;
          val _ = proof_status tr st';
          val do_print =
            not is_init andalso
              (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof st'));
        in (st', if do_print then print_state tr st' else no_print) end)
  end;

end;




(** update **)

(* perspective *)

fun update_perspective (old_id: version_id) (new_id: version_id) name perspective state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 -- needed? *)
    val new_version = edit_nodes (name, Perspective perspective) old_version;
  in define_version new_id new_version state end;


(* edits *)

local

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
    fun get_common ((prev, id), exec) (found, (_, flags)) =
      if found then NONE
      else
        let val found' =
          is_none exec orelse op <> (pairself (Option.map #1) (exec, lookup_entry node0 id));
        in SOME (found', (prev, update_flags prev flags)) end;
    val (found, (common, flags)) =
      iterate_entries get_common node (false, (NONE, (true, true)));
  in
    if found then (common, flags)
    else
      let val last = Entries.get_after (get_entries node) common
      in (last, update_flags last flags) end
  end;

fun illegal_init () = error "Illegal theory header after end of theory";

fun new_exec state bad_init command_id' (execs, command_exec, init) =
  if bad_init andalso is_none init then NONE
  else
    let
      val (name, tr0) = the_command state command_id' ||> Future.join;
      val (modify_init, init') =
        if Keyword.is_theory_begin name then
          (Toplevel.modify_init (the_default illegal_init init), NONE)
        else (I, init);
      val exec_id' = new_id ();
      val tr = tr0
        |> modify_init
        |> Toplevel.put_id (print_id exec_id');
      val exec' = snd (snd command_exec) |> Lazy.map (fn (st, _) => run_command tr st);
      val command_exec' = (command_id', (exec_id', exec'));
    in SOME (command_exec' :: execs, command_exec', init') end;

fun make_required nodes =
  let
    val all_visible =
      Graph.fold (fn (a, (node, _)) => is_some (#2 (get_perspective node)) ? cons a) nodes []
      |> Graph.all_preds nodes;
    val required =
      fold (fn a => exists (fn b => Graph.is_edge nodes (a, b)) all_visible ? Symtab.update (a, ()))
        all_visible Symtab.empty;
  in Symtab.defined required end;

fun check_theory nodes name =
  is_some (Thy_Info.lookup_theory name) orelse  (* FIXME more robust!? *)
  is_some (Exn.get_res (get_header (get_node nodes name)));

fun init_theory deps node =
  let
    (* FIXME provide files via Scala layer, not master_dir *)
    val ((master_dir, thy_name), imports, uses) = Exn.release (get_header node);
    val files = map (apfst Path.explode) uses;
    val parents =
      imports |> map (fn import =>
        (case Thy_Info.lookup_theory import of  (* FIXME more robust!? *)
          SOME thy => thy
        | NONE =>
            get_theory (Position.file_only import)
              (snd (Future.join (the (AList.lookup (op =) deps import))))));
  in Thy_Load.begin_theory (Path.explode master_dir) thy_name imports files parents end;

in

fun update (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 *)
    val new_version = fold edit_nodes edits old_version;

    val nodes = nodes_of new_version;
    val is_required = make_required nodes;

    val updated =
      nodes |> Graph.schedule
        (fn deps => fn (name, node) =>
          if not (is_touched node orelse is_required name)
          then Future.value (([], [], []), node)
          else
            let
              val node0 = node_of old_version name;
              fun init () = init_theory deps node;
              val bad_init =
                not (check_theory nodes name andalso forall (check_theory nodes o #1) deps);
            in
              (singleton o Future.forks)
                {name = "Document.update", group = NONE,
                  deps = map (Future.task_of o #2) deps, pri = 0, interrupts = false}
                (fn () =>
                  let
                    val required = is_required name;
                    val last_visible = #2 (get_perspective node);
                    val (common, (visible, initial)) = last_common state last_visible node0 node;
                    val common_command_exec = the_default_entry node common;

                    val (execs, (command_id, (_, exec)), _) =
                      ([], common_command_exec, if initial then SOME init else NONE) |>
                      (visible orelse required) ?
                        iterate_entries_after common
                          (fn ((prev, id), _) => fn res =>
                            if not required andalso prev = last_visible then NONE
                            else new_exec state bad_init id res) node;

                    val no_execs =
                      iterate_entries_after common
                        (fn ((_, id0), exec0) => fn res =>
                          if is_none exec0 then NONE
                          else if exists (fn (_, (id, _)) => id0 = id) execs then SOME res
                          else SOME (id0 :: res)) node0 [];

                    val last_exec = if command_id = no_id then NONE else SOME command_id;
                    val result =
                      if is_some (after_entry node last_exec) then no_result
                      else Lazy.map #1 exec;

                    val node' = node
                      |> fold reset_entry no_execs
                      |> fold (fn (id, exec) => update_entry id (SOME exec)) execs
                      |> set_last_exec last_exec
                      |> set_result result
                      |> set_touched false;
                  in ((no_execs, execs, [(name, node')]), node') end)
            end)
      |> Future.joins |> map #1;

    val command_execs =
      map (rpair NONE) (maps #1 updated) @
      map (fn (command_id, (exec_id, _)) => (command_id, SOME exec_id)) (maps #2 updated);
    val updated_nodes = maps #3 updated;
    val last_execs = map (fn (name, node) => (name, get_last_exec node)) updated_nodes;

    val state' = state
      |> define_version new_id (fold put_node updated_nodes new_version);
  in ((command_execs, last_execs), state') end;

end;


(* execute *)

fun execute version_id state =
  state |> map_state (fn (versions, commands, _) =>
    let
      val version = the_version state version_id;

      fun force_exec _ _ NONE = ()
        | force_exec node command_id (SOME (_, exec)) =
            let
              val (_, print) = Lazy.force exec;
              val _ =
                if #1 (get_perspective node) command_id
                then ignore (Lazy.future Future.default_params print)
                else ();
            in () end;

      val group = Future.new_group NONE;
      val _ =
        nodes_of version |> Graph.schedule
          (fn deps => fn (name, node) =>
            (singleton o Future.forks)
              {name = "theory:" ^ name, group = SOME (Future.new_group (SOME group)),
                deps = map (Future.task_of o #2) deps, pri = 1, interrupts = false}
              (iterate_entries (fn ((_, id), exec) => fn () =>
                SOME (force_exec node id exec)) node));

    in (versions, commands, (version_id, group)) end);


(* remove versions *)

fun remove_versions ids state = state |> map_state (fn (versions, _, execution) =>
  let
    val _ = member (op =) ids (#1 execution) andalso
      error ("Attempt to remove execution version " ^ print_id (#1 execution));

    val versions' = fold delete_version ids versions;
    val commands' =
      (versions', Inttab.empty) |->
        Inttab.fold (fn (_, version) => nodes_of version |>
          Graph.fold (fn (_, (node, _)) => node |>
            iterate_entries (fn ((_, id), _) =>
              SOME o Inttab.insert (K true) (id, the_command state id))));
  in (versions', commands', execution) end);



(** global state **)

val global_state = Synchronized.var "Document" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;

