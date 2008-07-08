(*  Title:      Pure/Isar/isar.ML
    ID:         $Id$
    Author:     Makarius

The global Isabelle/Isar state and main read-eval-print loop.
*)

signature ISAR =
sig
  val state: unit -> Toplevel.state
  val exn: unit -> (exn * string) option
  val context: unit -> Proof.context
  val goal: unit -> thm
  val >> : Toplevel.transition -> bool
  val >>> : Toplevel.transition list -> unit
  val crashes: exn list ref
  val toplevel_loop: {init: bool, welcome: bool, sync: bool, secure: bool} -> unit
  val loop: unit -> unit
  val main: unit -> unit
end;

structure Isar: ISAR =
struct


(** individual toplevel commands **)

(* unique identification *)

type id = string;
val no_id : id = "";

fun identify tr =
  (case Toplevel.get_id tr of
    SOME id => (id, tr)
  | NONE =>
      let val id = "isabelle:" ^ serial_string ()
      in (id, Toplevel.put_id id tr) end);


(* command category *)

datatype category = Empty | BeginTheory of string | Theory | Proof | Other;

fun category_of tr =
  let val name = Toplevel.name_of tr in
    if name = "" then Empty
    else
      (case Toplevel.init_of tr of
        SOME thy_name => BeginTheory thy_name
      | NONE =>
          if OuterKeyword.is_theory name then Theory
          else if OuterKeyword.is_proof name then Proof
          else Other)
  end;


(* datatype command *)

datatype status =
  Initial |
  Final of Toplevel.state * (exn * string) option;

datatype command = Command of
 {category: category,
  transition: Toplevel.transition,
  status: status};

fun make_command (category, transition, status) =
  Command {category = category, transition = transition, status = status};

val empty_command =
  make_command (Empty, Toplevel.empty, Final (Toplevel.toplevel, NONE));

fun map_command f (Command {category, transition, status}) =
  make_command (f (category, transition, status));

fun map_status f = map_command (fn (category, transition, status) =>
  (category, transition, f status));


(* global collection of identified commands *)

local

val empty_commands = Graph.empty: command Graph.T;
val global_commands = ref empty_commands;

in

fun change_commands f = NAMED_CRITICAL "Isar" (fn () => change global_commands f)
  handle Graph.DUP id => sys_error ("Duplicate command id " ^ quote id)
    | Graph.UNDEF id => sys_error ("Unknown command id " ^ quote id);

fun init_commands () = change_commands (K empty_commands);

fun the_command id =
  if id = no_id then empty_command
  else Graph.get_node (! global_commands) id;

end;


fun the_state id =
  let val Command {transition, status, ...} = the_command id in
    (case status of
      Final res => res
    | _ => error ("Unfinished command " ^ Toplevel.str_of transition))
  end;

fun new_command prev (id, cmd) =
  change_commands (Graph.new_node (id, cmd) #> prev <> no_id ? Graph.add_edge (prev, id));

fun dispose_command id = change_commands (Graph.del_nodes [id]);

fun change_command_status id f = change_commands (Graph.map_node id (map_status f));



(** TTY interaction **)

(* global point *)

local val global_point = ref no_id in

fun change_point f = NAMED_CRITICAL "Isar" (fn () => change global_point f);

fun point_state () = NAMED_CRITICAL "Isar" (fn () =>
  let val id = ! global_point in (id, the_state id) end);

end;

fun init_point () = change_point (K no_id);

fun state () = #1 (#2 (point_state ()));
fun exn () = #2 (#2 (point_state ()));

fun context () =
  Toplevel.context_of (state ())
    handle Toplevel.UNDEF => error "Unknown context";

fun goal () =
  #2 (#2 (Proof.get_goal (Toplevel.proof_of (state ()))))
    handle Toplevel.UNDEF => error "No goal present";


(* interactive state transformations --- NOT THREAD-SAFE! *)

nonfix >> >>>;

fun >> raw_tr =
  let
    val (id, tr) = identify raw_tr;
    val (prev, (prev_state, _)) = point_state ();
    val category = category_of tr;
    val _ = new_command prev (id, make_command (category, tr, Initial));
  in
    (case Toplevel.transition true tr prev_state of
      NONE => (dispose_command id; false)
    | SOME result =>
        (change_command_status id (K (Final result));
          change_point (K id);
          (case #2 result of
            NONE => ()
          | SOME err => Toplevel.error_msg tr err);
          true))
  end;

fun >>> [] = ()
  | >>> (tr :: trs) = if >> tr then >>> trs else ();


(* toplevel loop *)

val crashes = ref ([]: exn list);

local

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
    val prev = #1 (point_state ());
    val prompt_markup =
      if prev = no_id then I
      else Markup.markup (Markup.properties [(Markup.idN, prev)] Markup.position);
  in
    (case Source.get_single (Source.set_prompt (prompt_markup Source.default_prompt) src) of
      NONE => if secure then quit () else ()
    | SOME (tr, src') => if >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn => (Output.error_msg (Toplevel.exn_message exn) handle crash =>
      (CRITICAL (fn () => change crashes (cons crash));
        warning "Recovering after Isar toplevel crash -- see also Isar.crashes");
      raw_loop secure src)
  end;

in

fun toplevel_loop {init, welcome, sync, secure} =
 (Context.set_thread_data NONE;
  if init then (init_point (); init_commands ()) else ();
  if welcome then writeln (Session.welcome ()) else ();
  uninterruptible (fn _ => fn () => raw_loop secure (OuterSyntax.isar sync)) ());

end;

fun loop () =
  toplevel_loop {init = false, welcome = false, sync = false, secure = Secure.is_secure ()};
fun main () =
  toplevel_loop {init = true, welcome = true, sync = false, secure = Secure.is_secure ()};

end;

