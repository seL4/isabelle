(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.

General format of process output:

  (a) unmarked stdout/stderr, no line structure (output should be
  processed immediately as it arrives)

  (b) properly marked-up messages, e.g. for writeln channel

  "\002A" ^ props ^ "\002,\n" ^ text ^ "\002.\n"

  where the props consist of name=value lines terminated by "\002,\n"
  each, and the remaining text is any number of lines (output is
  supposed to be processed in one piece).

  (c) Special init message holds "pid" and "session" property.
*)

signature ISABELLE_PROCESS =
sig
  val test_markupN: string
  val test_markup: Markup.T -> output * output
  val isabelle_processN: string
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* test_markup *)

val test_markupN = "test_markup";

fun test_markup (name, props) =
 (enclose "<" ">" (space_implode " " (name :: map XML.attribute props)),
  enclose "</" ">" name);

val _ = Markup.add_mode test_markupN test_markup;


(* symbol output *)

val isabelle_processN = "isabelle_process";

local

fun output str =
  let
    fun out s = if Symbol.is_raw s then Symbol.decode_raw s else XML.text s;
    val syms = Symbol.explode str;
  in (implode (map out syms), Symbol.length syms) end;

in

val _ = Output.add_mode isabelle_processN output Symbol.encode_raw;

end;


(* message markup *)

val STX = chr 2;
val DEL = chr 127;

fun special ch = STX ^ ch;
val special_sep = special ",";
val special_end = special ".";

local

fun print_props props =
  let
    val clean = translate_string (fn c =>
      if c = STX orelse c = "\n" orelse c = "\r" then DEL else c);
  in implode (map (fn (x, y) => clean x ^ "=" ^ clean y ^ special_sep ^ "\n") props) end;

fun get_pos (elem as XML.Elem (name, atts, ts)) =
      if name = Markup.positionN then SOME (Position.of_properties atts)
      else get_first get_pos ts
  | get_pos _ = NONE;

in

fun message ch markup raw_txt =
  let
    val (txt, pos) =
      (case try XML.tree_of_string (XML.element "message" [] [raw_txt]) of
        NONE => (raw_txt, Position.none)
      | SOME xml => (XML.plain_content xml, the_default Position.none (get_pos xml)))
      |>> translate_string (fn c => if c = STX then DEL else c);
    val props =
      (case Position.properties_of (Position.thread_data ()) of
        [] => Position.properties_of pos
      | props => props);
    val s = special ch ^ print_props props ^ Markup.enclose markup txt ^ special_end;
  in Output.writeln_default s end;

fun init_message () =
  let
    val pid = string_of_pid (Posix.ProcEnv.getpid ());
    val session = List.last (Session.id ()) handle List.Empty => "unknown";
    val welcome = Session.welcome ();
    val s = special "H" ^ print_props [("pid", pid), ("session", session)] ^ welcome ^ special_end;
  in Output.writeln_default s end;

end;


(* channels *)

fun setup_channels () =
 (Output.writeln_fn  := message "A" Markup.writeln;
  Output.priority_fn := message "B" Markup.priority;
  Output.tracing_fn  := message "C" Markup.tracing;
  Output.warning_fn  := message "D" Markup.warning;
  Output.error_fn    := message "E" Markup.error;
  Output.debug_fn    := message "F" Markup.debug);

val _ = Markup.add_mode isabelle_processN (fn (name, props) =>
  if name = Markup.promptN then (special "G", special_end ^ "\n")
  else if name = Markup.positionN then test_markup (name, props)
  else ("", ""));


(* init *)

fun init () =
 (change print_mode (update (op =) isabelle_processN);
  setup_channels ();
  init_message ();
  Isar.secure_main ());

end;

