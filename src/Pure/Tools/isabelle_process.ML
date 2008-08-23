(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.

General format of process output:

  (a) unmarked stdout/stderr, no line structure (output should be
  processed immediately as it arrives);

  (b) properly marked-up messages, e.g. for writeln channel

  "\002A" ^ props ^ "\002,\n" ^ text ^ "\002.\n"

  where the props consist of name=value lines terminated by "\002,\n"
  each, and the remaining text is any number of lines (output is
  supposed to be processed in one piece);

  (c) special init message holds "pid" and "session" property.
*)

signature ISABELLE_PROCESS =
sig
  val isabelle_processN: string
  val xmlN: string
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* print modes *)

val isabelle_processN = "isabelle_process";
val xmlN = "XML";

val _ = Output.add_mode isabelle_processN Output.default_output Output.default_escape;
val _ = Markup.add_mode isabelle_processN (YXML.output_markup);


(* message markup *)

fun special ch = Symbol.STX ^ ch;
val special_sep = special ",";
val special_end = special ".";

local

fun clean_string bad str =
  if exists_string (member (op =) bad) str then
    translate_string (fn c => if member (op =) bad c then Symbol.DEL else c) str
  else str;

fun message_props props =
  let val clean = clean_string [Symbol.STX, "\n", "\r"]
  in implode (map (fn (x, y) => clean x ^ "=" ^ clean y ^ special_sep ^ "\n") props) end;

fun message_text class ts =
  let
    val doc = XML.Elem ("message", [("class", class)], ts);
    val msg =
      if print_mode_active xmlN then XML.header ^ XML.string_of doc
      else YXML.string_of doc;
  in clean_string [Symbol.STX] msg end;

fun message_pos ts = get_first get_pos ts
and get_pos (elem as XML.Elem (name, atts, ts)) =
      if name = Markup.positionN then SOME (Position.of_properties atts)
      else message_pos ts
  | get_pos _ = NONE;

in

fun message _ _ "" = ()
  | message ch class body =
      let
        val (txt, pos) =
          let val ts = YXML.parse_body body
          in (message_text class ts, the_default Position.none (message_pos ts)) end;
        val props =
          Position.properties_of (Position.thread_data ())
          |> Position.default_properties pos;
      in Output.writeln_default (special ch ^ message_props props ^ txt ^ special_end) end;

fun init_message () =
  let
    val pid = ("pid", string_of_pid (Posix.ProcEnv.getpid ()));
    val session = ("session", List.last (Session.id ()) handle List.Empty => "unknown");
    val welcome = Session.welcome ();
  in Output.writeln_default (special "H" ^ message_props [pid, session] ^ welcome ^ special_end) end;

end;


(* channels *)

fun setup_channels () =
 (Output.writeln_fn  := message "A" "writeln";
  Output.priority_fn := message "B" "priority";
  Output.tracing_fn  := message "C" "tracing";
  Output.warning_fn  := message "D" "warning";
  Output.error_fn    := message "E" "error";
  Output.debug_fn    := message "F" "debug";
  Output.prompt_fn   := message "G" "prompt";
  Output.status_fn   := message "I" "status");


(* init *)

fun init () =
 (change print_mode (update (op =) isabelle_processN);
  setup_channels ();
  init_message ();
  Isar.toplevel_loop {init = true, welcome = false, sync = true, secure = true});

end;

