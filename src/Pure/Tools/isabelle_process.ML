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
  val init: string -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* print modes *)

val isabelle_processN = "isabelle_process";
val xmlN = "XML";

val _ = Output.add_mode isabelle_processN Output.default_output Output.default_escape;
val _ = Markup.add_mode isabelle_processN YXML.output_markup;


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
    val doc = XML.Elem (Markup.messageN, [(Markup.classN, class)], ts);
    val msg =
      if print_mode_active xmlN then XML.header ^ XML.string_of doc
      else YXML.string_of doc;
  in clean_string [Symbol.STX] msg end;

fun message_pos ts = get_first get_pos ts
and get_pos (elem as XML.Elem (name, atts, ts)) =
      if name = Markup.positionN then SOME (Position.of_properties atts)
      else message_pos ts
  | get_pos _ = NONE;

fun output out_stream s = NAMED_CRITICAL "IO" (fn () =>
  (TextIO.output (out_stream, s); TextIO.output (out_stream, "\n")));

in

fun message _ _ _ "" = ()
  | message out_stream ch class body =
      let
        val (txt, pos) =
          let val ts = YXML.parse_body body
          in (message_text class ts, the_default Position.none (message_pos ts)) end;
        val props =
          Position.properties_of (Position.thread_data ())
          |> Position.default_properties pos;
      in output out_stream (special ch ^ message_props props ^ txt ^ special_end) end;

fun init_message out_stream =
  let
    val pid = (Markup.pidN, string_of_pid (Posix.ProcEnv.getpid ()));
    val session = (Markup.sessionN, List.last (Session.id ()) handle List.Empty => "unknown");
    val text = message_text Markup.initN [XML.Text (Session.welcome ())];
  in output out_stream (special "H" ^ message_props [pid, session] ^ text ^ special_end) end;

end;


(* channels *)

local

fun auto_flush stream =
  let
    fun loop () =
      (OS.Process.sleep (Time.fromMilliseconds 50); try TextIO.flushOut stream; loop ());
  in loop end;

in

fun setup_channels out =
  let val out_stream =
    if out = "-" then TextIO.stdOut
    else
      let
        val path = File.platform_path (Path.explode out);
        val out_stream = TextIO.openOut path;  (*fifo blocks until reader is ready*)
        val _ = OS.FileSys.remove path;  (*prevent alien access, indicate writer is ready*)
        val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream out_stream, IO.BLOCK_BUF);
        val _ = Thread.fork (auto_flush TextIO.stdOut, Multithreading.no_interrupts);
      in out_stream end;
    val _ = Thread.fork (auto_flush TextIO.stdErr, Multithreading.no_interrupts);
    val _ = Thread.fork (auto_flush out_stream, Multithreading.no_interrupts);
  in
    Output.writeln_fn  := message out_stream "A" Markup.writelnN;
    Output.priority_fn := message out_stream "B" Markup.priorityN;
    Output.tracing_fn  := message out_stream "C" Markup.tracingN;
    Output.warning_fn  := message out_stream "D" Markup.warningN;
    Output.error_fn    := message out_stream "E" Markup.errorN;
    Output.debug_fn    := message out_stream "F" Markup.debugN;
    Output.prompt_fn   := message out_stream "G" Markup.promptN;
    Output.status_fn   := message out_stream "I" Markup.statusN;
    out_stream
  end;

end;


(* init *)

fun init out =
 (change print_mode (update (op =) isabelle_processN);
  setup_channels out |> init_message;
  Isar.toplevel_loop {init = true, welcome = false, sync = true, secure = true});

end;
