(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.

General format of process output:

  (1) unmarked stdout/stderr, no line structure (output should be
  processed immediately as it arrives);

  (2) properly marked-up messages, e.g. for writeln channel

  "\002A" ^ props ^ "\002,\n" ^ text ^ "\002.\n"

  where the props consist of name=value lines terminated by "\002,\n"
  each, and the remaining text is any number of lines (output is
  supposed to be processed in one piece);

  (3) special init message holds "pid" and "session" property;

  (4) message content is encoded in YXML format.
*)

signature ISABELLE_PROCESS =
sig
  val isabelle_processN: string
  val init: string -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* print modes *)

val isabelle_processN = "isabelle_process";

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

fun message_pos trees = trees |> get_first
  (fn XML.Elem (name, atts, ts) =>
        if name = Markup.positionN then SOME (Position.of_properties atts)
        else message_pos ts
    | _ => NONE);

fun output out_stream s = NAMED_CRITICAL "IO" (fn () =>
  (TextIO.output (out_stream, s); TextIO.output (out_stream, "\n")));

in

fun message _ _ "" = ()
  | message out_stream ch body =
      let
        val pos = the_default Position.none (message_pos (YXML.parse_body body));
        val props =
          Position.properties_of (Position.thread_data ())
          |> Position.default_properties pos;
        val txt = clean_string [Symbol.STX] body;
      in output out_stream (special ch ^ message_props props ^ txt ^ special_end) end;

fun init_message out_stream =
  let
    val pid = (Markup.pidN, process_id ());
    val session = (Markup.sessionN, List.last (Session.id ()) handle List.Empty => "unknown");
    val text = Session.welcome ();
  in output out_stream (special "A" ^ message_props [pid, session] ^ text ^ special_end) end;

end;


(* channels *)

local

fun auto_flush stream =
  let
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream stream, IO.BLOCK_BUF);
    fun loop () =
      (OS.Process.sleep (Time.fromMilliseconds 50); try TextIO.flushOut stream; loop ());
  in loop end;

in

fun setup_channels out =
  let
    val out_stream =
      if out = "-" then TextIO.stdOut
      else
        let
          val path = File.platform_path (Path.explode out);
          val out_stream = TextIO.openOut path;  (*fifo blocks until reader is ready*)
          val _ = OS.FileSys.remove path;  (*prevent alien access, indicate writer is ready*)
          val _ = SimpleThread.fork false (auto_flush TextIO.stdOut);
        in out_stream end;
    val _ = SimpleThread.fork false (auto_flush out_stream);
    val _ = SimpleThread.fork false (auto_flush TextIO.stdErr);
  in
    Output.status_fn   := message out_stream "B";
    Output.writeln_fn  := message out_stream "C";
    Output.priority_fn := message out_stream "D";
    Output.tracing_fn  := message out_stream "E";
    Output.warning_fn  := message out_stream "F";
    Output.error_fn    := message out_stream "G";
    Output.debug_fn    := message out_stream "H";
    Output.prompt_fn   := ignore;
    out_stream
  end;

end;


(* init *)

fun init out =
 (change print_mode (update (op =) isabelle_processN);
  setup_channels out |> init_message;
  OuterKeyword.report ();
  Isar.toplevel_loop {init = true, welcome = false, sync = true, secure = true});

end;
