(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper.

General format of process output:
  (1) message = "\002"  header chunk  body chunk
  (2) chunk = size (ASCII digits)  \n  content (YXML)
*)

signature ISABELLE_PROCESS =
sig
  val isabelle_processN: string
  val init: string -> unit
end;

structure Isabelle_Process: ISABELLE_PROCESS =
struct

(* print modes *)

val isabelle_processN = "isabelle_process";

val _ = Output.add_mode isabelle_processN Output.default_output Output.default_escape;
val _ = Markup.add_mode isabelle_processN YXML.output_markup;


(* message markup *)

local

fun chunk s = string_of_int (size s) ^ "\n" ^ s;

fun message _ _ _ "" = ()
  | message out_stream ch props body =
      let
        val header = YXML.string_of (XML.Elem (ch, map (pairself YXML.binary_text) props, []));
        val msg = Symbol.STX ^ chunk header ^ chunk body;
      in TextIO.output (out_stream, msg) (*atomic output*) end;

in

fun standard_message out_stream ch body =
  message out_stream ch (Position.properties_of (Position.thread_data ())) body;

fun init_message out_stream =
  message out_stream "A" [(Markup.pidN, process_id ())] (Session.welcome ());

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
    val path = File.platform_path (Path.explode out);
    val out_stream = TextIO.openOut path;  (*fifo blocks until reader is ready*)
    val _ = OS.FileSys.remove path;  (*prevent alien access, indicate writer is ready*)
    val _ = SimpleThread.fork false (auto_flush out_stream);
    val _ = SimpleThread.fork false (auto_flush TextIO.stdOut);
    val _ = SimpleThread.fork false (auto_flush TextIO.stdErr);
  in
    Output.status_fn   := standard_message out_stream "B";
    Output.writeln_fn  := standard_message out_stream "C";
    Output.priority_fn := standard_message out_stream "D";
    Output.tracing_fn  := standard_message out_stream "E";
    Output.warning_fn  := standard_message out_stream "F";
    Output.error_fn    := standard_message out_stream "G";
    Output.debug_fn    := standard_message out_stream "H";
    Output.prompt_fn   := ignore;
    out_stream
  end;

end;


(* init *)

fun init out =
 (Unsynchronized.change print_mode
    (fold (update (op =)) [isabelle_processN, OuterKeyword.keyword_status_reportN]);
  setup_channels out |> init_message;
  OuterKeyword.report ();
  Output.status (Markup.markup Markup.ready "");
  Isar.toplevel_loop {init = true, welcome = false, sync = true, secure = true});

end;
