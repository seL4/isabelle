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
  val init: string -> string -> unit
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
        val header = YXML.string_of (XML.Elem ((ch, map (pairself YXML.binary_text) props), []));
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

fun rendezvous f fifo =
  let
    val path = File.platform_path (Path.explode fifo);
    val result = f fifo;  (*block until peer is ready*)
    val _ = OS.FileSys.remove path;  (*ready; prevent future access -- potential race condition*)
  in result end;

in

fun setup_channels in_fifo out_fifo =
  let
    val in_stream = rendezvous TextIO.openIn in_fifo;
    val out_stream = rendezvous TextIO.openOut out_fifo;
    val _ = Simple_Thread.fork false (auto_flush out_stream);
    val _ = Simple_Thread.fork false (auto_flush TextIO.stdOut);
    val _ = Simple_Thread.fork false (auto_flush TextIO.stdErr);
  in
    Output.status_fn   := standard_message out_stream "B";
    Output.report_fn   := standard_message out_stream "C";
    Output.writeln_fn  := standard_message out_stream "D";
    Output.tracing_fn  := standard_message out_stream "E";
    Output.warning_fn  := standard_message out_stream "F";
    Output.error_fn    := standard_message out_stream "G";
    Output.debug_fn    := standard_message out_stream "H";
    Output.priority_fn := ! Output.writeln_fn;
    Output.prompt_fn   := ignore;
    (in_stream, out_stream)
  end;

end;


(* init *)

fun init in_fifo out_fifo =
  let
    val _ = Unsynchronized.change print_mode
      (fold (update op =) [isabelle_processN, Keyword.keyword_statusN, Pretty.symbolicN]);
    val (in_stream, out_stream) = setup_channels in_fifo out_fifo;
    val _ = init_message out_stream;
    val _ = quick_and_dirty := true;  (* FIXME !? *)
    val _ = Keyword.status ();
    val _ = Output.status (Markup.markup Markup.ready "");
  in Isar.toplevel_loop in_stream {init = true, welcome = false, sync = true, secure = true} end;

end;
