(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper, based on private fifos for maximum
robustness and performance.
*)

signature ISABELLE_PROCESS =
sig
  val isabelle_processN: string
  val add_command: string -> (string list -> unit) -> unit
  val command: string -> string list -> unit
  val crashes: exn list Unsynchronized.ref
  val init: string -> string -> unit
end;

structure Isabelle_Process: ISABELLE_PROCESS =
struct

(* print modes *)

val isabelle_processN = "isabelle_process";

val _ = Output.add_mode isabelle_processN Output.default_output Output.default_escape;
val _ = Markup.add_mode isabelle_processN YXML.output_markup;


(* commands *)

local

val global_commands = Unsynchronized.ref (Symtab.empty: (string list -> unit) Symtab.table);

in

fun add_command name cmd = CRITICAL (fn () =>
  Unsynchronized.change global_commands (fn cmds =>
   (if not (Symtab.defined cmds name) then ()
    else warning ("Redefining Isabelle process command " ^ quote name);
    Symtab.update (name, cmd) cmds)));

fun command name args =
  (case Symtab.lookup (! global_commands) name of
    NONE => error ("Undefined Isabelle process command " ^ quote name)
  | SOME cmd => cmd args);

end;


(* message markup *)

local

fun chunk s = string_of_int (size s) ^ "\n" ^ s;

fun message _ _ _ "" = ()
  | message out_stream ch raw_props body =
      let
        val robust_props = map (pairself YXML.escape_controls) raw_props;
        val header = YXML.string_of (XML.Elem ((ch, robust_props), []));
      in TextIO.output (out_stream, chunk header ^ chunk body) (*atomic output!*) end;

in

fun standard_message out_stream ch body =
  message out_stream ch
    ((Markup.serialN, serial_string ()) :: Position.properties_of (Position.thread_data ())) body;

fun init_message out_stream =
  message out_stream "A" [(Markup.pidN, process_id ())] (Session.welcome ());

end;


(* channels *)

local

fun auto_flush stream =
  let
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream stream, IO.BLOCK_BUF);
    fun loop () =
      (OS.Process.sleep (Time.fromMilliseconds 20); try TextIO.flushOut stream; loop ());
  in loop end;

fun rendezvous f fifo =
  let
    val path = File.platform_path (Path.explode fifo);
    val result = f fifo;  (*should block until peer is ready*)
    val _ =
      if String.isSuffix "cygwin" ml_platform then ()  (*Cygwin 1.7: no proper blocking on open*)
      else OS.FileSys.remove path;  (*prevent future access*)
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


(* protocol loop -- uninterruptible *)

val crashes = Unsynchronized.ref ([]: exn list);

local

fun recover crash =
  (CRITICAL (fn () => Unsynchronized.change crashes (cons crash));
    warning "Recovering from Isabelle process crash -- see also Isabelle_Process.crashes");

fun read_chunk stream len =
  let
    val n =
      (case Int.fromString len of
        SOME n => n
      | NONE => error ("Isabelle process: malformed chunk header " ^ quote len));
    val chunk = TextIO.inputN (stream, n);
    val m = size chunk;
  in
    if m = n then chunk
    else error ("Isabelle process: bad chunk (" ^ string_of_int m ^ " vs. " ^ string_of_int n ^ ")")
  end;

fun read_command stream =
  (case TextIO.inputLine stream of
    NONE => raise Runtime.TERMINATE
  | SOME line => map (read_chunk stream) (space_explode "," line));

fun run_command name args =
  Runtime.debugging (command name) args
    handle exn =>
      error ("Isabelle process command failure: " ^ name ^ "\n" ^ ML_Compiler.exn_message exn);

in

fun loop stream =
  let val continue =
    (case read_command stream of
      [] => (Output.error_msg "Isabelle process: no input"; true)
    | name :: args => (run_command name args; true))
    handle Runtime.TERMINATE => false
      | exn => (Output.error_msg (ML_Compiler.exn_message exn) handle crash => recover crash; true);
  in if continue then loop stream else () end;

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
    val _ = Context.set_thread_data NONE;
    val _ = Simple_Thread.fork false (fn () => (loop in_stream; quit ()));
  in () end;

end;
