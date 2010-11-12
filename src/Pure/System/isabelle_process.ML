(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper, based on private fifos for maximum
robustness and performance.

Startup phases:
  . raw Posix process startup with uncontrolled output on stdout/stderr
  . stdout \002: ML running
  .. stdin/stdout/stderr freely available (raw ML loop)
  .. protocol thread initialization
  ... switch to in_fifo/out_fifo channels (rendezvous via open)
  ... out_fifo INIT(pid): channels ready
  ... out_fifo STATUS(keywords)
  ... out_fifo READY: main loop ready
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


(* message channels *)

local

fun chunk s = [string_of_int (size s), "\n", s];

fun message _ _ _ "" = ()
  | message mbox ch raw_props body =
      let
        val robust_props = map (pairself YXML.escape_controls) raw_props;
        val header = YXML.string_of (XML.Elem ((ch, robust_props), []));
      in Mailbox.send mbox (chunk header @ chunk body) end;

fun standard_message mbox with_serial ch body =
  message mbox ch
    ((if with_serial then cons (Markup.serialN, serial_string ()) else I)
      (Position.properties_of (Position.thread_data ()))) body;

fun message_output mbox out_stream =
  let
    fun loop receive =
      (case receive mbox of
        SOME msg =>
         (List.app (fn s => TextIO.output (out_stream, s)) msg;
          loop (Mailbox.receive_timeout (seconds 0.02)))
      | NONE => (try TextIO.flushOut out_stream; loop (SOME o Mailbox.receive)));
  in fn () => loop (SOME o Mailbox.receive) end;

in

fun setup_channels in_fifo out_fifo =
  let
    (*rendezvous*)
    val in_stream = TextIO.openIn in_fifo;
    val out_stream = TextIO.openOut out_fifo;

    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdOut, IO.LINE_BUF);
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdErr, IO.LINE_BUF);

    val mbox = Mailbox.create () : string list Mailbox.T;
    val _ = Simple_Thread.fork false (message_output mbox out_stream);
  in
    Output.Private_Hooks.status_fn := standard_message mbox false "B";
    Output.Private_Hooks.report_fn := standard_message mbox false "C";
    Output.Private_Hooks.writeln_fn := standard_message mbox true "D";
    Output.Private_Hooks.tracing_fn := standard_message mbox true "E";
    Output.Private_Hooks.warning_fn := standard_message mbox true "F";
    Output.Private_Hooks.error_fn := standard_message mbox true "G";
    Output.Private_Hooks.urgent_message_fn := ! Output.Private_Hooks.writeln_fn;
    Output.Private_Hooks.prompt_fn := ignore;
    message mbox "A" [] (Session.welcome ());
    in_stream
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

fun init in_fifo out_fifo = ignore (Simple_Thread.fork false (fn () =>
  let
    val _ = OS.Process.sleep (seconds 0.5);  (*yield to raw ML toplevel*)
    val _ = Output.raw_stdout Symbol.STX;

    val _ = quick_and_dirty := false;
    val _ = Goal.parallel_proofs := 0;
    val _ = Context.set_thread_data NONE;
    val _ = Unsynchronized.change print_mode
      (fold (update op =) [isabelle_processN, Keyword.keyword_statusN, Pretty.symbolicN]);

    val in_stream = setup_channels in_fifo out_fifo;
    val _ = Keyword.status ();
    val _ = Output.status (Markup.markup Markup.ready "process ready");
  in loop in_stream end));

end;

