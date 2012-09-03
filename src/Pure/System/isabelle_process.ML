(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper, based on private fifos for maximum
robustness and performance, or local socket for maximum portability.

Startup phases:
  - raw Posix process startup with uncontrolled output on stdout/stderr
  - stderr \002: ML running
  - stdin/stdout/stderr freely available (raw ML loop)
  - protocol thread initialization
  - rendezvous on system channel
  - message INIT: channels ready
*)

signature ISABELLE_PROCESS =
sig
  val is_active: unit -> bool
  val protocol_command: string -> (string list -> unit) -> unit
  val crashes: exn list Synchronized.var
  val init_fifos: string -> string -> unit
  val init_socket: string -> unit
end;

structure Isabelle_Process: ISABELLE_PROCESS =
struct

(* print mode *)

val isabelle_processN = "isabelle_process";

fun is_active () = Print_Mode.print_mode_active isabelle_processN;

val _ = Output.add_mode isabelle_processN Output.default_output Output.default_escape;
val _ = Markup.add_mode isabelle_processN YXML.output_markup;


(* protocol commands *)

local

val commands =
  Synchronized.var "Isabelle_Process.commands" (Symtab.empty: (string list -> unit) Symtab.table);

in

fun protocol_command name cmd =
  Synchronized.change commands (fn cmds =>
   (if not (Symtab.defined cmds name) then ()
    else warning ("Redefining Isabelle process command " ^ quote name);
    Symtab.update (name, cmd) cmds));

fun run_command name args =
  (case Symtab.lookup (Synchronized.value commands) name of
    NONE => error ("Undefined Isabelle process command " ^ quote name)
  | SOME cmd =>
      (Runtime.debugging cmd args handle exn =>
        error ("Isabelle process protocol failure: " ^ quote name ^ "\n" ^
          ML_Compiler.exn_message exn)));

end;


(* message channels *)

local

fun chunk s = [string_of_int (size s), "\n", s];

fun message do_flush mbox ch raw_props body =
  let
    val robust_props = map (pairself YXML.embed_controls) raw_props;
    val header = YXML.string_of (XML.Elem ((ch, robust_props), []));
  in Mailbox.send mbox (chunk header @ chunk body, do_flush) end;

fun standard_message mbox opt_serial ch body =
  if body = "" then ()
  else
    message false mbox ch
      ((case opt_serial of SOME i => cons (Isabelle_Markup.serialN, string_of_int i) | _ => I)
        (Position.properties_of (Position.thread_data ()))) body;

fun message_output mbox channel =
  let
    fun flush () = ignore (try System_Channel.flush channel);
    fun loop receive =
      (case receive mbox of
        SOME (msg, do_flush) =>
         (List.app (fn s => System_Channel.output channel s) msg;
          if do_flush then flush () else ();
          loop (Mailbox.receive_timeout (seconds 0.02)))
      | NONE => (flush (); loop (SOME o Mailbox.receive)));
  in fn () => loop (SOME o Mailbox.receive) end;

in

fun init_channels channel =
  let
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdOut, IO.LINE_BUF);
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdErr, IO.LINE_BUF);

    val mbox = Mailbox.create () : (string list * bool) Mailbox.T;
    val _ = Simple_Thread.fork false (message_output mbox channel);
  in
    Output.Private_Hooks.status_fn := standard_message mbox NONE "B";
    Output.Private_Hooks.report_fn := standard_message mbox NONE "C";
    Output.Private_Hooks.writeln_fn := (fn s => standard_message mbox (SOME (serial ())) "D" s);
    Output.Private_Hooks.tracing_fn := (fn s => standard_message mbox (SOME (serial ())) "E" s);
    Output.Private_Hooks.warning_fn := (fn s => standard_message mbox (SOME (serial ())) "F" s);
    Output.Private_Hooks.error_fn := (fn (i, s) => standard_message mbox (SOME i) "G" s);
    Output.Private_Hooks.protocol_message_fn := message true mbox "H";
    Output.Private_Hooks.urgent_message_fn := ! Output.Private_Hooks.writeln_fn;
    Output.Private_Hooks.prompt_fn := ignore;
    message true mbox "A" [] (Session.welcome ())
  end;

end;


(* protocol loop -- uninterruptible *)

val crashes = Synchronized.var "Isabelle_Process.crashes" ([]: exn list);

local

fun recover crash =
  (Synchronized.change crashes (cons crash);
    warning "Recovering from Isabelle process crash -- see also Isabelle_Process.crashes");

fun read_chunk channel len =
  let
    val n =
      (case Int.fromString len of
        SOME n => n
      | NONE => error ("Isabelle process: malformed chunk header " ^ quote len));
    val chunk = System_Channel.inputN channel n;
    val m = size chunk;
  in
    if m = n then chunk
    else error ("Isabelle process: bad chunk (" ^ string_of_int m ^ " vs. " ^ string_of_int n ^ ")")
  end;

fun read_command channel =
  (case System_Channel.input_line channel of
    NONE => raise Runtime.TERMINATE
  | SOME line => map (read_chunk channel) (space_explode "," line));

in

fun loop channel =
  let val continue =
    (case read_command channel of
      [] => (Output.error_msg "Isabelle process: no input"; true)
    | name :: args => (run_command name args; true))
    handle Runtime.TERMINATE => false
      | exn => (Output.error_msg (ML_Compiler.exn_message exn) handle crash => recover crash; true);
  in if continue then loop channel else () end;

end;


(* init *)

fun init rendezvous = ignore (Simple_Thread.fork false (fn () =>
  let
    val _ = OS.Process.sleep (seconds 0.5);  (*yield to raw ML toplevel*)
    val _ = Output.physical_stderr Symbol.STX;

    val _ = quick_and_dirty := false;
    val _ = Goal.parallel_proofs := 4;
    val _ =
      if Multithreading.max_threads_value () < 2
      then Multithreading.max_threads := 2 else ();
    val _ = Context.set_thread_data NONE;
    val _ =
      Unsynchronized.change print_mode
        (fn mode =>
          (mode @ [Syntax_Trans.no_bracketsN, Syntax_Trans.no_type_bracketsN])
          |> fold (update op =) [Symbol.xsymbolsN, isabelle_processN, Pretty.symbolicN]);

    val channel = rendezvous ();
    val _ = init_channels channel;
  in loop channel end));

fun init_fifos fifo1 fifo2 = init (fn () => System_Channel.fifo_rendezvous fifo1 fifo2);
fun init_socket name = init (fn () => System_Channel.socket_rendezvous name);

end;

