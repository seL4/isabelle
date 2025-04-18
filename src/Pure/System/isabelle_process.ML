(*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius

Isabelle process wrapper.
*)

signature ISABELLE_PROCESS =
sig
  val reset_tracing: Document_ID.exec -> unit
  val crashes: exn list Synchronized.var
  val init_options: unit -> unit
  val init_options_interactive: unit -> unit
  val init: unit -> unit
  val init_build: unit -> unit
end;

structure Isabelle_Process: ISABELLE_PROCESS =
struct

(* print modes *)

val protocol_modes1 = [Syntax_Trans.no_bracketsN, Syntax_Trans.no_type_bracketsN];
val protocol_modes2 = [Print_Mode.PIDE];


(* restricted tracing messages *)

val tracing_messages =
  Synchronized.var "tracing_messages" (Inttab.empty: int Inttab.table);

fun reset_tracing exec_id =
  Synchronized.change tracing_messages (Inttab.delete_safe exec_id);

fun update_tracing () =
  (case Position.parse_id (Position.thread_data ()) of
    NONE => ()
  | SOME exec_id =>
      let
        val ok =
          Synchronized.change_result tracing_messages (fn tab =>
            let
              val n = the_default 0 (Inttab.lookup tab exec_id) + 1;
              val limit = Options.default_int "editor_tracing_messages";
              val ok = limit <= 0 orelse n <= limit;
            in (ok, Inttab.update (exec_id, n) tab) end);
      in
        if ok then ()
        else
          let
            val (text, promise) = Active.dialog_text ();
            val _ =
              writeln ("Tracing paused.  " ^ text "Stop" ^ ", or continue with next " ^
                text "100" ^ ", " ^ text "1000" ^ ", " ^ text "10000" ^ " messages?")
            val m = Value.parse_int (Future.join promise)
              handle Fail _ => error "Stopped";
          in
            Synchronized.change tracing_messages
              (Inttab.map_default (exec_id, 0) (fn k => k - m))
          end
      end);


(* init protocol -- uninterruptible *)

val crashes = Synchronized.var "Isabelle_Process.crashes" ([]: exn list);

local

fun recover crash =
  (Synchronized.change crashes (cons crash);
    Output.physical_stderr
      "Recovered from Isabelle process crash -- see also Isabelle_Process.crashes\n");

fun ml_statistics () =
  Output.protocol_message
    (Markup.ML_statistics {pid = ML_Pid.get (), stats_dir = getenv "POLYSTATSDIR"}) [];

in

fun init_protocol modes = Thread_Attributes.uninterruptible (fn _ => fn (address, password) =>
  let
    val _ = SHA1.test_samples ()
      handle exn as Fail msg => (Output.physical_stderr (msg ^ "\n"); Exn.reraise exn);

    val _ = Output.physical_stderr Symbol.STX;


    (* streams *)

    val (in_stream, out_stream) = Socket_IO.open_streams address;
    val _ = Byte_Message.write_line out_stream (Bytes.string password);

    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdOut, IO.LINE_BUF);
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdErr, IO.LINE_BUF);
    val _ = BinIO.StreamIO.setBufferMode (BinIO.getOutstream out_stream, IO.BLOCK_BUF);


    (* messages *)

    val message_channel = Message_Channel.make out_stream;
    val message = Message_Channel.message message_channel;

    fun standard_message props name ss =
      if forall (fn s => s = "") ss then ()
      else
        let
          val pos_props =
            if exists Markup.position_property props then props
            else props @ Position.properties_of (Position.thread_data ());
        in message name pos_props [XML.blob ss] end;

    fun report_message ss =
      if Context_Position.reports_enabled0 ()
      then standard_message [] Markup.reportN ss else ();

    val serial_props = Markup.serial_properties o serial;

    val message_context =
      Unsynchronized.setmp Private_Output.status_fn (standard_message [] Markup.statusN) #>
      Unsynchronized.setmp Private_Output.report_fn report_message #>
      Unsynchronized.setmp Private_Output.result_fn
        (fn props => fn s => standard_message (props @ serial_props ()) Markup.resultN s) #>
      Unsynchronized.setmp Private_Output.writeln_fn
        (fn s => standard_message (serial_props ()) Markup.writelnN s) #>
      Unsynchronized.setmp Private_Output.writeln_urgent_fn
        (fn s => standard_message (serial_props () @ Markup.urgent_properties) Markup.writelnN s) #>
      Unsynchronized.setmp Private_Output.state_fn
        (fn s => standard_message (serial_props ()) Markup.stateN s) #>
      Unsynchronized.setmp Private_Output.information_fn
        (fn s => standard_message (serial_props ()) Markup.informationN s) #>
      Unsynchronized.setmp Private_Output.tracing_fn
        (fn s => (update_tracing (); standard_message (serial_props ()) Markup.tracingN s)) #>
      Unsynchronized.setmp Private_Output.warning_fn
        (fn s => standard_message (serial_props ()) Markup.warningN s) #>
      Unsynchronized.setmp Private_Output.legacy_fn
        (fn s => standard_message (serial_props ()) Markup.legacyN s) #>
      Unsynchronized.setmp Private_Output.error_message_fn
        (fn (i, s) => standard_message (Markup.serial_properties i) Markup.errorN s) #>
      Unsynchronized.setmp Private_Output.system_message_fn
        (fn ss => message Markup.systemN [] [XML.blob ss]) #>
      Unsynchronized.setmp Private_Output.protocol_message_fn
        (fn props => fn chunks => message Markup.protocolN props chunks) #>
      Unsynchronized.setmp print_mode
        ((! print_mode @ #1 modes) |> fold (update op =) (#2 modes));


    (* protocol *)

    fun protocol_loop () =
      let
        fun main () =
          (case Byte_Message.read_message in_stream of
            NONE => raise Protocol_Command.STOP 0
          | SOME [] => Output.system_message "Isabelle process: no input"
          | SOME (name :: args) => Protocol_Command.run (Bytes.content name) args);
        val _ =
          (case Exn.capture_body main of
            Exn.Res () => ()
          | Exn.Exn exn =>
              if Protocol_Command.is_protocol_exn exn then Exn.reraise exn
              else
                (case Exn.capture Runtime.exn_system_message exn of
                  Exn.Res () => ()
                | Exn.Exn crash => recover crash));
      in protocol_loop () end;

    fun protocol () =
     (message Markup.initN [] [[XML.Text (Session.welcome ())]];
      ml_statistics ();
      protocol_loop ());

    val result = Exn.capture_body (message_context protocol);


    (* shutdown *)

    val _ = Future.shutdown ();
    val _ = Execution.reset ();
    val _ = Message_Channel.shutdown message_channel;
    val _ = BinIO.closeIn in_stream;
    val _ = BinIO.closeOut out_stream;

    val _ = Options.reset_default ();
  in
    (case result of
      Exn.Exn (Protocol_Command.STOP rc) => if rc = 0 then () else exit rc
    | _ => Exn.release result)
  end);

end;


(* init options *)

fun init_options () =
 (ML_Print_Depth.set_print_depth (Options.default_int "ML_print_depth");
  Multithreading.trace := Options.default_int "threads_trace";
  Multithreading.max_threads_update (Options.default_int "threads");
  Multithreading.parallel_proofs := Options.default_int "parallel_proofs";
  Isabelle_Thread.threads_stack_limit := Options.default_real "threads_stack_limit";
  if Options.default_bool "export_standard_proofs" then Proofterm.proofs := 2 else ();
  let val proofs = Options.default_int "record_proofs"
  in if proofs < 0 then () else Proofterm.proofs := proofs end;
  Printer.show_markup_default := false;
  Context.theory_tracing := Options.default_bool "context_theory_tracing";
  Context.proof_tracing := Options.default_bool "context_proof_tracing";
  Context.data_timing := Options.default_bool "context_data_timing";
  Syntax.cache_persistent := false);

fun init_options_interactive () =
 (init_options ();
  Multithreading.parallel_proofs := (if Options.default_int "parallel_proofs" > 0 then 3 else 0);
  Printer.show_markup_default := true;
  Syntax.cache_persistent := true);


(* generic init *)

fun init_modes modes =
  let
    val address = Options.default_string \<^system_option>\<open>system_channel_address\<close>;
    val password = Options.default_string \<^system_option>\<open>system_channel_password\<close>;
  in
    if address <> "" andalso password <> ""
    then init_protocol modes (address, password)
    else init_options ()
  end;

fun init () = init_modes (protocol_modes1, protocol_modes2);
fun init_build () = init_modes ([], protocol_modes2);

end;
