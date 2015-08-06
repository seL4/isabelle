(*  Title:      Pure/Tools/debugger.ML
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*)

signature DEBUGGER =
sig
  val writeln_message: string -> unit
  val warning_message: string -> unit
  val error_message: string -> unit
end;

structure Debugger: DEBUGGER =
struct

(* messages *)

val _ = Session.protocol_handler "isabelle.Debugger$Handler";

fun output_message kind msg =
  Output.protocol_message
    (Markup.debugger_output (Simple_Thread.the_name ()))
    [Markup.markup (kind, Markup.serial_properties (serial ())) msg];

val writeln_message = output_message Markup.writelnN;
val warning_message = output_message Markup.warningN;
val error_message = output_message Markup.errorN;

fun error_wrapper e = e ()
  handle exn =>
    if Exn.is_interrupt exn then reraise exn
    else error_message (Runtime.exn_message exn);


(* global state *)

datatype state =
  State of {
    threads: Thread.thread Symtab.table,  (*thread name ~> thread*)
    input: string list Queue.T Symtab.table  (*thread name ~> input queue*)
  };

fun make_state (threads, input) = State {threads = threads, input = input};
val init_state = make_state (Symtab.empty, Symtab.empty);
fun map_state f (State {threads, input}) = make_state (f (threads, input));

val global_state = Synchronized.var "Debugger.state" init_state;

fun cancel thread_name =
  Synchronized.change global_state (tap (fn State {threads, ...} =>
    (case Symtab.lookup threads thread_name of
      NONE => ()
    | SOME thread => Simple_Thread.interrupt_unsynchronized thread)));

fun input thread_name msg =
  Synchronized.change global_state (map_state (fn (threads, input) =>
    let val input' = Symtab.map_default (thread_name, Queue.empty) (Queue.enqueue msg) input;
    in (threads, input') end));

fun get_input thread_name =
  Synchronized.guarded_access global_state (fn State {threads, input} =>
    (case Symtab.lookup input thread_name of
      NONE => NONE
    | SOME queue =>
        let
          val (msg, queue') = Queue.dequeue queue;
          val input' =
            if Queue.is_empty queue' then Symtab.delete_safe thread_name input
            else Symtab.update (thread_name, queue') input;
        in SOME (msg, make_state (threads, input')) end));


(* thread state *)

local
  val tag = Universal.tag () : ML_Debugger.state list Universal.tag;
in

fun get_debugging () = the_default [] (Thread.getLocal tag);
val is_debugging = not o null o get_debugging;

fun with_debugging e =
  setmp_thread_data tag (get_debugging ()) (ML_Debugger.state (Thread.self ())) e ();

end;


(* eval ML *)

fun eval thread_name index SML context expression =  (* FIXME *)
  writeln_message ("SML = " ^ Markup.print_bool SML ^
    "\ncontext = " ^ context ^ "\nexpression = " ^ expression);


(* debugger entry point *)

local

fun debugger_state thread_name =
  Output.protocol_message (Markup.debugger_state thread_name)
   [get_debugging ()
    |> map (fn st =>
      (Position.properties_of (Exn_Properties.position_of (ML_Debugger.debug_location st)),
       ML_Debugger.debug_function st))
    |> let open XML.Encode in list (pair properties string) end
    |> YXML.string_of_body];

fun debugger_command thread_name =
  (case get_input thread_name of
    ["continue"] => false
  | ["eval", index, SML, txt1, txt2] =>
     (error_wrapper (fn () =>
        eval thread_name (Markup.parse_int index) (Markup.parse_bool SML) txt1 txt2); true)
  | bad =>
     (Output.system_message
        ("Debugger: bad input " ^ ML_Syntax.print_list ML_Syntax.print_string bad); true));

fun debugger_loop thread_name =
  let
    fun loop () =
      (debugger_state thread_name; if debugger_command thread_name then loop () else ());
  in with_debugging loop; debugger_state thread_name end;

fun debugger cond =
  if is_debugging () orelse not (cond ()) orelse
    not (Options.default_bool @{system_option ML_debugger_active})
  then ()
  else
    (case Simple_Thread.get_name () of
      NONE => ()
    | SOME thread_name => debugger_loop thread_name);

in

fun init () =
  ML_Debugger.on_breakpoint
    (SOME (fn (_, b) =>
      debugger (fn () => ! b orelse Options.default_bool @{system_option ML_debugger_stepping})));

end;


(* protocol commands *)

val _ =
  Isabelle_Process.protocol_command "Debugger.init"
    (fn [] => init ());

val _ =
  Isabelle_Process.protocol_command "Debugger.cancel"
    (fn [thread_name] => cancel thread_name);

val _ =
  Isabelle_Process.protocol_command "Debugger.input"
    (fn thread_name :: msg => input thread_name msg);

end;
