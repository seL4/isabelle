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

(** global state **)

(* output messages *)

val _ = Session.protocol_handler "isabelle.Debugger$Handler";

fun output_message kind msg =
  if msg = "" then ()
  else
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


(* thread names and input *)

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



(** thread state **)

(* stack frame during debugging *)

local
  val tag = Universal.tag () : ML_Debugger.state list Universal.tag;
in

fun get_debugging () = the_default [] (Thread.getLocal tag);
val is_debugging = not o null o get_debugging;

fun with_debugging e =
  setmp_thread_data tag (get_debugging ()) (ML_Debugger.state (Thread.self ())) e ();

end;

fun the_debug_state thread_name index =
  (case get_debugging () of
    [] => error ("Missing debugger information for thread " ^ quote thread_name)
  | states =>
      if index < 0 orelse index >= length states then
        error ("Bad debugger stack index " ^ signed_string_of_int index ^ " for thread " ^
          quote thread_name)
      else nth states index);


(* flags for single-stepping *)

datatype stepping = Stepping of bool * int;  (*stepping enabled, stack depth limit*)

local
  val tag = Universal.tag () : stepping Universal.tag;
in

fun get_stepping () = the_default (Stepping (false, ~1)) (Thread.getLocal tag);
fun put_stepping stepping = Thread.setLocal (tag, Stepping stepping);

end;

fun is_stepping () =
  let
    val stack = ML_Debugger.state (Thread.self ());
    val Stepping (stepping, depth) = get_stepping ();
  in stepping andalso (depth < 0 orelse length stack <= depth) end;

fun step_stepping () = put_stepping (true, ~1);
fun step_over_stepping () = put_stepping (true, length (get_debugging ()));
fun step_out_stepping () = put_stepping (true, length (get_debugging ()) - 1);
fun continue_stepping () = put_stepping (false, ~1);


(** eval ML **)

local

val context_attempts =
  map ML_Lex.read
   ["Context.set_thread_data (SOME (Context.Theory ML_context))",
    "Context.set_thread_data (SOME (Context.Proof ML_context))",
    "Context.set_thread_data (SOME ML_context)"];

fun evaluate {SML, verbose} =
  ML_Context.eval
    {SML = SML, exchange = false, redirect = false, verbose = verbose,
      writeln = writeln_message, warning = warning_message}
    Position.none;

in

fun eval thread_name index SML txt1 txt2 =
  let
    val (toks1, toks2) = apply2 (ML_Lex.read_source SML o Input.string) (txt1, txt2);

    val evaluate_verbose = evaluate {SML = SML, verbose = true};
    val context1 = ML_Context.the_generic_context ()
      |> Context_Position.set_visible_generic false
      |> Config.put_generic ML_Options.debugger false
      |> ML_Env.add_name_space {SML = SML}
          (ML_Debugger.debug_name_space (the_debug_state thread_name index));
    val context2 =
      if SML orelse forall (fn Antiquote.Text tok => ML_Lex.is_improper tok | _ => false) toks1
      then context1
      else
        let
          val context' = context1
            |> ML_Context.exec (fn () => evaluate_verbose (ML_Lex.read "val ML_context = " @ toks1));
          fun try_exec toks =
            try (ML_Context.exec (fn () => evaluate {SML = false, verbose = false} toks)) context';
        in
          (case get_first try_exec context_attempts of
            SOME context2 => context2
          | NONE => error "Malformed context: expected type theory, Proof.context, Context.generic")
        end;
  in Context.setmp_thread_data (SOME context2) evaluate_verbose toks2 end;

end;



(** debugger entry point **)

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
    ["step"] => (step_stepping (); false)
  | ["step_over"] => (step_over_stepping (); false)
  | ["step_out"] => (step_out_stepping (); false)
  | ["continue"] => (continue_stepping (); false)
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

in

fun init () =
  ML_Debugger.on_breakpoint
    (SOME (fn (_, break) =>
      if not (is_debugging ()) andalso
        (! break orelse Options.default_bool @{system_option ML_debugger_stepping} orelse
          is_stepping ()) andalso
        Options.default_bool @{system_option ML_debugger_active}
      then
        (case Simple_Thread.get_name () of
          SOME thread_name => debugger_loop thread_name
        | NONE => ())
      else ()));

end;



(** protocol commands **)

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
