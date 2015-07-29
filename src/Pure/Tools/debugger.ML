(*  Title:      Pure/Tools/debugger.ML
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*)

structure Debugger: sig end =
struct

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

fun cancel name =
  Synchronized.change global_state (tap (fn State {threads, ...} =>
    (case Symtab.lookup threads name of
      NONE => ()
    | SOME thread => Simple_Thread.interrupt_unsynchronized thread)));

fun input name msg =
  Synchronized.change global_state (map_state (fn (threads, input) =>
    let val input' = Symtab.map_default (name, Queue.empty) (Queue.enqueue msg) input;
    in (threads, input') end));

fun get_input name =
  Synchronized.guarded_access global_state (fn State {threads, input} =>
    (case Symtab.lookup input name of
      NONE => NONE
    | SOME queue =>
        let
          val (msg, queue') = Queue.dequeue queue;
          val input' =
            if Queue.is_empty queue' then Symtab.delete_safe name input
            else Symtab.update (name, queue') input;
        in SOME (msg, make_state (threads, input')) end));


(* thread data *)

local val tag = Universal.tag () : ML_Debugger.state list Universal.tag in

fun get_data () = the_default [] (Thread.getLocal tag);
fun setmp_data data f x = setmp_thread_data tag (get_data ()) data f x;

end;

val debugging = not o null o get_data;
fun with_debugging e = setmp_data (ML_Debugger.state (Thread.self ())) e ();


(* protocol messages *)

val _ = Session.protocol_handler "isabelle.Debugger$Handler";


(* main entry point *)

fun debug_loop name =
  (case get_input name of
    ["continue"] => ()
  | bad =>
     (Output.system_message
        ("Debugger: bad input " ^ ML_Syntax.print_list ML_Syntax.print_string bad);
      debug_loop name));

fun debugger cond =
  if debugging () orelse not (cond ()) orelse
    not (Options.default_bool @{system_option ML_debugger_active})
  then ()
  else
    with_debugging (fn () =>
      (case Simple_Thread.name () of
        NONE => ()
      | SOME name => debug_loop name));

fun init () =
  ML_Debugger.on_breakpoint
    (SOME (fn (_, b) =>
      debugger (fn () => ! b orelse Options.default_bool @{system_option ML_debugger_stepping})));


(* protocol commands *)

val _ =
  Isabelle_Process.protocol_command "Debugger.init"
    (fn [] => init ());

val _ =
  Isabelle_Process.protocol_command "Debugger.cancel"
    (fn [name] => cancel name);

val _ =
  Isabelle_Process.protocol_command "Debugger.input"
    (fn name :: msg => input name msg);

end;
