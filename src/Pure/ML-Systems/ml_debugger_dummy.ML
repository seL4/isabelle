(*  Title:      Pure/ML/ml_debugger_dummy.ML
    Author:     Makarius

ML debugger interface -- dummy version.
*)

signature ML_DEBUGGER =
sig
  type location
  val on_entry: (string * location -> unit) option -> unit
  val on_exit: (string * location -> unit) option -> unit
  val on_exit_exception: (string * location -> exn -> unit) option -> unit
  val on_break_point: (location * bool Unsynchronized.ref -> unit) option -> unit
  type state
  val state: Thread.thread -> state list
  val debug_function: state -> string
  val debug_function_arg: state -> ML_Name_Space.valueVal
  val debug_function_result: state -> ML_Name_Space.valueVal
  val debug_location: state -> location
  val debug_name_space: state -> ML_Name_Space.T
end;

structure ML_Debugger: ML_DEBUGGER =
struct

(* hooks *)

type location = unit;
fun on_entry _ = ();
fun on_exit _ = ();
fun on_exit_exception _ = ();
fun on_break_point _ = ();


(* debugger *)

fun fail () = raise Fail "No debugger support on this ML platform";

type state = unit;

fun state _ = [];
fun debug_function () = fail ();
fun debug_function_arg () = fail ();
fun debug_function_result () = fail ();
fun debug_location () = fail ();
fun debug_name_space () = fail ();

end;


fun ml_debugger_parameters (_: bool) = [];
