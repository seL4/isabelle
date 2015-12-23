(*  Title:      Pure/ML/ml_debugger.ML
    Author:     Makarius

ML debugger interface -- dummy version.
*)

signature ML_DEBUGGER =
sig
  type exn_id
  val exn_id: exn -> exn_id
  val print_exn_id: exn_id -> string
  val eq_exn_id: exn_id * exn_id -> bool
  val on_entry: (string * 'location -> unit) option -> unit
  val on_exit: (string * 'location -> unit) option -> unit
  val on_exit_exception: (string * 'location -> exn -> unit) option -> unit
  val on_breakpoint: ('location * bool Unsynchronized.ref -> unit) option -> unit
  type state
  val state: Thread.thread -> state list
  val debug_function: state -> string
  val debug_function_arg: state -> ML_Name_Space.valueVal
  val debug_function_result: state -> ML_Name_Space.valueVal
  val debug_location: state -> 'location
  val debug_name_space: state -> ML_Name_Space.T
  val debug_local_name_space: state -> ML_Name_Space.T
end;

structure ML_Debugger: ML_DEBUGGER =
struct

(* exceptions *)

abstype exn_id = Exn_Id of string
with

fun exn_id exn = Exn_Id (General.exnName exn);
fun print_exn_id (Exn_Id name) = name;
fun eq_exn_id (Exn_Id name1, Exn_Id name2) = name1 = name2;  (*over-approximation*)

end;


(* hooks *)

fun on_entry _ = ();
fun on_exit _ = ();
fun on_exit_exception _ = ();
fun on_breakpoint _ = ();


(* debugger *)

fun fail () = raise Fail "No debugger support on this ML platform";

type state = unit;

fun state _ = [];
fun debug_function () = fail ();
fun debug_function_arg () = fail ();
fun debug_function_result () = fail ();
fun debug_location () = fail ();
fun debug_name_space () = fail ();
fun debug_local_name_space () = fail ();

end;
