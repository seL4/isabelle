(*  Title:      Pure/ML/ml_debugger.ML
    Author:     Makarius

ML debugger interface -- for Poly/ML 5.6, or later.
*)

signature ML_DEBUGGER =
sig
  type exn_id
  val exn_id: exn -> exn_id
  val print_exn_id: exn_id -> string
  val eq_exn_id: exn_id * exn_id -> bool
  val on_entry: (string * ML_Compiler0.polyml_location -> unit) option -> unit
  val on_exit: (string * ML_Compiler0.polyml_location -> unit) option -> unit
  val on_exit_exception: (string * ML_Compiler0.polyml_location -> exn -> unit) option -> unit
  val on_breakpoint: (ML_Compiler0.polyml_location * bool Unsynchronized.ref -> unit) option -> unit
  type state
  val state: Thread.thread -> state list
  val debug_function: state -> string
  val debug_function_arg: state -> PolyML.NameSpace.Values.value
  val debug_function_result: state -> PolyML.NameSpace.Values.value
  val debug_location: state -> ML_Compiler0.polyml_location
  val debug_name_space: state -> ML_Name_Space.T
  val debug_local_name_space: state -> ML_Name_Space.T
end;

structure ML_Debugger: ML_DEBUGGER =
struct

(* exceptions *)

abstype exn_id = Exn_Id of string * int Unsynchronized.ref
with

fun exn_id exn =
  Exn_Id (General.exnName exn, RunCall.run_call2 RuntimeCalls.POLY_SYS_load_word (exn, 0));

fun print_exn_id (Exn_Id (name, _)) = name;
fun eq_exn_id (Exn_Id (_, id1), Exn_Id (_, id2)) = pointer_eq (id1, id2);

end;

val _ =
  ML_system_pp (fn _ => fn _ => fn exn_id =>
    let val s = print_exn_id exn_id
    in ML_Pretty.to_polyml (ML_Pretty.String (s, FixedInt.fromInt (size s))) end);


(* hooks *)

val on_entry = PolyML.DebuggerInterface.setOnEntry;
val on_exit = PolyML.DebuggerInterface.setOnExit;
val on_exit_exception = PolyML.DebuggerInterface.setOnExitException;
val on_breakpoint = PolyML.DebuggerInterface.setOnBreakPoint;


(* debugger operations *)

type state = PolyML.DebuggerInterface.debugState;

val state = PolyML.DebuggerInterface.debugState;
val debug_function = PolyML.DebuggerInterface.debugFunction;
val debug_function_arg = PolyML.DebuggerInterface.debugFunctionArg;
val debug_function_result = PolyML.DebuggerInterface.debugFunctionResult;
val debug_location = PolyML.DebuggerInterface.debugLocation;
val debug_name_space = PolyML.DebuggerInterface.debugNameSpace;
val debug_local_name_space = PolyML.DebuggerInterface.debugLocalNameSpace;

end;
