(*  Title:      Pure/ML/ml_debugger_polyml-5.5.3.ML
    Author:     Makarius

ML debugger interface -- Poly/ML 5.5.3, or later.
*)

signature ML_DEBUGGER =
sig
  type location
  val on_entry: (string * location -> unit) option -> unit
  val on_exit: (string * location -> unit) option -> unit
  val on_exit_exception: (string * location -> exn -> unit) option -> unit
  val on_breakpoint: (location * bool Unsynchronized.ref -> unit) option -> unit
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

type location = PolyML.location;

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

end;
