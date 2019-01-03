(*  Title:      Pure/ML/ml_options.ML
    Author:     Makarius

ML configuration options.
*)

signature ML_OPTIONS =
sig
  val source_trace: bool Config.T
  val exception_trace: bool Config.T
  val exception_trace_enabled: Context.generic option -> bool
  val exception_debugger: bool Config.T
  val exception_debugger_enabled: Context.generic option -> bool
  val debugger: bool Config.T
  val debugger_enabled: Context.generic option -> bool
end;

structure ML_Options: ML_OPTIONS =
struct

(* source trace *)

val source_trace = Config.declare_bool ("ML_source_trace", \<^here>) (K false);


(* exception trace *)

val exception_trace = Config.declare_option_bool ("ML_exception_trace", \<^here>);

fun exception_trace_enabled NONE =
      (Options.default_bool (Config.name_of exception_trace) handle ERROR _ => false)
  | exception_trace_enabled (SOME context) = Config.get_generic context exception_trace;


(* exception debugger *)

val exception_debugger = Config.declare_option_bool ("ML_exception_debugger", \<^here>);

fun exception_debugger_enabled NONE =
      (Options.default_bool (Config.name_of exception_debugger) handle ERROR _ => false)
  | exception_debugger_enabled (SOME context) = Config.get_generic context exception_debugger;


(* debugger *)

val debugger = Config.declare_option_bool ("ML_debugger", \<^here>);

fun debugger_enabled NONE =
      (Options.default_bool (Config.name_of debugger) handle ERROR _ => false)
  | debugger_enabled (SOME context) = Config.get_generic context debugger;

end;
