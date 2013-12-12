(*  Title:      Pure/Tools/simplifier_trace.ML
    Author:     Lars Hupel, TU Muenchen

Interactive Simplifier trace.
*)

signature SIMPLIFIER_TRACE =
sig
  val simp_trace_test: bool Config.T
end

structure Simplifier_Trace: SIMPLIFIER_TRACE =
struct

(* Simplifier trace operations *)

val simp_trace_test =
  Attrib.setup_config_bool @{binding simp_trace_test} (K false)

val _ = Theory.setup
  (Simplifier.set_trace_ops
   {trace_invoke = fn {depth, term} => fn ctxt =>
      (if Config.get ctxt simp_trace_test then
        tracing ("Simplifier invocation " ^ string_of_int depth ^ ": " ^
          Syntax.string_of_term ctxt term)
       else (); ctxt),
    trace_apply = fn args => fn ctxt => fn cont =>
      (if Config.get ctxt simp_trace_test then
        tracing ("Simplifier " ^ @{make_string} args)
       else (); cont ctxt)})


(* PIDE protocol *)

val _ = Session.protocol_handler "isabelle.Simplifier_Trace$Handler"

end

