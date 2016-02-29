(*  Title:      Pure/RAW/exn_trace.ML
    Author:     Makarius

Exception trace via ML output, for Poly/ML 5.5.1 or later.
*)

fun print_exception_trace exn_message output e =
  PolyML.Exception.traceException
    (e, fn (trace, exn) =>
      let
        val title = "Exception trace - " ^ exn_message exn;
        val _ = output (String.concatWith "\n" (title :: trace));
      in reraise exn end);

PolyML.Compiler.reportExhaustiveHandlers := true;
