(*  Title:      Pure/RAW/exn_trace_raw.ML
    Author:     Makarius

Raw exception trace for Poly/ML 5.3.0.
*)

fun print_exception_trace (_: exn -> string) (_: string -> unit) =
  PolyML.exception_trace;
