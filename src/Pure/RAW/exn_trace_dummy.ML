(*  Title:      Pure/RAW/exn_trace.ML
    Author:     Makarius

Exception trace dummy.
*)

fun print_exception_trace (_: exn -> string) (_: string -> unit) = PolyML.exception_trace;
