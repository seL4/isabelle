(*  Title:      Pure/System/command_line.ML
    Author:     Makarius

Support for Isabelle/ML command line tools.
*)

signature COMMAND_LINE =
sig
  val tool: (unit -> unit) -> unit
end;

structure Command_Line: COMMAND_LINE =
struct

fun tool body =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val rc =
        (run body (); 0) handle exn =>
          ((Runtime.exn_error_message exn; Exn.failure_rc exn) handle err => Exn.failure_rc err);
    in exit rc end);

end;
