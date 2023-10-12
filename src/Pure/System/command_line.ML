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

fun tool main =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      fun print_failure exn = (Runtime.exn_error_message exn; Exn.failure_rc exn);
      val rc =
        (case Exn.capture_body (run main) of
          Exn.Res () => 0
        | Exn.Exn exn =>
            (case Exn.capture print_failure exn of
              Exn.Res rc => rc
            | Exn.Exn crash => Exn.failure_rc crash));
    in exit rc end);

end;
