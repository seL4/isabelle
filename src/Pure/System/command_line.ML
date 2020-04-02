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
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val rc =
        (restore_attributes body (); 0)
          handle exn => Exn.capture_exit 2 (fn () => (Runtime.exn_error_message exn; raise exn)) ();
    in exit rc end) ();

end;
