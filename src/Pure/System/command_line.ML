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
      fun return_code exn =
        if Exn.is_interrupt exn then 130 else 2;
      val rc =
        (restore_attributes body (); 0) handle exn =>
          ((Runtime.exn_error_message exn; return_code exn) handle err => return_code err);
    in exit rc end) ();

end;
