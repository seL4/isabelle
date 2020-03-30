(*  Title:      Pure/System/command_line.ML
    Author:     Makarius

Support for Isabelle/ML command line tools.
*)

signature COMMAND_LINE =
sig
  exception EXIT of int
  val tool: (unit -> int) -> unit
  val tool0: (unit -> unit) -> unit
end;

structure Command_Line: COMMAND_LINE =
struct

exception EXIT of int;

fun tool body =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val rc =
        restore_attributes body ()
          handle EXIT rc => rc
            | exn => Exn.capture_exit 2 (fn () => (Runtime.exn_error_message exn; raise exn)) ();
    in exit rc end) ();

fun tool0 body = tool (fn () => (body (); 0));

end;
