(*  Title:      Pure/System/command_line.ML
    Author:     Makarius

Support for Isabelle/ML command line tools.
*)

signature COMMAND_LINE =
sig
  val tool: (unit -> int) -> unit
end;

structure Command_Line: COMMAND_LINE =
struct

fun tool body =
  uninterruptible (fn restore_attributes => fn () =>
    let val rc =
      restore_attributes body () handle exn =>
        (Output.error_msg (ML_Compiler.exn_message exn); if Exn.is_interrupt exn then 130 else 1);
    in if rc = 0 then () else exit rc end) ();

end;

