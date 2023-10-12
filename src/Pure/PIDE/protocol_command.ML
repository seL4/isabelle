(*  Title:      Pure/PIDE/protocol_command.ML
    Author:     Makarius

Protocol commands.
*)

signature PROTOCOL_COMMAND =
sig
  exception STOP of int
  val is_protocol_exn: exn -> bool
  val define_bytes: string -> (Bytes.T list -> unit) -> unit
  val define: string -> (string list -> unit) -> unit
  val run: string -> Bytes.T list -> unit
end;

structure Protocol_Command: PROTOCOL_COMMAND =
struct

exception STOP of int;

val is_protocol_exn = fn STOP _ => true | _ => false;

local

val commands =
  Synchronized.var "Protocol_Command.commands"
    (Symtab.empty: (Bytes.T list -> unit) Symtab.table);

in

fun define_bytes name cmd =
  Synchronized.change commands (fn cmds =>
   (if not (Symtab.defined cmds name) then ()
    else warning ("Redefining Isabelle protocol command " ^ quote name);
    Symtab.update (name, cmd) cmds));

fun define name cmd = define_bytes name (map Bytes.content #> cmd);

fun run name args =
  (case Symtab.lookup (Synchronized.value commands) name of
    NONE => error ("Undefined Isabelle protocol command " ^ quote name)
  | SOME cmd =>
      (case Exn.capture_body (fn () => Runtime.exn_trace_system (fn () => cmd args)) of
        Exn.Res res => res
      | Exn.Exn exn =>
          if is_protocol_exn exn then Exn.reraise exn
          else error ("Isabelle protocol command failure: " ^ quote name)));

end;

end;
