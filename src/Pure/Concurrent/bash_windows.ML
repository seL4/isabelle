(*  Title:      Pure/Concurrent/bash.ML
    Author:     Makarius

GNU bash processes, with propagation of interrupts -- on native Windows (MinGW).
*)

signature BASH =
sig
  val process: string -> {out: string, err: string, rc: int, terminate: unit -> unit}
end;

structure Bash: BASH =
struct

fun process _ = raise Fail "FIXME";

end;
