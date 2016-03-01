(*  Title:      Pure/RAW/secure.ML
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> unit
  val is_secure: unit -> bool
  val deny: string -> unit
  val deny_ml: unit -> unit
end;

structure Secure: SECURE =
struct

val secure = Unsynchronized.ref false;

fun set_secure () = secure := true;
fun is_secure () = ! secure;

fun deny msg = if is_secure () then error msg else ();

fun deny_ml () = deny "Cannot evaluate ML source in secure mode";

end;
