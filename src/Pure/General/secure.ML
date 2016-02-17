(*  Title:      Pure/General/secure.ML
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> unit
  val is_secure: unit -> bool
  val deny_secure: string -> unit
  val secure_mltext: unit -> unit
  val use_text: use_context ->
    {line: int, file: string, verbose: bool, debug: bool} -> string -> unit
  val use_file: use_context -> {verbose: bool, debug: bool} -> string -> unit
end;

structure Secure: SECURE =
struct

(** secure flag **)

val secure = Unsynchronized.ref false;

fun set_secure () = secure := true;
fun is_secure () = ! secure;

fun deny_secure msg = if is_secure () then error msg else ();



(** critical operations **)

fun secure_mltext () = deny_secure "Cannot evaluate ML source in secure mode";

val raw_use_text = use_text;
val raw_use_file = use_file;

fun use_text context flags (text: string) = (secure_mltext (); raw_use_text context flags text);
fun use_file context flags (file: string) = (secure_mltext (); raw_use_file context flags file);

end;
