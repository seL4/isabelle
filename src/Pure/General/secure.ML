(*  Title:      Pure/General/secure.ML
    ID:         $Id$
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> bool
  val is_secure: unit -> bool
  val deny_secure: string -> unit
  val use: string -> unit
  val use_text: (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val commit: unit -> unit
end;

structure Secure: SECURE =
struct

(* secure flag *)

val secure = ref false;

fun set_secure () = set secure;
fun is_secure () = ! secure;

fun deny_secure msg = deny (is_secure ()) msg;


(* critical operations *)

fun secure_mltext () = deny_secure "Cannot evaluate ML source in secure mode";

val orig_use = use;
val orig_use_text = use_text;

fun use file = (secure_mltext (); orig_use file);
fun use_text pr verbose txt = (secure_mltext (); orig_use_text pr verbose txt);

(*commit is dynamically bound!*)
fun commit () = orig_use_text Output.ml_output false "commit();";

end;

val use = Secure.use;
val use_text = Secure.use_text;
