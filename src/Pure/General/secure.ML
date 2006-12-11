(*  Title:      Pure/General/secure.ML
    ID:         $Id$
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> unit
  val is_secure: unit -> bool
  val deny_secure: string -> unit
  val use_text: (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use_file: (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use: string -> unit
  val commit: unit -> unit
  val execute: string -> string
  val system: string -> int
end;

structure Secure: SECURE =
struct

(** secure flag **)

val secure = ref false;

fun set_secure () = secure := true;
fun is_secure () = ! secure;

fun deny_secure msg = deny (is_secure ()) msg;


(** critical operations **)

(* ML evaluation *)

fun secure_mltext () = deny_secure "Cannot evaluate ML source in secure mode";

val orig_use_text = use_text;
val orig_use_file = use_file;

fun use_text pr verbose txt = (secure_mltext (); orig_use_text pr verbose txt);
fun use_file pr verbose name = (secure_mltext (); orig_use_file pr verbose name);
val use = use_file Output.ml_output true;

(*commit is dynamically bound!*)
fun commit () = orig_use_text Output.ml_output false "commit();";


(* shell commands *)

fun secure_shell () = deny_secure "Cannot execute shell commands in secure mode";

val orig_execute = execute;
val orig_system = system;

fun execute s = (secure_shell (); orig_execute s);
fun system s = (secure_shell (); orig_system s);

end;

val use_text = Secure.use_text;
val use_file = Secure.use_file;
val use = Secure.use;
val execute = Secure.execute;
val system = Secure.system;
