(*  Title:      Pure/General/secure.ML
    ID:         $Id$
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> unit
  val is_secure: unit -> bool
  val use_text: string -> (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use_file: (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use_noncritical: string -> unit
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

fun deny_secure msg = if is_secure () then error msg else ();


(** critical operations **)

(* ML evaluation *)

fun secure_mltext () = deny_secure "Cannot evaluate ML source in secure mode";

fun orig_use_text x = use_text ML_Parse.fix_ints x;
fun orig_use_file x = use_file ML_Parse.fix_ints x;

fun use_text name pr verbose txt = NAMED_CRITICAL "ML" (fn () =>
  (secure_mltext (); orig_use_text name pr verbose txt));

fun use_file pr verbose name = NAMED_CRITICAL "ML" (fn () =>
  (secure_mltext (); orig_use_file pr verbose name));

fun use name = use_file Output.ml_output true name;

fun use_noncritical name =
  (secure_mltext (); orig_use_file Output.ml_output true name);

(*commit is dynamically bound!*)
fun commit () = orig_use_text "" Output.ml_output false "commit();";


(* shell commands *)

fun secure_shell () = deny_secure "Cannot execute shell commands in secure mode";

val orig_execute = execute;
val orig_system = system;

fun execute s = (secure_shell (); orig_execute s);
fun system s = (secure_shell (); orig_system s);

end;

(*override previous toplevel bindings!*)
val use_text = Secure.use_text;
val use_file = Secure.use_file;
fun use s = Secure.use s handle ERROR msg => (writeln msg; raise Fail "ML error");
val execute = Secure.execute;
val system = Secure.system;
