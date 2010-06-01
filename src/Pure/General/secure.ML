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
  val use_text: use_context -> int * string -> bool -> string -> unit
  val use_file: use_context -> bool -> string -> unit
  val toplevel_pp: string list -> string -> unit
  val Isar_setup: unit -> unit
  val PG_setup: unit -> unit
  val commit: unit -> unit
  val bash_output: string -> string * int
  val bash: string -> int
end;

structure Secure: SECURE =
struct

(** secure flag **)

val secure = Unsynchronized.ref false;

fun set_secure () = secure := true;
fun is_secure () = ! secure;

fun deny_secure msg = if is_secure () then error msg else ();



(** critical operations **)

(* ML evaluation *)

fun secure_mltext () = deny_secure "Cannot evaluate ML source in secure mode";

val raw_use_text = use_text;
val raw_use_file = use_file;
val raw_toplevel_pp = toplevel_pp;

fun use_text context pos verbose txt = (secure_mltext (); raw_use_text context pos verbose txt);
fun use_file context verbose name = (secure_mltext (); raw_use_file context verbose name);

fun toplevel_pp path pp = (secure_mltext (); raw_toplevel_pp ML_Parse.global_context path pp);


(* global evaluation *)

val use_global = raw_use_text ML_Parse.global_context (0, "") false;

fun commit () = use_global "commit();";   (*commit is dynamically bound!*)

fun Isar_setup () = use_global "open Unsynchronized;";
fun PG_setup () = use_global "structure ThyLoad = Thy_Load;";


(* shell commands *)

fun secure_shell () = deny_secure "Cannot execute shell commands in secure mode";

val orig_bash_output = bash_output;

fun bash_output s = (secure_shell (); orig_bash_output s);

fun bash s =
  (case bash_output s of
    ("", rc) => rc
  | (out, rc) => (writeln (perhaps (try (unsuffix "\n")) out); rc));

end;

(*override previous toplevel bindings!*)
val use_text = Secure.use_text;
val use_file = Secure.use_file;
fun use s = Secure.use_file ML_Parse.global_context true s
  handle ERROR msg => (writeln msg; error "ML error");
val toplevel_pp = Secure.toplevel_pp;
val bash_output = Secure.bash_output;
val bash = Secure.bash;
