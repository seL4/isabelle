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
  val open_unsynchronized: unit -> unit
  val commit: unit -> unit
  val system_out: string -> string * int
  val system: string -> int
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
fun open_unsynchronized () = use_global "open Unsynchronized";


(* shell commands *)

fun secure_shell () = deny_secure "Cannot execute shell commands in secure mode";

val orig_system_out = system_out;

fun system_out s = (secure_shell (); orig_system_out s);

fun system s =
  (case system_out s of
    ("", rc) => rc
  | (out, rc) => (writeln (perhaps (try (unsuffix "\n")) out); rc));

end;

(*override previous toplevel bindings!*)
val use_text = Secure.use_text;
val use_file = Secure.use_file;
fun use s = Secure.use_file ML_Parse.global_context true s
  handle ERROR msg => (writeln msg; error "ML error");
val toplevel_pp = Secure.toplevel_pp;
val system_out = Secure.system_out;
val system = Secure.system;
