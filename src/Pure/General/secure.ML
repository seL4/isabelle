(*  Title:      Pure/General/secure.ML
    Author:     Makarius

Secure critical operations.
*)

signature SECURE =
sig
  val set_secure: unit -> unit
  val is_secure: unit -> bool
  val deny_secure: string -> unit
  val use_text: ML_NameSpace.nameSpace -> int * string ->
    (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use_file: ML_NameSpace.nameSpace ->
    (string -> unit) * (string -> 'a) -> bool -> string -> unit
  val use: string -> unit
  val toplevel_pp: string list -> string -> unit
  val commit: unit -> unit
  val system_out: string -> string * int
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

fun raw_use_text ns = use_text ML_Parse.fix_ints (Position.str_of oo Position.line_file) ns;
fun raw_use_file ns = use_file ML_Parse.fix_ints (Position.str_of oo Position.line_file) ns;
fun raw_toplevel_pp x =
  toplevel_pp ML_Parse.fix_ints (Position.str_of oo Position.line_file) Output.ml_output x;

fun use_text ns pos pr verbose txt =
  (secure_mltext (); raw_use_text ns pos pr verbose txt);

fun use_file ns pr verbose name =
  (secure_mltext (); raw_use_file ns pr verbose name);

fun use name = use_file ML_NameSpace.global Output.ml_output true name;

fun toplevel_pp path pp = (secure_mltext (); raw_toplevel_pp path pp);

(*commit is dynamically bound!*)
fun commit () = raw_use_text ML_NameSpace.global (0, "") Output.ml_output false "commit();";


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
fun use s = Secure.use s handle ERROR msg => (writeln msg; raise Fail "ML error");
val toplevel_pp = Secure.toplevel_pp;
val system_out = Secure.system_out;
val system = Secure.system;
