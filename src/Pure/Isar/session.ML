(*  Title:      Pure/Isar/session.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val welcome: unit -> string
  val use_dir: bool -> bool -> string -> string -> string -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct


(* session state *)

val pure = "Pure";

val session = ref ([pure]: string list);
val session_path = ref ([]: string list);
val session_finished = ref false;

fun path () = ! session_path;

fun add_path reset s =
  (session := ! session @ [s]; session_path := ((if reset then [] else ! session_path) @ [s]));


(* diagnostics *)

fun str_of [] = "Pure"
  | str_of elems = space_implode "/" elems;

fun welcome () = "Welcome to Isabelle/" ^ str_of (path ()) ^ " (" ^ version ^ ")";


(* init *)

fun init reset parent name =
  if not (parent mem_string (! session)) orelse not (! session_finished) then
    error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
  else (add_path reset name; session_finished := false);


(* finish *)

fun finish () =
  (ThyInfo.finish ();
    Present.finish ();
    session_finished := true);


(* use_dir *)

val root_file = ThyLoad.ml_path "ROOT";

val rpath = ref (None : Url.T option);

fun use_dir reset info parent name rpath_str =
  (init reset parent name;
   if rpath_str = "" then () else
     if is_some (!rpath) then
       error "Path for remote theory browsing information may only be set once"
     else
       rpath := Some (Url.unpack rpath_str);
   Present.init info (path ()) name (!rpath);
   File.symbol_use root_file;
   finish ()) handle exn => (writeln (Toplevel.exn_message exn); exit 1);


end;
