(*  Title:      Pure/Isar/session.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val name: unit -> string
  val welcome: unit -> string
  val use_dir:
    string list -> bool -> bool -> string -> string -> string -> string -> string -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct


(* session state *)

val pure = "Pure";

val session = ref ([pure]: string list);
val session_path = ref ([]: string list);
val session_finished = ref false;
val rpath = ref (None: Url.T option);


(* access path *)

fun path () = ! session_path;

fun str_of [] = pure
  | str_of elems = space_implode "/" elems;

fun name () = "Isabelle/" ^ str_of (path ());
fun welcome () = "Welcome to " ^ name () ^ " (" ^ version ^ ")";


(* add_path *)

fun add_path reset s =
  let val sess = ! session @ [s] in
    (case Library.duplicates sess of
      [] => (session := sess; session_path := ((if reset then [] else ! session_path) @ [s]))
    | dups => error ("Duplicate session identifiers " ^ commas_quote dups ^ " in " ^ str_of sess))
  end;


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

fun get_rpath rpath_str =
  (if rpath_str = "" then () else
     if is_some (!rpath) then
       error "Path for remote theory browsing information may only be set once"
     else
       rpath := Some (Url.unpack rpath_str);
   (!rpath, rpath_str <> ""));

fun use_dir modes reset info doc parent name dump rpath_str =
  Library.setmp print_mode (modes @ ! print_mode) (fn () =>
    (init reset parent name;
     Present.init info doc (path ()) name
       (if dump = "" then None else Some (Path.unpack dump)) (get_rpath rpath_str);
     File.symbol_use root_file;
     finish ())) ()
  handle exn => (writeln (Toplevel.exn_message exn); exit 1);


end;
