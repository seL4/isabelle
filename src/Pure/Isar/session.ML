(*  Title:      Pure/Isar/session.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val name: unit -> string
  val welcome: unit -> string
  val use_dir: string -> bool -> string list -> bool -> bool -> string -> bool ->
    string list -> string -> string -> bool * string -> string -> int -> bool -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct


(* session state *)

val session = ref ([Context.PureN]: string list);
val session_path = ref ([]: string list);
val session_finished = ref false;
val remote_path = ref (NONE: Url.T option);


(* access path *)

fun path () = ! session_path;

fun str_of [] = Context.PureN
  | str_of elems = space_implode "/" elems;

fun name () = "Isabelle/" ^ str_of (path ());
fun welcome () = "Welcome to " ^ name () ^ " (" ^ version ^ ")";


(* add_path *)

fun add_path reset s =
  let val sess = ! session @ [s] in
    (case gen_duplicates (op =) sess of
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
  (Output.accumulated_time ();
    ThyInfo.finish ();
    Present.finish ();
    session_finished := true);


(* use_dir *)

fun get_rpath rpath =
  (if rpath = "" then () else
     if is_some (! remote_path) then
       error "Path for remote theory browsing information may only be set once"
     else
       remote_path := SOME (Url.unpack rpath);
   (! remote_path, rpath <> ""));

fun dumping (_, "") = NONE
  | dumping (cp, path) = SOME (cp, Path.unpack path);

fun use_dir root build modes reset info doc doc_graph doc_versions
    parent name dump rpath level verbose =
  Library.setmp print_mode (modes @ ! print_mode)
    (Library.setmp Proofterm.proofs level (fn () =>
      (init reset parent name;
       Present.init build info doc doc_graph doc_versions (path ()) name
         (dumping dump) (get_rpath rpath) verbose;
       ThyInfo.time_use root;
       finish ()))) ()
  handle exn => (Output.error_msg (Toplevel.exn_message exn); exit 1);


end;
