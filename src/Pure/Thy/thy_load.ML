(*  Title:      Pure/Thy/thy_load.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory loader primitives.
*)

signature BASIC_THY_LOAD =
sig
  val show_path: unit -> string list
  val add_path: string -> unit
  val del_path: string -> unit
end;

signature THY_LOAD =
sig
  include BASIC_THY_LOAD
  val thy_ext: string
  val find_file: Path.T -> (Path.T * File.info) option
  val check_file: Path.T -> File.info option
  val load_file: Path.T -> File.info
  val check_thy: string -> File.info
  val deps_thy: string -> File.info * (string list * Path.T list)
  val load_thy: string -> File.info * theory
end;

signature PRIVATE_THY_LOAD =
sig
  include THY_LOAD
  val deps_thy_fn: (Path.T -> string list * Path.T list) ref
  val load_thy_fn: (Path.T -> theory) ref
end;

structure ThyLoad: PRIVATE_THY_LOAD =
struct


(* load path *)

val load_path = ref [Path.current];
fun change_path f = load_path := f (! load_path);

fun show_path () = map Path.pack (! load_path);
fun add_path s = change_path (fn path => path @ [Path.unpack s]);
fun del_path s = change_path (filter_out (equal (Path.unpack s)));


(* find / check file *)

fun find_file file_src =
  let
    val file = Path.expand file_src;
    fun find dir =
      let val full_path = Path.append dir file
      in apsome (pair full_path) (File.info full_path) end;
  in get_first find (if Path.is_basic file then ! load_path else [Path.current]) end;


(* process ML files *)

val check_file = apsome #2 o find_file;

fun load_file raw_path =
  (case find_file raw_path of
    Some (path, info) => (Use.use_path path; info)
  | None => error ("Could not find ML file " ^ quote (Path.pack raw_path)));


(* process theory files *)

val thy_ext = "thy";

fun process_thy f name =
  let val path = Path.ext thy_ext (Path.basic name) in
    (case find_file path of
      Some (path, info) => (info, f path)
    | None => error ("Could not find theory file " ^ quote (Path.pack path)))
  end;

(*hooks for theory syntax dependent operations*)
fun undefined _ = raise Match;
val deps_thy_fn = ref (undefined: Path.T -> string list * Path.T list);
val load_thy_fn = ref (undefined: Path.T -> theory);

val check_thy = #1 o process_thy (K ());
val deps_thy = process_thy (fn path => ! deps_thy_fn path);
val load_thy = process_thy (fn path => ! load_thy_fn path);


end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
