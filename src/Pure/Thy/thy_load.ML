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
  val reset_path: unit -> unit
end;

signature THY_LOAD =
sig
  include BASIC_THY_LOAD
  val ml_path: string -> Path.T
  val find_file: Path.T -> (Path.T * File.info) option
  val check_file: Path.T -> File.info option
  val load_file: Path.T -> File.info
  val check_thy: string -> bool -> File.info
  val deps_thy: string -> bool -> File.info * (string list * Path.T list)
  val load_thy: string -> bool -> bool -> File.info
end;

signature PRIVATE_THY_LOAD =
sig
  include THY_LOAD
  val deps_thy_fn: (string -> bool -> Path.T -> string list * Path.T list) ref
  val load_thy_fn: (string -> bool -> bool -> Path.T -> unit) ref
end;

structure ThyLoad: PRIVATE_THY_LOAD =
struct


(* load path *)

val load_path = ref [Path.current];
fun change_path f = load_path := f (! load_path);

fun show_path () = map Path.pack (! load_path);
fun add_path s = change_path (fn path => path @ [Path.unpack s]);
fun del_path s = change_path (filter_out (equal (Path.unpack s)));
fun reset_path () = load_path := [Path.current];


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

val ml_path = Path.ext "ML" o Path.basic;


(* process theory files *)

val thy_ext = Path.ext "thy";

fun process_thy f name =
  let val path = thy_ext (Path.basic name) in
    (case find_file path of
      Some (path, info) => (info, f path)
    | None => error ("Could not find theory file " ^ quote (Path.pack path)))
  end;

(*hooks for theory syntax dependent operations*)
fun undefined _ = raise Match;
val deps_thy_fn = ref (undefined: string -> bool -> Path.T -> string list * Path.T list);
val load_thy_fn = ref (undefined: string -> bool -> bool -> Path.T -> unit);

fun check_thy name ml =
  let val (thy_info, _) = process_thy (K ()) name in
    (case if ml then check_file (ml_path name) else None of
      None => thy_info
    | Some info => File.join_info thy_info info)
  end;

fun deps_thy name ml = process_thy (fn path => ! deps_thy_fn name ml path) name;
fun load_thy name ml time = #1 (process_thy (fn path => ! load_thy_fn name ml time path) name);


end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
