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
  val with_path: string -> ('a -> 'b) -> 'a -> 'b
  val reset_path: unit -> unit
end;

signature THY_LOAD =
sig
  include BASIC_THY_LOAD
  val ml_path: string -> Path.T
  val check_file: Path.T -> (Path.T * File.info) option
  val may_load_file: bool -> Path.T -> (Path.T * File.info)
  eqtype master
  val get_thy: master -> Path.T * File.info
  val check_thy: Path.T -> string -> master
  val deps_thy: Path.T -> string -> master * (string list * Path.T list)
  val load_thy: Path.T -> string -> bool -> bool -> master
end;

(*backdoor sealed later*)
signature PRIVATE_THY_LOAD =
sig
  include THY_LOAD
  val deps_thy_fn: (string -> Path.T -> string list * Path.T list) ref
  val load_thy_fn: (string -> bool -> bool -> Path.T -> unit) ref
end;

structure ThyLoad: PRIVATE_THY_LOAD =
struct


(* maintain load path *)

val load_path = ref [Path.current];
fun change_path f = load_path := f (! load_path);

fun show_path () = map Path.pack (! load_path);
fun add_path s = change_path (cons (Path.unpack s));
fun del_path s = change_path (filter_out (equal (Path.unpack s)));
fun reset_path () = load_path := [Path.current];
fun with_path s f x = Library.setmp load_path (Path.unpack s :: ! load_path) f x;

fun cond_with_path path f x =
  if Path.is_current path then f x else Library.setmp load_path (path :: ! load_path) f x;


(* file formats *)

val ml_exts = ["", "ML", "sml"];
val ml_path = Path.ext "ML" o Path.basic;
val thy_path = Path.ext "thy" o Path.basic;


(* check_file *)

fun check_file src_path =
  let
    val path = Path.expand src_path;

    fun find_ext rel_path ext =
      let val ext_path = Path.ext ext rel_path
      in apsome (fn info => (File.full_path ext_path, info)) (File.info ext_path) end;

    fun find_dir dir =
      get_first (find_ext (Path.append dir path)) ml_exts;
  in get_first find_dir (if Path.is_basic path then ! load_path else [Path.current]) end;


(* may_load_file *)

fun may_load_file really raw_path =
  (case check_file raw_path of
    None => error ("Could not find ML file " ^ quote (Path.pack raw_path))
  | Some (path, info) => (if really then File.symbol_use path else (); (path, info)));


(* datatype master *)

datatype master = Master of (Path.T * File.info) * (Path.T * File.info) option;

fun get_thy (Master (thy, _)) = thy;


(* check_thy *)

fun check_thy_aux name =
  (case check_file (thy_path name) of
    None => error ("Could not find theory file for " ^ quote name ^ " in dir(s) " ^
      commas_quote (show_path ()))
  | Some thy_info => (thy_info, check_file (ml_path name)));

fun check_thy dir name = Master (cond_with_path dir check_thy_aux name);


(* process theory files *)

(*hooks for theory syntax dependent operations*)
fun undefined _ = raise Match;
val deps_thy_fn = ref (undefined: string -> Path.T -> string list * Path.T list);
val load_thy_fn = ref (undefined: string -> bool -> bool -> Path.T -> unit);

fun process_thy dir f name =
  let val master as Master ((path, _), _) = check_thy dir name
  in (master, cond_with_path dir f path) end;

fun deps_thy dir name = process_thy dir (! deps_thy_fn name) name;
fun load_thy dir name ml time = #1 (process_thy dir (! load_thy_fn name ml time) name);


end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
