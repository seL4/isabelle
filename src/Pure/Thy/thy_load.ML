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
  val check_file: Path.T -> (Path.T * File.info) option
  val load_file: Path.T -> (Path.T * File.info)
  val check_thy: Path.T option -> string -> bool -> (Path.T * File.info) list
  val deps_thy: Path.T option -> string -> bool ->
    (Path.T * File.info) list * (string list * Path.T list)
  val load_thy: Path.T option -> string -> bool -> bool -> (Path.T * File.info) list
end;

(*backdoor sealed later*)
signature PRIVATE_THY_LOAD =
sig
  include THY_LOAD
  val deps_thy_fn: (string -> bool -> Path.T -> string list * Path.T list) ref
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


(* load_file *)

fun load_file raw_path =
  (case check_file raw_path of
    None => error ("Could not find ML file " ^ quote (Path.pack raw_path))
  | Some (path, info) => (Symbol.use path; (path, info)));


(* check_thy *)

fun tmp_path None f x = f x
  | tmp_path (Some path) f x = Library.setmp load_path [path] f x;

fun check_thy_aux name ml =
  (case check_file (thy_path name) of
    None => error ("Could not find theory file for " ^ quote name ^ " in dir(s) " ^
      commas_quote (show_path ()))
  | Some thy_info => thy_info ::
      (case if ml then check_file (ml_path name) else None of
        None => []
      | Some info => [info]));

fun check_thy dir name ml = tmp_path dir (check_thy_aux name) ml;


(* process theory files *)

(*hooks for theory syntax dependent operations*)
fun undefined _ = raise Match;
val deps_thy_fn = ref (undefined: string -> bool -> Path.T -> string list * Path.T list);
val load_thy_fn = ref (undefined: string -> bool -> bool -> Path.T -> unit);

fun process_thy dir f name ml =
  let val master = check_thy dir name ml
  in (master, f (#1 (hd master))) end;

fun deps_thy dir name ml = process_thy dir (! deps_thy_fn name ml) name ml;
fun load_thy dir name ml time = #1 (process_thy dir (! load_thy_fn name ml time) name ml);


end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
