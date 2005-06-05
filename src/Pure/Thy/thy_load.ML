(*  Title:      Pure/Thy/thy_load.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory loader primitives, including load path.
*)

signature BASIC_THY_LOAD =
sig
  val show_path: unit -> string list
  val add_path: string -> unit
  val path_add: string -> unit
  val del_path: string -> unit
  val with_path: string -> ('a -> 'b) -> 'a -> 'b
  val with_paths: string list -> ('a -> 'b) -> 'a -> 'b
  val reset_path: unit -> unit
end;

signature THY_LOAD =
sig
  include BASIC_THY_LOAD
  val cond_add_path: Path.T -> ('a -> 'b) -> 'a -> 'b
  val ml_path: string -> Path.T
  val thy_path: string -> Path.T
  val check_file: Path.T option -> Path.T -> (Path.T * File.info) option
  val load_file: Path.T option -> Path.T -> (Path.T * File.info)
  eqtype master
  val get_thy: master -> Path.T * File.info
  val check_thy: Path.T -> string -> bool -> master
  val deps_thy: Path.T -> string -> bool -> master * (string list * Path.T list)
  val load_thy: Path.T -> string -> bool -> bool -> master
end;

(*this backdoor sealed later*)
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
fun del_path s = change_path (filter_out (equal (Path.unpack s)));
fun add_path s = (del_path s; change_path (cons (Path.unpack s)));
fun path_add s = (del_path s; change_path (fn path => path @ [Path.unpack s]));
fun reset_path () = load_path := [Path.current];
fun with_paths ss f x = Library.setmp load_path (! load_path @ map Path.unpack ss) f x;
fun with_path s f x = with_paths [s] f x;

fun cond_add_path path f x =
  if Path.is_current path then f x else Library.setmp load_path (path :: ! load_path) f x;


(* file formats *)

val ml_exts = ["", "ML", "sml"];
val ml_path = Path.ext "ML" o Path.basic;
val thy_path = Path.ext "thy" o Path.basic;


(* check_file *)

fun check_file current src_path =
  let
    val path = Path.expand src_path;

    fun find_ext rel_path ext =
      let val ext_path = Path.expand (Path.ext ext rel_path)
      in Option.map (fn info => (File.full_path ext_path, info)) (File.info ext_path) end;

    fun find_dir dir =
      get_first (find_ext (Path.append dir path)) ml_exts;

    fun add_current ps = (case current of NONE => ps
          | (SOME p) => if Path.is_current p then ps else p :: ps);

    val paths =
      if Path.is_current path then error "Bad file specification"
      else if Path.is_basic path then add_current (! load_path)
      else add_current [Path.current];
  in get_first find_dir paths end;


(* load_file *)

fun load_file current raw_path =
  (case check_file current raw_path of
    NONE => error ("Could not find ML file " ^ quote (Path.pack raw_path))
  | SOME (path, info) => (File.use path; (path, info)));


(* datatype master *)

datatype master = Master of (Path.T * File.info) * (Path.T * File.info) option;

fun get_thy (Master (thy, _)) = thy;


(* check / process theory files *)

local

fun check_thy_aux (name, ml) =
  let val thy_file = thy_path name in
    case check_file NONE thy_file of
      NONE => error ("Could not find theory file " ^ quote (Path.pack thy_file) ^
        " in dir(s) " ^ commas_quote (show_path ()))
    | SOME thy_info => (thy_info, if ml then check_file NONE (ml_path name) else NONE)
  end;

in

fun check_thy dir name ml = Master (cond_add_path dir check_thy_aux (name, ml));

fun process_thy dir f name ml =
  let val master as Master ((path, _), _) = check_thy dir name ml
  in (master, cond_add_path dir f path) end;

end;


(* deps_thy and load_thy *)

(*hooks for theory syntax dependent operations*)
fun undefined _ = raise Match;
val deps_thy_fn = ref (undefined: string -> bool -> Path.T -> string list * Path.T list);
val load_thy_fn = ref (undefined: string -> bool -> bool -> Path.T -> unit);

fun deps_thy dir name ml = process_thy dir (! deps_thy_fn name ml) name ml;
fun load_thy dir name ml time = #1 (process_thy dir (! load_thy_fn name ml time) name ml);


end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
