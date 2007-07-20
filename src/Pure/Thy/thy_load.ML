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
  val ml_exts: string list
  val ml_path: string -> Path.T
  val thy_path: string -> Path.T
  val check_file: Path.T -> Path.T -> (Path.T * File.ident) option
  val check_ml: Path.T -> Path.T -> (Path.T * File.ident) option
  val check_thy: Path.T -> string -> bool -> (Path.T * File.ident) * (Path.T * File.ident) option
  val deps_thy: Path.T -> string -> bool ->
    ((Path.T * File.ident) * (Path.T * File.ident) option) * (string list * Path.T list)
  val load_ml: Path.T -> Path.T -> Path.T * File.ident
  val load_thy: Path.T -> string -> bool -> bool ->
    (Path.T * File.ident) * (Path.T * File.ident) option
end;

(*this backdoor sealed later*)
signature PRIVATE_THY_LOAD =
sig
  include THY_LOAD
  val load_thy_fn: (Path.T -> string -> bool -> bool ->
    (Path.T * File.ident) * (Path.T * File.ident) option) ref
end;

structure ThyLoad: PRIVATE_THY_LOAD =
struct


(* maintain load path *)

val load_path = ref [Path.current];

fun show_path () = map Path.implode (! load_path);
fun del_path s = change load_path (remove (op =) (Path.explode s));
fun add_path s = (del_path s; change load_path (cons (Path.explode s)));
fun path_add s = (del_path s; change load_path (fn path => path @ [Path.explode s]));
fun reset_path () = load_path := [Path.current];
fun with_paths ss f x = Library.setmp load_path (! load_path @ map Path.explode ss) f x;
fun with_path s f x = with_paths [s] f x;


(* file formats *)

val ml_exts = ["ML", "sml"];
val ml_path = Path.ext "ML" o Path.basic;
val thy_path = Path.ext "thy" o Path.basic;


(* check files *)

fun check_ext exts dir src_path =
  let
    val path = Path.expand src_path;
    val _ = Path.is_current path andalso error "Bad file specification";

    fun try_ext rel_path ext =
      let val ext_path = Path.expand (Path.ext ext rel_path)
      in Option.map (fn id => (File.full_path ext_path, id)) (File.ident ext_path) end;
    fun try_prfx prfx = get_first (try_ext (Path.append prfx path)) ("" :: exts);
  in
    (case get_first try_prfx (if Path.is_basic path then (! load_path) else [Path.current]) of
      NONE => try_prfx dir
    | res => res)
  end;

val check_file = check_ext [];
val check_ml = check_ext ml_exts;

fun check_thy dir name ml =
  let val thy_file = thy_path name in
    (case check_file dir thy_file of
      NONE => error ("Could not find theory file " ^ quote (Path.implode thy_file) ^
        " in " ^ commas_quote (map Path.implode (dir :: ! load_path)))  (* FIXME imprecise *)
    | SOME thy_id => (thy_id, if ml then check_file dir (ml_path name) else NONE))
  end;


(* theory deps *)

fun deps_thy dir name ml =
  let
    val master as ((path, _), _) = check_thy dir name ml;
    val (name', imports, uses) =
      ThyHeader.read (Position.path path) (Source.of_string_limited (File.read path));
    val _ = name = name' orelse
      error ("Filename " ^ quote (Path.implode (Path.base path)) ^
        " does not agree with theory name " ^ quote name');
    val ml_file =
      if ml andalso is_some (check_file dir (ml_path name))
      then [ml_path name] else [];
  in (master, (imports, map (Path.explode o #1) uses @ ml_file)) end;


(* load files *)

fun load_ml dir raw_path =
  (case check_ml dir raw_path of
    NONE => error ("Could not find ML file " ^ quote (Path.implode raw_path))
  | SOME (path, id) => (ML_Context.use path; (path, id)));

(*dependent on outer syntax*)
val load_thy_fn = ref (undefined: Path.T -> string -> bool -> bool ->
  (Path.T * File.ident) * (Path.T * File.ident) option);
fun load_thy dir name ml time = ! load_thy_fn dir name ml time;

end;

structure BasicThyLoad: BASIC_THY_LOAD = ThyLoad;
open BasicThyLoad;
