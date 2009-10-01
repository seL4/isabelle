(*  Title:      Pure/Thy/thy_load.ML
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
  val split_thy_path: Path.T -> Path.T * string
  val check_file: Path.T -> Path.T -> (Path.T * File.ident) option
  val check_ml: Path.T -> Path.T -> (Path.T * File.ident) option
  val check_thy: Path.T -> string -> Path.T * File.ident
  val check_name: string -> string -> unit
  val deps_thy: Path.T -> string ->
   {master: Path.T * File.ident, text: string list, imports: string list, uses: Path.T list}
  val load_ml: Path.T -> Path.T -> Path.T * File.ident
end;

structure ThyLoad: THY_LOAD =
struct


(* maintain load path *)

local val load_path = Unsynchronized.ref [Path.current] in

fun show_path () = map Path.implode (! load_path);

fun del_path s = CRITICAL (fn () =>
    Unsynchronized.change load_path (remove (op =) (Path.explode s)));
fun add_path s = CRITICAL (fn () =>
    (del_path s; Unsynchronized.change load_path (cons (Path.explode s))));
fun path_add s = CRITICAL (fn () =>
    (del_path s; Unsynchronized.change load_path (fn path => path @ [Path.explode s])));
fun reset_path () = load_path := [Path.current];

fun with_paths ss f x =
  CRITICAL (fn () => Library.setmp load_path (! load_path @ map Path.explode ss) f x);
fun with_path s f x = with_paths [s] f x;

fun search_path dir path =
  distinct (op =) (dir :: (if Path.is_basic path then (! load_path) else [Path.current]));

end;


(* file formats *)

val ml_exts = ["ML", "sml"];
val ml_path = Path.ext "ML" o Path.basic;
val thy_path = Path.ext "thy" o Path.basic;

fun split_thy_path path =
  (case Path.split_ext path of
    (path', "thy") => (Path.dir path', Path.implode (Path.base path'))
  | _ => error ("Bad theory file specification " ^ Path.implode path));


(* check files *)

fun check_ext exts paths src_path =
  let
    val path = Path.expand src_path;
    val _ = Path.is_current path andalso error "Bad file specification";

    fun try_ext rel_path ext =
      let val ext_path = Path.expand (Path.ext ext rel_path)
      in Option.map (fn id => (File.full_path ext_path, id)) (File.ident ext_path) end;
    fun try_prfx prfx = get_first (try_ext (Path.append prfx path)) ("" :: exts);
  in get_first try_prfx paths end;

fun check_file dir path = check_ext [] (search_path dir path) path;
fun check_ml dir path = check_ext ml_exts (search_path dir path) path;

fun check_thy dir name =
  let
    val thy_file = thy_path name;
    val paths = search_path dir thy_file;
  in
    (case check_ext [] paths thy_file of
      NONE => error ("Could not find theory file " ^ quote (Path.implode thy_file) ^
        " in " ^ commas_quote (map Path.implode paths))
    | SOME thy_id => thy_id)
  end;

fun check_name name name' =
  if name = name' then ()
  else error ("Filename " ^ quote (Path.implode (thy_path name)) ^
    " does not agree with theory name " ^ quote name');


(* theory deps *)

fun deps_thy dir name =
  let
    val master as (path, _) = check_thy dir name;
    val text = explode (File.read path);
    val (name', imports, uses) =
      Thy_Header.read (Path.position path) (Source.of_list_limited 8000 text);
    val _ = check_name name name';
    val uses = map (Path.explode o #1) uses;
  in {master = master, text = text, imports = imports, uses = uses} end;


(* load files *)

fun load_ml dir raw_path =
  (case check_ml dir raw_path of
    NONE => error ("Could not find ML file " ^ quote (Path.implode raw_path))
  | SOME (path, id) => (ML_Context.eval_file path; (path, id)));

end;

structure Basic_Thy_Load: BASIC_THY_LOAD = ThyLoad;
open Basic_Thy_Load;
