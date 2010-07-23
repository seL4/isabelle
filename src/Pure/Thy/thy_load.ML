(*  Title:      Pure/Thy/thy_load.ML
    Author:     Markus Wenzel, TU Muenchen

Loading files that contribute to a theory, including global load path
management.
*)

signature BASIC_THY_LOAD =
sig
  val show_path: unit -> string list
  val add_path: string -> unit
  val path_add: string -> unit
  val del_path: string -> unit
  val reset_path: unit -> unit
end;

signature THY_LOAD =
sig
  include BASIC_THY_LOAD
  val ml_path: string -> Path.T
  val thy_path: string -> Path.T
  val split_thy_path: Path.T -> Path.T * string
  val consistent_name: string -> string -> unit
  val test_file: Path.T -> Path.T -> (Path.T * File.ident) option
  val check_file: Path.T -> Path.T -> Path.T * File.ident
  val check_thy: Path.T -> string -> Path.T * File.ident
  val deps_thy: Path.T -> string ->
   {master: Path.T * File.ident, text: string, imports: string list, uses: Path.T list}
  val load_ml: Path.T -> Path.T -> Path.T * File.ident
end;

structure Thy_Load: THY_LOAD =
struct

(* maintain load path *)

local val load_path = Unsynchronized.ref [Path.current] in

fun show_path () = map Path.implode (! load_path);

fun del_path s =
  CRITICAL (fn () => Unsynchronized.change load_path (remove (op =) (Path.explode s)));

fun add_path s =
  CRITICAL (fn () => (del_path s; Unsynchronized.change load_path (cons (Path.explode s))));

fun path_add s =
  CRITICAL (fn () =>
    (del_path s; Unsynchronized.change load_path (fn path => path @ [Path.explode s])));

fun reset_path () = CRITICAL (fn () => load_path := [Path.current]);

fun search_path dir path =
  distinct (op =) (dir :: (if Path.is_basic path then (! load_path) else [Path.current]));

end;


(* file formats *)

val ml_path = Path.ext "ML" o Path.basic;
val thy_path = Path.ext "thy" o Path.basic;

fun split_thy_path path =
  (case Path.split_ext path of
    (path', "thy") => (Path.dir path', Path.implode (Path.base path'))
  | _ => error ("Bad theory file specification " ^ Path.implode path));

fun consistent_name name name' =
  if name = name' then ()
  else error ("Filename " ^ quote (Path.implode (thy_path name)) ^
    " does not agree with theory name " ^ quote name');


(* check files *)

local

exception NOT_FOUND of Path.T list * Path.T;

fun try_file dir src_path =
  let
    val prfxs = search_path dir src_path;
    val path = Path.expand src_path;
    val _ = Path.is_current path andalso error "Bad file specification";
    val result =
      prfxs |> get_first (fn prfx =>
        let val full_path = File.full_path (Path.append prfx path)
        in Option.map (pair full_path) (File.ident full_path) end);
  in
    (case result of
      SOME res => res
    | NONE => raise NOT_FOUND (prfxs, path))
  end;

in

fun test_file dir file =
  SOME (try_file dir file) handle NOT_FOUND _ => NONE;

fun check_file dir file =
  try_file dir file handle NOT_FOUND (prfxs, path) =>
    error ("Could not find file " ^ quote (Path.implode path) ^
      "\nin " ^ commas_quote (map Path.implode prfxs));

fun check_thy dir name = check_file dir (thy_path name);

end;


(* theory deps *)

fun deps_thy dir name =
  let
    val master as (path, _) = check_thy dir name;
    val text = File.read path;
    val (name', imports, uses) =
      Thy_Header.read (Path.position path) (Source.of_string_limited 8000 text);
    val _ = consistent_name name name';
    val uses = map (Path.explode o #1) uses;
  in {master = master, text = text, imports = imports, uses = uses} end;


(* ML files *)

fun load_ml dir raw_path =
  let
    val (path, id) = check_file dir raw_path;
    val _ = ML_Context.eval_file path;
  in (path, id) end;

end;

structure Basic_Thy_Load: BASIC_THY_LOAD = Thy_Load;
open Basic_Thy_Load;
