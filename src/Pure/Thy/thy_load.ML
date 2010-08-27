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
  val set_master_path: Path.T -> unit
  val get_master_path: unit -> Path.T
  val master_directory: theory -> Path.T
  val require: Path.T -> theory -> theory
  val provide: Path.T * (Path.T * File.ident) -> theory -> theory
  val check_file: Path.T list -> Path.T -> Path.T * File.ident
  val check_thy: Path.T -> string -> Path.T * File.ident
  val deps_thy: Path.T -> string ->
   {master: Path.T * File.ident, text: string, imports: string list, uses: Path.T list}
  val loaded_files: theory -> Path.T list
  val all_current: theory -> bool
  val provide_file: Path.T -> theory -> theory
  val use_ml: Path.T -> unit
  val exec_ml: Path.T -> generic_theory -> generic_theory
  val begin_theory: Path.T -> string -> theory list -> (Path.T * bool) list -> theory
end;

structure Thy_Load: THY_LOAD =
struct

(* manage source files *)

type files =
 {master_dir: Path.T,                                 (*master directory of theory source*)
  required: Path.T list,                              (*source path*)
  provided: (Path.T * (Path.T * File.ident)) list};   (*source path, physical path, identifier*)

fun make_files (master_dir, required, provided): files =
 {master_dir = master_dir, required = required, provided = provided};

structure Files = Theory_Data
(
  type T = files;
  val empty = make_files (Path.current, [], []);
  fun extend _ = empty;
  fun merge _ = empty;
);

fun map_files f =
  Files.map (fn {master_dir, required, provided} =>
    make_files (f (master_dir, required, provided)));


val master_directory = #master_dir o Files.get;

fun master dir = map_files (fn _ => (dir, [], []));

fun require src_path =
  map_files (fn (master_dir, required, provided) =>
    if member (op =) required src_path then
      error ("Duplicate source file dependency: " ^ Path.implode src_path)
    else (master_dir, src_path :: required, provided));

fun provide (src_path, path_id) =
  map_files (fn (master_dir, required, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate resolution of source file dependency: " ^ Path.implode src_path)
    else (master_dir, required, (src_path, path_id) :: provided));


(* maintain default paths *)

local
  val load_path = Unsynchronized.ref [Path.current];
  val master_path = Unsynchronized.ref Path.current;
in

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

fun set_master_path path = master_path := path;
fun get_master_path () = ! master_path;

end;


(* check files *)

fun get_file dirs src_path =
  let
    val path = Path.expand src_path;
    val _ = Path.is_current path andalso error "Bad file specification";
  in
    dirs |> get_first (fn dir =>
      let val full_path = File.full_path (Path.append dir path) in
        (case File.ident full_path of
          NONE => NONE
        | SOME id => SOME (full_path, id))
      end)
  end;

fun check_file dirs file =
  (case get_file dirs file of
    SOME path_id => path_id
  | NONE => error ("Could not find file " ^ quote (Path.implode file) ^
      "\nin " ^ commas_quote (map Path.implode dirs)));

fun check_thy master_dir name =
  let
    val thy_file = Thy_Header.thy_path name;
    val dirs = search_path master_dir thy_file;
  in check_file dirs thy_file end;


(* theory deps *)

fun deps_thy master_dir name =
  let
    val master as (thy_path, _) = check_thy master_dir name;
    val text = File.read thy_path;
    val (name', imports, uses) = Thy_Header.read (Path.position thy_path) text;
    val _ = Thy_Header.consistent_name name name';
    val uses = map (Path.explode o #1) uses;
  in {master = master, text = text, imports = imports, uses = uses} end;



(* loaded files *)

val loaded_files = map (#1 o #2) o #provided o Files.get;

fun check_loaded thy =
  let
    val {required, provided, ...} = Files.get thy;
    val provided_paths = map #1 provided;
    val _ =
      (case subtract (op =) provided_paths required of
        [] => NONE
      | bad => error ("Pending source file dependencies: " ^ commas (map Path.implode (rev bad))));
    val _ =
      (case subtract (op =) required provided_paths of
        [] => NONE
      | bad => error ("Undeclared source file dependencies: " ^ commas (map Path.implode (rev bad))));
  in () end;

fun all_current thy =
  let
    val {master_dir, provided, ...} = Files.get thy;
    fun current (src_path, (_, id)) =
      (case get_file [master_dir] src_path of
        NONE => false
      | SOME (_, id') => id = id');
  in can check_loaded thy andalso forall current provided end;

val _ = Context.>> (Context.map_theory (Theory.at_end (fn thy => (check_loaded thy; NONE))));


(* provide files *)

fun provide_file src_path thy =
  provide (src_path, check_file [master_directory thy] src_path) thy;

fun use_ml src_path =
  if is_none (Context.thread_data ()) then
    ML_Context.eval_file (#1 (check_file [Path.current] src_path))
  else
    let
      val thy = ML_Context.the_global_context ();
      val (path, id) = check_file [master_directory thy] src_path;

      val _ = ML_Context.eval_file path;
      val _ = Context.>> Local_Theory.propagate_ml_env;

      val provide = provide (src_path, (path, id));
      val _ = Context.>> (Context.mapping provide (Local_Theory.background_theory provide));
    in () end;

fun exec_ml src_path = ML_Context.exec (fn () => use_ml src_path);


(* begin theory *)

fun begin_theory dir name parents uses =
  Theory.begin_theory name parents
  |> master dir
  |> fold (require o fst) uses
  |> fold (fn (path, true) => Context.theory_map (exec_ml path) o Theory.checkpoint | _ => I) uses
  |> Theory.checkpoint;

end;

structure Basic_Thy_Load: BASIC_THY_LOAD = Thy_Load;
open Basic_Thy_Load;
