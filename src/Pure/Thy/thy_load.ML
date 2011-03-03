(*  Title:      Pure/Thy/thy_load.ML
    Author:     Markus Wenzel, TU Muenchen

Loading files that contribute to a theory, including global load path
management.
*)

signature THY_LOAD =
sig
  eqtype file_ident
  val pretty_file_ident: file_ident -> Pretty.T
  val file_ident: Path.T -> file_ident option
  val set_master_path: Path.T -> unit
  val get_master_path: unit -> Path.T
  val master_directory: theory -> Path.T
  val imports_of: theory -> string list
  val provide: Path.T * (Path.T * file_ident) -> theory -> theory
  val check_file: Path.T -> Path.T -> Path.T * file_ident
  val check_thy: Path.T -> string -> Path.T * file_ident
  val deps_thy: Path.T -> string ->
   {master: Path.T * file_ident, text: string, imports: string list, uses: Path.T list}
  val loaded_files: theory -> Path.T list
  val all_current: theory -> bool
  val provide_file: Path.T -> theory -> theory
  val use_ml: Path.T -> unit
  val exec_ml: Path.T -> generic_theory -> generic_theory
  val begin_theory: Path.T -> string -> string list -> theory list -> (Path.T * bool) list -> theory
end;

structure Thy_Load: THY_LOAD =
struct

(* file identification *)

local
  val file_ident_cache =
    Synchronized.var "file_ident_cache"
      (Symtab.empty: {time_stamp: string, id: string} Symtab.table);
in

fun check_cache (path, time) =
  (case Symtab.lookup (Synchronized.value file_ident_cache) path of
    NONE => NONE
  | SOME {time_stamp, id} => if time_stamp = time then SOME id else NONE);

fun update_cache (path, (time, id)) =
  Synchronized.change file_ident_cache
    (Symtab.update (path, {time_stamp = time, id = id}));

end;

datatype file_ident = File_Ident of string;

fun pretty_file_ident (File_Ident s) = Pretty.str (quote s);

fun file_ident path =
  let val physical_path = perhaps (try OS.FileSys.fullPath) (File.platform_path path) in
    (case try (Time.toString o OS.FileSys.modTime) physical_path of
      NONE => NONE
    | SOME mod_time => SOME (File_Ident
        (case getenv "ISABELLE_FILE_IDENT" of
          "" => physical_path ^ ": " ^ mod_time
        | cmd =>
            (case check_cache (physical_path, mod_time) of
              SOME id => id
            | NONE =>
                let
                  val (id, rc) =  (*potentially slow*)
                    bash_output
                      ("\"$ISABELLE_HOME/lib/scripts/fileident\" " ^ File.shell_quote physical_path);
                in
                  if id <> "" andalso rc = 0 then (update_cache (physical_path, (mod_time, id)); id)
                  else error ("Failed to identify file " ^ quote (Path.implode path) ^ " by " ^ cmd)
                end))))
  end;


(* manage source files *)

type files =
 {master_dir: Path.T,  (*master directory of theory source*)
  imports: string list,  (*source specification of imports*)
  required: Path.T list,  (*source path*)
  provided: (Path.T * (Path.T * file_ident)) list};  (*source path, physical path, identifier*)

fun make_files (master_dir, imports, required, provided): files =
 {master_dir = master_dir, imports = imports, required = required, provided = provided};

structure Files = Theory_Data
(
  type T = files;
  val empty = make_files (Path.current, [], [], []);
  fun extend _ = empty;
  fun merge _ = empty;
);

fun map_files f =
  Files.map (fn {master_dir, imports, required, provided} =>
    make_files (f (master_dir, imports, required, provided)));


val master_directory = #master_dir o Files.get;
val imports_of = #imports o Files.get;

fun put_deps dir imports = map_files (fn _ => (dir, imports, [], []));

fun require src_path =
  map_files (fn (master_dir, imports, required, provided) =>
    if member (op =) required src_path then
      error ("Duplicate source file dependency: " ^ Path.implode src_path)
    else (master_dir, imports, src_path :: required, provided));

fun provide (src_path, path_id) =
  map_files (fn (master_dir, imports, required, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate resolution of source file dependency: " ^ Path.implode src_path)
    else (master_dir, imports, required, (src_path, path_id) :: provided));


(* stateful master path *)

local
  val master_path = Unsynchronized.ref Path.current;
in

fun set_master_path path = master_path := path;
fun get_master_path () = ! master_path;

end;


(* check files *)

fun get_file dir src_path =
  let
    val path = Path.expand src_path;
    val _ = Path.is_current path andalso error "Bad file specification";
    val full_path = File.full_path (Path.append dir path);
  in
    (case file_ident full_path of
      NONE => NONE
    | SOME id => SOME (full_path, id))
  end;

fun check_file dir file =
  (case get_file dir file of
    SOME path_id => path_id
  | NONE => error ("Could not find file " ^ quote (Path.implode file) ^
      "\nin " ^ quote (Path.implode dir)));

fun check_thy dir name =
  check_file dir (Thy_Header.thy_path name);


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
      (case get_file master_dir src_path of
        NONE => false
      | SOME (_, id') => id = id');
  in can check_loaded thy andalso forall current provided end;

val _ = Context.>> (Context.map_theory (Theory.at_end (fn thy => (check_loaded thy; NONE))));


(* provide files *)

fun provide_file src_path thy =
  provide (src_path, check_file (master_directory thy) src_path) thy;

fun use_ml src_path =
  if is_none (Context.thread_data ()) then
    ML_Context.eval_file (#1 (check_file Path.current src_path))
  else
    let
      val thy = ML_Context.the_global_context ();
      val (path, id) = check_file (master_directory thy) src_path;

      val _ = ML_Context.eval_file path;
      val _ = Context.>> Local_Theory.propagate_ml_env;

      val provide = provide (src_path, (path, id));
      val _ = Context.>> (Context.mapping provide (Local_Theory.background_theory provide));
    in () end;

fun exec_ml src_path = ML_Context.exec (fn () => use_ml src_path);


(* begin theory *)

fun begin_theory dir name imports parents uses =
  Theory.begin_theory name parents
  |> put_deps dir imports
  |> fold (require o fst) uses
  |> fold (fn (path, true) => Context.theory_map (exec_ml path) o Theory.checkpoint | _ => I) uses
  |> Theory.checkpoint;

end;

