(*  Title:      Pure/Thy/thy_load.ML
    Author:     Makarius

Loading files that contribute to a theory.  Global master path.
*)

signature THY_LOAD =
sig
  val master_directory: theory -> Path.T
  val imports_of: theory -> string list
  val provide: Path.T * (Path.T * SHA1.digest) -> theory -> theory
  val check_file: Path.T -> Path.T -> Path.T
  val thy_path: Path.T -> Path.T
  val check_thy: Path.T -> string ->
    {master: Path.T * SHA1.digest, text: string, imports: string list, uses: (Path.T * bool) list}
  val load_file: theory -> Path.T -> (Path.T * SHA1.digest) * string
  val use_file: Path.T -> theory -> string * theory
  val loaded_files: theory -> Path.T list
  val all_current: theory -> bool
  val use_ml: Path.T -> unit
  val exec_ml: Path.T -> generic_theory -> generic_theory
  val begin_theory: Path.T -> string -> string list -> (Path.T * bool) list ->
    theory list -> theory
  val load_thy: int -> Path.T -> string -> string list -> (Path.T * bool) list ->
    Position.T -> string -> theory list -> theory * unit future
  val set_master_path: Path.T -> unit
  val get_master_path: unit -> Path.T
end;

structure Thy_Load: THY_LOAD =
struct

(* manage source files *)

type files =
 {master_dir: Path.T,  (*master directory of theory source*)
  imports: string list,  (*source specification of imports*)
  required: Path.T list,  (*source path*)
  provided: (Path.T * (Path.T * SHA1.digest)) list};  (*source path, physical path, digest*)

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
      error ("Duplicate source file dependency: " ^ Path.print src_path)
    else (master_dir, imports, src_path :: required, provided));

fun provide (src_path, path_id) =
  map_files (fn (master_dir, imports, required, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate resolution of source file dependency: " ^ Path.print src_path)
    else (master_dir, imports, required, (src_path, path_id) :: provided));


(* check files *)

fun check_file dir file = File.check_file (File.full_path dir file);

val thy_path = Path.ext "thy";

fun check_thy dir name =
  let
    val path = thy_path (Path.basic name);
    val master_file = check_file dir path;
    val text = File.read master_file;
    val (name', imports, uses) =
      if name = Context.PureN then (Context.PureN, [], [])
      else Thy_Header.read (Path.position master_file) text;
    val _ = name <> name' andalso
      error ("Bad file name " ^ Path.print path ^ " for theory " ^ quote name');
  in {master = (master_file, SHA1.digest text), text = text, imports = imports, uses = uses} end;


(* load files *)

fun load_file thy src_path =
  let
    val full_path = check_file (master_directory thy) src_path;
    val text = File.read full_path;
    val id = SHA1.digest text;
  in ((full_path, id), text) end;

fun use_file src_path thy =
  let
    val (path_id, text) = load_file thy src_path;
    val thy' = provide (src_path, path_id) thy;
  in (text, thy') end;

val loaded_files = map (#1 o #2) o #provided o Files.get;

fun check_loaded thy =
  let
    val {required, provided, ...} = Files.get thy;
    val provided_paths = map #1 provided;
    val _ =
      (case subtract (op =) provided_paths required of
        [] => NONE
      | bad => error ("Pending source file dependencies: " ^ commas (map Path.print (rev bad))));
    val _ =
      (case subtract (op =) required provided_paths of
        [] => NONE
      | bad => error ("Undeclared source file dependencies: " ^ commas (map Path.print (rev bad))));
  in () end;

fun all_current thy =
  let
    val {provided, ...} = Files.get thy;
    fun current (src_path, (_, id)) =
      (case try (load_file thy) src_path of
        NONE => false
      | SOME ((_, id'), _) => id = id');
  in can check_loaded thy andalso forall current provided end;

val _ = Context.>> (Context.map_theory (Theory.at_end (fn thy => (check_loaded thy; NONE))));


(* provide files *)

fun eval_file path text = ML_Context.eval_text true (Path.position path) text;

fun use_ml src_path =
  if is_none (Context.thread_data ()) then
    let val path = check_file Path.current src_path
    in eval_file path (File.read path) end
  else
    let
      val thy = ML_Context.the_global_context ();

      val ((path, id), text) = load_file thy src_path;
      val _ = eval_file path text;
      val _ = Context.>> Local_Theory.propagate_ml_env;

      val provide = provide (src_path, (path, id));
      val _ = Context.>> (Context.mapping provide (Local_Theory.background_theory provide));
    in () end;

fun exec_ml src_path = ML_Context.exec (fn () => use_ml src_path);


(* load_thy *)

fun begin_theory dir name imports uses parents =
  Theory.begin_theory name parents
  |> put_deps dir imports
  |> fold (require o fst) uses
  |> fold (fn (path, true) => Context.theory_map (exec_ml path) o Theory.checkpoint | _ => I) uses
  |> Theory.checkpoint;

fun load_thy update_time dir name imports uses pos text parents =
  let
    val (lexs, outer_syntax) = Outer_Syntax.get_syntax ();
    val time = ! Toplevel.timing;

    val _ = Present.init_theory name;
    fun init () =
      begin_theory dir name imports uses parents
      |> Present.begin_theory update_time dir uses;

    val toks = Source.exhausted (Thy_Syntax.token_source lexs pos (Source.of_string text));
    val spans = Source.exhaust (Thy_Syntax.span_source toks);
    val elements =
      Source.exhaust (Thy_Syntax.element_source (Source.of_list spans))
      |> maps (Outer_Syntax.read_element outer_syntax init);

    val _ = Present.theory_source name
      (fn () => HTML.html_mode (implode o map Thy_Syntax.present_span) spans);

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val (results, thy) = cond_timeit time "" (fn () => Toplevel.excursion elements);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();

    val present =
      singleton (Future.cond_forks {name = "Outer_Syntax.present:" ^ name, group = NONE,
        deps = map Future.task_of results, pri = 0, interrupts = true})
      (fn () =>
        Thy_Output.present_thy (#1 lexs) Keyword.command_tags
          (Outer_Syntax.is_markup outer_syntax)
          (maps Future.join results) toks
        |> Buffer.content
        |> Present.theory_output name);

  in (thy, present) end;


(* global master path *)

local
  val master_path = Unsynchronized.ref Path.current;
in

fun set_master_path path = master_path := path;
fun get_master_path () = ! master_path;

end;

end;
