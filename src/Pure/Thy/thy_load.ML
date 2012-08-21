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
  val begin_theory: Path.T -> Thy_Header.header -> theory list -> theory
  val load_thy: int -> Path.T -> Thy_Header.header -> Position.T -> string ->
    theory list -> theory * unit future
  val resolve_files: Path.T -> Thy_Syntax.span -> Thy_Syntax.span
  val parse_files: string -> (theory -> Token.files) parser
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


(* inlined files *)

fun command_files cmd path =
  (case Keyword.command_files cmd of
    [] => [path]
  | exts => map (fn ext => Path.ext ext path) exts);

fun read_files cmd dir tok =
  let
    val path = Path.explode (Token.content_of tok);
    val files =
      command_files cmd path
      |> map (Path.append dir #> (fn p => (File.read p, Path.position p)));
  in (dir, files) end;

fun parse_files cmd =
  Scan.ahead Parse.not_eof -- Parse.group (fn () => "file name/path specification") Parse.name
    >> (fn (tok, name) => fn thy =>
      (case Token.get_files tok of
        SOME files => files
      | NONE =>
          (warning ("Dynamic loading of files: " ^ quote name ^ Token.pos_of tok);
            read_files cmd (master_directory thy) tok)));

local

fun clean ((i1, t1) :: (i2, t2) :: toks) =
      if Token.keyword_with (fn s => s = "%" orelse s = "--") t1 then clean toks
      else (i1, t1) :: clean ((i2, t2) :: toks)
  | clean toks = toks;

fun clean_tokens toks =
  ((0 upto length toks - 1) ~~ toks)
  |> filter (fn (_, tok) => Token.is_proper tok) |> clean;

in

fun resolve_files dir (span as Thy_Syntax.Span (Thy_Syntax.Command cmd, toks)) =
      if Keyword.is_theory_load cmd then
        (case find_first (Token.is_name o #2) (rev (clean_tokens toks)) of
          NONE => span
        | SOME (i, _) =>
            let
              val toks' = toks |> map_index (fn (j, tok) =>
                if i = j then Token.put_files (read_files cmd dir tok) tok
                else tok);
            in Thy_Syntax.Span (Thy_Syntax.Command cmd, toks') end)
      else span
  | resolve_files _ span = span;

end;


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
      else
        let val {name, imports, uses, ...} = Thy_Header.read (Path.position master_file) text
        in (name, imports, uses) end;
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

fun begin_theory dir {name, imports, keywords, uses} parents =
  Theory.begin_theory name parents
  |> put_deps dir imports
  |> fold Thy_Header.declare_keyword keywords
  |> fold (require o fst) uses
  |> fold (fn (path, true) => Context.theory_map (exec_ml path) o Theory.checkpoint | _ => I) uses
  |> Theory.checkpoint;

fun excursion init elements =
  let
    val immediate = not (Goal.future_enabled ());

    fun proof_result (tr, trs) (st, _) =
      let
        val (result, st') = Toplevel.proof_result immediate (tr, trs) st;
        val pos' = Toplevel.pos_of (List.last (tr :: trs));
      in (result, (st', pos')) end;

    fun element_result elem x =
      fold_map proof_result
        (Outer_Syntax.read_element (#2 (Outer_Syntax.get_syntax ())) init elem) x;

    val (results, (end_state, end_pos)) =
      fold_map element_result elements (Toplevel.toplevel, Position.none);

    val thy = Toplevel.end_theory end_pos end_state;
  in (flat results, thy) end;

fun load_thy update_time dir header pos text parents =
  let
    val time = ! Toplevel.timing;

    val {name, uses, ...} = header;
    val _ = Thy_Header.define_keywords header;
    val _ = Present.init_theory name;
    fun init () =
      begin_theory dir header parents
      |> Present.begin_theory update_time dir uses;

    val lexs = Keyword.get_lexicons ();

    val toks = Thy_Syntax.parse_tokens lexs pos text;
    val spans = map (resolve_files dir) (Thy_Syntax.parse_spans toks);
    val elements = Thy_Syntax.parse_elements spans;

    val _ = Present.theory_source name
      (fn () => HTML.html_mode (implode o map Thy_Syntax.present_span) spans);

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val (results, thy) = cond_timeit time "" (fn () => excursion init elements);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();

    val present =
      singleton (Future.cond_forks {name = "Outer_Syntax.present:" ^ name, group = NONE,
        deps = map Future.task_of results, pri = 0, interrupts = true})
      (fn () =>
        let val ((minor, _), outer_syntax) = Outer_Syntax.get_syntax () in
          Thy_Output.present_thy minor Keyword.command_tags
            (Outer_Syntax.is_markup outer_syntax)
            (maps Future.join results) toks
          |> Buffer.content
          |> Present.theory_output name
        end);

  in (thy, present) end;


(* global master path *)

local
  val master_path = Unsynchronized.ref Path.current;
in

fun set_master_path path = master_path := path;
fun get_master_path () = ! master_path;

end;

end;
