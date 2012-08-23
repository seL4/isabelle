(*  Title:      Pure/Thy/thy_load.ML
    Author:     Makarius

Loading files that contribute to a theory.  Global master path for TTY loop.
*)

signature THY_LOAD =
sig
  val master_directory: theory -> Path.T
  val imports_of: theory -> string list
  val provide: Path.T * SHA1.digest -> theory -> theory
  val check_file: Path.T -> Path.T -> Path.T
  val thy_path: Path.T -> Path.T
  val check_thy: Thy_Header.keywords -> Path.T -> string ->
   {master: Path.T * SHA1.digest, text: string, imports: string list,
    uses: (Path.T * bool) list, keywords: Thy_Header.keywords}
  val load_file: theory -> Path.T -> (Path.T * SHA1.digest) * string
  val use_file: Path.T -> theory -> string * theory
  val loaded_files: theory -> Path.T list
  val load_current: theory -> bool
  val use_ml: Path.T -> unit
  val exec_ml: Path.T -> generic_theory -> generic_theory
  val begin_theory: Path.T -> Thy_Header.header -> theory list -> theory
  val load_thy: int -> Path.T -> Thy_Header.header -> Position.T -> string ->
    theory list -> theory * unit future
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
  provided: (Path.T * SHA1.digest) list};  (*source path, digest*)

fun make_files (master_dir, imports, provided): files =
 {master_dir = master_dir, imports = imports, provided = provided};

structure Files = Theory_Data
(
  type T = files;
  val empty = make_files (Path.current, [], []);
  fun extend _ = empty;
  fun merge _ = empty;
);

fun map_files f =
  Files.map (fn {master_dir, imports, provided} =>
    make_files (f (master_dir, imports, provided)));


val master_directory = #master_dir o Files.get;
val imports_of = #imports o Files.get;

fun put_deps master_dir imports = map_files (fn _ => (master_dir, imports, []));

fun provide (src_path, id) =
  map_files (fn (master_dir, imports, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate use of source file: " ^ Path.print src_path)
    else (master_dir, imports, (src_path, id) :: provided));


(* inlined files *)

fun check_file dir file = File.check_file (File.full_path dir file);

local

fun clean ((i1, t1) :: (i2, t2) :: toks) =
      if Token.keyword_with (fn s => s = "%" orelse s = "--") t1 then clean toks
      else (i1, t1) :: clean ((i2, t2) :: toks)
  | clean toks = toks;

fun clean_tokens toks =
  ((0 upto length toks - 1) ~~ toks)
  |> filter (fn (_, tok) => Token.is_proper tok)
  |> clean;

fun find_file toks =
  rev (clean_tokens toks) |> get_first (fn (i, tok) =>
    if Token.is_name tok then
      SOME (i, Path.explode (Token.content_of tok))
        handle ERROR msg => error (msg ^ Token.pos_of tok)
    else NONE);

fun command_files path exts =
  if null exts then [path]
  else map (fn ext => Path.ext ext path) exts;

in

fun find_files syntax text =
  let val thy_load_commands = Keyword.thy_load_commands syntax in
    if exists (fn (cmd, _) => String.isSubstring cmd text) thy_load_commands then
      Thy_Syntax.parse_tokens (Keyword.lexicons_of syntax) Position.none text
      |> Thy_Syntax.parse_spans
      |> maps
        (fn Thy_Syntax.Span (Thy_Syntax.Command (cmd, _), toks) =>
              (case AList.lookup (op =) thy_load_commands cmd of
                SOME exts =>
                  (case find_file toks of
                    SOME (_, path) => command_files path exts
                  | NONE => [])
              | NONE => [])
          | _ => [])
    else []
  end;

fun read_files cmd dir path =
  let
    val files =
      command_files path (Keyword.command_files cmd)
      |> map (check_file dir #> (fn p => (File.read p, Path.position p)));
  in (dir, files) end;

fun parse_files cmd =
  Scan.ahead Parse.not_eof -- Parse.path >> (fn (tok, name) => fn thy =>
    (case Token.get_files tok of
      SOME files => files
    | NONE => read_files cmd (master_directory thy) (Path.explode name)));

fun resolve_files master_dir span =
  (case span of
    Thy_Syntax.Span (Thy_Syntax.Command (cmd, pos), toks) =>
      if Keyword.is_theory_load cmd then
        (case find_file toks of
          NONE => error ("Bad file argument of command " ^ quote cmd ^ Position.str_of pos)
        | SOME (i, path) =>
            let
              val toks' = toks |> map_index (fn (j, tok) =>
                if i = j then Token.put_files (read_files cmd master_dir path) tok
                else tok);
            in Thy_Syntax.Span (Thy_Syntax.Command (cmd, pos), toks') end)
      else span
  | span => span);

end;


(* check files *)

val thy_path = Path.ext "thy";

fun check_thy base_keywords dir thy_name =
  let
    val path = thy_path (Path.basic thy_name);
    val master_file = check_file dir path;
    val text = File.read master_file;

    val {name, imports, uses, keywords} = Thy_Header.read (Path.position master_file) text;
    val _ = thy_name <> name andalso
      error ("Bad file name " ^ Path.print path ^ " for theory " ^ quote name);

    val syntax =
      fold (Keyword.define_keywords o apsnd (Option.map Keyword.spec))
        (keywords @ base_keywords) (Keyword.get_keywords ());
    val more_uses = map (rpair false) (find_files syntax text);
  in
   {master = (master_file, SHA1.digest text), text = text,
    imports = imports, uses = uses @ more_uses, keywords = keywords}
  end;


(* load files *)

fun load_file thy src_path =
  let
    val full_path = check_file (master_directory thy) src_path;
    val text = File.read full_path;
    val id = SHA1.digest text;
  in ((full_path, id), text) end;

fun use_file src_path thy =
  let
    val ((_, id), text) = load_file thy src_path;
    val thy' = provide (src_path, id) thy;
  in (text, thy') end;

fun loaded_files thy =
  let val {master_dir, provided, ...} = Files.get thy
  in map (File.full_path master_dir o #1) provided end;

fun load_current thy =
  #provided (Files.get thy) |>
    forall (fn (src_path, id) =>
      (case try (load_file thy) src_path of
        NONE => false
      | SOME ((_, id'), _) => id = id'));


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

      val provide = provide (src_path, id);
      val _ = Context.>> (Context.mapping provide (Local_Theory.background_theory provide));
    in () end;

fun exec_ml src_path = ML_Context.exec (fn () => use_ml src_path);


(* load_thy *)

fun begin_theory master_dir {name, imports, keywords, uses} parents =
  Theory.begin_theory name parents
  |> put_deps master_dir imports
  |> fold Thy_Header.declare_keyword keywords
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

fun load_thy update_time master_dir header pos text parents =
  let
    val time = ! Toplevel.timing;

    val {name, uses, ...} = header;
    val _ = Thy_Header.define_keywords header;
    val _ = Present.init_theory name;
    fun init () =
      begin_theory master_dir header parents
      |> Present.begin_theory update_time master_dir uses;

    val lexs = Keyword.get_lexicons ();

    val toks = Thy_Syntax.parse_tokens lexs pos text;
    val spans = map (resolve_files master_dir) (Thy_Syntax.parse_spans toks);
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
