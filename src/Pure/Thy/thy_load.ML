(*  Title:      Pure/Thy/thy_load.ML
    Author:     Makarius

Loading files that contribute to a theory.  Global master path for TTY loop.
*)

signature THY_LOAD =
sig
  val master_directory: theory -> Path.T
  val imports_of: theory -> (string * Position.T) list
  val thy_path: Path.T -> Path.T
  val parse_files: string -> (theory -> Token.file list) parser
  val check_thy: Path.T -> string ->
   {master: Path.T * SHA1.digest, text: string, theory_pos: Position.T,
    imports: (string * Position.T) list, uses: (Path.T * bool) list, keywords: Thy_Header.keywords}
  val provide: Path.T * SHA1.digest -> theory -> theory
  val provide_parse_files: string -> (theory -> Token.file list * theory) parser
  val load_file: theory -> Path.T -> (Path.T * SHA1.digest) * string
  val use_file: Path.T -> theory -> string * theory
  val loaded_files: theory -> Path.T list
  val load_current: theory -> bool
  val use_ml: Path.T -> unit
  val exec_ml: Path.T -> generic_theory -> generic_theory
  val begin_theory: Path.T -> Thy_Header.header -> theory list -> theory
  val load_thy: int -> Path.T -> Thy_Header.header -> Position.T -> string ->
    theory list -> theory * unit future
  val set_master_path: Path.T -> unit
  val get_master_path: unit -> Path.T
end;

structure Thy_Load: THY_LOAD =
struct

(* manage source files *)

type files =
 {master_dir: Path.T,  (*master directory of theory source*)
  imports: (string * Position.T) list,  (*source specification of imports*)
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


(* inlined files *)

fun check_file dir file = File.check_file (File.full_path dir file);

fun read_files cmd dir (path, pos) =
  let
    fun make_file file =
      let
        val _ = Position.report pos (Isabelle_Markup.path (Path.implode file));
        val full_path = check_file dir file;
      in {src_path = file, text = File.read full_path, pos = Path.position full_path} end;
    val paths =
      (case Keyword.command_files cmd of
        [] => [path]
      | exts => map (fn ext => Path.ext ext path) exts);
  in map make_file paths end;

fun parse_files cmd =
  Scan.ahead Parse.not_eof -- Parse.path >> (fn (tok, name) => fn thy =>
    (case Token.get_files tok of
      SOME files => files
    | NONE => read_files cmd (master_directory thy) (Path.explode name, Token.position_of tok)));

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
      SOME (i, (Path.explode (Token.content_of tok), Token.position_of tok))
        handle ERROR msg => error (msg ^ Token.pos_of tok)
    else NONE);

in

fun resolve_files master_dir span =
  (case span of
    Thy_Syntax.Span (Thy_Syntax.Command (cmd, pos), toks) =>
      if Keyword.is_theory_load cmd then
        (case find_file toks of
          NONE => error ("Bad file argument of command " ^ quote cmd ^ Position.here pos)
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

fun check_thy dir thy_name =
  let
    val path = thy_path (Path.basic thy_name);
    val master_file = check_file dir path;
    val text = File.read master_file;

    val {name = (name, pos), imports, uses, keywords} =
      Thy_Header.read (Path.position master_file) text;
    val _ = thy_name <> name andalso
      error ("Bad file name " ^ Path.print path ^ " for theory " ^ quote name ^ Position.here pos);
  in
   {master = (master_file, SHA1.digest text), text = text, theory_pos = pos,
    imports = imports, uses = uses, keywords = keywords}
  end;


(* load files *)

fun provide (src_path, id) =
  map_files (fn (master_dir, imports, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate use of source file: " ^ Path.print src_path)
    else (master_dir, imports, (src_path, id) :: provided));

fun provide_parse_files cmd =
  parse_files cmd >> (fn files => fn thy =>
    let
      val fs = files thy;
      val thy' = fold (fn {src_path, text, ...} => provide (src_path, SHA1.digest text)) fs thy;
    in (fs, thy') end);

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

fun load_thy update_time master_dir header text_pos text parents =
  let
    val time = ! Toplevel.timing;

    val {name = (name, _), uses, ...} = header;
    val _ = Thy_Header.define_keywords header;
    val _ = Present.init_theory name;
    fun init () =
      begin_theory master_dir header parents
      |> Present.begin_theory update_time master_dir uses;

    val lexs = Keyword.get_lexicons ();

    val toks = Thy_Syntax.parse_tokens lexs text_pos text;
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


(* document antiquotation *)

val _ =
  Context.>> (Context.map_theory
   (Thy_Output.antiquotation (Binding.name "file") (Scan.lift (Parse.position Parse.path))
    (fn {context = ctxt, ...} => fn (name, pos) =>
      let
        val dir = master_directory (Proof_Context.theory_of ctxt);
        val path = Path.append dir (Path.explode name);
        val _ =
          if File.exists path then ()
          else error ("Bad file: " ^ Path.print (Path.expand path) ^ Position.here pos);
        val _ = Position.report pos (Isabelle_Markup.path name);
      in Thy_Output.verb_text name end)));


(* global master path *)

local
  val master_path = Unsynchronized.ref Path.current;
in

fun set_master_path path = master_path := path;
fun get_master_path () = ! master_path;

end;

end;
