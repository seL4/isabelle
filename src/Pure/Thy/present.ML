(*  Title:      Pure/Thy/present.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Theory presentation: HTML and PDF-LaTeX documents.
*)

signature PRESENT =
sig
  val tex_path: string -> Path.T
  val get_bibtex_entries: theory -> string list
  val theory_qualifier: theory -> string
  val document_option: Options.T -> {enabled: bool, disabled: bool}
  val document_variants: Options.T -> (string * string) list
  val init: HTML.symbols -> bool -> Path.T -> bool -> string -> (string * string) list ->
    (Path.T * Path.T) list -> Path.T -> string * string -> bool -> unit
  val finish: unit -> unit
  val theory_output: theory -> string list -> unit
  val begin_theory: string list -> int -> (unit -> HTML.text) -> theory -> theory
end;

structure Present: PRESENT =
struct


(** paths **)

val tex_ext = Path.ext "tex";
val tex_path = tex_ext o Path.basic;
val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val index_path = Path.basic "index.html";
val readme_html_path = Path.basic "README.html";
val doc_indexN = "session";
val session_graph_path = Path.basic "session_graph.pdf";
val document_path = Path.ext "pdf" o Path.basic;

fun show_path path = Path.implode (Path.expand (File.full_path Path.current path));



(** theory data **)

type browser_info = {chapter: string, name: string, bibtex_entries: string list};
val empty_browser_info: browser_info = {chapter = "Unsorted", name = "Unknown", bibtex_entries = []};

structure Browser_Info = Theory_Data
(
  type T = browser_info
  val empty = empty_browser_info;
  val extend = I;
  val merge = #1;
);

fun reset_browser_info thy =
  if Browser_Info.get thy = empty_browser_info then NONE
  else SOME (Browser_Info.put empty_browser_info thy);

val _ =
  Theory.setup
   (Theory.at_begin reset_browser_info #>
    Browser_Info.put {chapter = Context.PureN, name = Context.PureN, bibtex_entries = []});

val get_bibtex_entries = #bibtex_entries o Browser_Info.get;



(** global browser info state **)

(* type theory_info *)

type theory_info = {tex_source: string list, html_source: string};

fun make_theory_info (tex_source, html_source) =
  {tex_source = tex_source, html_source = html_source}: theory_info;

fun map_theory_info f {tex_source, html_source} =
  make_theory_info (f (tex_source, html_source));


(* type browser_info *)

type browser_info =
 {theories: theory_info Symtab.table,
  tex_index: (int * string) list,
  html_index: (int * string) list};

fun make_browser_info (theories, tex_index, html_index) : browser_info =
  {theories = theories, tex_index = tex_index, html_index = html_index};

val empty_browser_info = make_browser_info (Symtab.empty, [], []);

fun map_browser_info f {theories, tex_index, html_index} =
  make_browser_info (f (theories, tex_index, html_index));


(* state *)

val browser_info = Synchronized.var "browser_info" empty_browser_info;
fun change_browser_info f = Synchronized.change browser_info (map_browser_info f);

fun init_theory_info name info =
  change_browser_info (fn (theories, tex_index, html_index) =>
    (Symtab.update (name, info) theories, tex_index, html_index));

fun change_theory_info name f =
  change_browser_info (fn (theories, tex_index, html_index) =>
    (case Symtab.lookup theories name of
      NONE => error ("Browser info: cannot access theory document " ^ quote name)
    | SOME info => (Symtab.update (name, map_theory_info f info) theories, tex_index, html_index)));


fun add_tex_index txt =
  change_browser_info (fn (theories, tex_index, html_index) =>
    (theories, txt :: tex_index, html_index));

fun add_html_index txt =
  change_browser_info (fn (theories, tex_index, html_index) =>
    (theories, tex_index, txt :: html_index));



(** global session state **)

(* session_info *)

type session_info =
  {symbols: HTML.symbols, name: string, chapter: string, info_path: Path.T, info: bool,
    document: bool, doc_output: Path.T option, doc_files: (Path.T * Path.T) list,
    graph_file: Path.T, documents: (string * string) list, verbose: bool, readme: Path.T option};

fun make_session_info
  (symbols, name, chapter, info_path, info, document, doc_output, doc_files,
    graph_file, documents, verbose, readme) =
  {symbols = symbols, name = name, chapter = chapter, info_path = info_path, info = info,
    document = document, doc_output = doc_output, doc_files = doc_files, graph_file = graph_file,
    documents = documents, verbose = verbose, readme = readme}: session_info;


(* state *)

val session_info = Unsynchronized.ref (NONE: session_info option);

fun with_session_info x f = (case ! session_info of NONE => x | SOME info => f info);

val theory_qualifier = Resources.theory_qualifier o Context.theory_long_name;

fun is_session_theory thy =
  (case ! session_info of
    NONE => false
  | SOME {name, ...} => name = theory_qualifier thy);


(** document preparation **)

(* options *)

fun document_option options =
  (case Options.string options "document" of
    "" => {enabled = false, disabled = false}
  | "false" => {enabled = false, disabled = true}
  | _ => {enabled = true, disabled = false});

fun document_variants options =
  let
    val variants =
      space_explode ":" (Options.string options "document_variants") |> map (fn s =>
        (case space_explode "=" s of
          [name] => (name, "")
        | [name, tags] => (name, tags)
        | _ => error ("Malformed document variant specification: " ^ quote s)));
    val _ =
      (case duplicates (op =) (map #1 variants) of
        [] => ()
      | dups => error ("Duplicate document variants: " ^ commas_quote dups));
  in variants end;


(* init session *)

fun init symbols info info_path document document_output doc_variants doc_files graph_file
    (chapter, name) verbose =
  let
    val doc_output =
      if document_output = "" then NONE else SOME (Path.explode document_output);

    val documents = if not document orelse null doc_files then [] else doc_variants;
    val readme = if File.exists readme_html_path then SOME readme_html_path else NONE;

    val docs =
      (case readme of NONE => [] | SOME p => [(Url.File p, "README")]) @
        map (fn (name, _) => (Url.File (document_path name), name)) documents;
  in
    session_info :=
      SOME (make_session_info (symbols, name, chapter, info_path, info, document,
        doc_output, doc_files, graph_file, documents, verbose, readme));
    Synchronized.change browser_info (K empty_browser_info);
    add_html_index (0, HTML.begin_session_index symbols name (Url.File session_graph_path) docs)
  end;


(* isabelle tool wrappers *)

fun isabelle_document {verbose} doc_name tags dir =
  let
    val script =
      "isabelle document -d " ^ File.bash_path dir ^ " -n " ^ Bash.string doc_name ^
      (if tags = "" then "" else " -t " ^ Bash.string tags);
    val doc_path = dir + Path.parent + document_path doc_name;
    val _ = if verbose then writeln script else ();
    val {out, err, rc, ...} = Bash.process script;
    val _ = if verbose then writeln (trim_line (normalize_lines out)) else ();
    val _ = if not (File.exists doc_path) orelse rc <> 0 then error (trim_line err) else ();
  in doc_path end;


(* finish session -- output all generated text *)

fun sorted_index index = map snd (sort (int_ord o apply2 fst) (rev index));
fun index_buffer index = Buffer.add (implode (sorted_index index)) Buffer.empty;

fun write_tex src name path =
  File.write_buffer (path + tex_path name) src;

fun write_tex_index tex_index path =
  write_tex (index_buffer tex_index) doc_indexN path;

fun finish () =
  with_session_info () (fn {name, chapter, info, info_path, doc_output, doc_files, graph_file,
    documents, verbose, readme, ...} =>
  let
    val {theories, tex_index, html_index} = Synchronized.value browser_info;
    val thys = Symtab.dest theories;

    val session_prefix = info_path + Path.basic chapter + Path.basic name;

    fun finish_html (a, {html_source, ...}: theory_info) =
      File.write (session_prefix + html_path a) html_source;

    val _ =
      if info then
       (Isabelle_System.make_directory session_prefix;
        File.write_buffer (session_prefix + index_path)
          (index_buffer html_index |> Buffer.add HTML.end_document);
        (case readme of NONE => () | SOME path => Isabelle_System.copy_file path session_prefix);
        List.app finish_html thys;
        if verbose
        then Output.physical_stderr ("Browser info at " ^ show_path session_prefix ^ "\n")
        else ())
      else ();

    fun document_job doc_prefix backdrop (doc_name, tags) =
      let
        val doc_dir = doc_prefix + Path.basic doc_name;
        fun purge () = if backdrop then Isabelle_System.rm_tree doc_dir else ();
        val _ = purge ();
        val _ = Isabelle_System.make_directory doc_dir;
        val _ =
          Isabelle_System.bash ("isabelle latex -o sty " ^
            File.bash_path (doc_dir + Path.basic "root.tex"));
        val _ = List.app (fn file => Isabelle_System.copy_file_base file doc_dir) doc_files;
        val _ = Isabelle_System.copy_file graph_file (doc_dir + session_graph_path);
        val _ = write_tex_index tex_index doc_dir;
        val _ =
          List.app (fn (a, {tex_source, ...}) =>
            write_tex (fold Buffer.add tex_source Buffer.empty) a doc_dir) thys;
      in
        fn () =>
          (isabelle_document {verbose = true} doc_name tags doc_dir before purge (),
            fn doc =>
              if verbose orelse not backdrop then
                Output.physical_stderr ("Document at " ^ show_path doc ^ "\n")
              else ())
      end;

    val jobs =
      (if info orelse is_none doc_output then
        map (document_job session_prefix true) documents
       else []) @
      (case doc_output of
        NONE => []
      | SOME path => map (document_job path false) documents);

    val _ = jobs |> Par_List.map (fn job => job ()) |> List.app (op |>);
  in
    Synchronized.change browser_info (K empty_browser_info);
    session_info := NONE
  end);


(* theory elements *)

fun theory_output thy output =
  with_session_info () (fn _ =>
    if is_session_theory thy then
      (change_theory_info (Context.theory_name thy) o apfst) (K output)
    else ());

fun theory_link (curr_chapter, curr_session) thy =
  let
    val {chapter, name = session, ...} = Browser_Info.get thy;
    val link = html_path (Context.theory_name thy);
  in
    if curr_session = session then SOME link
    else if curr_chapter = chapter then
      SOME (Path.parent + Path.basic session + link)
    else if chapter = Context.PureN then NONE
    else SOME (Path.parent + Path.parent + Path.basic chapter + Path.basic session + link)
  end;

fun begin_theory bibtex_entries update_time mk_text thy =
  with_session_info thy (fn {symbols, name = session_name, chapter, ...} =>
    let
      val name = Context.theory_name thy;

      val parent_specs =
        Theory.parents_of thy |> map (fn parent =>
          (Option.map Url.File (theory_link (chapter, session_name) parent),
            (Context.theory_name parent)));
      val html_source = HTML.theory symbols name parent_specs (mk_text ());
      val _ = init_theory_info name (make_theory_info ([], html_source));

      val bibtex_entries' =
        if is_session_theory thy then
          (add_html_index (update_time, HTML.theory_entry symbols (Url.File (html_path name), name));
           add_tex_index (update_time, Latex.theory_entry name);
           bibtex_entries)
        else [];
    in
      thy
      |> Browser_Info.put {chapter = chapter, name = session_name, bibtex_entries = bibtex_entries'}
    end);

end;
