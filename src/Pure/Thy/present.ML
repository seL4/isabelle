(*  Title:      Pure/Thy/present.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Theory presentation: HTML, graph files, (PDF)LaTeX documents.
*)

signature BASIC_PRESENT =
sig
  val no_document: ('a -> 'b) -> 'a -> 'b  (*not thread-safe!*)
end;

signature PRESENT =
sig
  include BASIC_PRESENT
  val session_name: theory -> string
  datatype dump_mode = Dump_all | Dump_tex | Dump_tex_sty
  val dump_mode: string -> dump_mode
  val read_variant: string -> string * string
  val init: bool -> bool -> string -> string -> bool -> string -> (string * string) list ->
    string list -> string -> string * dump_mode -> Url.T option * bool -> bool ->
    theory list -> unit  (*not thread-safe!*)
  val finish: unit -> unit  (*not thread-safe!*)
  val init_theory: string -> unit
  val theory_source: string -> (unit -> HTML.text) -> unit
  val theory_output: string -> string -> unit
  val begin_theory: int -> Path.T -> (Path.T * bool) list -> theory -> theory
  val drafts: string -> Path.T list -> Path.T
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
val readme_path = Path.basic "README";
val documentN = "document";
val document_path = Path.basic documentN;
val doc_indexN = "session";
val graph_path = Path.basic "session.graph";
val graph_pdf_path = Path.basic "session_graph.pdf";
val graph_eps_path = Path.basic "session_graph.eps";

val session_path = Path.basic ".session";
val session_entries_path = Path.explode ".session/entries";
val pre_index_path = Path.explode ".session/pre-index";

fun mk_rel_path [] ys = Path.make ys
  | mk_rel_path xs [] = Path.appends (replicate (length xs) Path.parent)
  | mk_rel_path (ps as x :: xs) (qs as y :: ys) = if x = y then mk_rel_path xs ys else
      Path.appends (replicate (length ps) Path.parent @ [Path.make qs]);

fun show_path path = Path.implode (Path.append (File.pwd ()) path);



(** additional theory data **)

structure Browser_Info = Theory_Data
(
  type T = {name: string, session: string list, is_local: bool};
  val empty = {name = "", session = [], is_local = false}: T;
  fun extend _ = empty;
  fun merge _ = empty;
);

val put_info = Browser_Info.put;
val get_info = Browser_Info.get;
val session_name = #name o get_info;



(** graphs **)

fun ID_of sess s = space_implode "/" (sess @ [s]);
fun ID_of_thy thy = ID_of (#session (get_info thy)) (Context.theory_name thy);


(*retrieve graph data from initial collection of theories*)
fun init_graph remote_path curr_sess = rev o map (fn thy =>
  let
    val name = Context.theory_name thy;
    val {name = sess_name, session, is_local} = get_info thy;
    val entry =
     {name = name, ID = ID_of session name, dir = sess_name,
      path =
        if null session then "" else
        if is_some remote_path andalso not is_local then
          Url.implode (Url.append (the remote_path) (Url.File
            (Path.append (Path.make session) (html_path name))))
        else Path.implode (Path.append (mk_rel_path curr_sess session) (html_path name)),
      unfold = false,
      parents = map ID_of_thy (Theory.parents_of thy),
      content = []};
  in (0, entry) end);

fun ins_graph_entry (i, entry as {ID, ...}) (gr: (int * Graph_Display.node) list) =
  (i, entry) :: filter_out (fn (_, entry') => #ID entry' = ID) gr;



(** global browser info state **)

(* type theory_info *)

type theory_info = {tex_source: Buffer.T, html_source: Buffer.T, html: Buffer.T};

fun make_theory_info (tex_source, html_source, html) =
  {tex_source = tex_source, html_source = html_source, html = html}: theory_info;

val empty_theory_info = make_theory_info (Buffer.empty, Buffer.empty, Buffer.empty);

fun map_theory_info f {tex_source, html_source, html} =
  make_theory_info (f (tex_source, html_source, html));


(* type browser_info *)

type browser_info = {theories: theory_info Symtab.table, files: (Path.T * string) list,
  tex_index: (int * string) list, html_index: (int * string) list,
  graph: (int * Graph_Display.node) list};

fun make_browser_info (theories, files, tex_index, html_index, graph) =
  {theories = theories, files = files, tex_index = tex_index, html_index = html_index,
    graph = graph}: browser_info;

val empty_browser_info = make_browser_info (Symtab.empty, [], [], [], []);

fun init_browser_info remote_path curr_sess thys = make_browser_info
  (Symtab.empty, [], [], [], init_graph remote_path curr_sess thys);

fun map_browser_info f {theories, files, tex_index, html_index, graph} =
  make_browser_info (f (theories, files, tex_index, html_index, graph));


(* state *)

val browser_info = Unsynchronized.ref empty_browser_info;
fun change_browser_info f =
  CRITICAL (fn () => Unsynchronized.change browser_info (map_browser_info f));

val suppress_tex_source = Unsynchronized.ref false;
fun no_document f x = Unsynchronized.setmp suppress_tex_source true f x;

fun init_theory_info name info =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (Symtab.update (name, info) theories, files, tex_index, html_index, graph));

fun change_theory_info name f =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (case Symtab.lookup theories name of
      NONE => error ("Browser info: cannot access theory document " ^ quote name)
    | SOME info => (Symtab.update (name, map_theory_info f info) theories, files,
        tex_index, html_index, graph)));


fun add_file file =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, file :: files, tex_index, html_index, graph));

fun add_tex_index txt =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, txt :: tex_index, html_index, graph));

fun add_html_index txt =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, tex_index, txt :: html_index, graph));

fun add_graph_entry entry =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, tex_index, html_index, ins_graph_entry entry graph));

fun add_tex_source name txt =
  if ! suppress_tex_source then ()
  else change_theory_info name (fn (tex_source, html_source, html) =>
    (Buffer.add txt tex_source, html_source, html));

fun add_html_source name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (tex_source, Buffer.add txt html_source, html));



(** global session state **)

(* session_info *)

datatype dump_mode = Dump_all | Dump_tex | Dump_tex_sty;

fun dump_mode "all" = Dump_all
  | dump_mode "tex" = Dump_tex
  | dump_mode "tex+sty" = Dump_tex_sty
  | dump_mode s =
      error ("Illegal document dump mode: " ^ quote s ^ " (expected \"all\", \"tex\", \"tex+sty\")");

type session_info =
  {name: string, parent: string, session: string, path: string list, html_prefix: Path.T,
    info: bool, doc_format: string, doc_graph: bool, doc_output: Path.T option,
    documents: (string * string) list, doc_dump: (string * dump_mode), remote_path: Url.T option,
    verbose: bool, readme: Path.T option};

fun make_session_info
  (name, parent, session, path, html_prefix, info, doc_format, doc_graph, doc_output,
    documents, doc_dump, remote_path, verbose, readme) =
  {name = name, parent = parent, session = session, path = path, html_prefix = html_prefix,
    info = info, doc_format = doc_format, doc_graph = doc_graph, doc_output = doc_output,
    documents = documents, doc_dump = doc_dump, remote_path = remote_path,
    verbose = verbose, readme = readme}: session_info;


(* state *)

val session_info = Unsynchronized.ref (NONE: session_info option);

fun session_default x f = (case ! session_info of NONE => x | SOME info => f info);



(** document preparation **)

(* maintain index *)

val session_entries =
  HTML.session_entries o
    map (fn name => (Url.File (Path.append (Path.basic name) index_path), name));

fun get_entries dir =
  split_lines (File.read (Path.append dir session_entries_path));

fun put_entries entries dir =
  File.write (Path.append dir session_entries_path) (cat_lines entries);


fun create_index dir =
  File.read (Path.append dir pre_index_path) ^
    session_entries (get_entries dir) ^ HTML.end_document
  |> File.write (Path.append dir index_path);

fun update_index dir name =
  (case try get_entries dir of
    NONE => warning ("Browser info: cannot access session index of " ^ Path.print dir)
  | SOME es => (put_entries ((remove (op =) name es) @ [name]) dir; create_index dir));


(* document variants *)

fun read_variant str =
  (case space_explode "=" str of
    [name] => (name, "")
  | [name, tags] => (name, tags)
  | _ => error ("Malformed document variant specification: " ^ quote str));


(* init session *)

fun name_of_session elems = space_implode "/" ("Isabelle" :: elems);

fun init build info info_path doc doc_graph document_output doc_variants path name
    (doc_dump as (dump_prefix, _)) (remote_path, first_time) verbose thys =
  if not build andalso not info andalso doc = "" andalso dump_prefix = "" then
    (browser_info := empty_browser_info; session_info := NONE)
  else
    let
      val parent_name = name_of_session (take (length path - 1) path);
      val session_name = name_of_session path;
      val sess_prefix = Path.make path;
      val html_prefix = Path.append (Path.expand (Path.explode info_path)) sess_prefix;
      val doc_output = if document_output = "" then NONE else SOME (Path.explode document_output);

      val documents =
        if doc = "" then []
        else if not (can File.check_dir document_path) then
          (if verbose then Output.physical_stderr "Warning: missing document directory\n"
           else (); [])
        else doc_variants;

      val parent_index_path = Path.append Path.parent index_path;
      val index_up_lnk =
        if first_time then
          Url.append (the remote_path) (Url.File (Path.append sess_prefix parent_index_path))
        else Url.File parent_index_path;
      val readme =
        if File.exists readme_html_path then SOME readme_html_path
        else if File.exists readme_path then SOME readme_path
        else NONE;

      val docs =
        (case readme of NONE => [] | SOME p => [(Url.File p, "README")]) @
          map (fn (name, _) => (Url.File (Path.ext doc (Path.basic name)), name)) documents;
      val index_text = HTML.begin_index (index_up_lnk, parent_name)
        (Url.File index_path, session_name) docs (Url.explode "medium.html");
    in
      session_info :=
        SOME (make_session_info (name, parent_name, session_name, path, html_prefix, info, doc,
          doc_graph, doc_output, documents, doc_dump, remote_path, verbose, readme));
      browser_info := init_browser_info remote_path path thys;
      add_html_index (0, index_text)
    end;


(* isabelle tool wrappers *)

fun isabelle_document {verbose, purge} format name tags dir =
  let
    val s = "\"$ISABELLE_TOOL\" document" ^ (if purge then " -c" else "") ^ " -o '" ^ format ^ "' \
      \-n '" ^ name ^ "' -t '" ^ tags ^ "' " ^ File.shell_path dir ^ " 2>&1";
    val doc_path = Path.appends [dir, Path.parent, Path.basic name |> Path.ext format];
    val _ = if verbose then writeln s else ();
    val (out, rc) = Isabelle_System.bash_output s;
    val _ =
      if not (File.exists doc_path) orelse rc <> 0 then
        cat_error out ("Failed to build document " ^ quote (show_path doc_path))
      else if verbose then writeln out
      else ();
  in doc_path end;

fun isabelle_browser graph = Isabelle_System.with_tmp_dir "browser" (fn dir =>
  let
    val pdf_path = Path.append dir graph_pdf_path;
    val eps_path = Path.append dir graph_eps_path;
    val graph_path = Path.append dir graph_path;
    val _ = Graph_Display.write_graph graph_path graph;
    val args = "-o " ^ File.shell_path pdf_path ^ " " ^ File.shell_path graph_path;
  in
    if Isabelle_System.isabelle_tool "browser" args = 0 andalso
      File.exists pdf_path andalso File.exists eps_path
    then (File.read pdf_path, File.read eps_path)
    else error "Failed to prepare dependency graph"
  end);


(* finish session -- output all generated text *)

fun sorted_index index = map snd (sort (int_ord o pairself fst) (rev index));
fun index_buffer index = Buffer.add (implode (sorted_index index)) Buffer.empty;

fun write_tex src name path =
  File.write_buffer (Path.append path (tex_path name)) src;

fun write_tex_index tex_index path =
  write_tex (index_buffer tex_index |> Buffer.add Latex.tex_trailer) doc_indexN path;


fun finish () =
  session_default () (fn {name, info, html_prefix, doc_format, doc_graph, doc_output,
    documents, doc_dump = (dump_prefix, dump_mode), path, verbose, readme, ...} =>
  let
    val {theories, files, tex_index, html_index, graph} = ! browser_info;
    val thys = Symtab.dest theories;
    val parent_html_prefix = Path.append html_prefix Path.parent;

    fun finish_html (a, {html, ...}: theory_info) =
      File.write_buffer (Path.append html_prefix (html_path a)) (Buffer.add HTML.end_document html);

    val sorted_graph = sorted_index graph;
    val opt_graphs =
      if doc_graph andalso (not (null documents) orelse dump_prefix <> "") then
        SOME (isabelle_browser sorted_graph)
      else NONE;

    val _ =
      if info then
       (Isabelle_System.mkdirs (Path.append html_prefix session_path);
        File.write_buffer (Path.append html_prefix pre_index_path) (index_buffer html_index);
        File.write (Path.append html_prefix session_entries_path) "";
        create_index html_prefix;
        if length path > 1 then update_index parent_html_prefix name else ();
        (case readme of NONE => () | SOME path => File.copy path html_prefix);
        Graph_Display.write_graph (Path.append html_prefix graph_path) sorted_graph;
        Isabelle_System.isabelle_tool "browser" "-b";
        File.copy (Path.explode "~~/lib/browser/GraphBrowser.jar") html_prefix;
        List.app (fn (a, txt) => File.write (Path.append html_prefix (Path.basic a)) txt)
          (HTML.applet_pages name (Url.File index_path, name));
        File.copy (Path.explode "~~/etc/isabelle.css") html_prefix;
        List.app finish_html thys;
        List.app (uncurry File.write) files;
        if verbose then Output.physical_stderr ("Browser info at " ^ show_path html_prefix ^ "\n")
        else ())
      else ();

    fun prepare_sources doc_dir doc_mode =
     (Isabelle_System.mkdirs doc_dir;
      (case doc_mode of
        Dump_all => Isabelle_System.copy_dir document_path doc_dir
      | Dump_tex_sty =>
          ignore (Isabelle_System.isabelle_tool "latex"
            ("-o sty " ^ File.shell_path (Path.append doc_dir (Path.basic "root.tex"))))
      | Dump_tex => ());
      (case opt_graphs of NONE => () | SOME (pdf, eps) =>
        (File.write (Path.append doc_dir graph_pdf_path) pdf;
          File.write (Path.append doc_dir graph_eps_path) eps));
      write_tex_index tex_index doc_dir;
      List.app (fn (a, {tex_source, ...}) => write_tex tex_source a doc_dir) thys);

    val _ =
      if dump_prefix = "" then ()
      else
        let
          val path = Path.explode dump_prefix;
          val _ = prepare_sources path dump_mode;
        in
          if verbose then
            Output.physical_stderr ("Document sources at " ^ show_path path ^ "\n")
          else ()
        end;

    fun document_job doc_prefix backdrop (name, tags) =
      let
        val _ =
          File.eq (document_path, doc_prefix) andalso
            error ("Overlap of document input and output directory " ^ Path.print doc_prefix);
        val dir = Path.append doc_prefix (Path.basic name);
        val mode = if File.eq (document_path, dir) then Dump_tex_sty else Dump_all;
        val _ = prepare_sources dir mode;
        fun inform doc =
          if verbose orelse not backdrop then
            Output.physical_stderr ("Document at " ^ show_path doc ^ "\n")
          else ();
      in
        fn () =>
          (isabelle_document {verbose = true, purge = backdrop} doc_format name tags dir, inform)
      end;

    val jobs =
      (if info orelse is_none doc_output then
        map (document_job html_prefix true) documents
       else []) @
      (case doc_output of
        NONE => []
      | SOME path => map (document_job path false) documents);

    val _ = jobs |> Par_List.map (fn job => job ()) |> List.app (op |>);
  in
    browser_info := empty_browser_info;
    session_info := NONE
  end);


(* theory elements *)

fun init_theory name = session_default () (fn _ => init_theory_info name empty_theory_info);

fun theory_source name mk_text =
  session_default () (fn _ => add_html_source name (HTML.theory_source (mk_text ())));

fun theory_output name s =
  session_default () (fn _ => add_tex_source name (Latex.isabelle_file name s));


fun parent_link remote_path curr_session thy =
  let
    val {name = _, session, is_local} = get_info thy;
    val name = Context.theory_name thy;
    val link =
      if null session then NONE
      else SOME
       (if is_some remote_path andalso not is_local then
         Url.append (the remote_path) (Url.File (Path.append (Path.make session) (html_path name)))
        else Url.File (Path.append (mk_rel_path curr_session session) (html_path name)));
  in (link, name) end;

fun begin_theory update_time dir files thy =
    session_default thy (fn {name = sess_name, session, path, html_prefix, remote_path, ...} =>
  let
    val name = Context.theory_name thy;
    val parents = Theory.parents_of thy;
    val parent_specs = map (parent_link remote_path path) parents;

    val files_html = files |> map (fn (raw_path, loadit) =>
      let
        val path = File.check_file (File.full_path dir raw_path);
        val base = Path.base path;
        val base_html = html_ext base;
        val _ = add_file (Path.append html_prefix base_html,
          HTML.external_file (Url.File base) (File.read path));
      in (Url.File base_html, Url.File raw_path, loadit) end);

    fun prep_html_source (tex_source, html_source, html) =
      let
        val txt = HTML.begin_theory (Url.File index_path, session)
          name parent_specs files_html (Buffer.content html_source)
      in (tex_source, Buffer.empty, Buffer.add txt html) end;

    val entry =
     {name = name, ID = ID_of path name, dir = sess_name, unfold = true,
      path = Path.implode (html_path name),
      parents = map ID_of_thy parents,
      content = []};
  in
    change_theory_info name prep_html_source;
    add_graph_entry (update_time, entry);
    add_html_index (update_time, HTML.theory_entry (Url.File (html_path name), name));
    add_tex_index (update_time, Latex.theory_entry name);
    put_info {name = sess_name, session = path, is_local = is_some remote_path} thy
  end);



(** draft document output **)

fun drafts doc_format src_paths = Isabelle_System.with_tmp_dir "drafts" (fn dir =>
  let
    fun prep_draft path i =
      let
        val base = Path.base path;
        val name =
          (case Path.implode (#1 (Path.split_ext base)) of
            "" => "DUMMY"
          | s => s)  ^ serial_string ();
      in
        if File.exists path then
          (((name, base, File.read path), (i, Latex.theory_entry name)), i + 1)
        else error ("Bad file: " ^ Path.print path)
      end;
    val (srcs, tex_index) = split_list (fst (fold_map prep_draft src_paths 0));

    val doc_path = Path.append dir document_path;
    val _ = Isabelle_System.mkdirs doc_path;
    val root_path = Path.append doc_path (Path.basic "root.tex");
    val _ = File.copy (Path.explode "~~/lib/texinputs/draft.tex") root_path;
    val _ = Isabelle_System.isabelle_tool "latex" ("-o sty " ^ File.shell_path root_path);
    val _ = Isabelle_System.isabelle_tool "latex" ("-o syms " ^ File.shell_path root_path);

    fun known name =
      let val ss = split_lines (File.read (Path.append doc_path (Path.basic name)))
      in member (op =) ss end;
    val known_syms = known "syms.lst";
    val known_ctrls = known "ctrls.lst";

    val _ = srcs |> List.app (fn (name, base, txt) =>
      Symbol.explode txt
      |> Latex.symbol_source (known_syms, known_ctrls) (Path.implode base)
      |> File.write (Path.append doc_path (tex_path name)));
    val _ = write_tex_index tex_index doc_path;

    val result =
      isabelle_document {verbose = false, purge = true} doc_format documentN "" doc_path;
    val result' = Isabelle_System.create_tmp_path documentN doc_format;
    val _ = File.copy result result';
  in result' end);

end;

structure Basic_Present: BASIC_PRESENT = Present;
open Basic_Present;
