(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Theory presentation: HTML, graph files, (PDF)LaTeX documents.
*)

signature BASIC_PRESENT =
sig
  val no_document: ('a -> 'b) -> 'a -> 'b
  val section: string -> unit
end;

signature PRESENT =
sig
  include BASIC_PRESENT
  val write_graph: {name: string, ID: string, dir: string, unfold: bool,
   path: string, parents: string list} list -> Path.T -> unit
  val init: bool -> bool -> string -> bool -> string list -> string -> Path.T option
    -> Url.T option * bool -> bool -> unit
  val finish: unit -> unit
  val init_theory: string -> unit
  val verbatim_source: string -> (unit -> Symbol.symbol list) -> unit
  val old_symbol_source: string -> (unit -> Symbol.symbol list) -> unit
  val theory_output: string -> string -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> theory -> theory
  val result: string -> string -> thm -> unit
  val results: string -> string -> thm list -> unit
  val theorem: string -> thm -> unit
  val theorems: string -> thm list -> unit
  val chapter: string -> unit
  val subsection: string -> unit
  val subsubsection: string -> unit
  val setup: (theory -> theory) list
  val get_info: theory -> {name: string, session: string list, is_local: bool}
end;

structure Present: PRESENT =
struct


(** paths **)

val output_path = Path.variable "ISABELLE_BROWSER_INFO";

val tex_ext = Path.ext "tex";
val tex_path = tex_ext o Path.basic;
val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val index_path = Path.basic "index.html";
val readme_html_path = Path.basic "README.html";
val readme_path = Path.basic "README";
val doc_path = Path.basic "document";
val doc_indexN = "session";
val graph_path = Path.basic "session.graph";
val graph_pdf_path = Path.basic "session_graph.pdf";
val graph_eps_path = Path.basic "session_graph.eps";

val session_path = Path.basic ".session";
val session_entries_path = Path.unpack ".session/entries";
val pre_index_path = Path.unpack ".session/pre-index";

fun mk_rel_path [] ys = Path.make ys
  | mk_rel_path xs [] = Path.appends (replicate (length xs) Path.parent)
  | mk_rel_path (ps as x :: xs) (qs as y :: ys) = if x = y then mk_rel_path xs ys else
      Path.appends (replicate (length ps) Path.parent @ [Path.make qs]);

fun show_path path = Path.pack (Path.append (File.pwd ()) path);


(** additional theory data **)

structure BrowserInfoArgs =
struct
  val name = "Pure/browser_info";
  type T = {name: string, session: string list, is_local: bool};

  val empty = {name = "Pure", session = [], is_local = false};
  val copy = I;
  val finish = I;
  fun prep_ext _ = {name = "", session = [], is_local = false};
  fun merge _ = empty;
  fun print _ _ = ();
end;

structure BrowserInfoData = TheoryDataFun(BrowserInfoArgs);

fun get_info thy =
  if Theory.eq_thy (thy, ProtoPure.thy) then BrowserInfoArgs.empty
  else BrowserInfoData.get thy;



(** graphs **)

type graph_node =
  {name: string, ID: string, dir: string, unfold: bool,
   path: string, parents: string list};

fun write_graph gr path =
  File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents} =>
    "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
    path ^ "\" > " ^ space_implode " " (map quote parents) ^ " ;") gr));

fun ID_of sess s = space_implode "/" (sess @ [s]);

(*retrieve graph data from initial theory loader database*)
fun init_graph remote_path curr_sess = map (fn name =>
  let
    val {name = sess_name, session, is_local} = get_info (ThyInfo.theory name);
    val path' = Path.append (Path.make session) (html_path name);
  in
   {name = name, ID = ID_of session name, dir = sess_name,
    path =
      if null session then "" else
      if is_some remote_path andalso not is_local then
        Url.pack (Url.append (the remote_path) (Url.file
          (Path.append (Path.make session) (html_path name))))
      else Path.pack (Path.append (mk_rel_path curr_sess session) (html_path name)),
    unfold = false,
    parents =
      map (fn s => ID_of (#session (get_info (ThyInfo.theory s))) s) (ThyInfo.get_preds name)}
  end) (ThyInfo.names ());

fun ins_graph_entry (entry as {ID, ...}) (gr: graph_node list) =
  filter_out (fn entry' => #ID entry' = ID) gr @ [entry];



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
  tex_index: Buffer.T, html_index: Buffer.T, graph: graph_node list};

fun make_browser_info (theories, files, tex_index, html_index, graph) =
  {theories = theories, files = files, tex_index = tex_index, html_index = html_index,
    graph = graph}: browser_info;

val empty_browser_info = make_browser_info (Symtab.empty, [], Buffer.empty, Buffer.empty, []);

fun init_browser_info remote_path curr_sess = make_browser_info
  (Symtab.empty, [], Buffer.empty, Buffer.empty, init_graph remote_path curr_sess);

fun map_browser_info f {theories, files, tex_index, html_index, graph} =
  make_browser_info (f (theories, files, tex_index, html_index, graph));


(* state *)

val browser_info = ref empty_browser_info;
fun change_browser_info f = browser_info := map_browser_info f (! browser_info);

val suppress_tex_source = ref false;
fun no_document f x = Library.setmp suppress_tex_source true f x;

fun init_theory_info name info =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (Symtab.update ((name, info), theories), files, tex_index, html_index, graph));

fun change_theory_info name f =
  change_browser_info (fn (info as (theories, files, tex_index, html_index, graph)) =>
    (case Symtab.lookup (theories, name) of
      None => (warning ("Browser info: cannot access theory document " ^ quote name); info)
    | Some info => (Symtab.update ((name, map_theory_info f info), theories), files,
        tex_index, html_index, graph)));


fun add_file file =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, file :: files, tex_index, html_index, graph));

fun add_tex_index txt =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, Buffer.add txt tex_index, html_index, graph));

fun add_html_index txt =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, tex_index, Buffer.add txt html_index, graph));

fun add_graph_entry e =
  change_browser_info (fn (theories, files, tex_index, html_index, graph) =>
    (theories, files, tex_index, html_index, ins_graph_entry e graph));

fun add_tex_source name txt =
  if ! suppress_tex_source then ()
  else change_theory_info name (fn (tex_source, html_source, html) =>
    (Buffer.add txt tex_source, html_source, html));

fun add_html_source name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (tex_source, Buffer.add txt html_source, html));

fun add_html name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (tex_source, html_source, Buffer.add txt html));



(** global session state **)

(* session_info *)

type session_info =
  {name: string, parent: string, session: string, path: string list, html_prefix: Path.T,
    info: bool, doc_format: string, doc_graph: bool, doc_prefix1: Path.T option,
    doc_prefix2: Path.T option, remote_path: Url.T option, verbose: bool, readme: Path.T option};

fun make_session_info
  (name, parent, session, path, html_prefix, info, doc_format, doc_graph, doc_prefix1,
    doc_prefix2, remote_path, verbose, readme) =
  {name = name, parent = parent, session = session, path = path, html_prefix = html_prefix,
    info = info, doc_format = doc_format, doc_graph = doc_graph, doc_prefix1 = doc_prefix1,
    doc_prefix2 = doc_prefix2, remote_path = remote_path, verbose = verbose,
    readme = readme}: session_info;


(* state *)

val session_info = ref (None: session_info option);

fun with_session x f = (case ! session_info of None => x | Some info => f info);
fun with_context f = f (PureThy.get_name (Context.the_context ()));



(** HTML output **)

(* maintain index *)

val session_entries =
  HTML.session_entries o
    map (fn name => (Url.file (Path.append (Path.basic name) index_path), name));

fun get_entries dir =
  split_lines (File.read (Path.append dir session_entries_path));

fun put_entries entries dir =
  File.write (Path.append dir session_entries_path) (cat_lines entries);


fun create_index dir =
  File.read (Path.append dir pre_index_path) ^
    session_entries (get_entries dir) ^ HTML.end_index
  |> File.write (Path.append dir index_path);

fun update_index dir name =
  (case try get_entries dir of
    None => warning ("Browser info: cannot access session index of " ^ quote (Path.pack dir))
  | Some es => (put_entries ((es \ name) @ [name]) dir; create_index dir));


(* init session *)

fun name_of_session elems = space_implode "/" ("Isabelle" :: elems);

fun copy_files path1 path2 =
  (File.mkdir path2;
   File.system_command  (*FIXME: quote paths!?*)
     ("cp " ^ File.sysify_path path1 ^ " " ^ File.sysify_path path2));


fun init build info doc doc_graph path name doc_prefix2 (remote_path, first_time) verbose =
  if not build andalso not info andalso doc = "" andalso is_none doc_prefix2 then
    (browser_info := empty_browser_info; session_info := None)
  else
    let
      val parent_name = name_of_session (Library.take (length path - 1, path));
      val session_name = name_of_session path;
      val sess_prefix = Path.make path;
      val html_prefix = Path.append (Path.expand output_path) sess_prefix;

      val (doc_prefix1, document_path) =
        if doc = "" then (None, None)
        else if not (File.exists doc_path) then (conditional verbose (fn () =>
          std_error "Warning: missing document directory\n"); (None, None))
        else (Some (Path.append html_prefix doc_path), Some (Path.ext doc doc_path));

      val parent_index_path = Path.append Path.parent index_path;
      val index_up_lnk = if first_time then
          Url.append (the remote_path) (Url.file (Path.append sess_prefix parent_index_path))
        else Url.file parent_index_path;
      val readme =
        if File.exists readme_html_path then Some readme_html_path
        else if File.exists readme_path then Some readme_path
        else None;

      val index_text = HTML.begin_index (index_up_lnk, parent_name)
        (Url.file index_path, session_name) (apsome Url.file readme)
          (apsome Url.file document_path) (Url.unpack "medium.html");
    in
      session_info := Some (make_session_info (name, parent_name, session_name, path, html_prefix,
      info, doc, doc_graph, doc_prefix1, doc_prefix2, remote_path, verbose, readme));
      browser_info := init_browser_info remote_path path;
      add_html_index index_text
    end;


(* finish session -- output all generated text *)

fun write_tex src name path = Buffer.write (Path.append path (tex_path name)) src;

fun isatool_document doc_format path =
  let val s = "\"$ISATOOL\" document -c -o '" ^ doc_format ^ "' " ^ File.quote_sysify_path path in
    writeln s;
    if system s <> 0 orelse not (File.exists (Path.ext doc_format path)) then
      error "Failed to build document"
    else ()
  end;

fun isatool_browser graph =
  let
    val pdfpath = File.tmp_path graph_pdf_path;
    val epspath = File.tmp_path graph_eps_path;
    val gpath = File.tmp_path graph_path;
    val s = "\"$ISATOOL\" browser -o " ^ File.quote_sysify_path pdfpath ^ " " ^
      File.quote_sysify_path gpath;
  in
    write_graph graph gpath;
    if system s <> 0 orelse not (File.exists epspath) orelse not (File.exists pdfpath) then
      error "Failed to prepare dependency graph"
    else
      let val pdf = File.read pdfpath and eps = File.read epspath
      in File.rm pdfpath; File.rm epspath; File.rm gpath; (pdf, eps) end
  end;

fun finish () = with_session () (fn {name, info, html_prefix, doc_format, doc_graph,
    doc_prefix1, doc_prefix2, path, verbose, readme, ...} =>
  let
    val {theories, files, tex_index, html_index, graph} = ! browser_info;
    val thys = Symtab.dest theories;
    val parent_html_prefix = Path.append html_prefix Path.parent;

    fun finish_tex path (a, {tex_source, ...}: theory_info) = write_tex tex_source a path;
    fun finish_html (a, {html, ...}: theory_info) =
      Buffer.write (Path.append html_prefix (html_path a)) (Buffer.add HTML.end_theory html);

    val opt_graphs =
      if doc_graph andalso (is_some doc_prefix1 orelse is_some doc_prefix2) then
        Some (isatool_browser graph)
      else None;

    fun doc_common path =
      ((case opt_graphs of None => () | Some (pdf, eps) =>
        (File.write (Path.append path graph_pdf_path) pdf;
          File.write (Path.append path graph_eps_path) eps));
      write_tex (Buffer.add Latex.tex_trailer tex_index) doc_indexN path;
      seq (finish_tex path) thys);
  in
    conditional info (fn () =>
     (File.mkdir (Path.append html_prefix session_path);
      Buffer.write (Path.append html_prefix pre_index_path) html_index;
      File.write (Path.append html_prefix session_entries_path) "";
      create_index html_prefix;
      if length path > 1 then update_index parent_html_prefix name else ();
      (case readme of None => () | Some path => File.copy path (Path.append html_prefix path));
      write_graph graph (Path.append html_prefix graph_path);
      copy_files (Path.unpack "~~/lib/browser/awtUtilities/*.class")
        (Path.append html_prefix (Path.basic "awtUtilities"));
      copy_files (Path.unpack "~~/lib/browser/GraphBrowser/*.class")
        (Path.append html_prefix (Path.basic "GraphBrowser"));
      seq (fn (a, txt) => File.write (Path.append html_prefix (Path.basic a)) txt)
        (HTML.applet_pages name (Url.file index_path, name));
      seq finish_html thys;
      seq (uncurry File.write) files;
      conditional verbose (fn () =>
        std_error ("Browser info at " ^ show_path html_prefix ^ "\n"))));

    (case doc_prefix1 of None => () | Some path =>
     (File.mkdir html_prefix;
      File.copy_all doc_path html_prefix;
      doc_common path;
      isatool_document doc_format path;
      conditional verbose (fn () =>
        std_error ("Document at " ^ show_path (Path.ext doc_format path) ^ "\n"))));

    (case doc_prefix2 of None => () | Some path =>
     (File.mkdir path;
      copy_files (Path.unpack "~~/lib/texinputs/*.sty") path;
      doc_common path;
      conditional verbose (fn () => std_error ("Document sources at " ^ show_path path ^ "\n"))));

    browser_info := empty_browser_info;
    session_info := None
  end);


(* theory elements *)

fun init_theory name = with_session () (fn _ => init_theory_info name empty_theory_info);

fun verbatim_source name mk_text =
  with_session () (fn _ => add_html_source name (HTML.verbatim_source (mk_text ())));

fun old_symbol_source name mk_text =
  with_session () (fn _ => add_tex_source name (Latex.old_symbol_source name (mk_text ())));

fun theory_output name s =
  with_session () (fn _ => add_tex_source name (Latex.isabelle_file name s));


fun parent_link remote_path curr_session name =
  let val {name = _, session, is_local} = get_info (ThyInfo.theory name)
  in (if null session then None else
     Some (if is_some remote_path andalso not is_local then
       Url.append (the remote_path) (Url.file
         (Path.append (Path.make session) (html_path name)))
     else Url.file (Path.append (mk_rel_path curr_session session)
       (html_path name))), name)
  end;

fun begin_theory name raw_parents orig_files thy =
    with_session thy (fn {name = sess_name, session, path, html_prefix, remote_path, ...} =>
  let
    val parents = map (parent_link remote_path path) raw_parents;
    val ml_path = ThyLoad.ml_path name;
    val files = map (apsnd Some) orig_files @
      (if is_some (ThyLoad.check_file ml_path) then [(ml_path, None)] else []);

    fun prep_file (raw_path, loadit) =
      (case ThyLoad.check_file raw_path of
        Some (path, _) =>
          let
            val base = Path.base path;
            val base_html = html_ext base;
          in
            add_file (Path.append html_prefix base_html,
              HTML.ml_file (Url.file base) (File.read path));
            (Some (Url.file base_html), Url.file raw_path, loadit)
          end
      | None => (warning ("Browser info: expected to find ML file" ^ quote (Path.pack raw_path));
          (None, Url.file raw_path, loadit)));

    val files_html = map prep_file files;

    fun prep_html_source (tex_source, html_source, html) =
      let
        val txt = HTML.begin_theory (Url.file index_path, session)
          name parents files_html (Buffer.content html_source)
      in (tex_source, Buffer.empty, Buffer.add txt html) end;

    val entry =
     {name = name, ID = ID_of path name, dir = sess_name, unfold = true,
      path = Path.pack (html_path name),
      parents = map (fn s => ID_of (#session (get_info (ThyInfo.theory s))) s) raw_parents};

  in
    change_theory_info name prep_html_source;
    add_graph_entry entry;
    add_html_index (HTML.theory_entry (Url.file (html_path name), name));
    add_tex_index (Latex.theory_entry name);
    BrowserInfoData.put {name = sess_name, session = path, is_local = is_some remote_path} thy
  end);


fun result k a thm = with_session () (fn _ => with_context add_html (HTML.result k a thm));
fun results k a thms = with_session () (fn _ => with_context add_html (HTML.results k a thms));
fun theorem a thm = with_session () (fn _ => with_context add_html (HTML.theorem a thm));
fun theorems a thms = with_session () (fn _ => with_context add_html (HTML.theorems a thms));
fun chapter s = with_session () (fn _ => with_context add_html (HTML.chapter s));
fun section s = with_session () (fn _ => with_context add_html (HTML.section s));
fun subsection s = with_session () (fn _ => with_context add_html (HTML.subsection s));
fun subsubsection s = with_session () (fn _ => with_context add_html (HTML.subsubsection s));



(** theory setup **)

val setup = [BrowserInfoData.init];


end;


structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
