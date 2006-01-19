(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

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
  val get_info: theory -> {name: string, session: string list, is_local: bool}
  val write_graph: {name: string, ID: string, dir: string, unfold: bool,
   path: string, parents: string list} list -> Path.T -> unit
  val init: bool -> bool -> string -> bool -> string list -> string list ->
    string -> (bool * Path.T) option -> Url.T option * bool -> bool -> unit
  val finish: unit -> unit
  val init_theory: string -> unit
  val verbatim_source: string -> (unit -> Symbol.symbol list) -> unit
  val theory_output: string -> string -> unit
  val begin_theory: Path.T option -> string -> string list ->
    (Path.T * bool) list -> theory -> theory
  val add_hook: (string -> (string * thm list) list -> unit) -> unit
  val results: string -> (string * thm list) list -> unit
  val theorem: string -> thm -> unit
  val theorems: string -> thm list -> unit
  val chapter: string -> unit
  val subsection: string -> unit
  val subsubsection: string -> unit
  val drafts: string -> Path.T list -> Path.T
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
val documentN = "document";
val document_path = Path.basic documentN;
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

structure BrowserInfoData = TheoryDataFun
(struct
  val name = "Pure/browser_info";
  type T = {name: string, session: string list, is_local: bool};
  val empty = {name = "", session = [], is_local = false}: T;
  val copy = I;
  fun extend _ = empty;
  fun merge _ _ = empty;
  fun print _ _ = ();
end);

val _ = Context.add_setup BrowserInfoData.init;

fun get_info thy =
  if Context.theory_name thy mem_string [Context.ProtoPureN, Context.PureN, Context.CPureN]
  then {name = Context.PureN, session = [], is_local = false}
  else BrowserInfoData.get thy;



(** graphs **)

type graph_node =
  {name: string, ID: string, dir: string, unfold: bool,
   path: string, parents: string list};

fun write_graph gr path =
  File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents} =>
    "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
    path ^ "\" > " ^ space_implode " " (map Library.quote parents) ^ " ;") gr));

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
        Url.pack (Url.append (the remote_path) (Url.File
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
    (Symtab.update (name, info) theories, files, tex_index, html_index, graph));

fun change_theory_info name f =
  change_browser_info (fn (info as (theories, files, tex_index, html_index, graph)) =>
    (case Symtab.lookup theories name of
      NONE => (warning ("Browser info: cannot access theory document " ^ quote name); info)
    | SOME info => (Symtab.update (name, map_theory_info f info) theories, files,
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
    info: bool, doc_format: string, doc_graph: bool, documents: (string * string) list,
    doc_prefix1: (Path.T * Path.T) option, doc_prefix2: (bool * Path.T) option,
    remote_path: Url.T option, verbose: bool, readme: Path.T option};

fun make_session_info
  (name, parent, session, path, html_prefix, info, doc_format, doc_graph, documents,
    doc_prefix1, doc_prefix2, remote_path, verbose, readme) =
  {name = name, parent = parent, session = session, path = path, html_prefix = html_prefix,
    info = info, doc_format = doc_format, doc_graph = doc_graph, documents = documents,
    doc_prefix1 = doc_prefix1, doc_prefix2 = doc_prefix2, remote_path = remote_path,
    verbose = verbose, readme = readme}: session_info;


(* state *)

val session_info = ref (NONE: session_info option);

fun with_session x f = (case ! session_info of NONE => x | SOME info => f info);
fun with_context f = f (Context.theory_name (Context.the_context ()));



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
    session_entries (get_entries dir) ^ HTML.end_index
  |> File.write (Path.append dir index_path);

fun update_index dir name =
  (case try get_entries dir of
    NONE => warning ("Browser info: cannot access session index of " ^ quote (Path.pack dir))
  | SOME es => (put_entries ((es \ name) @ [name]) dir; create_index dir));


(* document versions *)

fun read_version str =
  (case space_explode "=" str of
    [name] => (name, "")
  | [name, tags] => (name, tags)
  | _ => error ("Malformed document version specification: " ^ quote str));

fun read_versions strs =
  rev (gen_distinct (eq_fst (op =)) (rev ((documentN, "") :: map read_version strs)))
  |> filter_out (equal "-" o #2);


(* init session *)

fun name_of_session elems = space_implode "/" ("Isabelle" :: elems);

fun init build info doc doc_graph doc_versions path name doc_prefix2
    (remote_path, first_time) verbose =
  if not build andalso not info andalso doc = "" andalso is_none doc_prefix2 then
    (browser_info := empty_browser_info; session_info := NONE)
  else
    let
      val parent_name = name_of_session (Library.take (length path - 1, path));
      val session_name = name_of_session path;
      val sess_prefix = Path.make path;
      val html_prefix = Path.append (Path.expand output_path) sess_prefix;

      val (doc_prefix1, documents) =
        if doc = "" then (NONE, [])
        else if not (File.exists document_path) then (conditional verbose (fn () =>
          std_error "Warning: missing document directory\n"); (NONE, []))
        else (SOME (Path.append html_prefix document_path, html_prefix),
          read_versions doc_versions);

      val parent_index_path = Path.append Path.parent index_path;
      val index_up_lnk = if first_time then
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
        (Url.File index_path, session_name) docs (Url.unpack "medium.html");
    in
      session_info := SOME (make_session_info (name, parent_name, session_name, path, html_prefix,
      info, doc, doc_graph, documents, doc_prefix1, doc_prefix2, remote_path, verbose, readme));
      browser_info := init_browser_info remote_path path;
      add_html_index index_text
    end;


(* isatool wrappers *)

fun isatool_document verbose format name tags path result_path =
  let
    val s = "\"$ISATOOL\" document -c -o '" ^ format ^ "' \
      \-n '" ^ name ^ "' -t '" ^ tags ^ "' " ^ File.shell_path path ^
      " 2>&1" ^ (if verbose then "" else " >/dev/null");
    val doc_path = Path.append result_path (Path.ext format (Path.basic name));
  in
    conditional verbose (fn () => writeln s);
    system s;
    conditional (not (File.exists doc_path)) (fn () =>
      error ("No document: " ^ quote (show_path doc_path)));
    doc_path
  end;

fun isatool_browser graph =
  let
    val pdf_path = File.tmp_path graph_pdf_path;
    val eps_path = File.tmp_path graph_eps_path;
    val gr_path = File.tmp_path graph_path;
    val s = "browser -o " ^ File.shell_path pdf_path ^ " " ^ File.shell_path gr_path;
  in
    write_graph graph gr_path;
    if File.isatool s <> 0 orelse not (File.exists eps_path) orelse not (File.exists pdf_path)
    then error "Failed to prepare dependency graph"
    else
      let val pdf = File.read pdf_path and eps = File.read eps_path
      in File.rm pdf_path; File.rm eps_path; File.rm gr_path; (pdf, eps) end
  end;


(* finish session -- output all generated text *)

fun write_tex src name path =
  Buffer.write (Path.append path (tex_path name)) src;

fun write_tex_index tex_index path =
  write_tex (Buffer.add Latex.tex_trailer tex_index) doc_indexN path;


fun finish () = with_session () (fn {name, info, html_prefix, doc_format, doc_graph,
    documents, doc_prefix1, doc_prefix2, path, verbose, readme, ...} =>
  let
    val {theories, files, tex_index, html_index, graph} = ! browser_info;
    val thys = Symtab.dest theories;
    val parent_html_prefix = Path.append html_prefix Path.parent;

    fun finish_tex path (a, {tex_source, ...}: theory_info) = write_tex tex_source a path;
    fun finish_html (a, {html, ...}: theory_info) =
      Buffer.write (Path.append html_prefix (html_path a)) (Buffer.add HTML.end_theory html);

    val opt_graphs =
      if doc_graph andalso (is_some doc_prefix1 orelse is_some doc_prefix2) then
        SOME (isatool_browser graph)
      else NONE;

    fun prepare_sources cp path =
     (File.mkdir path;
      if cp then File.copy_dir document_path path else ();
      File.isatool ("latex -o sty " ^ File.shell_path (Path.append path (Path.basic "root.tex")));
      (case opt_graphs of NONE => () | SOME (pdf, eps) =>
        (File.write (Path.append path graph_pdf_path) pdf;
          File.write (Path.append path graph_eps_path) eps));
      write_tex_index tex_index path;
      List.app (finish_tex path) thys);
  in
    conditional info (fn () =>
     (File.mkdir (Path.append html_prefix session_path);
      Buffer.write (Path.append html_prefix pre_index_path) html_index;
      File.write (Path.append html_prefix session_entries_path) "";
      create_index html_prefix;
      if length path > 1 then update_index parent_html_prefix name else ();
      (case readme of NONE => () | SOME path => File.copy path html_prefix);
      write_graph graph (Path.append html_prefix graph_path);
      File.copy (Path.unpack "~~/lib/browser/GraphBrowser.jar") html_prefix;
      List.app (fn (a, txt) => File.write (Path.append html_prefix (Path.basic a)) txt)
        (HTML.applet_pages name (Url.File index_path, name));
      File.copy (Path.unpack "~~/lib/html/isabelle.css") html_prefix;
      List.app finish_html thys;
      List.app (uncurry File.write) files;
      conditional verbose (fn () =>
        std_error ("Browser info at " ^ show_path html_prefix ^ "\n"))));

    (case doc_prefix2 of NONE => () | SOME (cp, path) =>
     (prepare_sources cp path;
      conditional verbose (fn () => std_error ("Document sources at " ^ show_path path ^ "\n"))));

    (case doc_prefix1 of NONE => () | SOME (path, result_path) =>
      documents |> List.app (fn (name, tags) =>
       let
         val _ = prepare_sources true path;
         val doc_path = isatool_document true doc_format name tags path result_path;
       in
         conditional verbose (fn () => std_error ("Document at " ^ show_path doc_path ^ "\n"))
       end));

    browser_info := empty_browser_info;
    session_info := NONE
  end);


(* theory elements *)

fun init_theory name = with_session () (fn _ => init_theory_info name empty_theory_info);

fun verbatim_source name mk_text =
  with_session () (fn _ => add_html_source name (HTML.verbatim_source (mk_text ())));

fun theory_output name s =
  with_session () (fn _ => add_tex_source name (Latex.isabelle_file name s));


fun parent_link remote_path curr_session name =
  let val {name = _, session, is_local} = get_info (ThyInfo.theory name)
  in (if null session then NONE else
     SOME (if is_some remote_path andalso not is_local then
       Url.append (the remote_path) (Url.File
         (Path.append (Path.make session) (html_path name)))
     else Url.File (Path.append (mk_rel_path curr_session session)
       (html_path name))), name)
  end;

fun begin_theory optpath name raw_parents orig_files thy =
    with_session thy (fn {name = sess_name, session, path, html_prefix, remote_path, ...} =>
  let
    val parents = map (parent_link remote_path path) raw_parents;
    val ml_path = ThyLoad.ml_path name;
    val files = map (apsnd SOME) orig_files @
      (if is_some (ThyLoad.check_file optpath ml_path) then [(ml_path, NONE)] else []);

    fun prep_file (raw_path, loadit) =
      (case ThyLoad.check_file optpath raw_path of
        SOME (path, _) =>
          let
            val base = Path.base path;
            val base_html = html_ext base;
          in
            add_file (Path.append html_prefix base_html,
              HTML.ml_file (Url.File base) (File.read path));
            (SOME (Url.File base_html), Url.File raw_path, loadit)
          end
      | NONE => (warning ("Browser info: expected to find ML file" ^ quote (Path.pack raw_path));
          (NONE, Url.File raw_path, loadit)));

    val files_html = map prep_file files;

    fun prep_html_source (tex_source, html_source, html) =
      let
        val txt = HTML.begin_theory (Url.File index_path, session)
          name parents files_html (Buffer.content html_source)
      in (tex_source, Buffer.empty, Buffer.add txt html) end;

    val entry =
     {name = name, ID = ID_of path name, dir = sess_name, unfold = true,
      path = Path.pack (html_path name),
      parents = map (fn s => ID_of (#session (get_info (ThyInfo.theory s))) s) raw_parents};

  in
    change_theory_info name prep_html_source;
    add_graph_entry entry;
    add_html_index (HTML.theory_entry (Url.File (html_path name), name));
    add_tex_index (Latex.theory_entry name);
    BrowserInfoData.put {name = sess_name, session = path, is_local = is_some remote_path} thy
  end);


val hooks = ref ([]: (string -> (string * thm list) list -> unit) list);
fun add_hook f = hooks := (f :: ! hooks);

fun results k xs =
 (List.app (fn f => (try (fn () => f k xs) (); ())) (! hooks);
  with_session () (fn _ => with_context add_html (HTML.results k xs)));

fun theorem a th = results "theorem" [(a, [th])];
fun theorems a ths = results "theorems" [(a, ths)];
fun chapter s = with_session () (fn _ => with_context add_html (HTML.chapter s));
fun section s = with_session () (fn _ => with_context add_html (HTML.section s));
fun subsection s = with_session () (fn _ => with_context add_html (HTML.subsection s));
fun subsubsection s = with_session () (fn _ => with_context add_html (HTML.subsubsection s));



(** draft document output **)

fun drafts doc_format src_paths =
  let
    fun prep_draft (tex_index, path) =
      let
        val base = Path.base path;
        val name =
          (case Path.pack (#1 (Path.split_ext base)) of "" => gensym "DUMMY" | s => s);
      in
        if File.exists path then
          (Buffer.add (Latex.theory_entry name) tex_index, (name, base, File.read path))
        else error ("Bad file: " ^ quote (Path.pack path))
      end;
    val (tex_index, srcs) = foldl_map prep_draft (Buffer.empty, src_paths);

    val doc_path = File.tmp_path document_path;
    val result_path = Path.append doc_path Path.parent;
    val _ = File.mkdir doc_path;
    val root_path = Path.append doc_path (Path.basic "root.tex");
    val _ = File.copy (Path.unpack "~~/lib/texinputs/draft.tex") root_path;
    val _ = File.isatool ("latex -o sty " ^ File.shell_path root_path);
    val _ = File.isatool ("latex -o syms " ^ File.shell_path root_path);

    fun known name =
      let val ss = split_lines (File.read (Path.append doc_path (Path.basic name)))
      in fn s => s mem_string ss end;
    val known_syms = known "syms.lst";
    val known_ctrls = known "ctrls.lst";

    val _ = srcs |> List.app (fn (name, base, txt) =>
      Symbol.explode txt
      |> Latex.symbol_source (known_syms, known_ctrls) (Path.pack base)
      |> File.write (Path.append doc_path (tex_path name)));
    val _ = write_tex_index tex_index doc_path;
  in isatool_document false doc_format documentN "" doc_path result_path end;


end;

structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
