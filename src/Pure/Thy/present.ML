(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Theory presentation (HTML, graph files, simple LaTeX documents).
*)

signature BASIC_PRESENT =
sig
  val section: string -> unit
end;

signature PRESENT =
sig
  include BASIC_PRESENT
  val init: bool -> string -> string list -> string -> Url.T option * bool -> unit
  val finish: unit -> unit
  val init_theory: string -> unit
  val verbatim_source: string -> (unit -> string list) -> unit
  type token
  val basic_token: OuterLex.token -> token
  val markup_token: string * string -> token
  val token_source: string -> (unit -> token list) -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> theory -> theory
  val result: string -> string -> thm -> unit
  val results: string -> string -> thm list -> unit
  val theorem: string -> thm -> unit
  val theorems: string -> thm list -> unit
  val subsection: string -> unit
  val subsubsection: string -> unit
  val setup: (theory -> theory) list
  val get_info: theory -> {session: string list, is_local: bool}
end;

structure Present: PRESENT =
struct


(** paths **)

val output_path = Path.variable "ISABELLE_BROWSER_INFO";

fun top_path sess_path offset =
  Path.append (Path.appends (replicate (offset + length sess_path) Path.parent));

val tex_ext = Path.ext "tex";
val tex_path = tex_ext o Path.basic;
val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val graph_path = Path.ext "graph" o Path.basic;
val index_path = Path.basic "index.html";
val doc_path = Path.basic "document";
val doc_index_path = tex_path "session";

val session_path = Path.basic ".session";
val session_entries_path = Path.unpack ".session/entries";
val pre_index_path = Path.unpack ".session/pre-index";



(** additional theory data **)

structure BrowserInfoArgs =
struct
  val name = "Pure/browser_info";
  type T = {session: string list, is_local: bool};

  val empty = {session = [], is_local = false};
  val copy = I;
  fun prep_ext _ = empty;
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

fun get_graph path = map (fn (a :: b :: c :: d :: e :: r) =>
  {name = unenclose a, ID = unenclose b,
   dir = unenclose c, unfold = (d = "+"),
   path = unenclose (if d = "+" then e else d),
   parents = map unenclose (fst (split_last (if d = "+" then tl r else r)))})
     (map (filter_out (equal "") o space_explode " ") (split_lines (File.read path)));

fun put_graph gr path =
    File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents} =>
      "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
      path ^ "\" > " ^ space_implode " " (map quote parents) ^ " ;") gr));

fun dir_of sess = space_implode "/" (case sess of
  [] => ["Pure"] | [x] => [x, "base"] | xs => xs);

fun ID_of sess s = dir_of sess ^ "/" ^ s;


(* retrieve graph data from theory loader database *)

fun make_graph remote_path unfold curr_sess = map (fn name =>
  let
    val {session, is_local} = get_info (ThyInfo.theory name);
    val path' = Path.append (Path.make session) (html_path name)
  in
    {name = name, ID = ID_of session name, dir = dir_of session,
     path = if null session then "" else
            if is_some remote_path andalso not is_local then
              Url.pack (Url.append (the remote_path) (Url.file path'))
            else Path.pack (top_path curr_sess 2 path'),
     unfold = unfold andalso (length session = 1),
     parents = map (fn s => ID_of (#session (get_info (ThyInfo.theory s))) s)
       (ThyInfo.get_preds name)}
  end) (ThyInfo.names ());

fun add_graph_entry' (entry as {ID, ...}) (gr : graph_node list) =
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

type browser_info = {theories: theory_info Symtab.table, tex_index: Buffer.T,
  html_index: Buffer.T, graph: graph_node list, all_graph: graph_node list};

fun make_browser_info (theories, tex_index, html_index, graph, all_graph) =
  {theories = theories, tex_index = tex_index, html_index = html_index,
    graph = graph, all_graph = all_graph}: browser_info;

val empty_browser_info = make_browser_info (Symtab.empty, Buffer.empty, Buffer.empty, [], []);

fun initial_browser_info remote_path graph_path curr_sess = make_browser_info
  (Symtab.empty, Buffer.empty, Buffer.empty, make_graph remote_path false curr_sess,
   if_none (try get_graph graph_path) (make_graph remote_path true [""]));

fun map_browser_info f {theories, tex_index, html_index, graph, all_graph} =
  make_browser_info (f (theories, tex_index, html_index, graph, all_graph));


(* state *)

val browser_info = ref empty_browser_info;

fun change_browser_info f = browser_info := map_browser_info f (! browser_info);

fun init_theory_info name info =
  change_browser_info (fn (theories, tex_index, html_index, graph, all_graph) =>
    (Symtab.update ((name, info), theories), tex_index, html_index, graph, all_graph));

fun change_theory_info name f =
  change_browser_info (fn (info as (theories, tex_index, html_index, graph, all_graph)) =>
    (case Symtab.lookup (theories, name) of
      None => (warning ("Browser info: cannot access theory document " ^ quote name); info)
    | Some info => (Symtab.update ((name, map_theory_info f info), theories),
        tex_index, html_index, graph, all_graph)));


fun add_tex_index txt =
  change_browser_info (fn (theories, tex_index, html_index, graph, all_graph) =>
    (theories, Buffer.add txt tex_index, html_index, graph, all_graph));

fun add_html_index txt =
  change_browser_info (fn (theories, tex_index, html_index, graph, all_graph) =>
    (theories, tex_index, Buffer.add txt html_index, graph, all_graph));

(*add entry to graph for current session*)
fun add_graph_entry e =
  change_browser_info (fn (theories, tex_index, html_index, graph, all_graph) =>
    (theories, tex_index, html_index, add_graph_entry' e graph, all_graph));

(*add entry to graph for all sessions*)
fun add_all_graph_entry e =
  change_browser_info (fn (theories, tex_index, html_index, graph, all_graph) =>
    (theories, tex_index, html_index, graph, add_graph_entry' e all_graph));

fun add_tex_source name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (Buffer.add txt tex_source, html_source, html));

fun add_html_source name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (tex_source, Buffer.add txt html_source, html));

fun add_html name txt = change_theory_info name (fn (tex_source, html_source, html) =>
  (tex_source, html_source, Buffer.add txt html));



(** global session state **)

(* session_info *)

type session_info =
  {name: string, parent: string, session: string, path: string list, html_prefix: Path.T,
    doc_prefix: Path.T option, graph_path: Path.T, all_graph_path: Path.T,
    remote_path: Url.T option};

fun make_session_info (name, parent, session, path, html_prefix, doc_prefix,
    graph_path, all_graph_path, remote_path) =
  {name = name, parent = parent, session = session, path = path,
    html_prefix = html_prefix, doc_prefix = doc_prefix, graph_path = graph_path,
    all_graph_path = all_graph_path, remote_path = remote_path}: session_info;


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

fun could_copy inpath outpath =
  if File.exists inpath then (File.copy inpath outpath; true)
  else false;

fun init false _ _ _ _ = (browser_info := empty_browser_info; session_info := None)
  | init true doc path name (remote_path, first_time) =
      let
        val parent_name = name_of_session (take (length path - 1, path));
        val session_name = name_of_session path;
        val sess_prefix = Path.make path;

        val out_path = Path.expand output_path;
        val html_prefix = Path.append out_path sess_prefix;

        val (doc_prefix, document_path) =
          if doc = "" then (None, None)
          else (Some (Path.append html_prefix doc_path), Some (Path.ext doc doc_path));

        val graph_prefix = Path.appends [out_path, Path.unpack "graph/data", sess_prefix];
        val graph_path = Path.append graph_prefix (Path.basic "session.graph");
        val graph_lnk = Url.file (top_path path 0 (Path.appends
          [Path.unpack "graph/data", sess_prefix, Path.basic "medium.html"]));
        val graph_up_lnk =
          (Url.file (top_path path 2 (Path.append sess_prefix index_path)), session_name);
        val codebase = Url.file (top_path path 1 Path.current);
        val all_graph_path = Path.appends [out_path, Path.unpack "graph/data",
          Path.basic (hd path), Path.basic "all_sessions.graph"];

        val _ = (File.mkdir html_prefix; File.mkdir graph_prefix);

        fun prep_readme readme =
          let val readme_path = Path.basic readme in
            if could_copy readme_path (Path.append html_prefix readme_path) then Some readme_path
            else None
          end;
        val opt_readme =
          (case prep_readme "README.html" of None => prep_readme "README" | some => some);

        val parent_index_path = Path.append Path.parent index_path;
        val index_up_lnk = if first_time then
            Url.append (the remote_path) (Url.file (Path.append sess_prefix parent_index_path))
          else Url.file parent_index_path;

        val index_text = HTML.begin_index (index_up_lnk, parent_name)
          (Url.file index_path, session_name) (apsome Url.file opt_readme)
            (apsome Url.file document_path) graph_lnk;
      in
        File.mkdir (Path.append html_prefix session_path);
        File.write (Path.append html_prefix session_entries_path) "";
        if is_some doc_prefix then File.copy_all doc_path html_prefix else ();
        seq (fn (name, txt) => File.write (Path.append graph_prefix (Path.basic name)) txt)
          (HTML.applet_pages session_name codebase graph_up_lnk (length path = 1));
        session_info := Some (make_session_info (name, parent_name, session_name, path,
          html_prefix, doc_prefix, graph_path, all_graph_path, remote_path));
        browser_info := initial_browser_info remote_path all_graph_path path;
        add_html_index index_text
      end;


(* finish session *)

fun finish () = with_session ()
    (fn {name, html_prefix, doc_prefix, graph_path, all_graph_path, path, ...} =>
  let
    val {theories, tex_index, html_index, graph, all_graph} = ! browser_info;

    fun finish_node (a, {tex_source, html_source = _, html}) =
     (apsome (fn p => Buffer.write (Path.append p (tex_path a)) tex_source) doc_prefix;
      Buffer.write (Path.append html_prefix (html_path a)) (Buffer.add HTML.end_theory html));
  in
    seq finish_node (Symtab.dest theories);
    Buffer.write (Path.append html_prefix pre_index_path) html_index;
    apsome (fn p => Buffer.write (Path.append p doc_index_path) tex_index) doc_prefix;
    put_graph graph graph_path;
    put_graph all_graph all_graph_path;
    create_index html_prefix;
    update_index (Path.append html_prefix Path.parent) name;
    browser_info := empty_browser_info;
    session_info := None
  end);


(* theory elements *)

fun init_theory name = with_session () (fn _ => init_theory_info name empty_theory_info);

fun verbatim_source name mk_text =
  with_session () (fn _ => add_html_source name (HTML.verbatim_source (mk_text ())));


type token = Latex.token;
val basic_token = Latex.Basic;
val markup_token = Latex.Markup;

fun token_source name mk_toks =
  with_session () (fn _ => add_tex_source name (Latex.token_source (mk_toks ())));


fun parent_link remote_path curr_session name =
  let
    val {session, is_local} = get_info (ThyInfo.theory name);
    val path = Path.append (Path.make session) (html_path name)
  in (if null session then None else
     Some (if is_some remote_path andalso not is_local then
       Url.append (the remote_path) (Url.file path)
     else Url.file (top_path curr_session 0 path)), name)
  end;

fun begin_theory name raw_parents orig_files thy =
  with_session thy (fn {session, path, html_prefix, remote_path, ...} =>
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
            File.write (Path.append html_prefix base_html)
              (HTML.ml_file (Url.file base) (File.read path));
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

    fun make_entry unfold all =
      {name = name, ID = ID_of path name, dir = dir_of path, unfold = unfold,
       path = Path.pack (top_path (if all then [""] else path) 2
         (Path.append (Path.make path) (html_path name))),
       parents = map (fn s => ID_of (#session (get_info (ThyInfo.theory s))) s) raw_parents};

  in
    change_theory_info name prep_html_source;
    add_all_graph_entry (make_entry (length path = 1) true);
    add_graph_entry (make_entry true false);
    add_html_index (HTML.theory_entry (Url.file (html_path name), name));
    add_tex_index (Latex.theory_entry name);
    BrowserInfoData.put {session = path, is_local = is_some remote_path} thy
  end);


fun result k a thm = with_session () (fn _ => with_context add_html (HTML.result k a thm));
fun results k a thms = with_session () (fn _ => with_context add_html (HTML.results k a thms));
fun theorem a thm = with_session () (fn _ => with_context add_html (HTML.theorem a thm));
fun theorems a thms = with_session () (fn _ => with_context add_html (HTML.theorems a thms));
fun section s = with_session () (fn _ => with_context add_html (HTML.section s));
fun subsection s = with_session () (fn _ => with_context add_html (HTML.subsection s));
fun subsubsection s = with_session () (fn _ => with_context add_html (HTML.subsubsection s));



(** theory setup **)

val setup = [BrowserInfoData.init];


end;


structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
