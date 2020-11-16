(*  Title:      Pure/Thy/present.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Theory presentation: HTML and PDF-LaTeX documents.
*)

signature PRESENT =
sig
  val init: bool -> Path.T -> string list -> string * string -> bool -> unit
  val finish: unit -> unit
  val begin_theory: int -> HTML.text -> theory -> theory
end;

structure Present: PRESENT =
struct


(** paths **)

val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val index_path = Path.basic "index.html";
val readme_html_path = Path.basic "README.html";
val session_graph_path = Path.basic "session_graph.pdf";
val document_path = Path.ext "pdf" o Path.basic;

fun show_path path = Path.implode (Path.expand (File.full_path Path.current path));



(** global browser info state **)

(* type browser_info *)

type browser_info =
 {html_theories: string Symtab.table,
  html_index: (int * string) list};

fun make_browser_info (html_theories, html_index) : browser_info =
  {html_theories = html_theories, html_index = html_index};

val empty_browser_info = make_browser_info (Symtab.empty, []);

fun map_browser_info f {html_theories, html_index} =
  make_browser_info (f (html_theories, html_index));


(* state *)

val browser_info = Synchronized.var "browser_info" empty_browser_info;
fun change_browser_info f = Synchronized.change browser_info (map_browser_info f);

fun update_html name html = change_browser_info (apfst (Symtab.update (name, html)));

fun add_html_index txt = change_browser_info (apsnd (cons txt));



(** global session state **)

(* session_info *)

type session_info =
  {name: string, chapter: string, info_path: Path.T, info: bool,
    verbose: bool, readme: Path.T option};

fun make_session_info (name, chapter, info_path, info, verbose, readme) =
  {name = name, chapter = chapter, info_path = info_path, info = info,
    verbose = verbose, readme = readme}: session_info;


(* state *)

val session_info = Unsynchronized.ref (NONE: session_info option);

fun with_session_info x f = (case ! session_info of NONE => x | SOME info => f info);

val theory_qualifier = Resources.theory_qualifier o Context.theory_long_name;

fun is_session_theory thy =
  (case ! session_info of
    NONE => false
  | SOME {name, ...} => name = theory_qualifier thy);


(** document preparation **)

(* init session *)

fun init info info_path documents (chapter, name) verbose =
  let
    val readme = if File.exists readme_html_path then SOME readme_html_path else NONE;
    val symbols = Resources.html_symbols ();
    val docs =
      (case readme of NONE => [] | SOME p => [(Url.File p, "README")]) @
        map (fn name => (Url.File (document_path name), name)) documents;
  in
    session_info := SOME (make_session_info (name, chapter, info_path, info, verbose, readme));
    Synchronized.change browser_info (K empty_browser_info);
    add_html_index (0, HTML.begin_session_index symbols name (Url.File session_graph_path) docs)
  end;


(* finish session -- output all generated text *)

fun sorted_index index = map snd (sort (int_ord o apply2 fst) (rev index));
fun index_buffer index = Buffer.add (implode (sorted_index index)) Buffer.empty;

fun finish () = with_session_info () (fn {name, chapter, info, info_path, verbose, readme, ...} =>
  let
    val {html_theories, html_index} = Synchronized.value browser_info;

    val session_prefix = info_path + Path.basic chapter + Path.basic name;

    fun finish_html (a, html) = File.write (session_prefix + html_path a) html;

    val _ =
      if info then
       (Isabelle_System.make_directory session_prefix;
        File.write_buffer (session_prefix + index_path)
          (index_buffer html_index |> Buffer.add HTML.end_document);
        (case readme of NONE => () | SOME path => Isabelle_System.copy_file path session_prefix);
        Symtab.fold (K o finish_html) html_theories ();
        if verbose
        then Output.physical_stderr ("Browser info at " ^ show_path session_prefix ^ "\n")
        else ())
      else ();
  in
    Synchronized.change browser_info (K empty_browser_info);
    session_info := NONE
  end);


(* theory elements *)

fun theory_link (curr_chapter, curr_session) thy =
  let
    val session = Resources.theory_qualifier (Context.theory_long_name thy);
    val chapter = Resources.session_chapter session;
    val link = html_path (Context.theory_name thy);
  in
    if curr_session = session then SOME link
    else if curr_chapter = chapter then
      SOME (Path.parent + Path.basic session + link)
    else if chapter = Context.PureN then NONE
    else SOME (Path.parent + Path.parent + Path.basic chapter + Path.basic session + link)
  end;

fun begin_theory update_time html thy =
  with_session_info thy (fn {name = session_name, chapter, ...} =>
    let
      val name = Context.theory_name thy;

      val parent_specs =
        Theory.parents_of thy |> map (fn parent =>
          (Option.map Url.File (theory_link (chapter, session_name) parent),
            (Context.theory_name parent)));

      val symbols = Resources.html_symbols ();
      val _ = update_html name (HTML.theory symbols name parent_specs html);

      val _ =
        if is_session_theory thy then
          add_html_index (update_time, HTML.theory_entry symbols (Url.File (html_path name), name))
        else ();
    in thy end);

end;
