(*  Title:      Pure/Thy/browser_info.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Theory browsing information (HTML and graph files).

TODO:
  - href parent theories (this vs. ancestor session!?);
  - ### Browser info: cannot access session index in "/usr/wiss/wenzelm/isabelle/browser_info";
  - usedir: exclude arrow gifs;
  - symlink ".parent", ".top" (URLs!?);
*)

signature BASIC_BROWSER_INFO =
sig
  val section: string -> unit
end;

signature BROWSER_INFO =
sig
  include BASIC_BROWSER_INFO
  val init: bool -> string list -> string -> unit
  val finish: unit -> unit
  val theory_source: string -> (string, 'a) Source.source -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> unit
  val end_theory: string -> unit
  val theorem: string -> thm -> unit
end;

structure BrowserInfo: BROWSER_INFO =
struct


(** global browser info state **)

(* type theory_info *)

type theory_info = {source: Buffer.T, html: Buffer.T, graph: Buffer.T};

fun make_theory_info (source, html, graph) =
  {source = source, html = html, graph = graph}: theory_info;

val empty_theory_info = make_theory_info (Buffer.empty, Buffer.empty, Buffer.empty);
fun map_theory_info f {source, html, graph} = make_theory_info (f (source, html, graph));


(* type browser_info *)

type browser_info = {theories: theory_info Symtab.table, index: Buffer.T};

fun make_browser_info (theories, index) =
  {theories = theories, index = index}: browser_info;

val empty_browser_info = make_browser_info (Symtab.empty, Buffer.empty);
fun map_browser_info f {theories, index} = make_browser_info (f (theories, index));


(* state *)

val browser_info = ref empty_browser_info;

fun change_browser_info f = browser_info := map_browser_info f (! browser_info);

fun init_theory_info name info = change_browser_info (fn (theories, index) =>
  (Symtab.update ((name, info), theories), index));

fun change_theory_info name f = change_browser_info (fn (theories, index) =>
  (case Symtab.lookup (theories, name) of
    None => (warning ("Browser info: cannot access theory document " ^ quote name);
      (theories, index))
  | Some info => (Symtab.update ((name, map_theory_info f info), theories), index)));


fun add_index txt = change_browser_info (fn (theories, index) =>
  (theories, Buffer.add txt index));

fun add_source name txt = change_theory_info name (fn (source, html, graph) =>
  (Buffer.add txt source, html, graph));

fun add_html name txt = change_theory_info name (fn (source, html, graph) =>
  (source, Buffer.add txt html, graph));

fun add_graph name txt = change_theory_info name (fn (source, html, graph) =>
  (source, html, Buffer.add txt graph));



(** global session state **)

(* paths *)

val output_path = Path.variable "ISABELLE_BROWSER_INFO";

fun top_path sess_path = Path.append (Path.appends (replicate (length sess_path) Path.parent));

val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val graph_path = Path.ext "graph" o Path.basic;
val index_path = Path.basic "index.html";

val session_path = Path.basic ".session";
val session_entries_path = Path.unpack ".session/entries";
val pre_index_path = Path.unpack ".session/pre-index";


(* session_info *)

type session_info =
  {name: string, parent: string, session: string, path: string list,
    html_prefix: Path.T, graph_prefix: Path.T};

fun make_session_info (name, parent, session, path, html_prefix, graph_prefix) =
  {name = name, parent = parent, session = session, path = path,
    html_prefix = html_prefix, graph_prefix = graph_prefix}: session_info;


(* state *)

val session_info = ref (None: session_info option);

fun with_session f = (case ! session_info of None => () | Some info => f info);
fun with_context f = f (PureThy.get_name (Context.the_context ()));




(** HTML output **)


(* maintain index *)

val session_entries =
  HTML.session_entries o map (fn name => (Path.append (Path.basic name) index_path, name));

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
    None => warning ("Browser info: cannot access session index in " ^ quote (Path.pack dir))
  | Some es => (put_entries ((es \ name) @ [name]) dir; create_index dir));


(* init session *)

fun name_of_session elems = space_implode "/" ("Isabelle" :: elems);

fun could_copy inpath outpath =
  if File.exists inpath then (File.copy inpath outpath; true)
  else false;

fun init false _ _ = (browser_info := empty_browser_info; session_info := None)
  | init true path name =
      let
        val parent_name = name_of_session (take (length path - 1, path));
        val session_name = name_of_session path;
        val sess_prefix = Path.make path;
        val out_path = Path.expand output_path;
        val html_prefix = Path.append out_path sess_prefix;
        val graph_prefix = Path.appends [out_path, Path.unpack "graph/data", sess_prefix];

        val _ = (File.mkdir html_prefix; File.mkdir graph_prefix);
        fun prep_readme readme =
          let val readme_path = Path.basic readme in
            if could_copy readme_path (Path.append html_prefix readme_path) then Some readme_path
            else None
          end;
        val opt_readme =
          (case prep_readme "README.html" of None => prep_readme "README" | some => some);
        val index_text = HTML.begin_index (Path.append Path.parent index_path, parent_name)
          (index_path, session_name) opt_readme;
      in
        File.mkdir (Path.append html_prefix session_path);
        File.write (Path.append html_prefix session_entries_path) "";
        session_info := Some (make_session_info (name, parent_name, session_name, path,
          html_prefix, graph_prefix));
        browser_info := empty_browser_info;
        add_index index_text
      end;


(* finish session *)

fun finish () = with_session (fn {name, html_prefix, graph_prefix, ...} =>
  let
    val {theories, index} = ! browser_info;

    fun finish_node (a, {source = _, html, graph}) =
      (Buffer.write (Path.append html_prefix (html_path a)) (Buffer.add HTML.end_theory html);
        Buffer.write (Path.append graph_prefix (graph_path a)) graph);
  in
    seq finish_node (Symtab.dest theories);
    Buffer.write (Path.append html_prefix pre_index_path) index;
    create_index html_prefix;
    update_index (Path.append html_prefix Path.parent) name;
    browser_info := empty_browser_info;
    session_info := None
  end);


(* theory elements *)

fun theory_source name src = with_session (fn _ =>
  (init_theory_info name empty_theory_info; add_source name (HTML.source src)));


(* FIXME clean *)

fun parent_link name =
  if is_some (Symtab.lookup (#theories (! browser_info), name)) then (Some (html_path name), name)
  else (None, name);

fun begin_theory name raw_parents orig_files = with_session (fn {session, html_prefix, ...} =>
  let
    val parents = map parent_link raw_parents;
    val ml_path = ThyLoad.ml_path name;
    val files = orig_files @		(* FIXME improve!? *)
      (if is_some (ThyLoad.check_file ml_path) then [(ml_path, true)] else []);

    fun prep_file (raw_path, loadit) =
      (case ThyLoad.check_file raw_path of
        Some (path, _) =>
          let
            val base = Path.base path;
            val base_html = html_ext base;
          in
            File.write (Path.append html_prefix base_html) (HTML.ml_file base (File.read path));
            (Some base_html, raw_path, loadit)
          end
      | None => (warning ("Browser info: expected to find ML file" ^ quote (Path.pack raw_path));
          (None, raw_path, loadit)));

    val files_html = map prep_file files;
    fun prep_source (source, html, graph) =
      let val txt =
        HTML.begin_theory (index_path, session) name parents files_html (Buffer.content source)
      in (Buffer.empty, Buffer.add txt html, graph) end;
  in
    change_theory_info name prep_source;
    add_index (HTML.theory_entry (html_path name, name))
  end);

fun end_theory _ = ();

fun theorem name thm = with_session (fn _ => with_context add_html (HTML.theorem name thm));
fun section s = with_session (fn _ => with_context add_html (HTML.section s));


end;


(* FIXME

(******************** Graph generation functions ************************)


(*flag that indicates whether graph files should be generated*)
val make_graph = ref false;


(*file to use as basis for new graph files*)
val graph_base_file = ref "";


(*directory containing basic theories (gets label "base")*)
val graph_root_dir = ref "";


(*name of current graph file*)
val graph_file = ref "";


(*name of large graph file which also contains
  theories defined in subdirectories *)
val large_graph_file = ref "";


(* initialize graph data generator *)
fun init_graph usedir_arg =
  let
      (*create default graph containing only Pure, CPure and ProtoPure*)
      fun default_graph outfile =
        let val os = TextIO.openOut outfile;
        in (TextIO.output(os,"\"ProtoPure\" \"ProtoPure\" \"Pure\" \"\" ;\n\
                             \\"CPure\" \"CPure\" \"Pure\" \"\" > \"ProtoPure\" ;\n\
                             \\"Pure\" \"Pure\" \"Pure\" \"\" > \"ProtoPure\" ;\n");
            TextIO.closeOut os)
        end;

      (*copy graph file, adjust relative paths for theory files*)
      fun copy_graph infile outfile unfold =
        let val is = TextIO.openIn infile;
            val (inp_dir, _) = split_filename infile;
            val (outp_dir, _) = split_filename outfile;
            val entries = map (BAD_space_explode " ")
                            (BAD_space_explode "\n" (TextIO.inputAll is));

            fun thyfile f = if f = "\"\"" then f else
              let val (dir, name) =
                    split_filename (implode (rev (tl (rev (tl (explode f))))));
                  val abs_path = normalize_path (tack_on inp_dir dir);
                  val rel_path = tack_on (relative_path outp_dir abs_path) name
              in quote rel_path end;

            fun process_entry (a::b::c::d::e::r) =
              if d = "+" then
                a::b::c::((if unfold then "+ " else "") ^ (thyfile e))::r
              else
                a::b::c::(thyfile d)::e::r;

            val _  = TextIO.closeIn is;
            val os = TextIO.openOut outfile;
            val _  = TextIO.output(os, (cat_lines
                          (map ((space_implode " ") o process_entry) entries)) ^ "\n");
            val _  = TextIO.closeOut os;
        in () end;

      (*create html page which contains graph browser applet*)
      fun mk_applet_page abs_path large other_graph =
        let
          val dir_name =
            (if subdir_of (!original_path, !base_path) then "Isabelle/" else "") ^
            (relative_path (normalize_path (tack_on (!graph_root_dir) "..")) (pwd ()));
          val rel_codebase =
            relative_path abs_path (tack_on (normalize_path (!output_dir)) "graph");
          val rel_index_path = tack_on (relative_path
            abs_path (tack_on (normalize_path (!output_dir)) "graph")) "index.html";
          val outfile =
            tack_on abs_path ((if large then "large" else "small") ^ ".html");
          val os = TextIO.openOut outfile;
          val _ = TextIO.output(os,
            "<HTML><HEAD><TITLE>" ^ dir_name ^ "</TITLE></HEAD>\n\
            \<BODY><H2>" ^ dir_name ^ "</H2>\n" ^
            (if other_graph then
              (if large then
                 "View <A HREF=\"small.html\">small graph</A> without \
                 \subdirectories<P>\n"
               else
                 "View <A HREF=\"large.html\">large graph</A> including \
                 \all subdirectories<P>\n")
             else "") ^
            "<A HREF=\"" ^ rel_index_path ^ "\">Back</A> to index\n<HR>\n\
            \<APPLET CODE=\"GraphBrowser/GraphBrowser.class\" \
            \CODEBASE=\"" ^ rel_codebase ^ "\" WIDTH=550 HEIGHT=450>\n\
            \<PARAM NAME=\"graphfile\" VALUE=\"" ^
            (if large then "large.graph" else "small.graph") ^ "\">\n\
            \</APPLET>\n<HR>\n</BODY></HTML>")
          val _ = TextIO.closeOut os
        in () end;

      val gpath = graph_path (pwd ());

  in
    (make_graph := true;
     base_path := normalize_path (!base_path);
     mkdir gpath;
     original_path := pwd ();
     graph_file := tack_on gpath "small.graph";
     graph_root_dir := (if usedir_arg = "." then pwd ()
                        else normalize_path (tack_on (pwd ()) ".."));
     (if (!graph_base_file) = "" then
        (large_graph_file := tack_on gpath "large.graph";
         default_graph (!graph_file);
         default_graph (!large_graph_file);
         mk_applet_page gpath false true;
         mk_applet_page gpath true true)
      else
        (if subdir_of (fst (split_filename (!graph_file)),
            (fst (split_filename (!graph_base_file))))
         then
           (copy_graph (!graph_base_file) (!graph_file) true;
            mk_applet_page gpath false false)
         else
           (large_graph_file := tack_on gpath "large.graph";
            mk_applet_page gpath false true;
            mk_applet_page gpath true true;
            copy_graph (!graph_base_file) (!graph_file) false;
            copy_graph (!graph_base_file) (!large_graph_file) false)));
     graph_base_file := (!graph_file))
  end;


(*add theory to graph definition file*)
fun mk_graph tname abs_path = if not (!make_graph) then () else
  let val parents =
        map (fn (t, _) => tack_on (path_of t) t)
          (filter (fn (_, {children,...}) => tname mem children)
             (Symtab.dest(!loaded_thys)));

      val dir_name = relative_path
         (normalize_path (tack_on (!graph_root_dir) "..")) abs_path;

      val dir_entry = "\"" ^ dir_name ^
         (if (tack_on abs_path "") = (tack_on (!graph_root_dir) "")
          then "/base\" + " else "\" ");

      val thy_file = (tack_on (html_path abs_path) tname) ^ ".html";

      val thy_ID = quote (tack_on abs_path tname);

      val entry_str_1 = (quote tname) ^ " " ^ thy_ID ^ " " ^ dir_entry ^
                (quote (relative_path (fst (split_filename (!graph_file))) thy_file)) ^
                " > " ^ (space_implode " " (map quote parents)) ^ " ;\n" ;

      val entry_str_2 = (quote tname) ^ " " ^ thy_ID ^ " " ^ dir_entry ^
                (quote (relative_path (fst (split_filename (!large_graph_file))) thy_file)) ^
                " > " ^ (space_implode " " (map quote parents)) ^ " ;\n" ;

      fun exists_entry id infile =
        let val is = TextIO.openIn(infile);
            val IDs = map (hd o tl o (BAD_space_explode " "))
                            (BAD_space_explode "\n" (TextIO.inputAll is));
            val _ = TextIO.closeIn is
        in id mem IDs end;

      fun mk_entry outfile entry_str =
        if exists_entry thy_ID outfile then ()
        else
          let val os = TextIO.openAppend outfile;
              val _ = TextIO.output (os, entry_str);
              val _ = TextIO.closeOut os;
          in () end

  in (mk_entry (!graph_file) entry_str_1;
      mk_entry (!large_graph_file) entry_str_2) handle _ =>
             (make_graph:=false;
              warning ("Unable to write to graph file " ^ (!graph_file)))
  end;

*)
