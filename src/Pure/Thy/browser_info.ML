(*  Title:      Pure/Thy/browser_info.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Theory browsing information (HTML and graph files).

TODO:
  - Contents: theories, sessions;
  - symlink ".parent", ".top" (URLs!?);
  - extend parent index: maintain "<!--insert--here-->" marker (!?);
  - proper handling of out of context theorems / sections (!?);
  - usedir: exclude arrow gifs;
*)

signature BASIC_BROWSER_INFO =
sig
  val section: string -> unit
end;

signature BROWSER_INFO =
sig
  include BASIC_BROWSER_INFO
  val init: bool -> string -> string list -> string -> string -> unit
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
val parent_path = Path.append Path.parent;

val html_ext = Path.ext "html";
val html_path = html_ext o Path.basic;
val graph_path = Path.ext "graph" o Path.basic;
val index_path = Path.basic "index.html";


(* session_info *)

type session_info =
  {session: string, path: string list, parent: string, name: string,
    html_prefix: Path.T, graph_prefix: Path.T};

fun make_session_info (session, path, parent, name, html_prefix, graph_prefix) =
  {session = session, path = path, parent = parent, name = name,
    html_prefix = html_prefix, graph_prefix = graph_prefix}: session_info;

val session_info = ref (None: session_info option);

fun in_context f = f (PureThy.get_name (Context.the_context ()));
fun conditional f = (case ! session_info of None => () | Some info => f info);


(* init session *)

fun init false _ _ _ _ = (browser_info := empty_browser_info; session_info := None)
  | init true session path parent name =
      let
        val out_path = Path.expand output_path;
        val sess_prefix = Path.make path;
        val html_prefix = Path.append out_path sess_prefix;
        val graph_prefix = Path.appends [out_path, Path.unpack "graph/data", sess_prefix];
      in
        File.mkdir html_prefix;
        File.mkdir graph_prefix;
        browser_info := empty_browser_info;
        session_info :=
          Some (make_session_info (session, path, parent, name, html_prefix, graph_prefix))
      end;


(* finish session *)

fun finish_node html_prefix graph_prefix (name, {source = _, html, graph}) =
 (Buffer.write (Path.append html_prefix (html_path name)) (Buffer.add HTML.conclude_theory html);
  Buffer.write (Path.append graph_prefix (graph_path name)) graph);

fun finish () = conditional (fn {html_prefix, graph_prefix, ...} =>
  let val {theories, index} = ! browser_info in
    seq (finish_node html_prefix graph_prefix) (Symtab.dest theories);
    Buffer.write (Path.append html_prefix index_path) index;
    browser_info := empty_browser_info;
    session_info := None
  end);



(** HTML output **)

fun theory_source name src = conditional (fn _ =>
  (init_theory_info name empty_theory_info; add_source name (HTML.source src)));

fun begin_theory name parents orig_files = conditional (fn {session, html_prefix, ...} =>
  let
    val ml_path = ThyLoad.ml_path name;
    val files = orig_files @		(* FIXME improve!? *)
      (if is_some (ThyLoad.check_file ml_path) then [(ml_path, true)] else []);
    val files_html = map (fn (p, loadit) => ((p, html_ext p), loadit)) files;

    fun prep_file raw_path =
      (case ThyLoad.check_file raw_path of
        Some (path, _) =>
          let val base = Path.base path in
            File.write (Path.append html_prefix (html_ext base))
              (HTML.ml_file base (File.read path))
          end
      | None => warning ("Browser info: expected to find ML file" ^ quote (Path.pack raw_path)));

    fun prep_source (source, html, graph) =
      let val txt =
        HTML.begin_theory (index_path, session) name parents files_html (Buffer.content source)
        in (Buffer.empty, Buffer.add txt html, graph) end;
  in
    seq (prep_file o #1) files;
    change_theory_info name prep_source
  end);

fun end_theory name = conditional (fn _ => add_html name HTML.end_theory);

fun theorem name thm = conditional (fn _ => in_context add_html (HTML.theorem name thm));
fun section s = conditional (fn _ => in_context add_html (HTML.section s));


end;





(* FIXME

(* head of HTML dependency chart *)

fun mk_charthead name title repeats top_path index_path parent =
  "<html><head><title>" ^ title ^ " of " ^ name ^
  "</title></head>\n<h2>" ^ title ^ " of theory " ^ name ^
  "</h2>\nThe name of every theory is linked to its theory file<br>\n" ^
  "<img src=" ^ htmlify (top_path red_arrow_path) ^
  " alt =\"\\/\"></a> stands for subtheories (child theories)<br>\n\
  \<img src=" ^ htmlify (top_path blue_arrow_path) ^
  " alt =\"/\\\"></a> stands for supertheories (parent theories)\n" ^
  (if not repeats then "" else "<br><tt>...</tt> stands for repeated subtrees") ^
  "<p>\n<a href=" ^ htmlify index_path ^ ">Back</a> to " ^ parent ^ "\n<hr>\n";

(* FIXME "<pre>"  *)


(* theory_file *)

(*convert .thy file to HTML and make chart of its super-theories*)

(* FIXME include ML file (!?!?) *)

    (* path of directory, where corresponding HTML file is stored *)
    val tpath = html_path thy_path;

    (* gif directory *)
    val rel_gif_path = relative_path tpath (gif_path ());

    val rel_index_path = relative_path tpath (!index_path);

    (*Make list of all theories and all theories that own a .thy file*)
    fun list_theories [] theories thy_files = (theories, thy_files)
      | list_theories ((tname, {thy_time, ...}: thy_info) :: ts)
                      theories thy_files =
          list_theories ts (tname :: theories)
            (if is_some thy_time andalso the thy_time <> "" then
               tname :: thy_files
             else thy_files);

    val (theories, thy_files) =
      list_theories (Symtab.dest (!loaded_thys)) [] [];


fun file_name path = "<tt>" ^ Path.pack src_path ^ "</tt>";

fun ml_file src_path = conditional (fn () =>
  (case ThyLoad.check_file src_path of
    None => file_name src_path
  | Some (path, _) =>
      let
        val base_path = Path.base path;
        val html_base_path = html_ext base_path;
        val name = Path.pack base_path;
        val txt = implode (html_escape (explode (File.read path)));
        val html_txt =
          "<html><head><title>" ^ name ^ "</title></head>\n\n<body>\n" ^
          "<h2>File " ^ name ^ "</h2>\n<hr>\n\n<pre>\n" ^ txt ^ "</pre><hr></body></html>";
      in
        File.write (output_path html_base_path) html_text;
        "<a href=" ^ htmlify html_base_path ^ ">" ^ file_name src_path ^ "</a>"
        "file <a href=" ^ "<tt>" ^ Path.pack src_path ^ "</tt>"
        

fun theory_header name parents files =
  FIXME;




fun theory_file name text = conditional (fn () =>
  let
    fun ml2html name abs_path =
      let val is  = TextIO.openIn (tack_on abs_path (name ^ ".ML"));
          val inp = implode (html_escape (explode (TextIO.inputAll is)));
          val _   = TextIO.closeIn is;
          val os  = TextIO.openOut (tack_on (html_path abs_path) (name ^ "_ML.html"));
          val _   = TextIO.output (os,
            "<HTML><HEAD><TITLE>" ^ name ^ ".ML</TITLE></HEAD>\n\n<BODY>\n" ^
            "<H2>" ^ name ^ ".ML</H2>\n<A HREF = \"" ^
            name ^ ".html\">Back</A> to theory " ^ name ^
            "\n<HR>\n\n<PRE>\n" ^ inp ^ "</PRE><HR></BODY></HTML>");
          val _   = TextIO.closeOut os;
     in () end;

    (*Do the conversion*)
    fun gettext thy_file  =
      let
        (*Convert special HTML characters ('&', '>', and '<')*)
        val file =
          let val is  = TextIO.openIn thy_file;
              val inp = TextIO.inputAll is;
          in (TextIO.closeIn is; html_escape (explode inp)) end;



        (*Process line defining theory's ancestors;
          convert valid theory names to links to their HTML file*)
        val (ancestors, body) =
          let
            fun make_links l result =
              let val (pre, letter) = take_prefix (not o Symbol.is_letter) l;

                  val (id, rest) =
                    take_prefix (Symbol.is_quasi_letter orf Symbol.is_digit) letter;

                  val id = implode id;

                  (*Make a HTML link out of a theory name*)
                  fun make_link t =
                    let val path = html_path (path_of t);
                    in "<A HREF = \"" ^
                       tack_on (relative_path tpath path) t ^
                       ".html\">" ^ t ^ "</A>" end;
              in if not (id mem theories) then (result, implode l)
                 else if id mem thy_files then
                   make_links rest (result ^ implode pre ^ make_link id)
                 else make_links rest (result ^ implode pre ^ id)
              end;

            val (pre, rest) = take_prefix (fn c => c <> "=") file';

            val (ancestors, body) =
              if null rest then
                error ("Missing \"=\" in file " ^ tname ^ ".thy.\n\
                       \(Make sure that the last line ends with a linebreak.)")
              else
                make_links rest "";
          in (implode pre ^ ancestors, body) end;
      in "<HTML><HEAD><TITLE>" ^ tname ^ ".thy</TITLE></HEAD>\n\n<BODY>\n" ^
         "<H2>" ^ tname ^ ".thy</H2>\n<A HREF = \"" ^
         tack_on rel_index_path "index.html\
         \\">Back</A> to the index of " ^ (!package) ^
         "\n<HR>\n\n<PRE>\n" ^ comment ^ ancestors ^ body ^
         "</PRE>\n"
      end;

    (** Make chart of super-theories **)

    val _ = mkdir tpath;
    val sup_out = TextIO.openOut (tack_on tpath (tname ^ "_sup.html"));
    val sub_out = TextIO.openOut (tack_on tpath (tname ^ "_sub.html"));

    (*Theories that already have been listed in this chart*)
    val listed = ref [];

    val wanted_theories =
      filter (fn s => s mem thy_files orelse s = "Pure" orelse s = "CPure")
             theories;

    (*Make tree of theory dependencies*)
    fun list_ancestors tname level continued =
      let
        fun mk_entry [] = ()
          | mk_entry (t::ts) =
            let
              val is_pure = t = "Pure" orelse t = "CPure";
              val path = if is_pure then (the (!pure_subchart))
                         else html_path (path_of t);
              val rel_path = relative_path tpath path;
              val repeated = t mem (!listed) andalso
                             not (null (parents_of_name t));

              fun mk_offset [] cur =
                    if level < cur then error "Error in mk_offset"
                    else implode (replicate (level - cur) "    ")
                | mk_offset (l::ls) cur =
                    implode (replicate (l - cur) "    ") ^ "|   " ^
                    mk_offset ls (l+1);
            in TextIO.output (sup_out,
                 " " ^ mk_offset continued 0 ^
                 "\\__" ^ (if is_pure then t else
                             "<A HREF=\"" ^ tack_on rel_path t ^
                             ".html\">" ^ t ^ "</A>") ^
                 (if repeated then "..." else " ") ^
                 "<A HREF = \"" ^ tack_on rel_path t ^
                 "_sub.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                 tack_on rel_gif_path "red_arrow.gif\" ALT = \\/></A>" ^
                 (if is_pure then ""
                  else "<A HREF = \"" ^ tack_on rel_path t ^
                       "_sup.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                       tack_on rel_gif_path "blue_arrow.gif\
                       \\" ALT = /\\></A>") ^
                 "\n");
              if repeated then ()
              else (listed := t :: (!listed);
                    list_ancestors t (level+1) (if null ts then continued
                                                else continued @ [level]);
                    mk_entry ts)
            end;

        val relatives =
          filter (fn s => s mem wanted_theories) (parents_of_name tname);
      in mk_entry relatives end;
  in if is_some (!cur_htmlfile) then
       (TextIO.closeOut (the (!cur_htmlfile));
        warning "Last theory's HTML file has not been closed.")
     else ();
     cur_htmlfile := Some (TextIO.openOut (tack_on tpath (tname ^ ".html")));
     cur_has_title := false;
     if File.exists (tack_on thy_path (tname ^ ".ML"))
       then ml2html tname thy_path else ();
     TextIO.output (the (!cur_htmlfile), gettext (tack_on thy_path tname ^ ".thy"));

     mk_charthead sup_out tname "Ancestors" true rel_gif_path rel_index_path
                  (!package);
     TextIO.output(sup_out,
       "<A HREF=\"" ^ tname ^ ".html\">" ^ tname ^ "</A> \
       \<A HREF = \"" ^ tname ^
       "_sub.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
       tack_on rel_gif_path "red_arrow.gif\" ALT = \\/></A>\n");
     list_ancestors tname 0 [];
     TextIO.output (sup_out, "</PRE><HR></BODY></HTML>");
     TextIO.closeOut sup_out;

     mk_charthead sub_out tname "Children" false rel_gif_path rel_index_path
                  (!package);
     TextIO.output(sub_out,
       "<A HREF=\"" ^ tname ^ ".html\">" ^ tname ^ "</A> \
       \<A HREF = \"" ^ tname ^ "_sup.html\"><IMG SRC = \"" ^
       tack_on rel_gif_path "blue_arrow.gif\" BORDER=0 ALT = \\/></A>\n");
     TextIO.closeOut sub_out
  end;


(*Makes HTML title for list of theorems; as this list may be empty and we
  don't want a title in that case, mk_theorems_title is only invoked when
  something is added to the list*)
fun mk_theorems_title out =
  if not (!cur_has_title) then
    (cur_has_title := true;
     TextIO.output (out, "<HR><H2>Theorems proved in <A HREF = \"" ^
                  (!cur_thyname) ^ "_ML.html\">" ^ (!cur_thyname) ^
                  ".ML</A>:</H2>\n"))
  else ();


exception MK_HTML;

(*Add theory to file listing all loaded theories (for index.html)
  and to the sub-charts of its parents*)
fun mk_html tname abs_path old_parents = if not (!make_html) then () else
  ( let val new_parents = parents_of_name tname \\ old_parents;

        fun robust_seq (proc: 'a -> unit) : 'a list -> unit =
          let fun seqf [] = ()
                | seqf (x :: xs) = (proc x  handle _ => (); seqf xs)
          in seqf end;

        (*Add child to parents' sub-theory charts*)
        fun add_to_parents t =
          let val path = if t = "Pure" orelse t = "CPure" then
                           (the (!pure_subchart))
                         else html_path (path_of t);

              val rel_gif_path = relative_path path (gif_path ());
              val rel_path = relative_path path (html_path abs_path);
              val tpath = tack_on rel_path tname;

              val fname = tack_on path (t ^ "_sub.html");
              val out = if File.exists fname then
                          TextIO.openAppend fname  handle e  =>
                            (warning ("Unable to write to file " ^
                                      fname); raise e)
                        else raise MK_HTML;
          in TextIO.output (out,
               " |\n \\__<A HREF=\"" ^
               tack_on rel_path tname ^ ".html\">" ^ tname ^
               "</A> <A HREF = \"" ^ tpath ^ "_sub.html\">\
               \<IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
               tack_on rel_gif_path "red_arrow.gif\" ALT = \\/></A>\
               \<A HREF = \"" ^ tpath ^ "_sup.html\">\
               \<IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
               tack_on rel_gif_path "blue_arrow.gif\" ALT = /\\></A>\n");
             TextIO.closeOut out
          end;

        val theory_list =
          TextIO.openAppend (tack_on (!index_path) "theory_list.txt")
            handle _ => (make_html := false;
                         warning ("Cannot write to " ^
                                (!index_path) ^ " while making HTML files.\n\
                                \HTML generation has been switched off.\n\
                                \Call init_html() from within a \
                                \writeable directory to reactivate it.");
                         raise MK_HTML)
    in TextIO.output (theory_list, tname ^ " " ^ abs_path ^ "\n");
       TextIO.closeOut theory_list;
       robust_seq add_to_parents new_parents
    end
  ) handle MK_HTML => ();


(*** Misc HTML functions ***)

(*Init HTML generator by setting paths and creating new files*)
fun init_html () =
  let val cwd = OS.FileSys.getDir();
      val _ = mkdir (html_path cwd);

      val theory_list = TextIO.closeOut (TextIO.openOut (tack_on (html_path cwd) "theory_list.txt"));

      val rel_gif_path = relative_path (html_path cwd) (gif_path ());

      (*Make new HTML files for Pure and CPure*)
      fun init_pure_html () =
        let val pure_out = TextIO.openOut (tack_on (html_path cwd) "Pure_sub.html");
            val cpure_out = TextIO.openOut (tack_on (html_path cwd) "CPure_sub.html");
        in mk_charthead pure_out "Pure" "Children" false rel_gif_path ""
                        (!package);
           mk_charthead cpure_out "CPure" "Children" false rel_gif_path ""
                        (!package);
           TextIO.output (pure_out, "Pure\n");
           TextIO.output (cpure_out, "CPure\n");
           TextIO.closeOut pure_out;
           TextIO.closeOut cpure_out;
           pure_subchart := Some (html_path cwd)
        end;

  in make_html := true;
     (*Make sure that base_path contains the physical path and no
       symbolic links*)
     base_path := normalize_path (!base_path);
     original_path := cwd;
     index_path := html_path cwd;
     package :=
        (if subdir_of (cwd, !base_path) then
          relative_path (!base_path) cwd
         else base_name cwd);


     (*copy README files to html directory*)  (* FIXME let usedir do this job !?*)
     handle_error
       (File.copy (tack_on cwd "README.html")) (tack_on (!index_path) "README.html");
     handle_error
       (File.copy (tack_on cwd "README")) (tack_on (!index_path) "README");

     if subdir_of (cwd, !base_path) then ()
     else warning "The current working directory seems to be no \
                  \subdirectory of\nIsabelle's main directory. \
                  \Please ensure that base_path's value is correct.\n";

     writeln ("Setting path for index.html to " ^ quote (!index_path) ^
              "\nGIF path has been set to " ^ quote (gif_path ()));

     if is_none (!pure_subchart) then init_pure_html()
     else ()
  end;


(*Generate index.html*)
fun finish_html () = if not (!make_html) then () else
  let val tlist_path = tack_on (!index_path) "theory_list.txt";
      val theory_list = TextIO.openIn tlist_path;
      val theories = BAD_space_explode "\n" (TextIO.inputAll theory_list);
      val dummy = (TextIO.closeIn theory_list; OS.FileSys.remove tlist_path);

      val rel_gif_path = relative_path (!index_path) (gif_path ());

      (*Make entry for main chart of all theories.*)
      fun main_entry t =
        let
          val (name, path) = take_prefix (not_equal " ") (explode t);

          val tname = implode name
          val tpath = tack_on (relative_path (!index_path) (html_path (implode (tl path))))
                              tname;
        in "<A HREF = \"" ^ tpath ^ "_sub.html\"><IMG SRC = \"" ^
           tack_on rel_gif_path "red_arrow.gif\" BORDER=0 ALT = \\/></A>" ^
           "<A HREF = \"" ^ tpath ^ "_sup.html\"><IMG SRC = \"" ^
           tack_on rel_gif_path "blue_arrow.gif\
           \\" BORDER=0 ALT = /\\></A> <A HREF = \"" ^ tpath ^
           ".html\">" ^ tname ^ "</A><BR>\n"
        end;

      val out = TextIO.openOut (tack_on (!index_path) "index.html");

      (*Find out in which subdirectory of Isabelle's main directory the
        index.html is placed; if original_path is no subdirectory of base_path
        then take the last directory of index_path*)
      val inside_isabelle = subdir_of (!original_path, !base_path);
      val subdir =
        if inside_isabelle then relative_path (html_path (!base_path)) (!index_path)
        else base_name (!index_path);
      val subdirs = BAD_space_explode "/" subdir;

      (*Look for index.html in superdirectories; stop when Isabelle's
        main directory is reached*)
      fun find_super_index [] n = ("", n)
        | find_super_index (p::ps) n =
          let val index_path = "/" ^ space_implode "/" (rev ps);
          in if File.exists (index_path ^ "/index.html") then (index_path, n)
             else if length subdirs - n > 0 then find_super_index ps (n+1)
             else ("", n)
          end;
      val (super_index, level_diff) =
        find_super_index (rev (BAD_space_explode "/" (!index_path))) 1;
      val level = length subdirs - level_diff;

      (*Add link to current directory to 'super' index.html*)
      fun link_directory () =
        let val old_index = TextIO.openIn (super_index ^ "/index.html");
            val content = rev (explode (TextIO.inputAll old_index));
            val dummy = TextIO.closeIn old_index;

            val out = TextIO.openAppend (super_index ^ "/index.html");
            val rel_path = space_implode "/" (drop (level, subdirs));
        in
           TextIO.output (out,
             (if nth_elem (3, content) <> "!" then ""
              else "\n<HR><H3>Subdirectories:</H3>\n") ^
             "<H3><A HREF = \"" ^ rel_path ^ "/index.html\">" ^ rel_path ^
             "</A></H3>\n");
           TextIO.closeOut out
        end;

     (*If original_path is no subdirectory of base_path then the title should
       not contain the string "Isabelle/"*)
     val title = (if inside_isabelle then "Isabelle/" else "") ^ subdir;
     val rel_graph_path = tack_on (relative_path (!index_path) (graph_path (!original_path)))
                                  "small.html"
  in TextIO.output (out,
       "<HTML><HEAD><TITLE>" ^ title ^ "</TITLE></HEAD>\n\
       \<BODY><H2>" ^ title ^ "</H2>\n\
       \The name of every theory is linked to its theory file<BR>\n\
       \<IMG SRC = \"" ^ tack_on rel_gif_path "red_arrow.gif\
       \\" ALT = \\/></A> stands for subtheories (child theories)<BR>\n\
       \<IMG SRC = \"" ^ tack_on rel_gif_path "blue_arrow.gif\
       \\" ALT = /\\></A> stands for supertheories (parent theories)<P>\n\
       \View <A HREF=\"" ^ rel_graph_path ^ "\">graph</A> of theories<P>\n" ^
       (if super_index = "" then "" else
        ("<A HREF = \"" ^ relative_path (!index_path) super_index ^
         "/index.html\">Back</A> to the index of " ^
         (if not inside_isabelle then
            hd (tl (rev (BAD_space_explode "/" (!index_path))))
          else if level = 0 then "Isabelle logics"
          else space_implode "/" (take (level, subdirs))))) ^
       "\n" ^
       (if File.exists (tack_on (!index_path) "README.html") then
          "<BR>View the <A HREF = \"README.html\">README</A> file.\n"
        else if File.exists (tack_on (!index_path) "README") then
          "<BR>View the <A HREF = \"README\">README</A> file.\n"
        else "") ^
       "<HR>" ^ implode (map main_entry theories) ^ "<!-->");
     TextIO.closeOut out;
     if super_index = "" orelse (inside_isabelle andalso level = 0) then ()
        else link_directory ()
  end;


(*Append section heading to HTML file*)
fun section s =
  case !cur_htmlfile of
      Some out => (mk_theorems_title out;
                   TextIO.output (out, "<H3>" ^ s ^ "</H3>\n"))
    | None => ();


(*Add theorem to HTML file*)
fun thm_to_html thm name =
  case !cur_htmlfile of
         Some out =>
           (mk_theorems_title out;
            TextIO.output (out, "<DD><EM>" ^ name ^ "</EM>\n<PRE>" ^
                         (implode o html_escape)
                          (explode
                           (string_of_thm (#1 (freeze_thaw thm)))) ^
                         "</PRE><P>\n")
           )
       | None => ();


(*Close HTML file*)
fun close_html () =
  case !cur_htmlfile of
      Some out => (TextIO.output (out, "<HR></BODY></HTML>\n");
                   TextIO.closeOut out;
                   cur_htmlfile := None)
    | None => () ;

*)

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
