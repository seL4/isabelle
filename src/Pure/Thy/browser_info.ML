(*  Title:      Pure/Thy/thy_browser_info.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Carsten Clasohm
    Copyright   1994, 1997 TU Muenchen

The first design of the text-based html browser is due to Mateja Jamnik.

Functions for generating theory browsing information
(i.e. *.html and *.graph - files).
*)


(** filenames and paths **)             (* FIXME FIXME FIXME eliminate!!! *)

(*BAD_space_explode "." "h.e..l.lo"; gives ["h", "e", "l", "lo"]*)
fun BAD_space_explode sep s =
  let fun divide [] "" = []
        | divide [] part = [part]
        | divide (c::s) part =
            if c = sep then
              (if part = "" then divide s "" else part :: divide s "")
            else divide s (part ^ c)
  in divide (explode s) "" end;

(*Convert UNIX filename of the form "path/file" to "path/" and "file";
  if filename contains no slash, then it returns "" and "file"*)
val split_filename =
  (pairself implode) o take_suffix (not_equal "/") o explode;

val base_name = #2 o split_filename;

(*Merge splitted filename (path and file);
  if path does not end with one a slash is appended*)
fun tack_on "" name = name
  | tack_on path name =
      if last_elem (explode path) = "/" then path ^ name
      else path ^ "/" ^ name;

(*Remove the extension of a filename, i.e. the part after the last '.'*)
val remove_ext = implode o #1 o take_suffix (not_equal ".") o explode;

(*Make relative path to reach an absolute location from a different one*)
fun relative_path cur_path dest_path =
  let (*Remove common beginning of both paths and make relative path*)
      fun mk_relative [] [] = []
        | mk_relative [] ds = ds
        | mk_relative cs [] = map (fn _ => "..") cs
        | mk_relative (c::cs) (d::ds) =
            if c = d then mk_relative cs ds
            else ".." :: map (fn _ => "..") cs @ (d::ds);
  in if cur_path = "" orelse hd (explode cur_path) <> "/" orelse
        dest_path = "" orelse hd (explode dest_path) <> "/" then
       error "Relative or empty path passed to relative_path"
     else ();
     space_implode "/" (mk_relative (BAD_space_explode "/" cur_path)
                                    (BAD_space_explode "/" dest_path))
  end;

(*Determine if absolute path1 is a subdirectory of absolute path2*)
fun subdir_of (path1, path2) =
  if hd (explode path1) <> "/" orelse hd (explode path2) <> "/" then
    error "Relative or empty path passed to subdir_of"
  else (BAD_space_explode "/" path2) prefix (BAD_space_explode "/" path1);

fun absolute_path cwd file =
  let fun rm_points [] result = rev result
        | rm_points (".."::ds) result = rm_points ds (tl result)
        | rm_points ("."::ds) result = rm_points ds result
        | rm_points (d::ds) result = rm_points ds (d::result);
  in if file = "" then ""
     else if hd (explode file) = "/" then file
     else "/" ^ space_implode "/"
                  (rm_points (BAD_space_explode "/" (tack_on cwd file)) [])
  end;



signature BROWSER_INFO =
sig
  val output_dir       : string ref
  val home_path        : string ref

  val make_graph       : bool ref
  val init_graph       : string -> unit
  val mk_graph         : string -> string -> unit
  val cur_thyname      : string ref
  val make_html        : bool ref
  val mk_html          : string -> string -> string list -> unit
  val thyfile2html     : string -> string -> unit
  val init_html        : unit -> unit
  val finish_html      : unit -> unit
  val section          : string -> unit
  val thm_to_html      : thm -> string -> unit
  val close_html       : unit -> unit
end;


structure BrowserInfo : BROWSER_INFO =
struct

open ThyInfo;


(*directory where to put html and graph files*)
val output_dir = ref "";


(*path of user home directory*)
val home_path = ref "";


(*normalize a path
  FIXME: move to library?*)
fun normalize_path p =
   let val curr_dir = pwd ();
       val _ = cd p;
       val norm_path = pwd ();
       val _ = cd curr_dir
   in norm_path end;


(*create directory
  FIXME: move to library?*)
fun mkdir path = (execute ("mkdir -p " ^ path); ());


(*Path of Isabelle's main (source) directory
  FIXME: this value should be provided by isatool!*)
val base_path = ref (
  "/" ^ space_implode "/" (rev (tl (tl (rev (BAD_space_explode "/" (OS.FileSys.getDir ())))))));



(******************** HTML generation functions *************************)

(*Set location of graphics for HTML files*)
fun gif_path () = tack_on (normalize_path (!output_dir)) "gif";


(*Name of theory currently being read*)
val cur_thyname = ref "";


(*Name of current logic*)
val package = ref "";


(* Return path of directory where to store html / graph data
   corresponding to theory with given path *)
local
  fun make_path q p =
    let val outp_dir = normalize_path (!output_dir);
        val base = if q = "" then outp_dir else tack_on outp_dir q;
        val rpath = if subdir_of (p, !base_path) then relative_path (!base_path) p
                    else relative_path (normalize_path (!home_path)) p;
    in tack_on base rpath end
in
  val html_path = make_path "";
  val graph_path = make_path "graph/data"
end;


(*Location of theory-list.txt and index.html (set by init_html)*)
val index_path = ref "";


(*Original path of ROOT.ML*)
val original_path = ref "";


(*Location of Pure_sub.html and CPure_sub.html*)
val pure_subchart = ref (None : string option);


(*Controls whether HTML files should be generated*)
val make_html = ref false;


(*HTML file of theory currently being read
  (Initialized by thyfile2html; used by use_thy and store_thm)*)
val cur_htmlfile = ref None : TextIO.outstream option ref;


(*Boolean variable which indicates if the title "Theorems proved in foo.ML"
  has already been inserted into the current HTML file*)
val cur_has_title = ref false;


(*Make head of HTML dependency charts
  Parameters are:
    file: HTML file
    tname: theory name
    suffix: suffix of complementary chart
            (sup if this head is for a sub-chart, sub if it is for a sup-chart;
             empty for Pure and CPure sub-charts)
    gif_path: relative path to directory containing GIFs
    index_path: relative path to directory containing main theory chart
*)
fun mk_charthead file tname title repeats gif_path index_path package =
  TextIO.output (file,
   "<HTML><HEAD><TITLE>" ^ title ^ " of " ^ tname ^
   "</TITLE></HEAD>\n<H2>" ^ title ^ " of theory " ^ tname ^
   "</H2>\nThe name of every theory is linked to its theory file<BR>\n" ^
   "<IMG SRC = \"" ^ tack_on gif_path "red_arrow.gif\
   \\" ALT = \\/></A> stands for subtheories (child theories)<BR>\n\
   \<IMG SRC = \"" ^ tack_on gif_path "blue_arrow.gif\
   \\" ALT = /\\></A> stands for supertheories (parent theories)\n" ^
   (if not repeats then "" else
      "<BR><TT>...</TT> stands for repeated subtrees") ^
   "<P>\n<A HREF = \"" ^ tack_on index_path "index.html\
   \\">Back</A> to the index of " ^ package ^ "\n<HR>\n<PRE>");


(*Convert special HTML characters ('&', '>', and '<')*)
fun escape []       = []
  | escape ("<"::s) = "&lt;" :: escape s
  | escape (">"::s) = "&gt;" :: escape s
  | escape ("&"::s) = "&amp;" :: escape s
  | escape (c::s)   = c :: escape s;


(*Convert .thy file to HTML and make chart of its super-theories*)
fun thyfile2html tname thy_path = if not (!make_html) then () else
  let
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

    (*convert ML file to html *)
    fun ml2html name abs_path =
      let val is  = TextIO.openIn (tack_on abs_path (name ^ ".ML"));
          val inp = implode (escape (explode (TextIO.inputAll is)));
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
          in (TextIO.closeIn is; escape (explode inp)) end;


        (*Isolate first (possibly nested) comment;
          skip all leading whitespaces*)
        val (comment, file') =
          let fun first_comment ("*" :: ")" :: cs) co 1 = (co ^ "*)", cs)
                | first_comment ("*" :: ")" :: cs) co d =
                    first_comment cs (co ^ "*)") (d-1)
                | first_comment ("(" :: "*" :: cs) co d =
                    first_comment cs (co ^ "(*") (d+1)
                | first_comment (" "  :: cs) "" 0 = first_comment cs "" 0
                | first_comment ("\n" :: cs) "" 0 = first_comment cs "" 0
                | first_comment ("\t" :: cs) "" 0 = first_comment cs "" 0
                | first_comment cs           "" 0 = ("", cs)
                | first_comment (c :: cs) co d =
                    first_comment cs (co ^ implode [c]) d
                | first_comment [] co _ =
                    error ("Unexpected end of file " ^ tname ^ ".thy.");
          in first_comment file "" 0 end;

        (*Process line defining theory's ancestors;
          convert valid theory names to links to their HTML file*)
        val (ancestors, body) =
          let
            fun make_links l result =
              let val (pre, letter) = take_prefix (not o is_letter) l;

                  val (id, rest) =
                    take_prefix (is_quasi_letter orf is_digit) letter;

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
                         (implode o escape)
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


end;
