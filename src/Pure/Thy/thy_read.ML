(*  Title:      Pure/Thy/thy_read.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel and Sonia Mahjoub and
                Tobias Nipkow and L C Paulson
    Copyright   1994 TU Muenchen

Functions for reading theory files, and storing and retrieving theories,
theorems and the global simplifier set.
*)

(*Type for theory storage*)
datatype thy_info =
  ThyInfo of {path: string,
              children: string list, parents: string list,
              thy_time: string option, ml_time: string option,
              theory: theory option, thms: thm Symtab.table,
              thy_ss: Simplifier.simpset option,
              simpset: Simplifier.simpset option};
      (*meaning of special values:
        thy_time, ml_time = None     theory file has not been read yet
                          = Some ""  theory was read but has either been marked
                                     as outdated or there is no such file for
                                     this theory (see e.g. 'virtual' theories
                                     like Pure or theories without a ML file)
        theory = None  theory has not been read yet

        parents: While 'children' contains all theories the theory depends
                 on (i.e. also ones quoted in the .thy file),
                 'parents' only contains the theories which were used to form
                 the base of this theory.

        origin of the simpsets:
        thy_ss: snapshot of !Simpset.simpset after .thy file was read
        simpset: snapshot of !Simpset.simpset after .ML file was read
       *)

signature READTHY =
sig
  datatype basetype = Thy  of string
                    | File of string

  val loaded_thys    : thy_info Symtab.table ref
  val loadpath       : string list ref
  val delete_tmpfiles: bool ref

  val use_thy        : string -> unit
  val time_use_thy   : string -> unit
  val use_dir        : string -> unit
  val exit_use_dir   : string -> unit
  val update         : unit -> unit
  val unlink_thy     : string -> unit
  val mk_base        : basetype list -> string -> bool -> theory
  val store_theory   : theory * string -> unit

  val theory_of_sign : Sign.sg -> theory
  val theory_of_thm  : thm -> theory
  val children_of    : string -> string list
  val parents_of     : string -> string list

  val store_thm: string * thm -> thm
  val bind_thm: string * thm -> unit
  val qed: string -> unit
  val qed_thm: thm ref
  val qed_goal: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw: string -> theory->thm list->string->(thm list->tactic list)
                 -> unit
  val get_thm       : theory -> string -> thm
  val thms_of       : theory -> (string * thm) list
  val simpset_of    : string -> Simplifier.simpset
  val print_theory  : theory -> unit

  val base_path     : string ref
  val gif_path      : string ref
  val index_path    : string ref
  val pure_subchart : string option ref
  val make_html     : bool ref
  val init_html     : unit -> unit
  val make_chart    : unit -> unit
end;


functor ReadthyFun(structure ThySyn: THY_SYN and ThmDB: THMDB): READTHY =
struct

open ThmDB Simplifier;

datatype basetype = Thy  of string
                  | File of string;

val loaded_thys =
  ref (Symtab.make [("ProtoPure",
                     ThyInfo {path = "",
                              children = ["Pure", "CPure"], parents = [],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some proto_pure_thy, thms = Symtab.null,
                              thy_ss = None, simpset = None}),
                    ("Pure",
                     ThyInfo {path = "", children = [],
                              parents = ["ProtoPure"],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some pure_thy, thms = Symtab.null,
                              thy_ss = None, simpset = None}),
                    ("CPure",
                     ThyInfo {path = "",
                              children = [], parents = ["ProtoPure"],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some cpure_thy,
                              thms = Symtab.null,
                              thy_ss = None, simpset = None})
                   ]);

val loadpath = ref ["."];              (*default search path for theory files*)

val delete_tmpfiles = ref true;            (*remove temporary files after use*)


(*Set location of graphics for HTML files
  (When this is executed for the first time we are in $ISABELLE/Pure/Thy.
   This path is converted to $ISABELLE/Tools by removing the last two
   directories and appending "Tools". All subsequently made ReadThy
   structures inherit this value.)
*)
val gif_path = ref (tack_on ("/" ^
  space_implode "/" (rev (tl (tl (rev (space_explode "/" (pwd ())))))))
  "Tools");

(*Path of Isabelle's main directory*)
val base_path = ref (
  "/" ^ space_implode "/" (rev (tl (tl (rev (space_explode "/" (pwd ())))))));


(** HTML variables **)

(*Location of .theory-list.txt and index.html (set by init_html)*)
val index_path = ref "";

(*Location of .Pure_sub.html and .CPure_sub.html*)
val pure_subchart = ref (None : string option);

(*Controls whether HTML files should be generated*)
val make_html = ref false;

(*HTML file of theory currently being read
  (Initialized by thyfile2html; used by use_thy and store_thm)*)
val cur_htmlfile = ref None : outstream option ref;

(*Boolean variable which indicates if the title "Theorems proved in foo.ML"
  has already been inserted into the current HTML file*)
val cur_has_title = ref false;

(*Name of theory currently being read*)
val cur_name = ref "";



(*Make name of the output ML file for a theory *)
fun out_name tname = "." ^ tname ^ ".thy.ML";

(*Read a file specified by thy_file containing theory thy *)
fun read_thy tname thy_file =
  let
    val instream  = open_in thy_file;
    val outstream = open_out (out_name tname);
  in
    output (outstream, ThySyn.parse tname (input (instream, 999999)));
    close_out outstream;
    close_in instream
  end;

fun file_exists file =
  let val instream = open_in file in close_in instream; true end
    handle Io _ => false;

(*Get thy_info for a loaded theory *)
fun get_thyinfo tname = Symtab.lookup (!loaded_thys, tname);

(*Check if a theory was completly loaded *)
fun already_loaded thy =
  let val t = get_thyinfo thy
  in if is_none t then false
     else let val ThyInfo {thy_time, ml_time, ...} = the t
          in is_some thy_time andalso is_some ml_time end
  end;

(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML *)
fun thy_unchanged thy thy_file ml_file =
  case get_thyinfo thy of
      Some (ThyInfo {thy_time, ml_time, ...}) =>
       let val tn = is_none thy_time;
           val mn = is_none ml_time
       in if not tn andalso not mn then
            ((file_info thy_file = the thy_time),
             (file_info ml_file = the ml_time))
          else if not tn andalso mn then
            (file_info thy_file = the thy_time, false)
          else
            (false, false)
       end
    | None => (false, false)

(*Get all direct descendants of a theory*)
fun children_of t =
  case get_thyinfo t of Some (ThyInfo {children, ...}) => children
                      | _ => [];

(*Get all direct ancestors of a theory*)
fun parents_of t =
  case get_thyinfo t of Some (ThyInfo {parents, ...}) => parents
                      | _ => [];

(*Get all descendants of a theory list *)
fun get_descendants [] = []
  | get_descendants (t :: ts) =
      let val children = children_of t
      in children union (get_descendants (children union ts)) end;

(*Get theory object for a loaded theory *)
fun theory_of name =
  let val ThyInfo {theory, ...} = the (get_thyinfo name)
  in the theory end;

(*Get path where theory's files are located*)
fun path_of tname =
  let val ThyInfo {path, ...} = the (get_thyinfo tname)
  in path end;

exception FILE_NOT_FOUND;   (*raised by find_file *)

(*Find a file using a list of paths if no absolute or relative path is
  specified.*)
fun find_file "" name =
      let fun find_it (cur :: paths) =
                if file_exists (tack_on cur name) then
                  (if cur = "." then name else tack_on cur name)
                else
                  find_it paths
           | find_it [] = ""
      in find_it (!loadpath) end
  | find_file path name =
      if file_exists (tack_on path name) then tack_on path name
                                         else "";

(*Get absolute pathnames for a new or already loaded theory *)
fun get_filenames path name =
  let fun make_absolute file =
        let fun rm_points [] result = rev result
              | rm_points (".."::ds) result = rm_points ds (tl result)
              | rm_points ("."::ds) result = rm_points ds result
              | rm_points (d::ds) result = rm_points ds (d::result);
        in if file = "" then ""
           else if hd (explode file) = "/" then file
           else "/" ^ space_implode "/"
                     (rm_points (space_explode "/" (tack_on (pwd ()) file)) [])
        end;

      fun new_filename () =
        let val found = find_file path (name ^ ".thy")
                        handle FILE_NOT_FOUND => "";
            val thy_file = make_absolute found;
            val (thy_path, _) = split_filename thy_file;
            val found = find_file path (name ^ ".ML");
            val ml_file = if thy_file = "" then make_absolute found
                          else if file_exists (tack_on thy_path (name ^ ".ML"))
                          then tack_on thy_path (name ^ ".ML")
                          else "";
            val searched_dirs = if path = "" then (!loadpath) else [path]
        in if thy_file = "" andalso ml_file = "" then
             error ("Could not find file \"" ^ name ^ ".thy\" or \""
                    ^ name ^ ".ML\" for theory \"" ^ name ^ "\"\n"
                    ^ "in the following directories: \"" ^
                    (space_implode "\", \"" searched_dirs) ^ "\"")
           else ();
           (thy_file, ml_file)
        end;

      val tinfo = get_thyinfo name;
  in if is_some tinfo andalso path = "" then
       let val ThyInfo {path = abs_path, ...} = the tinfo;
           val (thy_file, ml_file) = if abs_path = "" then new_filename ()
                                     else (find_file abs_path (name ^ ".thy"),
                                           find_file abs_path (name ^ ".ML"))
       in if thy_file = "" andalso ml_file = "" then
            (writeln ("Warning: File \"" ^ (tack_on path name)
                      ^ ".thy\"\ncontaining theory \"" ^ name
                      ^ "\" no longer exists.");
             new_filename ()
            )
          else (thy_file, ml_file)
       end
     else new_filename ()
  end;

(*Remove theory from all child lists in loaded_thys *)
fun unlink_thy tname =
  let fun remove (ThyInfo {path, children, parents, thy_time, ml_time,
                           theory, thms, thy_ss, simpset}) =
        ThyInfo {path = path, children = children \ tname, parents = parents,
                 thy_time = thy_time, ml_time = ml_time, theory = theory, 
                 thms = thms, thy_ss = thy_ss, simpset = simpset}
  in loaded_thys := Symtab.map remove (!loaded_thys) end;

(*Remove a theory from loaded_thys *)
fun remove_thy tname =
  loaded_thys := Symtab.make (filter_out (fn (id, _) => id = tname)
                 (Symtab.dest (!loaded_thys)));

(*Change thy_time and ml_time for an existent item *)
fun set_info tname thy_time ml_time =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
          Some (ThyInfo {path, children, parents, theory, thms,
                         thy_ss, simpset,...}) =>
            ThyInfo {path = path, children = children, parents = parents,
                     thy_time = thy_time, ml_time = ml_time,
                     theory = theory, thms = thms,
                     thy_ss = thy_ss, simpset = simpset}
        | None => error ("set_info: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys)
  end;

(*Mark theory as changed since last read if it has been completly read *)
fun mark_outdated tname =
  let val t = get_thyinfo tname;
  in if is_none t then ()
     else
       let val ThyInfo {thy_time, ml_time, ...} = the t
       in set_info tname (if is_none thy_time then None else Some "")
                         (if is_none ml_time then None else Some "")
       end
  end;

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
  output (file,
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

(*Convert .thy file to HTML and make chart of its super-theories*)
fun thyfile2html tpath tname =
  let
    val gif_path = relative_path tpath (!gif_path);
    val package =
      if (!index_path) = "" then
        error "index_path is empty. Please use 'init_html()' instead of \
              \'make_html := true'"
      else relative_path (!base_path) (!index_path);
    val rel_index_path = relative_path tpath (!index_path);

    (*Make list of all theories and all theories that own a .thy file*)
    fun list_theories [] theories thy_files = (theories, thy_files)
      | list_theories ((tname, ThyInfo {thy_time, ...}) :: ts)
                      theories thy_files =
          list_theories ts (tname :: theories)
            (if is_some thy_time andalso the thy_time <> "" then
               tname :: thy_files
             else thy_files);

    val (theories, thy_files) =
      list_theories (Symtab.dest (!loaded_thys)) [] [];

    (*Do the conversion*)
    fun gettext thy_file  =
      let
        (*Convert special HTML characters ('&', '>', and '<')*)
        val file =
          explode (execute ("sed -e 's/\\&/\\&amp;/g' -e 's/>/\\&gt;/g' \
                            \-e 's/</\\&lt;/g' " ^ thy_file));

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
                    let val path = path_of t;
                    in "<A HREF = \"" ^
                       tack_on (relative_path tpath path) ("." ^ t) ^
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
         \\">Back</A> to the index of " ^ package ^
         "\n<HR>\n\n<PRE>\n" ^ comment ^ ancestors ^ body ^
         "</PRE>\n"
      end;

    (** Make chart of super-theories **)

    val sup_out = open_out (tack_on tpath ("." ^ tname ^ "_sup.html"));
    val sub_out = open_out (tack_on tpath ("." ^ tname ^ "_sub.html"));

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
                         else path_of t;
              val rel_path = relative_path tpath path;
              val repeated = t mem (!listed) andalso not (null (parents_of t));

              fun mk_offset [] cur =
                    if level < cur then error "Error in mk_offset"
                    else implode (replicate (level - cur) "    ")
                | mk_offset (l::ls) cur =
                    implode (replicate (l - cur) "    ") ^ "|   " ^
                    mk_offset ls (l+1);
            in output (sup_out,
                 " " ^ mk_offset continued 0 ^
                 "\\__" ^ (if is_pure then t else
                             "<A HREF=\"" ^ tack_on rel_path ("." ^ t) ^
                             ".html\">" ^ t ^ "</A>") ^
                 (if repeated then "..." else " ") ^
                 "<A HREF = \"" ^ tack_on rel_path ("." ^ t) ^
                 "_sub.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                 tack_on gif_path "red_arrow.gif\" ALT = \\/></A>" ^
                 (if is_pure then ""
                  else "<A HREF = \"" ^ tack_on rel_path ("." ^ t) ^
                       "_sup.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                       tack_on gif_path "blue_arrow.gif\
                       \\" ALT = /\\></A>") ^
                 "\n");
              if repeated then ()
              else (listed := t :: (!listed);
                    list_ancestors t (level+1) (if null ts then continued
                                                else continued @ [level]);
                    mk_entry ts)
            end;

        val relatives =
          filter (fn s => s mem wanted_theories) (parents_of tname);
      in mk_entry relatives end;
  in if is_some (!cur_htmlfile) then
       error "thyfile2html: Last theory's HTML file has not been closed."
     else ();
     cur_htmlfile := Some (open_out (tack_on tpath ("." ^ tname ^ ".html")));
     cur_has_title := false;
     cur_name := tname;
     output (the (!cur_htmlfile), gettext (tack_on tpath tname ^ ".thy"));

     mk_charthead sup_out tname "Ancestors" true gif_path rel_index_path
                  package;
     output(sup_out,
       "<A HREF=\"." ^ tname ^ ".html\">" ^ tname ^ "</A> \
       \<A HREF = \"." ^ tname ^
       "_sub.html\"><IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
       tack_on gif_path "red_arrow.gif\" ALT = \\/></A>\n");
     list_ancestors tname 0 [];
     output (sup_out, "</PRE><HR></BODY></HTML>");
     close_out sup_out;

     mk_charthead sub_out tname "Children" false gif_path rel_index_path
                  package;
     output(sub_out,
       "<A HREF=\"." ^ tname ^ ".html\">" ^ tname ^ "</A> \
       \<A HREF = \"." ^ tname ^ "_sup.html\"><IMG SRC = \"" ^
       tack_on gif_path "blue_arrow.gif\" BORDER=0 ALT = \\/></A>\n");
     close_out sub_out
  end;


(*Read .thy and .ML files that haven't been read yet or have changed since
  they were last read;
  loaded_thys is a thy_info list ref containing all theories that have
  completly been read by this and preceeding use_thy calls.
  If a theory changed since its last use its children are marked as changed *)
fun use_thy name =
  let
    val (path, tname) = split_filename name;
    val (thy_file, ml_file) = get_filenames path tname;
    val (abs_path, _) = if thy_file = "" then split_filename ml_file
                        else split_filename thy_file;
    val (thy_uptodate, ml_uptodate) = thy_unchanged tname thy_file ml_file;
    val old_parents = parents_of tname;

    (*Set absolute path for loaded theory *)
    fun set_path () =
      let val ThyInfo {children, parents, thy_time, ml_time, theory, thms,
                       thy_ss, simpset, ...} =
            the (Symtab.lookup (!loaded_thys, tname));
      in loaded_thys := Symtab.update ((tname,
                          ThyInfo {path = abs_path,
                                   children = children, parents = parents,
                                   thy_time = thy_time, ml_time = ml_time,
                                   theory = theory, thms = thms,
                                   thy_ss = thy_ss, simpset = simpset}),
                          !loaded_thys)
      end;

    (*Mark all direct descendants of a theory as changed *)
    fun mark_children thy =
      let val children = children_of thy;
          val present = filter (is_some o get_thyinfo) children;
          val loaded = filter already_loaded present;
      in if loaded <> [] then
           writeln ("The following children of theory " ^ (quote thy)
                    ^ " are now out-of-date: "
                    ^ (quote (space_implode "\",\"" loaded)))
         else ();
         seq mark_outdated present
      end;

    (*Remove theorems associated with a theory*)
    fun delete_thms () =
      let
        val tinfo = case get_thyinfo tname of
            Some (ThyInfo {path, children, parents, thy_time, ml_time, theory,
                           thy_ss, simpset, ...}) =>
              ThyInfo {path = path, children = children, parents = parents,
                       thy_time = thy_time, ml_time = ml_time,
                       theory = theory, thms = Symtab.null,
                       thy_ss = thy_ss, simpset = simpset}
          | None => ThyInfo {path = "", children = [], parents = [],
                             thy_time = None, ml_time = None,
                             theory = None, thms = Symtab.null,
                             thy_ss = None, simpset = None};

        val ThyInfo {theory, ...} = tinfo;
      in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys);
         case theory of
             Some t => delete_thm_db t
           | None => ()
      end;

    fun save_thy_ss () =
      let val ThyInfo {path, children, parents, thy_time, ml_time,
                       theory, thms, simpset, ...} = the (get_thyinfo tname);
      in loaded_thys := Symtab.update
           ((tname, ThyInfo {path = path,
                             children = children, parents = parents,
                             thy_time = thy_time, ml_time = ml_time,
                             theory = theory, thms = thms,
                             thy_ss = Some (!Simplifier.simpset),
                             simpset = simpset}),
            !loaded_thys)
      end;

    fun save_simpset () =
      let val ThyInfo {path, children, parents, thy_time, ml_time,
                       theory, thms, thy_ss, ...} = the (get_thyinfo tname);
      in loaded_thys := Symtab.update
           ((tname, ThyInfo {path = path,
                             children = children, parents = parents,
                             thy_time = thy_time, ml_time = ml_time,
                             theory = theory, thms = thms,
                             thy_ss = thy_ss,
                             simpset = Some (!Simplifier.simpset)}),
            !loaded_thys)
      end;

   (*Add theory to file listing all loaded theories (for index.html)
     and to the sub-charts of its parents*)
   fun mk_html () =
     let val new_parents = parents_of tname \\ old_parents;

         (*Add child to parents' sub-theory charts*)
         fun add_to_parents t =
           let val path = if t = "Pure" orelse t = "CPure" then
                            (the (!pure_subchart))
                          else path_of t;

               val gif_path = relative_path path (!gif_path);
               val rel_path = relative_path path abs_path;
               val tpath = tack_on rel_path ("." ^ tname);

               val out = open_append (tack_on path ("." ^ t ^ "_sub.html"));
           in output (out,
                " |\n \\__<A HREF=\"" ^
                tack_on rel_path ("." ^ tname) ^ ".html\">" ^ tname ^
                "</A> <A HREF = \"" ^ tpath ^ "_sub.html\">\
                \<IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                tack_on gif_path "red_arrow.gif\" ALT = \\/></A>\
                \<A HREF = \"" ^ tpath ^ "_sup.html\">\
                \<IMG ALIGN=BOTTOM BORDER=0 SRC = \"" ^
                tack_on gif_path "blue_arrow.gif\" ALT = /\\></A>\n");
              close_out out
           end;

         val theory_list =
           open_append (tack_on (!index_path) ".theory_list.txt");
     in output (theory_list, tname ^ " " ^ abs_path ^ "\n");
        close_out theory_list;

        seq add_to_parents new_parents
     end
  in if thy_uptodate andalso ml_uptodate then ()
     else
      (if thy_file = "" then ()
       else if thy_uptodate then
         simpset := let val ThyInfo {thy_ss, ...} = the (get_thyinfo tname);
                    in the thy_ss end
       else
         (writeln ("Reading \"" ^ name ^ ".thy\"");

          delete_thms ();
          read_thy tname thy_file;
          use (out_name tname);
          save_thy_ss ();

          (*Store axioms of theory
            (but only if it's not a copy of an older theory)*)
          let val parents = parents_of tname;
              val this_thy = theory_of tname;
              val axioms =
                if length parents = 1
                   andalso Sign.eq_sg (sign_of (theory_of (hd parents)),
                                       sign_of this_thy) then []
                else axioms_of this_thy;
          in map store_thm_db axioms end;

          if not (!delete_tmpfiles) then ()
          else delete_file (out_name tname);

          if not (!make_html) then ()
          else thyfile2html abs_path tname
         );

       set_info tname (Some (file_info thy_file)) None;
                                       (*mark thy_file as successfully loaded*)

       if ml_file = "" then ()
       else (writeln ("Reading \"" ^ name ^ ".ML\"");
             use ml_file);
       save_simpset ();

       (*Store theory again because it could have been redefined*)
       use_string
         ["val _ = store_theory (" ^ tname ^ ".thy, " ^ quote tname ^ ");"];

       (*Add theory to list of all loaded theories (for index.html)
         and add it to its parents' sub-charts*)
       if !make_html then
         let val path = path_of tname;
         in if path = "" then mk_html ()    (*first time theory has been read*)
            else ()
         end
       else ();

       (*Now set the correct info*)
       set_info tname (Some (file_info thy_file)) (Some (file_info ml_file));
       set_path ();

       (*Mark theories that have to be reloaded*)
       mark_children tname;

       (*Close HTML file*)
       case !cur_htmlfile of
           Some out => (output (out, "<HR></BODY></HTML>\n");
                        close_out out;
                        cur_htmlfile := None)
         | None => ()
      )
  end;

fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");
    use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****"))
   );

(*Load all thy or ML files that have been changed and also
  all theories that depend on them *)
fun update () =
  let (*List theories in the order they have to be loaded *)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level [] = []
                  | next_level (t :: ts) =
                      let val children = children_of t
                      in children union (next_level ts) end;

                val descendants = next_level thys;
            in load_order descendants ((result \\ descendants) @ descendants)
            end;

      fun reload_changed (t :: ts) =
            let fun abspath () = case get_thyinfo t of
                                     Some (ThyInfo {path, ...}) => path
                                   | None => "";

                val (thy_file, ml_file) = get_filenames (abspath ()) t;
                val (thy_uptodate, ml_uptodate) =
                        thy_unchanged t thy_file ml_file;
            in if thy_uptodate andalso ml_uptodate then ()
                                                   else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ();

     (*Remove all theories that are no descendants of ProtoPure.
       If there are still children in the deleted theory's list
       schedule them for reloading *)
     fun collect_garbage no_garbage =
       let fun collect ((tname, ThyInfo {children, ...}) :: ts) =
                 if tname mem no_garbage then collect ts
                 else (writeln ("Theory \"" ^ tname ^
                       "\" is no longer linked with ProtoPure - removing it.");
                       remove_thy tname;
                       seq mark_outdated children)
             | collect [] = ()
       in collect (Symtab.dest (!loaded_thys)) end;
  in collect_garbage ("ProtoPure" :: (load_order ["ProtoPure"] []));
     reload_changed (load_order ["Pure", "CPure"] [])
  end;

(*Merge theories to build a base for a new theory.
  Base members are only loaded if they are missing.*)
fun mk_base bases child mk_draft =
  let (*Show the cycle that would be created by add_child*)
      fun show_cycle base =
        let fun find_it result curr =
              let val tinfo = get_thyinfo curr
              in if base = curr then
                   error ("Cyclic dependency of theories: "
                          ^ child ^ "->" ^ base ^ result)
                 else if is_some tinfo then
                   let val ThyInfo {children, ...} = the tinfo
                   in seq (find_it ("->" ^ curr ^ result)) children
                   end
                 else ()
              end
        in find_it "" child end;

      (*Check if a cycle would be created by add_child*)
      fun find_cycle base =
        if base mem (get_descendants [child]) then show_cycle base
        else ();

      (*Add child to child list of base*)
      fun add_child base =
        let val tinfo =
              case Symtab.lookup (!loaded_thys, base) of
                  Some (ThyInfo {path, children, parents, thy_time, ml_time,
                           theory, thms, thy_ss, simpset}) =>
                    ThyInfo {path = path,
                             children = child ins children, parents = parents,
                             thy_time = thy_time, ml_time = ml_time,
                             theory = theory, thms = thms,
                             thy_ss = thy_ss, simpset = simpset}
                | None => ThyInfo {path = "", children = [child], parents = [],
                                   thy_time = None, ml_time = None,
                                   theory = None, thms = Symtab.null,
                                   thy_ss = None, simpset = None};
        in loaded_thys := Symtab.update ((base, tinfo), !loaded_thys) end;

      (*Load a base theory if not already done
        and no cycle would be created *)
      fun load base =
          let val thy_loaded = already_loaded base
                                       (*test this before child is added *)
          in
            if child = base then
                error ("Cyclic dependency of theories: " ^ child
                       ^ "->" ^ child)
            else
              (find_cycle base;
               add_child base;
               if thy_loaded then ()
               else (writeln ("Autoloading theory " ^ (quote base)
                              ^ " (used by " ^ (quote child) ^ ")");
                     use_thy base)
              )
          end;

      (*Get simpset for a theory*)
      fun get_simpset tname =
        let val ThyInfo {simpset, ...} = the (get_thyinfo tname);
        in simpset end;

      (*Load all needed files and make a list of all real theories *)
      fun load_base (Thy b :: bs) =
           (load b;
            b :: load_base bs)
        | load_base (File b :: bs) =
           (load b;
            load_base bs)                    (*don't add it to mergelist *)
        | load_base [] = [];

      val dummy = unlink_thy child;
      val mergelist = load_base bases;

      val dummy =
        let val tinfo = case Symtab.lookup (!loaded_thys, child) of
              Some (ThyInfo {path, children, thy_time, ml_time, theory, thms,
                             thy_ss, simpset, ...}) =>
                 ThyInfo {path = path,
                          children = children, parents = mergelist,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = theory, thms = thms,
                          thy_ss = thy_ss, simpset = simpset}
             | None => error ("set_parents: theory " ^ child ^ " not found");
        in loaded_thys := Symtab.update ((child, tinfo), !loaded_thys) end;

      val base_thy = (writeln ("Loading theory " ^ (quote child));
                      merge_thy_list mk_draft (map theory_of mergelist));
 in simpset := foldr merge_ss (mapfilter get_simpset mergelist, empty_ss);
    base_thy
 end;

(*Change theory object for an existent item of loaded_thys*)
fun store_theory (thy, tname) =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
               Some (ThyInfo {path, children, parents, thy_time, ml_time, thms,
                              thy_ss, simpset, ...}) =>
                 ThyInfo {path = path, children = children, parents = parents,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = Some thy, thms = thms,
                          thy_ss = thy_ss, simpset = simpset}
             | None => error ("store_theory: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys)
  end;


(** store and retrieve theorems **)

(*Guess to which theory a signature belongs and return it's thy_info*)
fun thyinfo_of_sign sg =
  let
    val ref xname = hd (#stamps (Sign.rep_sg sg));
    val opt_info = get_thyinfo xname;

    fun eq_sg (ThyInfo {theory = None, ...}) = false
      | eq_sg (ThyInfo {theory = Some thy, ...}) = Sign.eq_sg (sg,sign_of thy);

    val show_sg = Pretty.str_of o Sign.pretty_sg;
  in
    if is_some opt_info andalso eq_sg (the opt_info) then
      (xname, the opt_info)
    else
      (case Symtab.find_first (eq_sg o snd) (!loaded_thys) of
        Some name_info => name_info
      | None => error ("Theory " ^ show_sg sg ^ " not stored by loader"))
  end;


(*Try to get the theory object corresponding to a given signature*)
fun theory_of_sign sg =
  (case thyinfo_of_sign sg of
    (_, ThyInfo {theory = Some thy, ...}) => thy
  | _ => sys_error "theory_of_sign");

(*Try to get the theory object corresponding to a given theorem*)
val theory_of_thm = theory_of_sign o #sign o rep_thm;


(* Store theorems *)

(*Store a theorem in the thy_info of its theory,
  and in the theory's HTML file*)
fun store_thm (name, thm) =
  let
    val (thy_name, ThyInfo {path, children, parents, thy_time, ml_time,
                            theory, thms, thy_ss, simpset}) =
      thyinfo_of_sign (#sign (rep_thm thm));

    val (thms', duplicate) = (Symtab.update_new ((name, thm), thms), false)
      handle Symtab.DUPLICATE s => 
        (if eq_thm (the (Symtab.lookup (thms, name)), thm) then 
           (writeln ("Warning: Theory database already contains copy of\
                     \ theorem " ^ quote name);
            (thms, true))
         else error ("Duplicate theorem name " ^ quote s
                     ^ " used in theory database"));

    fun thm_to_html () =
      let fun escape []       = ""
            | escape ("<"::s) = "&lt;" ^ escape s
            | escape (">"::s) = "&gt;" ^ escape s
            | escape ("&"::s) = "&amp;" ^ escape s
            | escape (c::s)   = c ^ escape s;
      in case !cur_htmlfile of
             Some out =>
               (if not (!cur_has_title) then
                  (cur_has_title := true;
                   output (out, "<HR><H2>Theorems proved in <A HREF = \"" ^
                                (!cur_name) ^ ".ML\">" ^ (!cur_name) ^
                                ".ML</A>:</H2>\n"))
                else ();
                output (out, "<EM>" ^ name ^ "</EM>\n<PRE>" ^
                             escape (explode (string_of_thm (freeze thm))) ^
                             "</PRE><P>\n")
               )
           | None => ()
      end;
  in
    loaded_thys := Symtab.update
     ((thy_name, ThyInfo {path = path, children = children, parents = parents,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = theory, thms = thms',
                          thy_ss = thy_ss, simpset = simpset}),
      !loaded_thys);
    thm_to_html ();
    if duplicate then thm else store_thm_db (name, thm)
  end;

(*Store result of proof in loaded_thys and as ML value*)

val qed_thm = ref flexpair_def(*dummy*);

fun bind_thm (name, thm) =
 (qed_thm := standard thm;
  store_thm (name, standard thm);
  use_string ["val " ^ name ^ " = !qed_thm;"]);

fun qed name =
 (qed_thm := result ();
  store_thm (name, !qed_thm);
  use_string ["val " ^ name ^ " = !qed_thm;"]);

fun qed_goal name thy agoal tacsf =
 (qed_thm := prove_goal thy agoal tacsf;
  store_thm (name, !qed_thm);
  use_string ["val " ^ name ^ " = !qed_thm;"]);

fun qed_goalw name thy rths agoal tacsf =
 (qed_thm := prove_goalw thy rths agoal tacsf;
  store_thm (name, !qed_thm);
  use_string ["val " ^ name ^ " = !qed_thm;"]);


(* Retrieve theorems *)

(*Get all theorems belonging to a given theory*)
fun thmtab_of_thy thy =
  let val (_, ThyInfo {thms, ...}) = thyinfo_of_sign (sign_of thy);
  in thms end;

fun thmtab_of_name name =
  let val ThyInfo {thms, ...} = the (get_thyinfo name);
  in thms end;

(*Get a stored theorem specified by theory and name*)
fun get_thm thy name =
  let fun get [] [] searched =
           raise THEORY ("get_thm: no theorem " ^ quote name, [thy])
        | get [] ng searched =
            get (ng \\ searched) [] searched
        | get (t::ts) ng searched =
            (case Symtab.lookup (thmtab_of_name t, name) of
                 Some thm => thm
               | None => get ts (ng union (parents_of t)) (t::searched));

      val (tname, _) = thyinfo_of_sign (sign_of thy);
  in get [tname] [] [] end;

(*Get stored theorems of a theory*)
val thms_of = Symtab.dest o thmtab_of_thy;

(*Get simpset of a theory*)
fun simpset_of tname =
  case get_thyinfo tname of
      Some (ThyInfo {simpset, ...}) =>
        if is_some simpset then the simpset
        else error ("Simpset of theory " ^ tname ^ " has not been stored yet")
    | None => error ("Theory " ^ tname ^ " not stored by loader");

(* print theory *)

fun print_thms thy =
  let
    val thms = thms_of thy;
    fun prt_thm (s, th) = Pretty.block [Pretty.str (s ^ ":"), Pretty.brk 1,
      Pretty.quote (pretty_thm th)];
  in
    Pretty.writeln (Pretty.big_list "stored theorems:" (map prt_thm thms))
  end;

fun print_theory thy = (Drule.print_theory thy; print_thms thy);


(* Misc HTML functions *)

(*Init HTML generator by setting paths and creating new files*)
fun init_html () =
  let val cwd = pwd();

      val theory_list = close_out (open_out ".theory_list.txt");

      val rel_gif_path = relative_path cwd (!gif_path);
      val package = relative_path (!base_path) cwd;

      (*Make new HTML files for Pure and CPure*)
      fun init_pure_html () =
        let val pure_out = open_out ".Pure_sub.html";
            val cpure_out = open_out ".CPure_sub.html";
        in mk_charthead pure_out "Pure" "Children" false rel_gif_path ""
                        package;
           mk_charthead cpure_out "CPure" "Children" false rel_gif_path ""
                        package;
           output (pure_out, "Pure\n");
           output (cpure_out, "CPure\n");
           close_out pure_out;
           close_out cpure_out;
           pure_subchart := Some cwd
        end;
  in make_html := true;
     index_path := cwd;

     writeln ("Setting path for index.html to " ^ quote cwd ^
              "\nGIF path has been set to " ^ quote (!gif_path));

     if is_none (!pure_subchart) then init_pure_html()
     else ()
  end;

(*Generate index.html*)
fun make_chart () = if not (!make_html) then () else
  let val tlist_path = tack_on (!index_path) ".theory_list.txt";
      val theory_list = open_in tlist_path;
      val theories = space_explode "\n" (input (theory_list, 999999));
      val dummy = (close_in theory_list; delete_file tlist_path);

      val gif_path = relative_path (!index_path) (!gif_path);

      (*Make entry for main chart of all theories.*)
      fun main_entry t =
        let
          val (name, path) = take_prefix (not_equal " ") (explode t);

          val tname = implode name
          val tpath = tack_on (relative_path (!index_path) (implode (tl path)))
                              ("." ^ tname);
        in "<A HREF = \"" ^ tpath ^ "_sub.html\"><IMG SRC = \"" ^
           tack_on gif_path "red_arrow.gif\" BORDER=0 ALT = \\/></A>" ^
           "<A HREF = \"" ^ tpath ^ "_sup.html\"><IMG SRC = \"" ^
           tack_on gif_path "blue_arrow.gif\
           \\" BORDER=0 ALT = /\\></A> <A HREF = \"" ^ tpath ^
           ".html\">" ^ tname ^ "</A><BR>\n"
        end;

      val out = open_out (tack_on (!index_path) "index.html");
      val subdir = relative_path (!base_path) (!index_path);
      val subdirs = space_explode "/" subdir;

      (*Look for index.html in superdirectories*)
      fun find_super_index [] _ =
            error "make_chart: Unable to find super index file."
        | find_super_index (p::ps) n =
          let val index_path = "/" ^ space_implode "/" (rev ps);
          in if file_exists (index_path ^ "/index.html") then (index_path, n)
             else find_super_index ps (n+1)
          end;
      val (super_index, level_diff) =
        find_super_index (rev (space_explode "/" (!index_path))) 1;
      val level = length subdirs - level_diff;

      (*Add link to current directory to 'super' index.html*)
      fun link_directory () =
        let val old_index = open_in (super_index ^ "/index.html");
            val content = rev (explode (input (old_index, 999999)));
            val dummy = close_in old_index;

            val out = open_append (super_index ^ "/index.html");
            val rel_path = space_implode "/" (drop (level, subdirs));
        in 
           output (out,
             (if nth_elem (3, content) <> "!" then ""
              else "\n<HR><H3>Subdirectories:</H3>\n") ^
             "<H3><A HREF = \"" ^ rel_path ^ "/index.html\">" ^ rel_path ^
             "</A></H3>\n");
           close_out out
        end;
  in output (out,
       "<HTML><HEAD><TITLE>Isabelle/" ^ subdir ^ "</TITLE></HEAD>\n\
       \<BODY><H2>Isabelle/" ^ subdir ^ "</H2>\n\
       \The name of every theory is linked to its theory file<BR>\n\
       \<IMG SRC = \"" ^ tack_on gif_path "red_arrow.gif\
       \\" ALT = \\/></A> stands for subtheories (child theories)<BR>\n\
       \<IMG SRC = \"" ^ tack_on gif_path "blue_arrow.gif\
       \\" ALT = /\\></A> stands for supertheories (parent theories)\
       \<P>\n<A HREF = \"" ^ relative_path (!index_path) super_index ^ 
       "/index.html\">Back</A> to the index of " ^
       (if level = 0 then "Isabelle logics"
        else space_implode "/" (take (level, subdirs))) ^
       "\n" ^
       (if file_exists (tack_on (!index_path) "README.html") then
          "<BR>View the <A HREF = \"README.html\">ReadMe</A> file.\n"
        else if file_exists (tack_on (!index_path) "README") then
          "<BR>View the <A HREF = \"README\">ReadMe</A> file.\n"
        else "") ^
       "<HR>" ^ implode (map main_entry theories) ^ "<!-->");
     close_out out;
     if level = 0 then () else link_directory ()
  end;

(*CD to a directory and load its ROOT.ML file*)
fun use_dir dirname =
  (cd dirname;
   if !make_html then init_html() else ();
   use "ROOT.ML";
   make_chart());

fun exit_use_dir dirname =
  (cd dirname;
   if !make_html then init_html() else ();
   exit_use "ROOT.ML";
   make_chart());

end;
