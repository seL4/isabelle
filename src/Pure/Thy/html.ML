(*  Title:      Pure/Thy/HTML.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HTML presentation primitives.
*)

signature HTML =
sig
  val output: string -> string
  val output_width: string -> string * real
  type text (* = string *)
  val plain: string -> text
  val name: string -> text
  val keyword: string -> text
  val file_name: string -> text
  val file_path: Url.T -> text
  val href_name: string -> text -> text
  val href_path: Url.T -> text -> text
  val href_opt_name: string option -> text -> text
  val href_opt_path: Url.T option -> text -> text
  val para: text -> text
  val preform: text -> text
  val verbatim: string -> text
  val begin_index: Url.T * string -> Url.T * string -> Url.T option
    -> Url.T option -> Url.T -> text
  val end_index: text
  val applet_pages: string -> Url.T -> Url.T * string -> bool -> (string * string) list
  val theory_entry: Url.T * string -> text
  val session_entries: (Url.T * string) list -> text
  val verbatim_source: string list -> text
  val begin_theory: Url.T * string -> string -> (Url.T option * string) list ->
    (Url.T option * Url.T * bool option) list -> text -> text
  val end_theory: text
  val ml_file: Url.T -> string -> text
  val result: string -> string -> thm -> text
  val results: string -> string -> thm list -> text
  val theorem: string -> thm -> text
  val theorems: string -> thm list -> text
  val section: string -> text
  val subsection: string -> text
  val subsubsection: string -> text
  val setup: (theory -> theory) list
end;

structure HTML: HTML =
struct


(** HTML print modes **)

(* mode *)

val htmlN = "HTML";
fun html_mode f x = setmp print_mode [htmlN] f x;


(* symbol output *)

local
  val escape = fn "<" => "&lt;" | ">" => "&gt;" | "&" => "&amp;" | c => c;

  val output_sym =
    fn "\\<not>" => (1.0, "&not;")
     | "\\<hyphen>" => (1.0, "&shy;")
     | "\\<cdot>" => (1.0, "&middot;")
     | "\\<times>" => (1.0, "&times;")
     | "\\<copyright>" => (1.0, "&copy;")
     | "\\<mu>" => (1.0, "&micro;")
     | s => (real (size s), implode (map escape (explode s)));

  fun add_sym (width, (w: real, s)) = (width + w, s);
in

fun output_width str =
  if not (exists_string (equal "<" orf equal ">" orf equal "&") str) then (str, real (size str))
  else
    let val (width, syms) = foldl_map add_sym (0.0, map output_sym (Symbol.explode str))
    in (implode syms, width) end;

val output = #1 o output_width;
val output_symbols = map (#2 o output_sym);

end;


val _ = Symbol.add_mode htmlN output_width;


(* token translations *)

fun color col =
  apfst (enclose ("<font color=" ^ quote col ^ ">") "</font>") o output_width;

val html_trans =
 [("class", color "red"),
  ("tfree", color "purple"),
  ("tvar",  color "purple"),
  ("free",  color "blue"),
  ("bound", color "green"),
  ("var",   color "blue"),
  ("xnum",  color "yellow"),
  ("xstr",  color "brown")];



(** HTML markup **)

type text = string;


(* atoms *)

val plain = output;
fun name s = "<i>" ^ output s ^ "</i>";
fun keyword s = "<b>" ^ output s ^ "</b>";
fun file_name s = "<tt>" ^ output s ^ "</tt>";
val file_path = file_name o Url.pack;


(* misc *)

fun href_name s txt = "<a href=" ^ quote s ^ ">" ^ txt ^ "</a>";
fun href_path path txt = href_name (Url.pack path) txt;

fun href_opt_name None txt = txt
  | href_opt_name (Some s) txt = href_name s txt;

fun href_opt_path None txt = txt
  | href_opt_path (Some p) txt = href_path p txt;

fun para txt = "\n<p>\n" ^ txt ^ "\n</p>\n";
fun preform txt = "<pre>" ^ txt ^ "</pre>";
val verbatim = preform o output;


(* document *)

fun begin_document title =
  "<html>\n\
  \<head>\n\
  \<title>" ^ plain (title ^ " (" ^ version ^ ")") ^ "</title>\n\
  \</head>\n\
  \\n\
  \<body>\n\
  \<h1>" ^ plain title ^ "</h1>\n"

val end_document = "\n</body>\n</html>\n";

fun gen_link how (path, name) = para (href_path path how ^ " to index of " ^ plain name);
val up_link = gen_link "Up";
val back_link = gen_link "Back";


(* session index *)

fun begin_index up (index_path, session) opt_readme opt_doc graph =
  begin_document ("Index of " ^ session) ^ up_link up ^
  para ("View " ^ href_path graph "theory dependencies" ^
    (case opt_readme of None => "" | Some p => "<br>\nView " ^ href_path p "README") ^
    (case opt_doc of None => "" | Some p => "<br>\nView " ^ href_path p "document")) ^
  "\n<hr>\n\n<h2>Theories</h2>\n<ul>\n";

val end_index = end_document;

fun choice chs s = space_implode " " (map (fn (s', lnk) =>
  enclose "[" "]" (if s = s' then keyword s' else href_name lnk s')) chs);

fun applet_pages session codebase back alt_graph =
  let
    val choices = [("none", "small",  "small.html"),
                   ("none", "medium", "medium.html"),
                   ("none", "large",  "large.html"),
                   ("all",  "small",  "small_all.html"),
                   ("all",  "medium", "medium_all.html"),
                   ("all",  "large",  "large_all.html")];

    val sizes = [("small",  ("500", "400")),
                 ("medium", ("650", "520")),
                 ("large",  ("800", "640"))];

    fun applet_page (gtype, size, name) =
      let
        val (width, height) = the (assoc (sizes, size));
        val subsessions =
          if alt_graph then
            "View subsessions: " ^ choice (map (fn (x, _, z) => (x, z))
              (filter (fn (_, y, _) => y = size) choices)) gtype ^ "<br>\n"
          else "";
        val browser_size = "Set browser size: " ^
          choice (map (fn (_, y, z) => (y, z)) (filter (fn (x, _, _) => x = gtype) choices)) size;
      in
        (name, begin_document ("Theory dependencies of " ^ session) ^
          back_link back ^
          para (subsessions ^ browser_size) ^
          "\n<hr>\n<applet code=\"GraphBrowser/GraphBrowser.class\" \
          \codebase=\"" ^ Url.pack codebase ^ "\" width=" ^ width ^ " height=" ^ height ^ ">\n\
          \<param name=\"graphfile\" value=\"" ^
          (if gtype = "all" then "all_sessions.graph" else "session.graph") ^ "\">\n\
          \</applet>\n<hr>" ^ end_document)
      end;
  in map applet_page (take (if alt_graph then 6 else 3, choices)) end;


fun entry (p, s) = "<li>" ^ href_path p (plain s) ^ "\n";

val theory_entry = entry;

fun session_entries [] = "</ul>"
  | session_entries es =
      "</ul>\n<hr>\n\n<h2>Sessions</h2>\n<ul>\n" ^ implode (map entry es) ^ "</ul>";


(* theory *)

fun verbatim_source ss = "\n<hr>\n<pre>" ^ implode (output_symbols ss)  ^ "</pre>\n<hr>\n";


local
  fun encl None = enclose "[" "]"
    | encl (Some false) = enclose "(" ")"
    | encl (Some true) = I;

  fun file (opt_ref, path, loadit) = href_opt_path opt_ref (encl loadit (file_path path));
  val files = space_implode " " o map file;
  val parents = space_implode " + " o map (uncurry href_opt_path o apsnd name);

  fun theory up A =
    begin_document ("Theory " ^ A) ^ "\n" ^ up_link up ^
    keyword "theory" ^ " " ^ name A ^ " = ";
in

fun begin_theory up A Bs [] body = theory up A ^ parents Bs ^ ":\n" ^ body
  | begin_theory up A Bs Ps body = theory up A ^ parents Bs ^ "<br>" ^ keyword "files" ^
      " " ^ files Ps ^ ":" ^ "\n" ^ body;
end;

val end_theory = end_document;


(* ML file *)

fun ml_file path str =
  begin_document ("File " ^ Url.pack path) ^
  "\n<hr>\n" ^ verbatim str ^ "\n<hr>\n" ^ end_document;


(* theorems *)

local

val string_of_thm =
  Pretty.setmp_margin 80 Pretty.string_of o
    Display.pretty_thm_no_quote o #1 o Drule.freeze_thaw;

fun thm th = preform (prefix_lines "  " (html_mode string_of_thm th));

fun thm_name "" = ""
  | thm_name a = " " ^ name (a ^ ":");

in

fun result k a th = para (keyword k ^ thm_name a ^ "\n" ^ thm th);
fun results k a ths = para (cat_lines ((keyword k ^ thm_name a) :: map thm ths));

val theorem = result "theorem";
val theorems = results "theorems";

end;


(* sections *)

fun section heading = "\n\n<h2>" ^ plain heading ^ "</h2>\n";
fun subsection heading = "\n\n<h3>" ^ plain heading ^ "</h3>\n";
fun subsubsection heading = "\n\n<h4>" ^ plain heading ^ "</h4>\n";



(** theory setup **)

val setup =
 [Theory.add_mode_tokentrfuns htmlN html_trans];


end;
