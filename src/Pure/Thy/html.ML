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
  val file_path: Path.T -> text
  val para: text -> text
  val href_name: string -> text -> text
  val href_path: Path.T -> text -> text
  val preform: text -> text
  val verbatim: string -> text
  val begin_document: string -> text
  val end_document: text
  val begin_index: Path.T * string -> Path.T * string -> Path.T option -> text
  val end_index: text
  val theory_entry: Path.T * string -> text
  val session_entries: (Path.T * string) list -> text
  val source: (string, 'a) Source.source -> text
  val begin_theory: Path.T * string -> string -> string list ->
    (Path.T option * Path.T * bool) list -> text -> text
  val end_theory: text
  val ml_file: Path.T -> string -> text
  val theorem: string -> thm -> text
  val section: string -> text
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
val file_path = file_name o Path.pack;


(* misc *)

fun para txt = "\n<p>\n" ^ txt ^ "\n</p>\n";
fun href_name s txt = "<a href=" ^ quote s ^ ">" ^ txt ^ "</a>";
fun href_path path txt = href_name (Path.pack path) txt;
fun preform txt = "<pre>" ^ txt ^ "</pre>";
val verbatim = preform o output;


(* document *)

fun begin_document title =
  let val txt = plain title in
    "<html>\n\
    \<head>\n\
    \<title>" ^ txt ^ "</title>\n\
    \</head>\n\
    \\n\
    \<body>\n\
    \<h1>" ^ txt ^ "</h1>\n"
  end;

val end_document =
  "</body>\n\
  \</html>\n";

fun back_link (back_path, back_name) =
  para (href_path back_path "Back" ^ " to index of " ^ plain back_name);


(* session index *)

fun begin_index back (index_path, session) opt_readme =
  begin_document ("Index of " ^ session) ^ back_link back ^
  (case opt_readme of None => "" | Some p => href_path p "README" ^ " file") ^
  "\n<hr>\n\n<h2>Theories</h2>\n";

val end_index = end_document;

fun entry (p, s) = href_path p (plain s) ^ "<br>\n";
val theory_entry = entry;

fun session_entries [] = ""
  | session_entries es = "\n<hr>\n\n<h2>Sessions</h2>\n" ^ cat_lines (map entry es);


(* theory *)

fun output_source src = implode (output_symbols (Source.exhaust (Symbol.source false src)));
fun source src = "\n<hr>\n<pre>" ^ output_source src ^ "</pre>\n<hr>\n";


local
  fun file (opt_ref, path, loadit) =
    (case opt_ref of None => I | Some p => href_path p)
      ((if not loadit then enclose "(" ")" else I) (file_path path));

  fun suffix_last _ [] = []
    | suffix_last s lst = let val (xs, x) = split_last lst in xs @ [x ^ s] end;

  val plus_names = space_implode " + " o map name;

  fun theory back A =
    begin_document ("Theory " ^ A) ^ "\n" ^ back_link back ^
    keyword "theory" ^ " " ^ name A ^ " = ";
in

fun begin_theory back A Bs [] body = theory back A ^ plus_names (suffix_last ":" Bs) ^ "\n" ^ body
  | begin_theory back A Bs Ps body =
      theory back A ^ plus_names Bs ^
      "<br>" ^ keyword "files" ^ " " ^ space_implode " + " (map file Ps) ^ ":" ^ "\n" ^ body;
end;

val end_theory = end_document;


(* ML file *)

fun ml_file path str =
  begin_document ("File " ^ Path.pack path) ^
  "\n<hr>\n" ^ verbatim str ^ "\n<hr>\n" ^ end_document;


(* theorem *)

(* FIXME improve freeze_thaw (?) *)
val string_of_thm =
  Pretty.setmp_margin 80 Pretty.string_of o
    Display.pretty_thm_no_quote o #1 o Drule.freeze_thaw;

fun thm th = preform (prefix_lines "  " (html_mode string_of_thm th));
fun theorem a th = para (keyword "theorem" ^ " " ^ name (a ^ ":") ^ "\n" ^ thm th);


(* section *)

fun section heading = "\n\n<h2>" ^ plain heading ^ "</h2>\n";



(** theory setup **)

val setup =
 [Theory.add_mode_tokentrfuns htmlN html_trans];


end;
