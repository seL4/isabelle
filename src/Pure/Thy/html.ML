(*  Title:      Pure/Thy/HTML.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HTML markup elements.
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
  val insert_here: text
  val source: (string, 'a) Source.source -> text
  val begin_theory: Path.T * string -> string -> string list -> ((Path.T * Path.T) * bool) list
    -> text -> text
  val end_theory: text
  val ml_file: Path.T -> string -> text
  val conclude_theory: text
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

val escape = fn "<" => "&lt;" | ">" => "&gt;" | "&" => "&amp;" | c => c;

val output_chars = implode o map escape;

fun output s =
  if not (exists_string (equal "<" orf equal ">" orf equal "&") s) then s
  else implode (map escape (explode s));        (*sic!*)

fun output_width s = (output s, real (size s));

val _ = Symbol.add_mode htmlN output_width;


(* token translations *)

fun tagit bg en = apfst (enclose bg en) o output_width;
fun color col = tagit ("<font color=" ^ quote col ^ ">") "</font>";

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

val insert_here = "<!--insert--here-->";


(* theory *)

fun source src =
  "\n<hr>\n<pre>" ^ output_chars (Source.exhaust src) ^ "</pre>\n<hr>\n";


local
  fun file ((p, p'), loadit) =
    href_path p' ((if not loadit then enclose "(" ")" else I) (file_path p));

  fun suffix_last _ [] = []
    | suffix_last s lst = let val (xs, x) = split_last lst in xs @ [x ^ s] end;

  val plus_names = space_implode " + " o map name;

  fun theory (back_path, back_name) A =
    begin_document ("Theory " ^ A) ^ "\n" ^
    href_path back_path "Back" ^ " to the index of " ^ plain back_name ^ "\n<p>\n" ^
    keyword "theory" ^ " " ^ name A ^ " = ";
in

fun begin_theory back A Bs [] body = theory back A ^ plus_names (suffix_last ":" Bs) ^ "\n" ^ body
  | begin_theory back A Bs Ps body =
      theory back A ^ plus_names Bs ^
      "<br>" ^ keyword "files" ^ " " ^ space_implode " + " (map file Ps) ^ ":" ^ "\n" ^ body;
end;

val end_theory = "";
val conclude_theory = end_document;


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
