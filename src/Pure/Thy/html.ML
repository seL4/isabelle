(*  Title:      Pure/Thy/html.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

HTML presentation elements.
*)

signature HTML =
sig
  val reset_symbols: unit -> unit
  val init_symbols: (string * int) list -> unit
  val present_span: Keyword.keywords -> Command_Span.span -> Output.output
  type text = string
  val plain: string -> text
  val name: string -> text
  val keyword: string -> text
  val command: string -> text
  val href_name: string -> text -> text
  val href_path: Url.T -> text -> text
  val href_opt_path: Url.T option -> text -> text
  val para: text -> text
  val begin_document: string -> text
  val end_document: text
  val begin_session_index: string -> Url.T -> (Url.T * string) list -> text
  val theory_entry: Url.T * string -> text
  val theory: string -> (Url.T option * string) list -> text -> text
end;

structure HTML: HTML =
struct


(* common markup *)

fun span class = ("<span class=" ^ quote (XML.text class) ^ ">", "</span>");

val hidden = span Markup.hiddenN |-> enclose;


(* symbol output *)

local

val symbols =
  Synchronized.var "HTML.symbols" (NONE: (int * string) Symtab.table option);

fun output_sym s =
  if Symbol.is_raw s then (1, Symbol.decode_raw s)
  else
    (case Synchronized.value symbols of
      SOME tab =>
        (case Symtab.lookup tab s of
          SOME x => x
        | NONE => (size s, XML.text s))
    | NONE => raise Fail "Missing HTML.init_symbols: cannot output symbols");

fun output_markup (bg, en) s1 s2 =
  let val (n, txt) = output_sym s2
  in (n, hidden s1 ^ enclose bg en txt) end;

val output_sub = output_markup ("<sub>", "</sub>");
val output_sup = output_markup ("<sup>", "</sup>");
val output_bold = output_markup (span "bold");

fun output_syms [] (result, width) = (implode (rev result), width)
  | output_syms (s1 :: rest) (result, width) =
      let
        val (s2, ss) = (case rest of [] => ("", []) | s2 :: ss => (s2, ss));
        val ((w, s), r) =
          if s1 = "\\<^sub>" then (output_sub "&#8681;" s2, ss)
          else if s1 = "\\<^sup>" then (output_sup "&#8679;" s2, ss)
          else if s1 = "\\<^bold>" then (output_bold "&#10073;" s2, ss)
          else (output_sym s1, rest);
      in output_syms r (s :: result, width + w) end;

in

fun output_width str = output_syms (Symbol.explode str) ([], 0);
val output = #1 o output_width;

fun reset_symbols () = Synchronized.change symbols (K NONE);

fun init_symbols codes =
  let
    val mapping =
      map (fn (s, c) => (s, (Symbol.length [s], "&#" ^ Markup.print_int c ^ ";"))) codes @
       [("", (0, "")),
        ("'", (1, "&#39;")),
        ("\\<^bsub>", (0, hidden "&#8664;" ^ "<sub>")),
        ("\\<^esub>", (0, hidden "&#8665;" ^ "</sub>")),
        ("\\<^bsup>", (0, hidden "&#8663;" ^ "<sup>")),
        ("\\<^esup>", (0, hidden "&#8662;" ^ "</sup>"))];
  in Synchronized.change symbols (K (SOME (fold Symtab.update mapping Symtab.empty))) end;

end;


(* presentation *)

fun present_token keywords tok =
  fold_rev (uncurry enclose o span o #1)
    (Token.markups keywords tok) (output (Token.unparse tok));

fun present_span keywords =
  implode o map (present_token keywords) o Command_Span.content;



(** HTML markup **)

type text = string;


(* atoms *)

val plain = output;
val name = enclose "<span class=\"name\">" "</span>" o output;
val keyword = enclose "<span class=\"keyword\">" "</span>" o output;
val command = enclose "<span class=\"command\">" "</span>" o output;


(* misc *)

fun href_name s txt = "<a href=" ^ quote s ^ ">" ^ txt ^ "</a>";
fun href_path path txt = href_name (Url.implode path) txt;

fun href_opt_path NONE txt = txt
  | href_opt_path (SOME p) txt = href_path p txt;

fun para txt = "\n<p>" ^ txt ^ "</p>\n";


(* document *)

fun begin_document title =
  "<?xml version=\"1.0\" encoding=\"utf-8\" ?>\n\
  \<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \
  \\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">\n\
  \<html xmlns=\"http://www.w3.org/1999/xhtml\">\n\
  \<head>\n\
  \<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\"/>\n\
  \<title>" ^ plain (title ^ " (" ^ Distribution.version ^ ")") ^ "</title>\n\
  \<link media=\"all\" rel=\"stylesheet\" type=\"text/css\" href=\"isabelle.css\"/>\n\
  \</head>\n\
  \\n\
  \<body>\n\
  \<div class=\"head\">\
  \<h1>" ^ plain title ^ "</h1>\n";

val end_document = "\n</div>\n</body>\n</html>\n";


(* session index *)

fun begin_session_index session graph docs =
  begin_document ("Session " ^ plain session) ^
  para ("View " ^ href_path graph "theory dependencies" ^
    implode (map (fn (p, name) => "<br/>\nView " ^ href_path p name) docs)) ^
  "\n</div>\n<div class=\"theories\">\n<h2>Theories</h2>\n<ul>\n";

fun theory_entry (p, s) = "<li>" ^ href_path p (plain s) ^ "</li>\n";


(* theory *)

fun theory A Bs txt =
  begin_document ("Theory " ^ A) ^ "\n" ^
  command "theory" ^ " " ^ name A ^ "<br/>\n" ^
  keyword "imports" ^ " " ^ space_implode " " (map (uncurry href_opt_path o apsnd name) Bs) ^
  "<br/>\n" ^
  enclose "\n</div>\n<div class=\"source\">\n<pre class=\"source\">" "</pre>\n" txt ^
  end_document;

end;
