(*  Title:      Pure/Thy/HTML.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

HTML presentation elements.
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
  val applet_pages: string -> Url.T * string -> (string * string) list
  val theory_entry: Url.T * string -> text
  val session_entries: (Url.T * string) list -> text
  val verbatim_source: Symbol.symbol list -> text
  val begin_theory: Url.T * string -> string -> (Url.T option * string) list ->
    (Url.T option * Url.T * bool option) list -> text -> text
  val end_theory: text
  val ml_file: Url.T -> string -> text
  val results: string -> (string * thm list) list -> text
  val chapter: string -> text
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
fun html_mode f x = setmp print_mode (htmlN :: ! print_mode) f x;


(* symbol output *)

local
  val escape = fn "<" => "&lt;" | ">" => "&gt;" | "&" => "&amp;" | c => c;

  val output_sym =
    fn "\\<spacespace>" => (2.0, "&nbsp;&nbsp;")
     | "\\<exclamdown>" => (1.0, "&iexcl;")
     | "\\<cent>" => (1.0, "&cent;")
     | "\\<pounds>" => (1.0, "&pound;")
     | "\\<currency>" => (1.0, "&curren;")
     | "\\<yen>" => (1.0, "&yen;")
     | "\\<bar>" => (1.0, "&brvbar;")
     | "\\<section>" => (1.0, "&sect;")
     | "\\<dieresis>" => (1.0, "&uml;")
     | "\\<copyright>" => (1.0, "&copy;")
     | "\\<ordfeminine>" => (1.0, "&ordf;")
     | "\\<guillemotleft>" => (1.0, "&laquo;")
     | "\\<not>" => (1.0, "&not;")
     | "\\<hyphen>" => (1.0, "&shy;")
     | "\\<registered>" => (1.0, "&reg;")
     | "\\<inverse>" => (1.0, "&macr;")
     | "\\<degree>" => (1.0, "&deg;")
     | "\\<plusminus>" => (1.0, "&plusmn;")
     | "\\<twosuperior>" => (1.0, "&sup2;")
     | "\\<threesuperior>" => (1.0, "&sup3;")
     | "\\<acute>" => (1.0, "&acute;")
     | "\\<paragraph>" => (1.0, "&para;")
     | "\\<cdot>" => (1.0, "&middot;")
     | "\\<cedilla>" => (1.0, "&cedil;")
     | "\\<onesuperior>" => (1.0, "&sup1;")
     | "\\<ordmasculine>" => (1.0, "&ordm;")
     | "\\<guillemotright>" => (1.0, "&raquo;")
     | "\\<onequarter>" => (1.0, "&frac14;")
     | "\\<onehalf>" => (1.0, "&frac12;")
     | "\\<threequarters>" => (1.0, "&frac34;")
     | "\\<questiondown>" => (1.0, "&iquest;")
     | "\\<times>" => (1.0, "&times;")
     | "\\<div>" => (1.0, "&divide;")
     | "\\<circ>" => (1.0, "&circ;")
     | "\\<Alpha>" => (1.0, "&Alpha;")
     | "\\<Beta>" => (1.0, "&Beta;")
     | "\\<Gamma>" => (1.0, "&Gamma;")
     | "\\<Delta>" => (1.0, "&Delta;")
     | "\\<Epsilon>" => (1.0, "&Epsilon;")
     | "\\<Zeta>" => (1.0, "&Zeta;")
     | "\\<Eta>" => (1.0, "&Eta;")
     | "\\<Theta>" => (1.0, "&Theta;")
     | "\\<Iota>" => (1.0, "&Iota;")
     | "\\<Kappa>" => (1.0, "&Kappa;")
     | "\\<Lambda>" => (1.0, "&Lambda;")
     | "\\<Mu>" => (1.0, "&Mu;")
     | "\\<Nu>" => (1.0, "&Nu;")
     | "\\<Xi>" => (1.0, "&Xi;")
     | "\\<Omicron>" => (1.0, "&Omicron;")
     | "\\<Pi>" => (1.0, "&Pi;")
     | "\\<Rho>" => (1.0, "&Rho;")
     | "\\<Sigma>" => (1.0, "&Sigma;")
     | "\\<Tau>" => (1.0, "&Tau;")
     | "\\<Upsilon>" => (1.0, "&Upsilon;")
     | "\\<Phi>" => (1.0, "&Phi;")
     | "\\<Chi>" => (1.0, "&Chi;")
     | "\\<Psi>" => (1.0, "&Psi;")
     | "\\<Omega>" => (1.0, "&Omega;")
     | "\\<alpha>" => (1.0, "&alpha;")
     | "\\<beta>" => (1.0, "&beta;")
     | "\\<gamma>" => (1.0, "&gamma;")
     | "\\<delta>" => (1.0, "&delta;")
     | "\\<epsilon>" => (1.0, "&epsilon;")
     | "\\<zeta>" => (1.0, "&zeta;")
     | "\\<eta>" => (1.0, "&eta;")
     | "\\<theta>" => (1.0, "&thetasym;")
     | "\\<iota>" => (1.0, "&iota;")
     | "\\<kappa>" => (1.0, "&kappa;")
     | "\\<lambda>" => (1.0, "&lambda;")
     | "\\<mu>" => (1.0, "&mu;")
     | "\\<nu>" => (1.0, "&nu;")
     | "\\<xi>" => (1.0, "&xi;")
     | "\\<omicron>" => (1.0, "&omicron;")
     | "\\<pi>" => (1.0, "&pi;")
     | "\\<rho>" => (1.0, "&rho;")
     | "\\<sigma>" => (1.0, "&sigma;")
     | "\\<tau>" => (1.0, "&tau;")
     | "\\<upsilon>" => (1.0, "&upsilon;")
     | "\\<phi>" => (1.0, "&phi;")
     | "\\<chi>" => (1.0, "&chi;")
     | "\\<psi>" => (1.0, "&psi;")
     | "\\<omega>" => (1.0, "&omega;")
     | "\\<buller>" => (1.0, "&bull;")
     | "\\<dots>" => (1.0, "&hellip;")
     | "\\<Re>" => (1.0, "&real;")
     | "\\<Im>" => (1.0, "&image;")
     | "\\<wp>" => (1.0, "&weierp;")
     | "\\<forall>" => (1.0, "&forall;")
     | "\\<partial>" => (1.0, "&part;")
     | "\\<exists>" => (1.0, "&exist;")
     | "\\<emptyset>" => (1.0, "&empty;")
     | "\\<nabla>" => (1.0, "&nabla;")
     | "\\<in>" => (1.0, "&isin;")
     | "\\<notin>" => (1.0, "&notin;")
     | "\\<Prod>" => (1.0, "&prod;")
     | "\\<Sum>" => (1.0, "&sum;")
     | "\\<star>" => (1.0, "&lowast;")
     | "\\<propto>" => (1.0, "&prop;")
     | "\\<infinity>" => (1.0, "&infin;")
     | "\\<angle>" => (1.0, "&ang;")
     | "\\<and>" => (1.0, "&and;")
     | "\\<or>" => (1.0, "&or;")
     | "\\<inter>" => (1.0, "&cap;")
     | "\\<union>" => (1.0, "&cup;")
     | "\\<sim>" => (1.0, "&sim;")
     | "\\<cong>" => (1.0, "&cong;")
     | "\\<approx>" => (1.0, "&asymp;")
     | "\\<noteq>" => (1.0, "&ne;")
     | "\\<equiv>" => (1.0, "&equiv;")
     | "\\<le>" => (1.0, "&le;")
     | "\\<ge>" => (1.0, "&ge;")
     | "\\<subset>" => (1.0, "&sub;")
     | "\\<supset>" => (1.0, "&sup;")
     | "\\<subseteq>" => (1.0, "&sube;")
     | "\\<supseteq>" => (1.0, "&supe;")
     | "\\<oplus>" => (1.0, "&oplus;")
     | "\\<otimes>" => (1.0, "&otimes;")
     | "\\<bottom>" => (1.0, "&perp;")
     | "\\<lceil>" => (1.0, "&lceil;")
     | "\\<rceil>" => (1.0, "&rceil;")
     | "\\<lfloor>" => (1.0, "&lfloor;")
     | "\\<rfloor>" => (1.0, "&rfloor;")
     | "\\<langle>" => (1.0, "&lang;")
     | "\\<rangle>" => (1.0, "&rang;")
     | "\\<lozenge>" => (1.0, "&loz;")
     | "\\<spadesuit>" => (1.0, "&spades;")
     | "\\<clubsuit>" => (1.0, "&clubs;")
     | "\\<heartsuit>" => (1.0, "&hearts;")
     | "\\<diamondsuit>" => (1.0, "&diams;")
     | "\\<lbrakk>" => (2.0, "[|")
     | "\\<rbrakk>" => (2.0, "|]")
     | "\\<Longrightarrow>" => (3.0, "==&gt;")
     | "\\<Rightarrow>" => (2.0, "=&gt;")
     | "\\<And>" => (2.0, "!!")
     | "\\<Colon>" => (2.0, "::")
     | "\\<lparr>" => (2.0, "(|")
     | "\\<rparr>" => (2.0, "|)")
     | "\\<longleftrightarrow>" => (3.0, "&lt;-&gt;")
     | "\\<longrightarrow>" => (3.0, "--&gt;")
     | "\\<rightarrow>" => (2.0, "-&gt;")
     | "\\<^bsub>" => (0.0, "<sub>")
     | "\\<^esub>" => (0.0, "</sub>")
     | "\\<^bsup>" => (0.0, "<sup>")
     | "\\<^esup>" => (0.0, "</sup>")
     | "\\<^sub>" => (0.0, "\\<^sub>")
     | "\\<^sup>" => (0.0, "\\<^sup>")
     | "\\<^isub>" => (0.0, "\\<^isub>")
     | "\\<^isup>" => (0.0, "\\<^isup>")
     | s => (real (size s), implode (map escape (explode s)));

  fun add_sym (width, (w: real, s)) = (width + w, s);

  fun script (0, "\\<^sub>") = (1, "<sub>")
    | script (0, "\\<^isub>") = (1, "<sub>")
    | script (1, x) = (0, x ^ "</sub>")
    | script (0, "\\<^sup>") = (2, "<sup>")
    | script (0, "\\<^isup>") = (2, "<sup>")
    | script (2, x) = (0, x ^ "</sup>")
    | script (s, x) = (s, x);

  fun scripts ss = #2 (foldl_map script (0, ss));
in

fun output_width str =
  if not (exists_string (equal "<" orf equal ">" orf equal "&") str)
  then (str, real (size str))
  else
    let val (width, syms) = foldl_map add_sym (0.0, map output_sym (Symbol.explode str))
    in (implode (scripts syms), width) end;

val output = #1 o output_width;
val output_symbols = scripts o map (#2 o output_sym);

end;


val _ = Symbol.add_mode htmlN (output_width, Symbol.default_indent);


(* token translations *)

fun style stl =
  apfst (enclose ("<span class=" ^ Library.quote stl ^ ">") "</span>") o output_width;

val html_trans =
 [("class", style "tclass"),
  ("tfree", style "tfree"),
  ("tvar",  style "tvar"),
  ("free",  style "free"),
  ("bound", style "bound"),
  ("var",   style "var"),
  ("xstr",  style "xstr")];



(** HTML markup **)

type text = string;


(* atoms *)

val plain = output;
fun name s = "<span class=\"name\">" ^ output s ^ "</span>";
fun keyword s = "<span class=\"keyword\">" ^ output s ^ "</span>";
fun file_name s = "<span class=\"filename\">" ^ output s ^ "</span>";
val file_path = file_name o Url.pack;


(* misc *)

fun href_name s txt = "<a href=" ^ Library.quote s ^ ">" ^ txt ^ "</a>";
fun href_path path txt = href_name (Url.pack path) txt;

fun href_opt_name None txt = txt
  | href_opt_name (Some s) txt = href_name s txt;

fun href_opt_path None txt = txt
  | href_opt_path (Some p) txt = href_path p txt;

fun para txt = "\n<p>" ^ txt ^ "</p>\n";
fun preform txt = "<pre>" ^ txt ^ "</pre>";
val verbatim = preform o output;


(* document *)

fun begin_document title =
  "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">\n\
  \\n\
  \<html>\n\
  \<head>\n\
  \<meta http-equiv=\"Content-Type\" content=\"text/html; charset=iso-8859-1\">\n\
  \<title>" ^ plain (title ^ " (" ^ version ^ ")") ^ "</title>\n\
  \<link rel=\"stylesheet\" type=\"text/css\" href=\"isabelle.css\">\n\
  \</head>\n\
  \\n\
  \<body>\n\
  \<div class=\"head\">\
  \<h1>" ^ plain title ^ "</h1>\n"

val end_document = "\n</div>\n</body>\n</html>\n";

fun gen_link how (path, name) = para (href_path path how ^ " to index of " ^ plain name);
val up_link = gen_link "Up";
val back_link = gen_link "Back";


(* session index *)

fun begin_index up (index_path, session) opt_readme opt_doc graph =
  begin_document ("Index of " ^ session) ^ up_link up ^
  para ("View " ^ href_path graph "theory dependencies" ^
    (case opt_readme of None => "" | Some p => "<br>\nView " ^ href_path p "README") ^
    (case opt_doc of None => "" | Some p => "<br>\nView " ^ href_path p "document")) ^
  "\n</div>\n<hr>\n<div class=\"theories\">\n<h2>Theories</h2>\n<ul>\n";

val end_index = end_document;

fun choice chs s = space_implode " " (map (fn (s', lnk) =>
  enclose "[" "]" (if s = s' then keyword s' else href_name lnk s')) chs);

fun applet_pages session back =
  let
    val sizes =
     [("small", "small.html", ("500", "400")),
      ("medium", "medium.html", ("650", "520")),
      ("large", "large.html", ("800", "640"))];

    fun applet_page (size, name, (width, height)) =
      let
        val browser_size = "Set browser size: " ^
          choice (map (fn (y, z, _) => (y, z)) sizes) size;
      in
        (name, begin_document ("Theory dependencies of " ^ session) ^
          back_link back ^
          para browser_size ^
          "\n</div>\n<hr>\n<div class=\"graphbrowser\">\n<applet code=\"GraphBrowser/GraphBrowser.class\" \
          \archive=\"GraphBrowser.jar\" \
          \width=" ^ width ^ " height=" ^ height ^ ">\n\
          \<param name=\"graphfile\" value=\"" ^ "session.graph" ^ "\">\n\
          \</applet>\n<hr>" ^ end_document)
      end;
  in map applet_page sizes end;


fun entry (p, s) = "<li>" ^ href_path p (plain s) ^ "\n";

val theory_entry = entry;

fun session_entries [] = "</ul>"
  | session_entries es =
      "</ul>\n</div>\n<hr>\n<div class=\"sessions\">\n<h2>Sessions</h2>\n<ul>\n" ^ implode (map entry es) ^ "</ul>";


(* theory *)

fun verbatim_source ss =
  "\n</div>\n<hr>\n<div class=\"source\">\n<pre>" ^
  implode (output_symbols ss)  ^
  "</pre>\n</div>\n<hr>\n<div class=\"theorems\">\n";


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
  | begin_theory up A Bs Ps body = theory up A ^ parents Bs ^ "<br>\n" ^ keyword "files" ^
      " " ^ files Ps ^ ":" ^ "\n" ^ body;
end;

val end_theory = end_document;


(* ML file *)

fun ml_file path str =
  begin_document ("File " ^ Url.pack path) ^
  "\n</div>\n<hr><div class=\"mlsource\">\n" ^
  verbatim str ^
  "\n</div>\n<hr>\n<div class=\"mlfooter\">\n" ^
  end_document;


(* theorems *)

local

val string_of_thm =
  Pretty.setmp_margin 80 Pretty.string_of o
    Display.pretty_thm_no_quote o #1 o Drule.freeze_thaw;

fun thm th = preform (prefix_lines "  " (html_mode string_of_thm th));

fun thm_name "" = ""
  | thm_name a = " " ^ name (a ^ ":");

in

fun result k (a, ths) = para (cat_lines ((keyword k ^ thm_name a) :: map thm ths));

fun results _ [] = ""
  | results k (res :: ress) = cat_lines (result k res :: map (result "and") ress);

end;


(* sections *)

fun chapter heading = "\n\n<h1>" ^ plain heading ^ "</h1>\n";
fun section heading = "\n\n<h2>" ^ plain heading ^ "</h2>\n";
fun subsection heading = "\n\n<h3>" ^ plain heading ^ "</h3>\n";
fun subsubsection heading = "\n\n<h4>" ^ plain heading ^ "</h4>\n";


(** theory setup **)

val setup =
 [Theory.add_mode_tokentrfuns htmlN html_trans];


end;
