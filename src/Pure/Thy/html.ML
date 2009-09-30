(*  Title:      Pure/Thy/html.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

HTML presentation elements.
*)

signature HTML =
sig
  val html_mode: ('a -> 'b) -> 'a -> 'b
  type text = string
  val plain: string -> text
  val name: string -> text
  val keyword: string -> text
  val command: string -> text
  val file_name: string -> text
  val file_path: Url.T -> text
  val href_name: string -> text -> text
  val href_path: Url.T -> text -> text
  val href_opt_path: Url.T option -> text -> text
  val para: text -> text
  val preform: text -> text
  val verbatim: string -> text
  val with_charset: string -> ('a -> 'b) -> 'a -> 'b
  val begin_document: string -> text
  val end_document: text
  val begin_index: Url.T * string -> Url.T * string -> (Url.T * string) list -> Url.T -> text
  val applet_pages: string -> Url.T * string -> (string * string) list
  val theory_entry: Url.T * string -> text
  val session_entries: (Url.T * string) list -> text
  val theory_source: text -> text
  val begin_theory: Url.T * string -> string -> (Url.T option * string) list ->
    (Url.T * Url.T * bool) list -> text -> text
  val ml_file: Url.T -> string -> text
end;

structure HTML: HTML =
struct


(** HTML print modes **)

(* mode *)

val htmlN = "HTML";
fun html_mode f x = PrintMode.with_modes [htmlN] f x;


(* symbol output *)

local
  val html_syms = Symtab.make
   [("\\<spacespace>", (2, "&nbsp;&nbsp;")),
    ("\\<exclamdown>", (1, "&iexcl;")),
    ("\\<cent>", (1, "&cent;")),
    ("\\<pounds>", (1, "&pound;")),
    ("\\<currency>", (1, "&curren;")),
    ("\\<yen>", (1, "&yen;")),
    ("\\<bar>", (1, "&brvbar;")),
    ("\\<section>", (1, "&sect;")),
    ("\\<dieresis>", (1, "&uml;")),
    ("\\<copyright>", (1, "&copy;")),
    ("\\<ordfeminine>", (1, "&ordf;")),
    ("\\<guillemotleft>", (1, "&laquo;")),
    ("\\<not>", (1, "&not;")),
    ("\\<hyphen>", (1, "&shy;")),
    ("\\<registered>", (1, "&reg;")),
    ("\\<inverse>", (1, "&macr;")),
    ("\\<degree>", (1, "&deg;")),
    ("\\<plusminus>", (1, "&plusmn;")),
    ("\\<twosuperior>", (1, "&sup2;")),
    ("\\<threesuperior>", (1, "&sup3;")),
    ("\\<acute>", (1, "&acute;")),
    ("\\<paragraph>", (1, "&para;")),
    ("\\<cdot>", (1, "&middot;")),
    ("\\<cedilla>", (1, "&cedil;")),
    ("\\<onesuperior>", (1, "&sup1;")),
    ("\\<ordmasculine>", (1, "&ordm;")),
    ("\\<guillemotright>", (1, "&raquo;")),
    ("\\<onequarter>", (1, "&frac14;")),
    ("\\<onehalf>", (1, "&frac12;")),
    ("\\<threequarters>", (1, "&frac34;")),
    ("\\<questiondown>", (1, "&iquest;")),
    ("\\<times>", (1, "&times;")),
    ("\\<div>", (1, "&divide;")),
    ("\\<circ>", (1, "o")),
    ("\\<Alpha>", (1, "&Alpha;")),
    ("\\<Beta>", (1, "&Beta;")),
    ("\\<Gamma>", (1, "&Gamma;")),
    ("\\<Delta>", (1, "&Delta;")),
    ("\\<Epsilon>", (1, "&Epsilon;")),
    ("\\<Zeta>", (1, "&Zeta;")),
    ("\\<Eta>", (1, "&Eta;")),
    ("\\<Theta>", (1, "&Theta;")),
    ("\\<Iota>", (1, "&Iota;")),
    ("\\<Kappa>", (1, "&Kappa;")),
    ("\\<Lambda>", (1, "&Lambda;")),
    ("\\<Mu>", (1, "&Mu;")),
    ("\\<Nu>", (1, "&Nu;")),
    ("\\<Xi>", (1, "&Xi;")),
    ("\\<Omicron>", (1, "&Omicron;")),
    ("\\<Pi>", (1, "&Pi;")),
    ("\\<Rho>", (1, "&Rho;")),
    ("\\<Sigma>", (1, "&Sigma;")),
    ("\\<Tau>", (1, "&Tau;")),
    ("\\<Upsilon>", (1, "&Upsilon;")),
    ("\\<Phi>", (1, "&Phi;")),
    ("\\<Chi>", (1, "&Chi;")),
    ("\\<Psi>", (1, "&Psi;")),
    ("\\<Omega>", (1, "&Omega;")),
    ("\\<alpha>", (1, "&alpha;")),
    ("\\<beta>", (1, "&beta;")),
    ("\\<gamma>", (1, "&gamma;")),
    ("\\<delta>", (1, "&delta;")),
    ("\\<epsilon>", (1, "&epsilon;")),
    ("\\<zeta>", (1, "&zeta;")),
    ("\\<eta>", (1, "&eta;")),
    ("\\<theta>", (1, "&thetasym;")),
    ("\\<iota>", (1, "&iota;")),
    ("\\<kappa>", (1, "&kappa;")),
    ("\\<lambda>", (1, "&lambda;")),
    ("\\<mu>", (1, "&mu;")),
    ("\\<nu>", (1, "&nu;")),
    ("\\<xi>", (1, "&xi;")),
    ("\\<omicron>", (1, "&omicron;")),
    ("\\<pi>", (1, "&pi;")),
    ("\\<rho>", (1, "&rho;")),
    ("\\<sigma>", (1, "&sigma;")),
    ("\\<tau>", (1, "&tau;")),
    ("\\<upsilon>", (1, "&upsilon;")),
    ("\\<phi>", (1, "&phi;")),
    ("\\<chi>", (1, "&chi;")),
    ("\\<psi>", (1, "&psi;")),
    ("\\<omega>", (1, "&omega;")),
    ("\\<bullet>", (1, "&bull;")),
    ("\\<dots>", (1, "&hellip;")),
    ("\\<Re>", (1, "&real;")),
    ("\\<Im>", (1, "&image;")),
    ("\\<wp>", (1, "&weierp;")),
    ("\\<forall>", (1, "&forall;")),
    ("\\<partial>", (1, "&part;")),
    ("\\<exists>", (1, "&exist;")),
    ("\\<emptyset>", (1, "&empty;")),
    ("\\<nabla>", (1, "&nabla;")),
    ("\\<in>", (1, "&isin;")),
    ("\\<notin>", (1, "&notin;")),
    ("\\<Prod>", (1, "&prod;")),
    ("\\<Sum>", (1, "&sum;")),
    ("\\<star>", (1, "&lowast;")),
    ("\\<propto>", (1, "&prop;")),
    ("\\<infinity>", (1, "&infin;")),
    ("\\<angle>", (1, "&ang;")),
    ("\\<and>", (1, "&and;")),
    ("\\<or>", (1, "&or;")),
    ("\\<inter>", (1, "&cap;")),
    ("\\<union>", (1, "&cup;")),
    ("\\<sim>", (1, "&sim;")),
    ("\\<cong>", (1, "&cong;")),
    ("\\<approx>", (1, "&asymp;")),
    ("\\<noteq>", (1, "&ne;")),
    ("\\<equiv>", (1, "&equiv;")),
    ("\\<le>", (1, "&le;")),
    ("\\<ge>", (1, "&ge;")),
    ("\\<subset>", (1, "&sub;")),
    ("\\<supset>", (1, "&sup;")),
    ("\\<subseteq>", (1, "&sube;")),
    ("\\<supseteq>", (1, "&supe;")),
    ("\\<oplus>", (1, "&oplus;")),
    ("\\<otimes>", (1, "&otimes;")),
    ("\\<bottom>", (1, "&perp;")),
    ("\\<lceil>", (1, "&lceil;")),
    ("\\<rceil>", (1, "&rceil;")),
    ("\\<lfloor>", (1, "&lfloor;")),
    ("\\<rfloor>", (1, "&rfloor;")),
    ("\\<langle>", (1, "&lang;")),
    ("\\<rangle>", (1, "&rang;")),
    ("\\<lozenge>", (1, "&loz;")),
    ("\\<spadesuit>", (1, "&spades;")),
    ("\\<clubsuit>", (1, "&clubs;")),
    ("\\<heartsuit>", (1, "&hearts;")),
    ("\\<diamondsuit>", (1, "&diams;")),
    ("\\<lbrakk>", (2, "[|")),
    ("\\<rbrakk>", (2, "|]")),
    ("\\<Longrightarrow>", (3, "==&gt;")),
    ("\\<Rightarrow>", (2, "=&gt;")),
    ("\\<And>", (2, "!!")),
    ("\\<Colon>", (2, "::")),
    ("\\<lparr>", (2, "(|")),
    ("\\<rparr>", (2, "|)),")),
    ("\\<longleftrightarrow>", (3, "&lt;-&gt;")),
    ("\\<longrightarrow>", (3, "--&gt;")),
    ("\\<rightarrow>", (2, "-&gt;")),
    ("\\<^bsub>", (0, "<sub>")),
    ("\\<^esub>", (0, "</sub>")),
    ("\\<^bsup>", (0, "<sup>")),
    ("\\<^esup>", (0, "</sup>"))];

  fun output_sym s =
    if Symbol.is_raw s then (1, Symbol.decode_raw s)
    else
      (case Symtab.lookup html_syms s of SOME x => x
      | NONE => (size s, XML.text s));

  fun output_sub s = apsnd (enclose "<sub>" "</sub>") (output_sym s);
  fun output_sup s = apsnd (enclose "<sup>" "</sup>") (output_sym s);
  fun output_loc s = apsnd (enclose "<span class=\"loc\">" "</span>") (output_sym s);

  fun output_syms ("\\<^sub>" :: s :: ss) = output_sub s :: output_syms ss
    | output_syms ("\\<^isub>" :: s :: ss) = output_sub s :: output_syms ss
    | output_syms ("\\<^sup>" :: s :: ss) = output_sup s :: output_syms ss
    | output_syms ("\\<^isup>" :: s :: ss) = output_sup s :: output_syms ss
    | output_syms ("\\<^loc>" :: s :: ss) = output_loc s :: output_syms ss
    | output_syms (s :: ss) = output_sym s :: output_syms ss
    | output_syms [] = [];
in

fun output_width str =
  if not (exists_string (fn s => s = "\\" orelse s = "<" orelse s = ">" orelse s = "&") str)
  then Output.default_output str
  else
    let val (syms, width) = fold_map (fn (w, s) => fn width => (s, w + width))
      (output_syms (Symbol.explode str)) 0
    in (implode syms, width) end;

val output = #1 o output_width;

val _ = Output.add_mode htmlN output_width Symbol.encode_raw;

end;


(* common markup *)

fun span s = ("<span class=" ^ quote (XML.text s) ^ ">", "</span>");

val _ = Markup.add_mode htmlN (fn (name, _) => span name);



(** HTML markup **)

type text = string;


(* atoms *)

val plain = output;
val name = enclose "<span class=\"name\">" "</span>" o output;
val keyword = enclose "<span class=\"keyword\">" "</span>" o output;
val command = enclose "<span class=\"command\">" "</span>" o output;
val file_name = enclose "<span class=\"filename\">" "</span>" o output;
val file_path = file_name o Url.implode;


(* misc *)

fun href_name s txt = "<a href=" ^ quote s ^ ">" ^ txt ^ "</a>";
fun href_path path txt = href_name (Url.implode path) txt;

fun href_opt_path NONE txt = txt
  | href_opt_path (SOME p) txt = href_path p txt;

fun para txt = "\n<p>" ^ txt ^ "</p>\n";
fun preform txt = "<pre>" ^ txt ^ "</pre>";
val verbatim = preform o output;


(* document *)

val charset = Unsynchronized.ref "ISO-8859-1";
fun with_charset s = setmp_noncritical charset s;   (* FIXME *)

fun begin_document title =
  let val cs = ! charset in
    "<?xml version=\"1.0\" encoding=\"" ^ cs ^ "\" ?>\n\
    \<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \
    \\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">\n\
    \<html xmlns=\"http://www.w3.org/1999/xhtml\">\n\
    \<head>\n\
    \<meta http-equiv=\"Content-Type\" content=\"text/html; charset=" ^ cs ^ "\"/>\n\
    \<title>" ^ plain (title ^ " (" ^ Distribution.version ^ ")") ^ "</title>\n\
    \<link media=\"all\" rel=\"stylesheet\" type=\"text/css\" href=\"isabelle.css\"/>\n\
    \</head>\n\
    \\n\
    \<body>\n\
    \<div class=\"head\">\
    \<h1>" ^ plain title ^ "</h1>\n"
  end;

val end_document = "\n</div>\n</body>\n</html>\n";

fun gen_link how (path, name) = para (href_path path how ^ " to index of " ^ plain name);
val up_link = gen_link "Up";
val back_link = gen_link "Back";


(* session index *)

fun begin_index up (index_path, session) docs graph =
  begin_document ("Index of " ^ session) ^ up_link up ^
  para ("View " ^ href_path graph "theory dependencies" ^
    implode (map (fn (p, name) => "<br/>\nView " ^ href_path p name) docs)) ^
  "\n</div>\n<hr/>\n<div class=\"theories\">\n<h2>Theories</h2>\n<ul>\n";

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
          "\n</div>\n<hr/>\n<div class=\"graphbrowser\">\n\
          \<applet code=\"GraphBrowser/GraphBrowser.class\" \
          \archive=\"GraphBrowser.jar\" \
          \width=" ^ quote width ^ " height=" ^ quote height ^ ">\n\
          \<param name=\"graphfile\" value=\"" ^ "session.graph" ^ "\"/>\n\
          \</applet>\n<hr/>" ^ end_document)
      end;
  in map applet_page sizes end;


fun entry (p, s) = "<li>" ^ href_path p (plain s) ^ "</li>\n";

val theory_entry = entry;

fun session_entries [] = "</ul>"
  | session_entries es =
      "</ul>\n</div>\n<hr/>\n<div class=\"sessions\">\n\
      \<h2>Sessions</h2>\n<ul>\n" ^ implode (map entry es) ^ "</ul>";


(* theory *)

val theory_source = enclose
  "\n</div>\n<hr/>\n<div class=\"source\">\n<pre>"
  "</pre>\n<hr/>\n";


local
  fun file (href, path, loadit) =
    href_path href (if loadit then file_path path else enclose "(" ")" (file_path path));

  fun theory up A =
    begin_document ("Theory " ^ A) ^ "\n" ^ up_link up ^
    command "theory" ^ " " ^ name A;

  fun imports Bs =
    keyword "imports" ^ " " ^ space_implode " " (map (uncurry href_opt_path o apsnd name) Bs);

  fun uses Ps = keyword "uses" ^ " " ^ space_implode " " (map file Ps) ^ "<br/>\n";
in

fun begin_theory up A Bs Ps body =
  theory up A ^ "<br/>\n" ^
  imports Bs ^ "<br/>\n" ^
  (if null Ps then "" else uses Ps) ^
  body;

end;


(* ML file *)

fun ml_file path str =
  begin_document ("File " ^ Url.implode path) ^
  "\n</div>\n<hr/><div class=\"mlsource\">\n" ^
  verbatim str ^
  "\n</div>\n<hr/>\n<div class=\"mlfooter\">" ^
  end_document;

end;
