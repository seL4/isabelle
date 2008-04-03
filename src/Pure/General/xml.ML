(*  Title:      Pure/General/xml.ML
    ID:         $Id$
    Author:     David Aspinall, Stefan Berghofer and Markus Wenzel

Basic support for XML.
*)

signature XML =
sig
  (*string functions*)
  val detect: string -> bool
  val header: string
  val text: string -> string
  type attributes = (string * string) list
  val attribute: string * string -> string
  val element: string -> attributes -> string list -> string
  (*tree functions*)
  datatype tree =
      Elem of string * attributes * tree list
    | Text of string
    | Output of output
  type content = tree list
  type element = string * attributes * content
  val string_of_tree: tree -> string
  val plain_content: tree -> string
  val parse_string : string -> string option
  val parse_content: string list -> tree list * string list
  val parse_elem: string list -> tree * string list
  val parse_document: string list -> (string option * tree) * string list
  val tree_of_string: string -> tree
  val scan_comment_whspc: string list -> unit * string list
end;

structure XML: XML =
struct


(** string representation **)

val detect = String.isPrefix "<?xml";
val header = "<?xml version=\"1.0\"?>\n";


(* text and character data *)

fun decode "&lt;" = "<"
  | decode "&gt;" = ">"
  | decode "&amp;" = "&"
  | decode "&apos;" = "'"
  | decode "&quot;" = "\""
  | decode c = c;

fun encode "<" = "&lt;"
  | encode ">" = "&gt;"
  | encode "&" = "&amp;"
  | encode "'" = "&apos;"
  | encode "\"" = "&quot;"
  | encode c = c;

val text = translate_string encode;


(* elements *)

fun attribute (a, x) = a ^ " = \"" ^ text x ^ "\"";

fun element name atts body =
  let
    val elem = space_implode " " (name :: map attribute atts);
    val b = implode body;
  in
    if b = "" then enclose "<" "/>" elem
    else enclose "<" ">" elem ^ b ^ enclose "</" ">" name
  end;



(** explicit XML trees **)

type attributes = (string * string) list;

datatype tree =
    Elem of string * attributes * tree list
  | Text of string
  | Output of output;

type content = tree list;
type element = string * attributes * content;

fun string_of_tree t =
  let
    fun name_atts name atts = fold Buffer.add (separate " " (name :: map attribute atts));
    fun tree (Elem (name, atts, [])) =
          Buffer.add "<" #> name_atts name atts #> Buffer.add "/>"
      | tree (Elem (name, atts, ts)) =
          Buffer.add "<" #> name_atts name atts #> Buffer.add ">" #>
          fold tree ts #>
          Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
      | tree (Text s) = Buffer.add (text s)
      | tree (Output s) = Buffer.add s;
  in Buffer.empty |> tree t |> Buffer.content end;

fun plain_content tree =
  let
    fun content (Elem (_, _, ts)) = fold content ts
      | content (Text s) = Buffer.add s
      | content (Output _) = I;    (* FIXME !? *)
  in Buffer.empty |> content tree |> Buffer.content end;



(** XML parsing **)

fun err s (xs, _) =
  "XML parsing error: " ^ s ^ "\nfound: " ^ quote (Symbol.beginning 100 xs);

val scan_whspc = Scan.many Symbol.is_blank;

val scan_special = $$ "&" ^^ Symbol.scan_id ^^ $$ ";" >> decode;

val parse_chars = Scan.repeat1 (Scan.unless ((* scan_whspc -- *)$$ "<")
  (scan_special || Scan.one Symbol.is_regular)) >> implode;

val parse_string = Scan.read Symbol.stopper parse_chars o explode;

val parse_cdata = Scan.this_string "<![CDATA[" |--
  (Scan.repeat (Scan.unless (Scan.this_string "]]>") (Scan.one Symbol.is_regular)) >>
    implode) --| Scan.this_string "]]>";

val parse_att =
  Symbol.scan_id --| scan_whspc --| $$ "=" --| scan_whspc --
  (($$ "\"" || $$ "'") :|-- (fn s => (Scan.repeat (Scan.unless ($$ s)
    (scan_special || Scan.one Symbol.is_regular)) >> implode) --| $$ s));

val parse_comment = Scan.this_string "<!--" --
  Scan.repeat (Scan.unless (Scan.this_string "-->") (Scan.one Symbol.is_regular)) --
  Scan.this_string "-->";

val scan_comment_whspc =
  (scan_whspc >> K()) --| (Scan.repeat (parse_comment |-- (scan_whspc >> K())));

val parse_pi = Scan.this_string "<?" |--
  Scan.repeat (Scan.unless (Scan.this_string "?>") (Scan.one Symbol.is_regular)) --|
  Scan.this_string "?>";

fun parse_content xs =
  ((Scan.optional ((* scan_whspc |-- *) parse_chars >> (single o Text)) [] --
    (Scan.repeat ((* scan_whspc |-- *)
       (   parse_elem >> single
        || parse_cdata >> (single o Text)
        || parse_pi >> K []
        || parse_comment >> K []) --
       Scan.optional ((* scan_whspc |-- *) parse_chars >> (single o Text)) []
         >> op @) >> flat) >> op @)(* --| scan_whspc*)) xs

and parse_elem xs =
  ($$ "<" |-- Symbol.scan_id --
    Scan.repeat (scan_whspc |-- parse_att) --| scan_whspc :-- (fn (s, _) =>
      !! (err "Expected > or />")
        (Scan.this_string "/>" >> K []
         || $$ ">" |-- parse_content --|
            !! (err ("Expected </" ^ s ^ ">"))
              (Scan.this_string ("</" ^ s) --| scan_whspc --| $$ ">"))) >>
    (fn ((s, atts), ts) => Elem (s, atts, ts))) xs;

val parse_document =
  Scan.option (Scan.this_string "<!DOCTYPE" -- scan_whspc |--
    (Scan.repeat (Scan.unless ($$ ">")
      (Scan.one Symbol.is_regular)) >> implode) --| $$ ">" --| scan_whspc) --
  parse_elem;

fun tree_of_string s =
  (case Scan.finite Symbol.stopper (Scan.error (!! (err "Malformed element")
      (scan_whspc |-- parse_elem --| scan_whspc))) (Symbol.explode s) of
    (x, []) => x
  | (_, ys) => error ("XML parsing error: Unprocessed input\n" ^ Symbol.beginning 100 ys));

end;
