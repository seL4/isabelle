(*  Title:      Pure/General/xml.ML
    ID:         $Id$
    Author:     Markus Wenzel, LMU Muenchen
                Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Basic support for XML input and output.
*)

signature XML =
sig
  datatype tree =
      Elem of string * (string * string) list * tree list
    | Text of string
  val element: string -> (string * string) list -> string list -> string
  val text: string -> string
  val header: string
  val string_of_tree: tree -> string
  val tree_of_string: string -> tree
  val parse_content: string list -> tree list * string list
  val parse_elem: string list -> tree * string list
  val parse_document: string list -> (string option * tree) * string list
end;

structure XML: XML =
struct

(* character data *)

fun encode "<" = "&lt;"
  | encode ">" = "&gt;"
  | encode "&" = "&amp;"
  | encode "'" = "&apos;"
  | encode "\"" = "&quot;"
  | encode c = c;

fun decode "&lt;" = "<"
  | decode "&gt;" = ">"
  | decode "&amp;" = "&"
  | decode "&apos;" = "'"
  | decode "&quot;" = "\""
  | decode c = c;

val text = implode o map encode o explode;


(* elements *)

datatype tree =
    Elem of string * (string * string) list * tree list
  | Text of string;

fun attribute (a, x) = a ^ " = " ^ quote (text x);

fun element name atts cs =
  let val elem = space_implode " " (name :: map attribute atts) in
    if null cs then enclose "<" "/>" elem
    else enclose "<" ">" elem ^ implode cs ^ enclose "</" ">" name
  end;

fun string_of_tree (Elem (name, atts, ts)) =
      element name atts (map string_of_tree ts)
  | string_of_tree (Text s) = s
  
val header = "<?xml version=\"1.0\"?>\n";


(* parser *)

fun err s (xs, _) = "XML parsing error: " ^ s ^ "\nfound:\n" ^
  implode (take (100, xs));

val scan_whspc = Scan.repeat ($$ " " || $$ "\n");

val literal = Scan.literal o Scan.make_lexicon o single o explode;

val scan_special = $$ "&" ^^ Symbol.scan_id ^^ $$ ";" >> decode;

val parse_chars = Scan.repeat1 (Scan.unless (scan_whspc -- $$ "<")
  (scan_special || Scan.one Symbol.not_eof)) >> implode;

val parse_cdata = literal "<![CDATA[" |--
  (Scan.repeat (Scan.unless (literal "]]>") (Scan.one Symbol.not_eof)) >>
    implode) --| literal "]]>";

val parse_att =
  Symbol.scan_id --| scan_whspc --| $$ "=" --| scan_whspc --| $$ "\"" --
  (Scan.repeat (Scan.unless ($$ "\"")
    (scan_special || Scan.one Symbol.not_eof)) >> implode) --| $$ "\"";

val parse_comment = literal "<!--" --
  Scan.repeat (Scan.unless (literal "-->") (Scan.one Symbol.not_eof)) --
  literal "-->";

val parse_pi = literal "<?" |--
  Scan.repeat (Scan.unless (literal "?>") (Scan.one Symbol.not_eof)) --|
  literal "?>";

fun parse_content xs =
  ((Scan.optional (scan_whspc |-- parse_chars >> (single o Text)) [] --
    (Scan.repeat (scan_whspc |--
       (   parse_elem >> single
        || parse_cdata >> (single o Text)
        || parse_pi >> K []
        || parse_comment >> K []) --
       Scan.optional (scan_whspc |-- parse_chars >> (single o Text)) []
         >> op @) >> flat) >> op @) --| scan_whspc) xs

and parse_elem xs =
  ($$ "<" |-- Symbol.scan_id --
    Scan.repeat (scan_whspc |-- parse_att) --| scan_whspc :-- (fn (s, _) =>
      !! (err "Expected > or />")
        (   literal "/>" >> K []
         || $$ ">" |-- parse_content --|
            !! (err ("Expected </" ^ s ^ ">"))
              (literal ("</" ^ s) --| scan_whspc --| $$ ">"))) >>
    (fn ((s, atts), ts) => Elem (s, atts, ts))) xs;

val parse_document =
  Scan.option (literal "<!DOCTYPE" -- scan_whspc |--
    (Scan.repeat (Scan.unless ($$ ">")
      (Scan.one Symbol.not_eof)) >> implode) --| $$ ">" --| scan_whspc) --
  parse_elem;

fun tree_of_string s =
  (case Scan.finite Symbol.stopper (Scan.error (!! (err "Malformed element")
      (scan_whspc |-- parse_elem --| scan_whspc))) (Symbol.explode s) of
     (x, []) => x
   | (_, ys) => error ("XML parsing error: Unprocessed input\n" ^
       implode (take (100, ys))));

end;
