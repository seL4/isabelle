(*  Title:      Pure/General/xml.ML
    ID:         $Id$
    Author:     David Aspinall, Stefan Berghofer and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Basic support for XML.
*)

signature XML =
sig
  val header: string
  val text: string -> string
  val cdata: string -> string
  val element: string -> (string * string) list -> string list -> string
  datatype tree =
      Elem of string * (string * string) list * tree list
    | Text of string
  val string_of_tree: tree -> string
  val parse_content: string list -> tree list * string list
  val parse_elem: string list -> tree * string list
  val parse_document: string list -> (string option * tree) * string list
  val tree_of_string: string -> tree
end;

structure XML: XML =
struct

(** string based representation (small scale) **)

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

val text = Library.translate_string encode;

val cdata = enclose "<![CDATA[" "]]>";


(* elements *)

fun attribute (a, x) = a ^ " = \"" ^ text x ^ "\"";

fun element name atts cs =
  let val elem = space_implode " " (name :: map attribute atts) in
    if null cs then enclose "<" "/>" elem
    else enclose "<" ">" elem ^ implode cs ^ enclose "</" ">" name
  end;



(** explicit XML trees **)

datatype tree =
    Elem of string * (string * string) list * tree list
  | Text of string;

fun string_of_tree tree =
  let
    fun string_of (Elem (name, atts, ts)) buf =
        let val buf' =
          buf |> Buffer.add "<"
          |> fold Buffer.add (separate " " (name :: map attribute atts))
        in
          if null ts then
            buf' |> Buffer.add "/>"
          else
            buf' |> Buffer.add ">"
            |> fold string_of ts
            |> Buffer.add "</" |> Buffer.add name |> Buffer.add ">"
        end
      | string_of (Text s) buf = Buffer.add (text s) buf;
  in Buffer.content (string_of tree Buffer.empty) end;



(** XML parsing **)

fun err s (xs, _) =
  "XML parsing error: " ^ s ^ "\nfound: " ^ quote (Symbol.beginning 100 xs);

val scan_whspc = Scan.any Symbol.is_blank;

val scan_special = $$ "&" ^^ Symbol.scan_id ^^ $$ ";" >> decode;

val parse_chars = Scan.repeat1 (Scan.unless (scan_whspc -- $$ "<")
  (scan_special || Scan.one Symbol.not_eof)) >> implode;

val parse_cdata = Scan.this_string "<![CDATA[" |--
  (Scan.repeat (Scan.unless (Scan.this_string "]]>") (Scan.one Symbol.not_eof)) >>
    implode) --| Scan.this_string "]]>";

val parse_att =
  Symbol.scan_id --| scan_whspc --| $$ "=" --| scan_whspc --
  (($$ "\"" || $$ "'") :-- (fn s => (Scan.repeat (Scan.unless ($$ s)
    (scan_special || Scan.one Symbol.not_eof)) >> implode) --| $$ s) >> snd);

val parse_comment = Scan.this_string "<!--" --
  Scan.repeat (Scan.unless (Scan.this_string "-->") (Scan.one Symbol.not_eof)) --
  Scan.this_string "-->";

val parse_pi = Scan.this_string "<?" |--
  Scan.repeat (Scan.unless (Scan.this_string "?>") (Scan.one Symbol.not_eof)) --|
  Scan.this_string "?>";

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
        (Scan.this_string "/>" >> K []
         || $$ ">" |-- parse_content --|
            !! (err ("Expected </" ^ s ^ ">"))
              (Scan.this_string ("</" ^ s) --| scan_whspc --| $$ ">"))) >>
    (fn ((s, atts), ts) => Elem (s, atts, ts))) xs;

val parse_document =
  Scan.option (Scan.this_string "<!DOCTYPE" -- scan_whspc |--
    (Scan.repeat (Scan.unless ($$ ">")
      (Scan.one Symbol.not_eof)) >> implode) --| $$ ">" --| scan_whspc) --
  parse_elem;

fun tree_of_string s =
  (case Scan.finite Symbol.stopper (Scan.error (!! (err "Malformed element")
      (scan_whspc |-- parse_elem --| scan_whspc))) (Symbol.explode s) of
    (x, []) => x
  | (_, ys) => error ("XML parsing error: Unprocessed input\n" ^ Symbol.beginning 100 ys));

end;
