(*  Title:      HOL/Import/xml.ML
    ID:         $Id$

Yet another version of XML support.
*)

signature XML =
sig
  val header: string
  val text: string -> string
  val text_charref: string -> string
  val cdata: string -> string
  val element: string -> (string * string) list -> string list -> string
  
  datatype tree =
      Elem of string * (string * string) list * tree list
    | Text of string
  
  val string_of_tree: tree -> string
  val tree_of_string: string -> tree

  val encoded_string_of_tree : tree -> string
  val tree_of_encoded_string : string -> tree
end;

structure XML :> XML =
struct

(*structure Seq = VectorScannerSeq
structure Scan = Scanner (structure Seq = Seq)*)
structure Seq = StringScannerSeq
structure Scan = StringScanner


open Scan

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

fun encode_charref c = "&#" ^ Int.toString (ord c) ^ ";"

val text = Library.translate_string encode

val text_charref = translate_string encode_charref;

val cdata = enclose "<![CDATA[" "]]>\n"

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

fun beginning n xs = Symbol.beginning n (Seq.take_at_most xs n)

fun err s xs =
  "XML parsing error: " ^ s ^ "\nfound: " ^ quote (beginning 100 xs) ;

val scan_whspc = Scan.any Symbol.is_blank;

val scan_special = $$ "&" ^^ scan_id ^^ $$ ";" >> decode;

val parse_chars = Scan.repeat1 (Scan.unless ((* scan_whspc -- *)$$ "<")
  (scan_special || Scan.one Symbol.is_regular)) >> implode;

val parse_cdata = Scan.this_string "<![CDATA[" |--
  (Scan.repeat (Scan.unless (Scan.this_string "]]>") (Scan.one Symbol.is_regular)) >>
    implode) --| Scan.this_string "]]>";

val parse_att =
    scan_id --| scan_whspc --| $$ "=" --| scan_whspc --
    (($$ "\"" || $$ "'") :-- (fn s => (Scan.repeat (Scan.unless ($$ s)
    (scan_special || Scan.one Symbol.is_regular)) >> implode) --| $$ s) >> snd);

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
  ($$ "<" |-- scan_id --
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
    let
	val seq = Seq.fromString s
	val scanner = !! (err "Malformed element") (scan_whspc |-- parse_elem --| scan_whspc)
	val (x, toks) = scanner seq
    in
	if Seq.null toks then x else error ("Unprocessed input: '"^(beginning 100 toks)^"'")
    end

(* More efficient saving and loading of xml trees employing a proprietary external format *)

fun write_lstring s buf = buf |> Buffer.add (string_of_int (size s)) |> Buffer.add " " |> Buffer.add s
fun parse_lstring toks = (scan_nat --| one Symbol.is_blank :-- (fn i => repeat_fixed i (one (K true))) >> snd >> implode) toks

fun write_list w l buf = buf |> Buffer.add (string_of_int (length l)) |> Buffer.add " " |> fold w l     
fun parse_list sc = scan_nat --| one Symbol.is_blank :-- (fn i => repeat_fixed i sc) >> snd

fun write_tree (Text s) buf = buf |> Buffer.add "T" |> write_lstring s
  | write_tree (Elem (name, attrs, children)) buf = 
    buf |> Buffer.add "E" 
	|> write_lstring name 
	|> write_list (fn (a,b) => fn buf => buf |> write_lstring a |> write_lstring b) attrs 
	|> write_list write_tree children

fun parse_tree toks = (one (K true) :-- (fn "T" => parse_lstring >> Text | "E" => parse_elem | _ => raise SyntaxError) >> snd) toks
and parse_elem toks = (parse_lstring -- parse_list (parse_lstring -- parse_lstring) -- parse_list parse_tree >> (fn ((n, a), c) => Elem (n,a,c))) toks

fun encoded_string_of_tree tree = Buffer.content (write_tree tree Buffer.empty)

fun tree_of_encoded_string s = 
    let
	fun print (a,b) = writeln (a^" "^(string_of_int b))
	val _ = print ("length of encoded string: ", size s)
	val _ = writeln "Seq.fromString..."
	val seq = timeit (fn () => Seq.fromString s)
	val  _ = print ("length of sequence", timeit (fn () => Seq.length seq))
	val scanner = !! (err "Malformed encoded xml") parse_tree
	val (x, toks) = scanner seq
    in
	if Seq.null toks then x else error ("Unprocessed input: '"^(beginning 100 toks)^"'")
    end	       

end;
