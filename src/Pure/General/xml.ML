(*  Title:      Pure/General/xml.ML
    Author:     David Aspinall, Stefan Berghofer and Markus Wenzel

Simple XML tree values.
*)

signature XML_DATA_OPS =
sig
  type 'a T
  val properties: Properties.T T
  val string: string T
  val int: int T
  val bool: bool T
  val unit: unit T
  val pair: 'a T -> 'b T -> ('a * 'b) T
  val triple: 'a T -> 'b T -> 'c T -> ('a * 'b * 'c) T
  val list: 'a T -> 'a list T
  val option: 'a T -> 'a option T
  val variant: 'a T list -> 'a T
end;

signature XML =
sig
  type attributes = Properties.T
  datatype tree =
      Elem of Markup.T * tree list
    | Text of string
  type body = tree list
  val add_content: tree -> Buffer.T -> Buffer.T
  val content_of: body -> string
  val header: string
  val text: string -> string
  val element: string -> attributes -> string list -> string
  val output_markup: Markup.T -> Output.output * Output.output
  val string_of: tree -> string
  val output: tree -> TextIO.outstream -> unit
  val parse_comments: string list -> unit * string list
  val parse_string : string -> string option
  val parse_element: string list -> tree * string list
  val parse_document: string list -> tree * string list
  val parse: string -> tree
  exception XML_ATOM of string
  exception XML_BODY of body
  structure Encode: XML_DATA_OPS where type 'a T = 'a -> body
  structure Decode: XML_DATA_OPS where type 'a T = body -> 'a
end;

structure XML: XML =
struct

(** XML trees **)

type attributes = Properties.T;

datatype tree =
    Elem of Markup.T * tree list
  | Text of string;

type body = tree list;

fun add_content (Elem (_, ts)) = fold add_content ts
  | add_content (Text s) = Buffer.add s;

fun content_of body = Buffer.empty |> fold add_content body |> Buffer.content;



(** string representation **)

val header = "<?xml version=\"1.0\"?>\n";


(* escaped text *)

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

fun elem name atts =
  space_implode " " (name :: map (fn (a, x) => a ^ "=\"" ^ text x ^ "\"") atts);

fun element name atts body =
  let val b = implode body in
    if b = "" then enclose "<" "/>" (elem name atts)
    else enclose "<" ">" (elem name atts) ^ b ^ enclose "</" ">" name
  end;

fun output_markup (markup as (name, atts)) =
  if Markup.is_empty markup then Markup.no_output
  else (enclose "<" ">" (elem name atts), enclose "</" ">" name);


(* output *)

fun buffer_of tree =
  let
    fun traverse (Elem ((name, atts), [])) =
          Buffer.add "<" #> Buffer.add (elem name atts) #> Buffer.add "/>"
      | traverse (Elem ((name, atts), ts)) =
          Buffer.add "<" #> Buffer.add (elem name atts) #> Buffer.add ">" #>
          fold traverse ts #>
          Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
      | traverse (Text s) = Buffer.add (text s);
  in Buffer.empty |> traverse tree end;

val string_of = Buffer.content o buffer_of;
val output = Buffer.output o buffer_of;



(** XML parsing (slow) **)

local

fun err s (xs, _) =
  "XML parsing error: " ^ s ^ "\nfound: " ^ quote (Symbol.beginning 100 xs);

fun ignored _ = [];

val blanks = Scan.many Symbol.is_blank;
val special = $$ "&" ^^ Symbol.scan_id ^^ $$ ";" >> decode;
val regular = Scan.one Symbol.is_regular;
fun regular_except x = Scan.one (fn c => Symbol.is_regular c andalso c <> x);

val parse_chars = Scan.repeat1 (special || regular_except "<") >> implode;

val parse_cdata =
  Scan.this_string "<![CDATA[" |--
  (Scan.repeat (Scan.unless (Scan.this_string "]]>") regular) >> implode) --|
  Scan.this_string "]]>";

val parse_att =
  (Symbol.scan_id --| (blanks -- $$ "=" -- blanks)) --
  (($$ "\"" || $$ "'") :|-- (fn s =>
    (Scan.repeat (special || regular_except s) >> implode) --| $$ s));

val parse_comment =
  Scan.this_string "<!--" --
  Scan.repeat (Scan.unless (Scan.this_string "-->") regular) --
  Scan.this_string "-->" >> ignored;

val parse_processing_instruction =
  Scan.this_string "<?" --
  Scan.repeat (Scan.unless (Scan.this_string "?>") regular) --
  Scan.this_string "?>" >> ignored;

val parse_doctype =
  Scan.this_string "<!DOCTYPE" --
  Scan.repeat (Scan.unless ($$ ">") regular) --
  $$ ">" >> ignored;

val parse_misc =
  Scan.one Symbol.is_blank >> ignored ||
  parse_processing_instruction ||
  parse_comment;

val parse_optional_text =
  Scan.optional (parse_chars >> (single o Text)) [];

in

val parse_comments =
  blanks -- Scan.repeat (parse_comment -- blanks >> K ()) >> K ();

val parse_string = Scan.read Symbol.stopper parse_chars o raw_explode;

fun parse_content xs =
  (parse_optional_text @@@
    (Scan.repeat
      ((parse_element >> single ||
        parse_cdata >> (single o Text) ||
        parse_processing_instruction ||
        parse_comment)
      @@@ parse_optional_text) >> flat)) xs

and parse_element xs =
  ($$ "<" |-- Symbol.scan_id --
    Scan.repeat (blanks |-- parse_att) --| blanks :-- (fn (s, _) =>
      !! (err "Expected > or />")
        (Scan.this_string "/>" >> ignored
         || $$ ">" |-- parse_content --|
            !! (err ("Expected </" ^ s ^ ">"))
              (Scan.this_string ("</" ^ s) --| blanks --| $$ ">"))) >> Elem) xs;

val parse_document =
  (Scan.repeat parse_misc -- Scan.option parse_doctype -- Scan.repeat parse_misc)
  |-- parse_element;

fun parse s =
  (case Scan.finite Symbol.stopper (Scan.error (!! (err "Malformed element")
      (blanks |-- parse_document --| blanks))) (raw_explode s) of
    (x, []) => x
  | (_, ys) => error ("XML parsing error: Unprocessed input\n" ^ Symbol.beginning 100 ys));

end;



(** XML as data representation language **)

exception XML_ATOM of string;
exception XML_BODY of tree list;


structure Encode =
struct

type 'a T = 'a -> body;


(* basic values *)

fun int_atom i = signed_string_of_int i;

fun bool_atom false = "0"
  | bool_atom true = "1";

fun unit_atom () = "";


(* structural nodes *)

fun node ts = Elem ((":", []), ts);

fun tagged (tag, ts) = Elem ((int_atom tag, []), ts);


(* representation of standard types *)

fun properties props = [Elem ((":", props), [])];

fun string "" = []
  | string s = [Text s];

val int = string o int_atom;

val bool = string o bool_atom;

val unit = string o unit_atom;

fun pair f g (x, y) = [node (f x), node (g y)];

fun triple f g h (x, y, z) = [node (f x), node (g y), node (h z)];

fun list f xs = map (node o f) xs;

fun option _ NONE = []
  | option f (SOME x) = [node (f x)];

fun variant fs x = [tagged (the (get_index (fn f => try f x) fs))];

end;


structure Decode =
struct

type 'a T = body -> 'a;


(* basic values *)

fun int_atom s =
  (case Int.fromString s of
    SOME i => i
  | NONE => raise XML_ATOM s);

fun bool_atom "0" = false
  | bool_atom "1" = true
  | bool_atom s = raise XML_ATOM s;

fun unit_atom "" = ()
  | unit_atom s = raise XML_ATOM s;


(* structural nodes *)

fun node (Elem ((":", []), ts)) = ts
  | node t = raise XML_BODY [t];

fun tagged (Elem ((s, []), ts)) = (int_atom s, ts)
  | tagged t = raise XML_BODY [t];


(* representation of standard types *)

fun properties [Elem ((":", props), [])] = props
  | properties ts = raise XML_BODY ts;

fun string [] = ""
  | string [Text s] = s
  | string ts = raise XML_BODY ts;

val int = int_atom o string;

val bool = bool_atom o string;

val unit = unit_atom o string;

fun pair f g [t1, t2] = (f (node t1), g (node t2))
  | pair _ _ ts = raise XML_BODY ts;

fun triple f g h [t1, t2, t3] = (f (node t1), g (node t2), h (node t3))
  | triple _ _ _ ts = raise XML_BODY ts;

fun list f ts = map (f o node) ts;

fun option _ [] = NONE
  | option f [t] = SOME (f (node t))
  | option _ ts = raise XML_BODY ts;

fun variant fs [t] =
      let
        val (tag, ts) = tagged t;
        val f = nth fs tag handle General.Subscript => raise XML_BODY [t];
      in f ts end
  | variant _ ts = raise XML_BODY ts;

end;

end;
