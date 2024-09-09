(*  Title:      Pure/PIDE/yxml.ML
    Author:     Makarius

Efficient text representation of XML trees using extra characters X
and Y -- no escaping, may nest marked text verbatim.  Suitable for
direct inlining into plain text.

Markup <elem att="val" ...>...body...</elem> is encoded as:

  X Y name Y att=val ... X
  ...
  body
  ...
  X Y X
*)

signature YXML =
sig
  val X: Symbol.symbol
  val Y: Symbol.symbol
  val detect: string -> bool
  val traverse: (string -> 'a -> 'a) -> XML.tree -> 'a -> 'a
  val tree_size: XML.tree -> int
  val body_size: XML.body -> int
  val string_of_body: XML.body -> string
  val string_of: XML.tree -> string
  val bytes_of_body: XML.body -> Bytes.T
  val bytes_of: XML.tree -> Bytes.T
  val write_body: Path.T -> XML.body -> unit
  val output_markup: Markup.T -> string * string
  val output_markup_elem: Markup.T -> (string * string) * string
  val markup_ops: Markup.ops
  val parse_body: string -> XML.body
  val parse_body_bytes: Bytes.T -> XML.body
  val parse: string -> XML.tree
  val parse_bytes: Bytes.T -> XML.tree
  val is_wellformed: string -> bool
end;

structure YXML: YXML =
struct

(** string representation **)

(* markers *)

val X_char = Char.chr 5;
val Y_char = Char.chr 6;

val X = String.str X_char;
val Y = String.str Y_char;
val XY = X ^ Y;
val XYX = XY ^ X;

fun detect s = Char.contains s X_char orelse Char.contains s Y_char;


(* traverse *)

fun traverse string =
  let
    fun attrib (a, x) = string Y #> string a #> string "=" #> string x;
    fun tree (XML.Elem (markup as (name, atts), ts)) =
          if Markup.is_empty markup then fold tree ts
          else
            string XY #> string name #> fold attrib atts #> string X #>
            fold tree ts #>
            string XYX
      | tree (XML.Text s) = string s;
  in tree end;

val tree_size = Integer.build o traverse (Integer.add o size);
val body_size = Integer.build o fold (Integer.add o tree_size);


(* output *)

val string_of_body = Buffer.build_content o fold (traverse Buffer.add);
val string_of = string_of_body o single;

val bytes_of_body = Bytes.build o fold (traverse Bytes.add);
val bytes_of = bytes_of_body o single;

fun write_body path body =
  path |> File_Stream.open_output (fn file =>
    fold (traverse (fn s => fn () => File_Stream.output file s)) body ());


(* markup elements *)

val Z = chr 0;
val Z_text = [XML.Text Z];

fun output_markup (markup as (name, atts)) =
  if Markup.is_empty markup then Markup.no_output
  else (XY ^ name ^ implode (map (fn p => Y ^ Properties.print_eq p) atts) ^ X, XYX);

fun output_markup_elem markup =
  let val [bg1, bg2, en] = space_explode Z (string_of (XML.wrap_elem ((markup, Z_text), Z_text)))
  in ((bg1, bg2), en) end;

val markup_ops: Markup.ops = {output = output_markup};


(** efficient YXML parsing **)

local

(* splitting *)

val split_string =
  Substring.full #>
  Substring.tokens (fn c => c = X_char) #>
  map (Substring.fields (fn c => c = Y_char) #> map Substring.string);

val split_bytes =
  Bytes.space_explode X
  #> map_filter (fn "" => NONE | s => SOME (space_explode Y s));


(* structural errors *)

fun err msg = raise Fail ("Malformed YXML: " ^ msg);
fun err_attribute () = err "bad attribute";
fun err_element () = err "bad element";
fun err_unbalanced "" = err "unbalanced element"
  | err_unbalanced name = err ("unbalanced element " ^ quote name);


(* stack operations *)

fun add x ((elem, body) :: pending) = (elem, x :: body) :: pending;

fun push "" _ _ = err_element ()
  | push name atts pending = ((name, atts), []) :: pending;

fun pop ((("", _), _) :: _) = err_unbalanced ""
  | pop ((markup, body) :: pending) = add (XML.Elem (markup, rev body)) pending;


(* parsing *)

fun parse_attrib s =
  (case first_field "=" s of
    NONE => err_attribute ()
  | SOME ("", _) => err_attribute ()
  | SOME att => att);

fun parse_chunk ["", ""] = pop
  | parse_chunk ("" :: name :: atts) = push name (map parse_attrib atts)
  | parse_chunk txts = fold (add o XML.Text) txts;

fun parse_body' chunks =
  (case fold parse_chunk chunks [(("", []), [])] of
    [(("", _), result)] => rev result
  | ((name, _), _) :: _ => err_unbalanced name);

fun parse' chunks =
  (case parse_body' chunks of
    [result] => result
  | [] => XML.Text ""
  | _ => err "multiple results");

in

val parse_body = parse_body' o split_string;
val parse_body_bytes = parse_body' o split_bytes;

val parse = parse' o split_string;
val parse_bytes = parse' o split_bytes;

end;

fun is_wellformed s = string_of_body (parse_body s) = s
  handle Fail _ => false;

end;
