(*  Title:      Pure/General/yxml.ML
    ID:         $Id$
    Author:     Makarius

Why XML notation?  Efficient text representation of XML trees, using
extra characters ETX and EOT -- no escaping, may nest marked text
verbatim.  Markup <elem att="val" ...>...body...</elem> is encoded as:

  ETX EOT name EOT att=val ... ETX
  ...
  body
  ...
  ETX EOT ETX
*)

signature YXML =
sig
  val detect: string -> bool
  val element: string -> XML.attributes -> string list -> string
  val string_of: XML.tree -> string
  val parse_body: string -> XML.tree list
  val parse: string -> XML.tree
end;

structure YXML: YXML =
struct

(* string representation *)

val ETX = Symbol.ETX;
val EOT = Symbol.EOT;

fun detect s = ord s = ord EOT;


(*naive pasting of strings*)
fun element name atts body =
  ETX ^ EOT ^ name ^ implode (map (fn (a, x) => EOT ^ a ^ "=" ^ x) atts) ^ ETX ^
  implode body ^
  ETX ^ EOT ^ ETX;

(*scalable buffer output*)
fun string_of t =
  let
    fun attrib (a, x) =
      Buffer.add EOT #>
      Buffer.add a #> Buffer.add "=" #> Buffer.add x;
    fun tree (XML.Elem (name, atts, ts)) =
          Buffer.add ETX #>
          Buffer.add EOT #> Buffer.add name #>
          fold attrib atts #>
          Buffer.add ETX #>
          fold tree ts #>
          Buffer.add ETX #>
          Buffer.add EOT #>
          Buffer.add ETX
      | tree (XML.Text s) = Buffer.add s
      | tree (XML.Output s) = Buffer.add s;
  in Buffer.empty |> tree t |> Buffer.content end;


(* efficient YXML parsing *)

local

(* errors *)

fun err msg = raise Fail ("Malformed YXML encoding: " ^ msg);
fun err_attribute () = err "bad attribute";
fun err_element () = err "bad element";
fun err_unbalanced "" = err "unbalanced element"
  | err_unbalanced name = err ("unbalanced element " ^ quote name);


(* stack operations *)

fun add x ((elem, body) :: pending) = (elem, x :: body) :: pending;

fun push "" _ _ = err_element ()
  | push name atts pending = ((name, atts), []) :: pending;

fun pop ((("", _), _) :: _) = err_unbalanced ""
  | pop (((name, atts), body) :: pending) = add (XML.Elem (name, atts, rev body)) pending;


(* parsers *)

fun is_char s c = ord s = Char.ord c;

fun parse_attrib s =
  (case String.fields (is_char "=") s of
    [] => err_attribute ()
  | "" :: _ => err_attribute ()
  | a :: xs => (a, space_implode "=" xs));

fun parse_chunk chunk =
  (case String.fields (is_char EOT) chunk of
    ["", ""] => pop
  | "" :: name :: atts => push name (map parse_attrib atts)
  | [_] => add (XML.Text chunk)
  | _ => err "bad text");

in

fun parse_body source =
  (case fold parse_chunk (String.tokens (is_char ETX) source) [(("", []), [])] of
    [(("", _), result)] => rev result
  | ((name, _), _) :: _ => err_unbalanced name);

fun parse source =
  (case parse_body source of
    [result as XML.Elem _] => result
  | _ => err "no root element");

end;

end;

