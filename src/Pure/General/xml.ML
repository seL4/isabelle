(*  Title:      Pure/General/xml.ML
    ID:         $Id$
    Author:     Markus Wenzel, LMU München
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Basic support for XML output.
*)

signature XML =
sig
  val element: string -> (string * string) list -> string list -> string
  val text: string -> string
  val header: string
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

val text = implode o map encode o explode;


(* elements *)

fun attribute (a, x) = a ^ " = " ^ quote (text x);

fun element name atts cs =
  let val elem = space_implode " " (name :: map attribute atts) in
    if null cs then enclose "<" "/>" elem
    else enclose "<" ">" elem ^ implode cs ^ enclose "</" ">" name
  end;

val header = "<?xml version=\"1.0\"?>\n";

end;
