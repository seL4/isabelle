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

datatype token_kind = Idt | Sym | Str | Chr;

fun is_kind k (k', _) = k = k';

val stopper = ((Sym, ""), fn (Sym, "") => true | _ => false);

val scan_whspc = $$ " " || $$ "\n";

val scan_symb = Scan.literal (Scan.make_lexicon
  (map explode ["<", "</", ">", "/>", "\"", "=", "&"])) >> implode;

val scan_special = $$ "&" ^^ Symbol.scan_id ^^ $$ ";" >> decode;

val lexer = Scan.repeat (Scan.repeat scan_whspc |--
  (   Scan.max (op <= o pairself (size o snd))
        (Symbol.scan_id >> pair Idt)
        (Scan.repeat1 (scan_special || Scan.unless (scan_whspc || scan_symb)
           (Scan.one Symbol.not_eof)) >> (pair Chr o implode))
   || $$ "\"" |-- Scan.repeat
        (   scan_special
         || Scan.unless ($$ "\"") (Scan.one Symbol.not_eof)) --|
           $$ "\"" >> (pair Str o implode)
   || scan_symb >> pair Sym) --| Scan.repeat scan_whspc);

val parse_att = (Scan.one (is_kind Idt) >> snd) --| $$ (Sym, "=") --
  (Scan.one (is_kind Str) >> snd);

fun parse_tree xs =
  ($$ (Sym, "<") |-- (Scan.one (is_kind Idt) >> snd) --
    Scan.repeat parse_att :-- (fn (s, _) =>
          $$ (Sym, "/>") >> K []
       || $$ (Sym, ">") |-- Scan.repeat
            (   Scan.one (not o is_kind Sym) >> (Text o snd)
             || parse_tree) --|
          $$ (Sym, "</") --| Scan.one (equal (Idt, s)) --| $$ (Sym, ">")) >>
    (fn ((s, atts), ts) => Elem (s, atts, ts))) xs;

fun tree_of_string s =
  let val msg = "Malformed XML expression:\n" ^ s
  in case Scan.finite Symbol.stopper lexer (explode s) of
      (toks, []) => (case Scan.finite stopper
        (Scan.error (!! (K msg) parse_tree)) toks of
          (t, []) => t | _ => error msg)
    | _ => error msg
  end;

end;
