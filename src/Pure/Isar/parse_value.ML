(*  Title:      Pure/Isar/parse_value.ML
    Author:     Makarius

Outer syntax parsers for basic ML values.
*)

signature PARSE_VALUE =
sig
  val comma: 'a parser -> 'a parser
  val equal: 'a parser -> 'a parser
  val parens: 'a parser -> 'a parser
  val unit: unit parser
  val pair: 'a parser -> 'b parser -> ('a * 'b) parser
  val triple: 'a parser -> 'b parser -> 'c parser -> ('a * 'b * 'c) parser
  val list: 'a parser -> 'a list parser
  val properties: Properties.T parser
end;

structure Parse_Value: PARSE_VALUE =
struct

(* syntax utilities *)

fun comma p = Parse.$$$ "," |-- Parse.!!! p;
fun equal p = Parse.$$$ "=" |-- Parse.!!! p;
fun parens p = Parse.$$$ "(" |-- Parse.!!! (p --| Parse.$$$ ")");


(* tuples *)

val unit = parens (Scan.succeed ());
fun pair p1 p2 = parens (p1 -- comma p2);
fun triple p1 p2 p3 = parens (p1 -- comma p2 -- comma p3) >> Parse.triple1;


(* lists *)

fun list p = parens (Parse.enum "," p);
val properties = list (Parse.string -- equal Parse.string);

end;

