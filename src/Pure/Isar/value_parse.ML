(*  Title:      Pure/Isar/value_parse.ML
    Author:     Makarius

Outer syntax parsers for basic ML values.
*)

signature VALUE_PARSE =
sig
  val comma: 'a parser -> 'a parser
  val equal: 'a parser -> 'a parser
  val parens: 'a parser -> 'a parser
  val pair: 'a parser -> 'b parser -> ('a * 'b) parser
  val triple: 'a parser -> 'b parser -> 'c parser -> ('a * 'b * 'c) parser
  val list: 'a parser -> 'a list parser
  val properties: Properties.T parser
end;

structure ValueParse: VALUE_PARSE =
struct

structure P = OuterParse;


(* syntax utilities *)

fun comma p = P.$$$ "," |-- P.!!! p;
fun equal p = P.$$$ "=" |-- P.!!! p;
fun parens p = P.$$$ "(" |-- P.!!! (p --| P.$$$ ")");


(* tuples *)

val unit = parens (Scan.succeed ());
fun pair p1 p2 = parens (p1 -- comma p2);
fun triple p1 p2 p3 = parens (p1 -- comma p2 -- comma p3) >> P.triple1;


(* lists *)

fun list p = parens (P.enum "," p);
val properties = list (P.string -- equal P.string);

end;

