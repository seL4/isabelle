(*  Title:      Pure/Thy/thy_header.ML
    Author:     Makarius

Static theory header information.
*)

signature THY_HEADER =
sig
  type header =
   {name: string, imports: string list,
    keywords: (string * Keyword.spec option) list,
    uses: (Path.T * bool) list}
  val make: string -> string list -> (string * Keyword.spec option) list ->
    (Path.T * bool) list -> header
  val define_keywords: header -> unit
  val declare_keyword: string * Keyword.spec option -> theory -> theory
  val the_keyword: theory -> string -> Keyword.spec option
  val args: header parser
  val read: Position.T -> string -> header
end;

structure Thy_Header: THY_HEADER =
struct

type header =
 {name: string, imports: string list,
  keywords: (string * Keyword.spec option) list,
  uses: (Path.T * bool) list};

fun make name imports keywords uses : header =
  {name = name, imports = imports, keywords = keywords, uses = uses};



(** keyword declarations **)

fun define_keywords ({keywords, ...}: header) =
  List.app (Keyword.define o apsnd (Option.map Keyword.spec)) keywords;

fun err_dup name = error ("Inconsistent declaration of outer syntax keyword " ^ quote name);

structure Data = Theory_Data
(
  type T = Keyword.spec option Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (op =) data handle Symtab.DUP name => err_dup name;
);

fun declare_keyword (name, spec) =
  Data.map (fn data =>
    (Option.map Keyword.spec spec;
      Symtab.update_new (name, spec) data handle Symtab.DUP dup => err_dup dup));

fun the_keyword thy name =
  (case Symtab.lookup (Data.get thy) name of
    SOME spec => spec
  | NONE => error ("Undeclared outer syntax keyword " ^ quote name));



(** concrete syntax **)

(* header keywords *)

val headerN = "header";
val theoryN = "theory";
val importsN = "imports";
val keywordsN = "keywords";
val usesN = "uses";
val beginN = "begin";

val header_lexicon =
  Scan.make_lexicon
    (map Symbol.explode
      ["%", "(", ")", "::", ";", "and", beginN, headerN, importsN, keywordsN, theoryN, usesN]);


(* header args *)

local

val file_name = Parse.group (fn () => "file name") Parse.path;
val theory_name = Parse.group (fn () => "theory name") Parse.name;

val keyword_kind = Parse.group (fn () => "outer syntax keyword kind") (Parse.name -- Parse.tags);
val keyword_decl =
  Scan.repeat1 Parse.string -- Scan.option (Parse.$$$ "::" |-- Parse.!!! keyword_kind) >>
  (fn (names, kind) => map (rpair kind) names);
val keyword_decls = Parse.and_list1 keyword_decl >> flat;

val file =
  Parse.$$$ "(" |-- Parse.!!! (file_name --| Parse.$$$ ")") >> rpair false ||
  file_name >> rpair true;

in

val args =
  theory_name --
  (Parse.$$$ importsN |-- Parse.!!! (Scan.repeat1 theory_name)) --
  Scan.optional (Parse.$$$ keywordsN |-- Parse.!!! keyword_decls) [] --
  Scan.optional (Parse.$$$ usesN |-- Parse.!!! (Scan.repeat1 file)) [] --|
  Parse.$$$ beginN >>
  (fn (((name, imports), keywords), uses) => make name imports keywords uses);

end;


(* read header *)

val header =
  (Parse.$$$ headerN -- Parse.tags) |--
    (Parse.!!! (Parse.doc_source -- Scan.repeat Parse.semicolon --
      (Parse.$$$ theoryN -- Parse.tags) |-- args)) ||
  (Parse.$$$ theoryN -- Parse.tags) |-- Parse.!!! args;

fun read pos str =
  let val res =
    str
    |> Source.of_string_limited 8000
    |> Symbol.source
    |> Token.source {do_recover = NONE} (fn () => (header_lexicon, Scan.empty_lexicon)) pos
    |> Token.source_proper
    |> Source.source Token.stopper (Scan.single (Scan.error (Parse.!!! header))) NONE
    |> Source.get_single;
  in
    (case res of
      SOME (h, _) => h
    | NONE => error ("Unexpected end of input" ^ Position.str_of pos))
  end;

end;
