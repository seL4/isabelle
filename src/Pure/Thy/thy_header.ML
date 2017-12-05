(*  Title:      Pure/Thy/thy_header.ML
    Author:     Makarius

Static theory header information.
*)

signature THY_HEADER =
sig
  type keywords = ((string * Position.T) * Keyword.spec) list
  type header =
   {name: string * Position.T,
    imports: (string * Position.T) list,
    keywords: keywords}
  val make: string * Position.T -> (string * Position.T) list -> keywords -> header
  val theoryN: string
  val bootstrap_keywords: Keyword.keywords
  val add_keywords: keywords -> theory -> theory
  val get_keywords: theory -> Keyword.keywords
  val get_keywords': Proof.context -> Keyword.keywords
  val ml_bootstrapN: string
  val ml_roots: string list
  val bootstrap_thys: string list
  val is_base_name: string -> bool
  val import_name: string -> string
  val args: header parser
  val read: Position.T -> string -> header
  val read_tokens: Token.T list -> header
end;

structure Thy_Header: THY_HEADER =
struct

(** keyword declarations **)

(* header *)

type keywords = ((string * Position.T) * Keyword.spec) list;

type header =
 {name: string * Position.T,
  imports: (string * Position.T) list,
  keywords: keywords};

fun make name imports keywords : header =
  {name = name, imports = imports, keywords = keywords};


(* bootstrap keywords *)

val chapterN = "chapter";
val sectionN = "section";
val subsectionN = "subsection";
val subsubsectionN = "subsubsection";
val paragraphN = "paragraph";
val subparagraphN = "subparagraph";
val textN = "text";
val txtN = "txt";
val text_rawN = "text_raw";

val theoryN = "theory";
val importsN = "imports";
val keywordsN = "keywords";
val abbrevsN = "abbrevs";
val beginN = "begin";

val bootstrap_keywords =
  Keyword.empty_keywords
  |> Keyword.add_keywords
    [(("%", \<^here>), Keyword.no_spec),
     (("(", \<^here>), Keyword.no_spec),
     ((")", \<^here>), Keyword.no_spec),
     ((",", \<^here>), Keyword.no_spec),
     (("::", \<^here>), Keyword.no_spec),
     (("=", \<^here>), Keyword.no_spec),
     (("and", \<^here>), Keyword.no_spec),
     ((beginN, \<^here>), Keyword.quasi_command_spec),
     ((importsN, \<^here>), Keyword.quasi_command_spec),
     ((keywordsN, \<^here>), Keyword.quasi_command_spec),
     ((abbrevsN, \<^here>), Keyword.quasi_command_spec),
     ((chapterN, \<^here>), Keyword.document_heading_spec),
     ((sectionN, \<^here>), Keyword.document_heading_spec),
     ((subsectionN, \<^here>), Keyword.document_heading_spec),
     ((subsubsectionN, \<^here>), Keyword.document_heading_spec),
     ((paragraphN, \<^here>), Keyword.document_heading_spec),
     ((subparagraphN, \<^here>), Keyword.document_heading_spec),
     ((textN, \<^here>), Keyword.document_body_spec),
     ((txtN, \<^here>), Keyword.document_body_spec),
     ((text_rawN, \<^here>), ((Keyword.document_raw, []), ["document"])),
     ((theoryN, \<^here>), ((Keyword.thy_begin, []), ["theory"])),
     (("ML", \<^here>), ((Keyword.thy_decl, []), ["ML"]))];


(* theory data *)

structure Data = Theory_Data
(
  type T = Keyword.keywords;
  val empty = bootstrap_keywords;
  val extend = I;
  val merge = Keyword.merge_keywords;
);

val add_keywords = Data.map o Keyword.add_keywords;

val get_keywords = Data.get;
val get_keywords' = get_keywords o Proof_Context.theory_of;



(** concrete syntax **)

(* names *)

val ml_bootstrapN = "ML_Bootstrap";
val ml_roots = ["ML_Root0", "ML_Root"];
val bootstrap_thys = ["Bootstrap_Pure", "Bootstrap_ML_Bootstrap"];

fun is_base_name s =
  s <> "" andalso not (exists_string (member (op =) ["/", "\\", ":"]) s)

val import_name = Path.base_name o Path.explode;


(* header args *)

local

fun imports name =
  if name = Context.PureN then Scan.succeed []
  else Parse.$$$ importsN |-- Parse.!!! (Scan.repeat1 (Parse.position Parse.theory_name));

val opt_files =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Parse.list1 Parse.name) --| Parse.$$$ ")") [];

val keyword_spec =
  Parse.group (fn () => "outer syntax keyword specification")
    (Parse.name -- opt_files -- Parse.tags);

val keyword_decl =
  Scan.repeat1 (Parse.position Parse.string) --
  Scan.optional (Parse.$$$ "::" |-- Parse.!!! keyword_spec) Keyword.no_spec
  >> (fn (names, spec) => map (rpair spec) names);

val abbrevs = Parse.and_list1 (Parse.text -- (Parse.$$$ "=" |-- Parse.!!! Parse.text));

val keyword_decls = Parse.and_list1 keyword_decl >> flat;

in

val args =
  Parse.position Parse.theory_name :|-- (fn (name, pos) =>
    imports name --
    Scan.optional (Parse.$$$ keywordsN |-- Parse.!!! keyword_decls) [] --|
    (Scan.optional (Parse.$$$ abbrevsN |-- Parse.!!! abbrevs) [] -- Parse.$$$ beginN)
    >> (fn (imports, keywords) => make (name, pos) imports keywords));

end;


(* read header *)

val heading =
  (Parse.command_name chapterN ||
    Parse.command_name sectionN ||
    Parse.command_name subsectionN ||
    Parse.command_name subsubsectionN ||
    Parse.command_name paragraphN ||
    Parse.command_name subparagraphN ||
    Parse.command_name textN ||
    Parse.command_name txtN ||
    Parse.command_name text_rawN) --
  Parse.tags -- Parse.!!! Parse.document_source;

val header =
  (Scan.repeat heading -- Parse.command_name theoryN -- Parse.tags) |-- Parse.!!! args;

fun token_source pos =
  Symbol.explode
  #> Source.of_list
  #> Token.source_strict bootstrap_keywords pos;

fun read_source pos source =
  let val res =
    source
    |> Token.source_proper
    |> Source.source Token.stopper (Scan.single (Scan.error (Parse.!!! header)))
    |> Source.get_single;
  in
    (case res of
      SOME (h, _) => h
    | NONE => error ("Unexpected end of input" ^ Position.here pos))
  end;

fun read pos str = read_source pos (token_source pos str);
fun read_tokens toks = read_source Position.none (Source.of_list toks);

end;
