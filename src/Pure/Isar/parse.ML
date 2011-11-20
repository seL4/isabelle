(*  Title:      Pure/Isar/parse.ML
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)

signature PARSE =
sig
  type 'a parser = Token.T list -> 'a * Token.T list
  type 'a context_parser = Context.generic * Token.T list -> 'a * (Context.generic * Token.T list)
  val group: (unit -> string) -> (Token.T list -> 'a) -> Token.T list -> 'a
  val !!! : (Token.T list -> 'a) -> Token.T list -> 'a
  val !!!! : (Token.T list -> 'a) -> Token.T list -> 'a
  val triple1: ('a * 'b) * 'c -> 'a * 'b * 'c
  val triple2: 'a * ('b * 'c) -> 'a * 'b * 'c
  val triple_swap: ('a * 'b) * 'c -> ('a * 'c) * 'b
  val not_eof: Token.T parser
  val position: 'a parser -> ('a * Position.T) parser
  val source_position: 'a parser -> (Symbol_Pos.text * Position.T) parser
  val inner_syntax: 'a parser -> string parser
  val command: string parser
  val keyword: string parser
  val short_ident: string parser
  val long_ident: string parser
  val sym_ident: string parser
  val minus: string parser
  val term_var: string parser
  val type_ident: string parser
  val type_var: string parser
  val number: string parser
  val float_number: string parser
  val string: string parser
  val alt_string: string parser
  val verbatim: string parser
  val sync: string parser
  val eof: string parser
  val keyword_with: (string -> bool) -> string parser
  val keyword_ident_or_symbolic: string parser
  val $$$ : string -> string parser
  val reserved: string -> string parser
  val semicolon: string parser
  val underscore: string parser
  val maybe: 'a parser -> 'a option parser
  val tag_name: string parser
  val tags: string list parser
  val opt_unit: unit parser
  val opt_keyword: string -> bool parser
  val begin: string parser
  val opt_begin: bool parser
  val nat: int parser
  val int: int parser
  val real: real parser
  val enum: string -> 'a parser -> 'a list parser
  val enum1: string -> 'a parser -> 'a list parser
  val and_list: 'a parser -> 'a list parser
  val and_list1: 'a parser -> 'a list parser
  val enum': string -> 'a context_parser -> 'a list context_parser
  val enum1': string -> 'a context_parser -> 'a list context_parser
  val and_list': 'a context_parser -> 'a list context_parser
  val and_list1': 'a context_parser -> 'a list context_parser
  val list: 'a parser -> 'a list parser
  val list1: 'a parser -> 'a list parser
  val properties: Properties.T parser
  val name: bstring parser
  val binding: binding parser
  val xname: xstring parser
  val text: string parser
  val path: Path.T parser
  val liberal_name: xstring parser
  val parname: string parser
  val parbinding: binding parser
  val sort: string parser
  val arity: (string * string list * string) parser
  val multi_arity: (string list * string list * string) parser
  val type_args: string list parser
  val type_args_constrained: (string * string option) list parser
  val typ_group: string parser
  val typ: string parser
  val mixfix: mixfix parser
  val mixfix': mixfix parser
  val opt_mixfix: mixfix parser
  val opt_mixfix': mixfix parser
  val where_: string parser
  val const_decl: (string * string * mixfix) parser
  val const_binding: (binding * string * mixfix) parser
  val params: (binding * string option) list parser
  val simple_fixes: (binding * string option) list parser
  val fixes: (binding * string option * mixfix) list parser
  val for_fixes: (binding * string option * mixfix) list parser
  val ML_source: (Symbol_Pos.text * Position.T) parser
  val doc_source: (Symbol_Pos.text * Position.T) parser
  val term_group: string parser
  val prop_group: string parser
  val term: string parser
  val prop: string parser
  val type_const: string parser
  val const: string parser
  val literal_fact: string parser
  val propp: (string * string list) parser
  val termp: (string * string list) parser
  val target: (xstring * Position.T) parser
  val opt_target: (xstring * Position.T) option parser
end;

structure Parse: PARSE =
struct

type 'a parser = Token.T list -> 'a * Token.T list;
type 'a context_parser = Context.generic * Token.T list -> 'a * (Context.generic * Token.T list);


(** error handling **)

(* group atomic parsers (no cuts!) *)

fun group s scan = scan || Scan.fail_with
  (fn [] => (fn () => s () ^ " expected (past end-of-file!)")
    | tok :: _ =>
        (fn () =>
          (case Token.text_of tok of
            (txt, "") =>
              s () ^ " expected,\nbut " ^ txt ^ Token.pos_of tok ^ " was found"
          | (txt1, txt2) =>
              s () ^ " expected,\nbut " ^ txt1 ^ Token.pos_of tok ^ " was found:\n" ^ txt2)));


(* cut *)

fun cut kind scan =
  let
    fun get_pos [] = " (past end-of-file!)"
      | get_pos (tok :: _) = Token.pos_of tok;

    fun err (toks, NONE) = (fn () => kind ^ get_pos toks)
      | err (toks, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos toks ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!! scan = cut "Outer syntax error" scan;
fun !!!! scan = cut "Corrupted outer syntax in presentation" scan;



(** basic parsers **)

(* utils *)

fun triple1 ((x, y), z) = (x, y, z);
fun triple2 (x, (y, z)) = (x, y, z);
fun triple_swap ((x, y), z) = ((x, z), y);


(* tokens *)

fun RESET_VALUE atom = (*required for all primitive parsers*)
  Scan.ahead (Scan.one (K true)) -- atom >> (fn (arg, x) => (Token.assign NONE arg; x));


val not_eof = RESET_VALUE (Scan.one Token.not_eof);

fun position scan = (Scan.ahead not_eof >> Token.position_of) -- scan >> Library.swap;
fun source_position atom = Scan.ahead atom |-- not_eof >> Token.source_position_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> Token.source_of;

fun kind k =
  group (fn () => Token.str_of_kind k)
    (RESET_VALUE (Scan.one (Token.is_kind k) >> Token.content_of));

val command = kind Token.Command;
val keyword = kind Token.Keyword;
val short_ident = kind Token.Ident;
val long_ident = kind Token.LongIdent;
val sym_ident = kind Token.SymIdent;
val term_var = kind Token.Var;
val type_ident = kind Token.TypeIdent;
val type_var = kind Token.TypeVar;
val number = kind Token.Nat;
val float_number = kind Token.Float;
val string = kind Token.String;
val alt_string = kind Token.AltString;
val verbatim = kind Token.Verbatim;
val sync = kind Token.Sync;
val eof = kind Token.EOF;

fun keyword_with pred = RESET_VALUE (Scan.one (Token.keyword_with pred) >> Token.content_of);
val keyword_ident_or_symbolic = keyword_with Token.ident_or_symbolic;

fun $$$ x =
  group (fn () => Token.str_of_kind Token.Keyword ^ " " ^ quote x)
    (keyword_with (fn y => x = y));

fun reserved x =
  group (fn () => "reserved identifier " ^ quote x)
    (RESET_VALUE (Scan.one (Token.ident_with (fn y => x = y)) >> Token.content_of));

val semicolon = $$$ ";";

val minus = sym_ident :-- (fn "-" => Scan.succeed () | _ => Scan.fail) >> #1;
val underscore = sym_ident :-- (fn "_" => Scan.succeed () | _ => Scan.fail) >> #1;
fun maybe scan = underscore >> K NONE || scan >> SOME;

val nat = number >> (#1 o Library.read_int o Symbol.explode);
val int = Scan.optional (minus >> K ~1) 1 -- nat >> op *;
val real = float_number >> (the o Real.fromString) || int >> Real.fromInt;

val tag_name = group (fn () => "tag name") (short_ident || string);
val tags = Scan.repeat ($$$ "%" |-- !!! tag_name);

val opt_unit = Scan.optional ($$$ "(" -- $$$ ")" >> (K ())) ();
fun opt_keyword s = Scan.optional ($$$ "(" |-- !!! (($$$ s >> K true) --| $$$ ")")) false;

val begin = $$$ "begin";
val opt_begin = Scan.optional (begin >> K true) false;


(* enumerations *)

fun enum1 sep scan = scan ::: Scan.repeat ($$$ sep |-- !!! scan);
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun enum1' sep scan = scan ::: Scan.repeat (Scan.lift ($$$ sep) |-- scan);
fun enum' sep scan = enum1' sep scan || Scan.succeed [];

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;

fun and_list1' scan = enum1' "and" scan;
fun and_list' scan = enum' "and" scan;

fun list1 scan = enum1 "," scan;
fun list scan = enum "," scan;

val properties = $$$ "(" |-- !!! (list (string -- ($$$ "=" |-- string)) --| $$$ ")");


(* names and text *)

val name = group (fn () => "name declaration") (short_ident || sym_ident || string || number);

val binding = position name >> Binding.make;

val xname = group (fn () => "name reference")
  (short_ident || long_ident || sym_ident || string || number);

val text = group (fn () => "text")
  (short_ident || long_ident || sym_ident || string || number || verbatim);

val path = group (fn () => "file name/path specification") name >> Path.explode;

val liberal_name = keyword_ident_or_symbolic || xname;

val parname = Scan.optional ($$$ "(" |-- name --| $$$ ")") "";
val parbinding = Scan.optional ($$$ "(" |-- binding --| $$$ ")") Binding.empty;


(* sorts and arities *)

val sort = group (fn () => "sort") (inner_syntax xname);

val arity = xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;

val multi_arity = and_list1 xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;


(* types *)

val typ_group =
  group (fn () => "type")
    (short_ident || long_ident || sym_ident || type_ident || type_var || string || number);

val typ = inner_syntax typ_group;

fun type_arguments arg =
  arg >> single ||
  $$$ "(" |-- !!! (list1 arg --| $$$ ")") ||
  Scan.succeed [];

val type_args = type_arguments type_ident;
val type_args_constrained = type_arguments (type_ident -- Scan.option ($$$ "::" |-- !!! sort));


(* mixfix annotations *)

val mfix = string --
  !!! (Scan.optional ($$$ "[" |-- !!! (list nat --| $$$ "]")) [] --
    Scan.optional nat 1000) >> (Mixfix o triple2);

val infx = $$$ "infix" |-- !!! (string -- nat >> Infix);
val infxl = $$$ "infixl" |-- !!! (string -- nat >> Infixl);
val infxr = $$$ "infixr" |-- !!! (string -- nat >> Infixr);

val binder = $$$ "binder" |--
  !!! (string -- ($$$ "[" |-- nat --| $$$ "]" -- nat || nat >> (fn n => (n, n))))
  >> (Binder o triple2);

fun annotation guard fix = $$$ "(" |-- guard (fix --| $$$ ")");
fun opt_annotation guard fix = Scan.optional (annotation guard fix) NoSyn;

val mixfix = annotation !!! (mfix || binder || infxl || infxr || infx);
val mixfix' = annotation I (mfix || binder || infxl || infxr || infx);
val opt_mixfix = opt_annotation !!! (mfix || binder || infxl || infxr || infx);
val opt_mixfix' = opt_annotation I (mfix || binder || infxl || infxr || infx);


(* fixes *)

val where_ = $$$ "where";

val const_decl = name -- ($$$ "::" |-- !!! typ) -- opt_mixfix >> triple1;
val const_binding = binding -- ($$$ "::" |-- !!! typ) -- opt_mixfix >> triple1;

val params = Scan.repeat1 binding -- Scan.option ($$$ "::" |-- !!! typ)
  >> (fn (xs, T) => map (rpair T) xs);

val simple_fixes = and_list1 params >> flat;

val fixes =
  and_list1 (binding -- Scan.option ($$$ "::" |-- typ) -- mixfix' >> (single o triple1) ||
    params >> map (fn (x, y) => (x, y, NoSyn))) >> flat;

val for_fixes = Scan.optional ($$$ "for" |-- !!! fixes) [];


(* embedded source text *)

val ML_source = source_position (group (fn () => "ML source") text);
val doc_source = source_position (group (fn () => "document source") text);


(* terms *)

val tm = short_ident || long_ident || sym_ident || term_var || number || string;

val term_group = group (fn () => "term") tm;
val prop_group = group (fn () => "proposition") tm;

val term = inner_syntax term_group;
val prop = inner_syntax prop_group;

val type_const = inner_syntax (group (fn () => "type constructor") xname);
val const = inner_syntax (group (fn () => "constant") xname);

val literal_fact = inner_syntax (group (fn () => "literal fact") alt_string);


(* patterns *)

val is_terms = Scan.repeat1 ($$$ "is" |-- term);
val is_props = Scan.repeat1 ($$$ "is" |-- prop);

val propp = prop -- Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];
val termp = term -- Scan.optional ($$$ "(" |-- !!! (is_terms --| $$$ ")")) [];


(* targets *)

val target = ($$$ "(" -- $$$ "in") |-- !!! (position xname --| $$$ ")");
val opt_target = Scan.option target;

end;

type 'a parser = 'a Parse.parser;
type 'a context_parser = 'a Parse.context_parser;

