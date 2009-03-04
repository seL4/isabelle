(*  Title:      Pure/Isar/outer_parse.ML
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)

signature OUTER_PARSE =
sig
  type token = OuterLex.token
  type 'a parser = token list -> 'a * token list
  val group: string -> (token list -> 'a) -> token list -> 'a
  val !!! : (token list -> 'a) -> token list -> 'a
  val !!!! : (token list -> 'a) -> token list -> 'a
  val triple1: ('a * 'b) * 'c -> 'a * 'b * 'c
  val triple2: 'a * ('b * 'c) -> 'a * 'b * 'c
  val triple_swap: ('a * 'b) * 'c -> ('a * 'c) * 'b
  val not_eof: token parser
  val position: (token list -> 'a * 'b) -> token list -> ('a * Position.T) * 'b
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
  val enum: string -> 'a parser -> 'a list parser
  val enum1: string -> 'a parser -> 'a list parser
  val and_list: 'a parser -> 'a list parser
  val and_list1: 'a parser -> 'a list parser
  val enum': string -> ('a * token list -> 'b * ('a * token list)) ->
    'a * token list -> 'b list * ('a * token list)
  val enum1': string -> ('a * token list -> 'b * ('a * token list)) ->
    'a * token list -> 'b list * ('a * token list)
  val and_list': ('a * token list -> 'b * ('a * token list)) ->
    'a * token list -> 'b list * ('a * token list)
  val and_list1': ('a * token list -> 'b * ('a * token list)) ->
    'a * token list -> 'b list * ('a * token list)
  val list: 'a parser -> 'a list parser
  val list1: 'a parser -> 'a list parser
  val name: bstring parser
  val binding: binding parser
  val xname: xstring parser
  val text: string parser
  val path: Path.T parser
  val parname: string parser
  val parbinding: binding parser
  val sort: string parser
  val arity: (string * string list * string) parser
  val multi_arity: (string list * string list * string) parser
  val type_args: string list parser
  val typ_group: string parser
  val typ: string parser
  val mixfix: mixfix parser
  val mixfix': mixfix parser
  val opt_infix: mixfix parser
  val opt_infix': mixfix parser
  val opt_mixfix: mixfix parser
  val opt_mixfix': mixfix parser
  val where_: string parser
  val const: (string * string * mixfix) parser
  val params: (binding * string option) list parser
  val simple_fixes: (binding * string option) list parser
  val fixes: (binding * string option * mixfix) list parser
  val for_fixes: (binding * string option * mixfix) list parser
  val for_simple_fixes: (binding * string option) list parser
  val ML_source: (SymbolPos.text * Position.T) parser
  val doc_source: (SymbolPos.text * Position.T) parser
  val term_group: string parser
  val prop_group: string parser
  val term: string parser
  val prop: string parser
  val propp: (string * string list) parser
  val termp: (string * string list) parser
  val target: xstring parser
  val opt_target: xstring option parser
end;

structure OuterParse: OUTER_PARSE =
struct

structure T = OuterLex;
type token = T.token;

type 'a parser = token list -> 'a * token list;


(** error handling **)

(* group atomic parsers (no cuts!) *)

fun fail_with s = Scan.fail_with
  (fn [] => s ^ " expected (past end-of-file!)"
    | (tok :: _) =>
        (case T.text_of tok of
          (txt, "") => s ^ " expected,\nbut " ^ txt ^ T.pos_of tok ^ " was found"
        | (txt1, txt2) => s ^ " expected,\nbut " ^ txt1 ^ T.pos_of tok ^ " was found:\n" ^ txt2));

fun group s scan = scan || fail_with s;


(* cut *)

fun cut kind scan =
  let
    fun get_pos [] = " (past end-of-file!)"
      | get_pos (tok :: _) = T.pos_of tok;

    fun err (toks, NONE) = kind ^ get_pos toks
      | err (toks, SOME msg) =
          if String.isPrefix kind msg then msg
          else kind ^ get_pos toks ^ ": " ^ msg;
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
  Scan.ahead (Scan.one (K true)) -- atom >> (fn (arg, x) => (T.assign NONE arg; x));


val not_eof = RESET_VALUE (Scan.one T.not_eof);

fun position scan = (Scan.ahead not_eof >> T.position_of) -- scan >> Library.swap;
fun source_position atom = Scan.ahead atom |-- not_eof >> T.source_position_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> T.source_of;

fun kind k =
  group (T.str_of_kind k) (RESET_VALUE (Scan.one (T.is_kind k) >> T.content_of));

val command = kind T.Command;
val keyword = kind T.Keyword;
val short_ident = kind T.Ident;
val long_ident = kind T.LongIdent;
val sym_ident = kind T.SymIdent;
val term_var = kind T.Var;
val type_ident = kind T.TypeIdent;
val type_var = kind T.TypeVar;
val number = kind T.Nat;
val string = kind T.String;
val alt_string = kind T.AltString;
val verbatim = kind T.Verbatim;
val sync = kind T.Sync;
val eof = kind T.EOF;

fun keyword_with pred = RESET_VALUE (Scan.one (T.keyword_with pred) >> T.content_of);
val keyword_ident_or_symbolic = keyword_with T.ident_or_symbolic;

fun $$$ x =
  group (T.str_of_kind T.Keyword ^ " " ^ quote x) (keyword_with (fn y => x = y));

fun reserved x =
  group ("reserved identifier " ^ quote x)
    (RESET_VALUE (Scan.one (T.ident_with (fn y => x = y)) >> T.content_of));

val semicolon = $$$ ";";

val minus = sym_ident :-- (fn "-" => Scan.succeed () | _ => Scan.fail) >> #1;
val underscore = sym_ident :-- (fn "_" => Scan.succeed () | _ => Scan.fail) >> #1;
fun maybe scan = underscore >> K NONE || scan >> SOME;

val nat = number >> (#1 o Library.read_int o Symbol.explode);
val int = Scan.optional (minus >> K ~1) 1 -- nat >> op *;

val tag_name = group "tag name" (short_ident || string);
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


(* names and text *)

val name = group "name declaration" (short_ident || sym_ident || string || number);
val binding = position name >> Binding.make;
val xname = group "name reference" (short_ident || long_ident || sym_ident || string || number);
val text = group "text" (short_ident || long_ident || sym_ident || string || number || verbatim);
val path = group "file name/path specification" name >> Path.explode;

val parname = Scan.optional ($$$ "(" |-- name --| $$$ ")") "";
val parbinding = Scan.optional ($$$ "(" |-- binding --| $$$ ")") Binding.empty;


(* sorts and arities *)

val sort = group "sort" (inner_syntax xname);

val arity = xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;

val multi_arity = and_list1 xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;


(* types *)

val typ_group = group "type"
  (short_ident || long_ident || sym_ident || type_ident || type_var || string || number);

val typ = inner_syntax typ_group;

val type_args =
  type_ident >> single ||
  $$$ "(" |-- !!! (list1 type_ident --| $$$ ")") ||
  Scan.succeed [];


(* mixfix annotations *)

val mfix = string --
  !!! (Scan.optional ($$$ "[" |-- !!! (list nat --| $$$ "]")) [] --
    Scan.optional nat Syntax.max_pri) >> (Mixfix o triple2);

val infx = $$$ "infix" |-- !!! (nat >> Infix || string -- nat >> InfixName);
val infxl = $$$ "infixl" |-- !!! (nat >> Infixl || string -- nat >> InfixlName);
val infxr = $$$ "infixr" |-- !!! (nat >> Infixr || string -- nat >> InfixrName);

val binder = $$$ "binder" |--
  !!! (string -- ($$$ "[" |-- nat --| $$$ "]" -- nat || nat >> (fn n => (n, n))))
  >> (Binder o triple2);

fun annotation guard fix = $$$ "(" |-- guard (fix --| $$$ ")");
fun opt_annotation guard fix = Scan.optional (annotation guard fix) NoSyn;

val mixfix = annotation !!! (mfix || binder || infxl || infxr || infx);
val mixfix' = annotation I (mfix || binder || infxl || infxr || infx);
val opt_infix = opt_annotation !!! (infxl || infxr || infx);
val opt_infix' = opt_annotation I (infxl || infxr || infx);
val opt_mixfix = opt_annotation !!! (mfix || binder || infxl || infxr || infx);
val opt_mixfix' = opt_annotation I (mfix || binder || infxl || infxr || infx);


(* fixes *)

val where_ = $$$ "where";

val const = name -- ($$$ "::" |-- !!! typ) -- opt_mixfix >> triple1;

val params = Scan.repeat1 binding -- Scan.option ($$$ "::" |-- !!! typ)
  >> (fn (xs, T) => map (rpair T) xs);

val simple_fixes = and_list1 params >> flat;

val fixes =
  and_list1 (binding -- Scan.option ($$$ "::" |-- typ) -- mixfix >> (single o triple1) ||
    params >> map Syntax.no_syn) >> flat;

val for_fixes = Scan.optional ($$$ "for" |-- !!! fixes) [];
val for_simple_fixes = Scan.optional ($$$ "for" |-- !!! simple_fixes) [];


(* embedded source text *)

val ML_source = source_position (group "ML source" text);
val doc_source = source_position (group "document source" text);


(* terms *)

val trm = short_ident || long_ident || sym_ident || term_var || number || string;

val term_group = group "term" trm;
val prop_group = group "proposition" trm;

val term = inner_syntax term_group;
val prop = inner_syntax prop_group;


(* patterns *)

val is_terms = Scan.repeat1 ($$$ "is" |-- term);
val is_props = Scan.repeat1 ($$$ "is" |-- prop);

val propp = prop -- Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];
val termp = term -- Scan.optional ($$$ "(" |-- !!! (is_terms --| $$$ ")")) [];


(* targets *)

val target = ($$$ "(" -- $$$ "in") |-- !!! (xname --| $$$ ")");
val opt_target = Scan.option target;

end;
