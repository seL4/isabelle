(*  Title:      Pure/Isar/outer_parse.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)

signature OUTER_PARSE =
sig
  type token
  val group: string -> (token list -> 'a) -> token list -> 'a
  val !!! : (token list -> 'a) -> token list -> 'a
  val !!!! : (token list -> 'a) -> token list -> 'a
  val triple1: ('a * 'b) * 'c -> 'a * 'b * 'c
  val triple2: 'a * ('b * 'c) -> 'a * 'b * 'c
  val triple_swap: ('a * 'b) * 'c -> ('a * 'c) * 'b
  val not_eof: token list -> token * token list
  val position: (token list -> 'a * 'b) -> token list -> ('a * Position.T) * 'b
  val command: token list -> string * token list
  val keyword: token list -> string * token list
  val short_ident: token list -> string * token list
  val long_ident: token list -> string * token list
  val sym_ident: token list -> string * token list
  val minus: token list -> string * token list
  val term_var: token list -> string * token list
  val type_ident: token list -> string * token list
  val type_var: token list -> string * token list
  val number: token list -> string * token list
  val string: token list -> string * token list
  val alt_string: token list -> string * token list
  val verbatim: token list -> string * token list
  val sync: token list -> string * token list
  val eof: token list -> string * token list
  val $$$ : string -> token list -> string * token list
  val reserved : string -> token list -> string * token list
  val semicolon: token list -> string * token list
  val underscore: token list -> string * token list
  val maybe: (token list -> 'a * token list) -> token list -> 'a option * token list
  val tag_name: token list -> string * token list
  val tags: token list -> string list * token list
  val opt_unit: token list -> unit * token list
  val opt_keyword: string -> token list -> bool * token list
  val begin: token list -> string * token list
  val opt_begin: token list -> bool * token list
  val nat: token list -> int * token list
  val enum: string -> (token list -> 'a * token list) -> token list -> 'a list * token list
  val enum1: string -> (token list -> 'a * token list) -> token list -> 'a list * token list
  val list: (token list -> 'a * token list) -> token list -> 'a list * token list
  val list1: (token list -> 'a * token list) -> token list -> 'a list * token list
  val and_list: (token list -> 'a * token list) -> token list -> 'a list * token list
  val and_list1: (token list -> 'a * token list) -> token list -> 'a list * token list
  val properties: token list -> Markup.property list * token list
  val name: token list -> bstring * token list
  val xname: token list -> xstring * token list
  val text: token list -> string * token list
  val path: token list -> Path.T * token list
  val parname: token list -> string * token list
  val sort: token list -> string * token list
  val arity: token list -> (string * string list * string) * token list
  val multi_arity: token list -> (string list * string list * string) * token list
  val type_args: token list -> string list * token list
  val typ: token list -> string * token list
  val mixfix: token list -> mixfix * token list
  val mixfix': token list -> mixfix * token list
  val opt_infix: token list -> mixfix * token list
  val opt_infix': token list -> mixfix * token list
  val opt_mixfix: token list -> mixfix * token list
  val opt_mixfix': token list -> mixfix * token list
  val where_: token list -> string * token list
  val const: token list -> (string * string * mixfix) * token list
  val params: token list -> (string * string option) list * token list
  val simple_fixes: token list -> (string * string option) list * token list
  val fixes: token list -> (string * string option * mixfix) list * token list
  val for_fixes: token list -> (string * string option * mixfix) list * token list
  val for_simple_fixes: token list -> (string * string option) list * token list
  val term: token list -> string * token list
  val prop: token list -> string * token list
  val propp: token list -> (string * string list) * token list
  val termp: token list -> (string * string list) * token list
  val keyword_sid: token list -> string * token list
  val args: (string -> bool) -> bool -> token list -> Args.T list * token list
  val args1: (string -> bool) -> bool -> token list -> Args.T list * token list
  val arguments: token list -> Args.T list * token list
  val target: token list -> xstring * token list
  val opt_target: token list -> xstring option * token list
end;

structure OuterParse: OUTER_PARSE =
struct

structure T = OuterLex;
type token = T.token;


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

val not_eof = Scan.one T.not_eof;

fun position scan = (Scan.ahead not_eof >> T.position_of) -- scan >> Library.swap;

fun kind k =
  group (T.str_of_kind k) (Scan.one (T.is_kind k) >> T.val_of);

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

fun $$$ x =
  group (T.str_of_kind T.Keyword ^ " " ^ quote x)
    (Scan.one (T.keyword_with (equal x)) >> T.val_of);

fun reserved x =
  group ("Reserved identifier " ^ quote x)
    (Scan.one (T.ident_with (fn y => x = y)) >> T.val_of);

val semicolon = $$$ ";";

val minus = sym_ident :-- (fn "-" => Scan.succeed () | _ => Scan.fail) >> #1;
val underscore = sym_ident :-- (fn "_" => Scan.succeed () | _ => Scan.fail) >> #1;
fun maybe scan = underscore >> K NONE || scan >> SOME;

val nat = number >> (#1 o Library.read_int o Symbol.explode);

val tag_name = group "tag name" (short_ident || string);
val tags = Scan.repeat ($$$ "%" |-- !!! tag_name);

val opt_unit = Scan.optional ($$$ "(" -- $$$ ")" >> (K ())) ();
fun opt_keyword s = Scan.optional ($$$ "(" |-- !!! (($$$ s >> K true) --| $$$ ")")) false;

val begin = $$$ "begin";
val opt_begin = Scan.optional (begin >> K true) false;


(* enumerations *)

fun enum1 sep scan = scan -- Scan.repeat ($$$ sep |-- !!! scan) >> op ::;
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun list1 scan = enum1 "," scan;
fun list scan = enum "," scan;

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;

val properties = $$$ "(" |-- !!! (list1 (string -- ($$$ "=" |-- string)) --| $$$ ")");


(* names and text *)

val name = group "name declaration" (short_ident || sym_ident || string || number);
val xname = group "name reference" (short_ident || long_ident || sym_ident || string || number);
val text = group "text" (short_ident || long_ident || sym_ident || string || number || verbatim);
val path = group "file name/path specification" name >> Path.explode;

val parname = Scan.optional ($$$ "(" |-- name --| $$$ ")") "";


(* sorts and arities *)

val sort = group "sort" xname;

val arity = xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;

val multi_arity = and_list1 xname -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> triple2;


(* types *)

val typ = group "type"
  (short_ident || long_ident || sym_ident || type_ident || type_var || string || number);

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

val params = Scan.repeat1 name -- Scan.option ($$$ "::" |-- !!! typ)
  >> (fn (xs, T) => map (rpair T) xs);

val simple_fixes = and_list1 params >> flat;

val fixes =
  and_list1 (name -- Scan.option ($$$ "::" |-- typ) -- mixfix >> (single o triple1) ||
    params >> map Syntax.no_syn) >> flat;

val for_fixes = Scan.optional ($$$ "for" |-- !!! fixes) [];
val for_simple_fixes = Scan.optional ($$$ "for" |-- !!! simple_fixes) [];


(* terms *)

val trm = short_ident || long_ident || sym_ident || term_var || number || string;

val term = group "term" trm;
val prop = group "proposition" trm;


(* patterns *)

val is_terms = Scan.repeat1 ($$$ "is" |-- term);
val is_props = Scan.repeat1 ($$$ "is" |-- prop);

val propp = prop -- Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];
val termp = term -- Scan.optional ($$$ "(" |-- !!! (is_terms --| $$$ ")")) [];


(* arguments *)

fun keyword_symid is_symid = Scan.one (T.keyword_with is_symid) >> T.val_of;
val keyword_sid = keyword_symid T.is_sid;

fun atom_arg is_symid blk =
  group "argument"
    (position (short_ident || long_ident || sym_ident || term_var ||
        type_ident || type_var || number) >> Args.mk_ident ||
      position (keyword_symid is_symid) >> Args.mk_keyword ||
      position (string || verbatim) >> Args.mk_string ||
      position alt_string >> Args.mk_alt_string ||
      position (if blk then $$$ "," else Scan.fail) >> Args.mk_keyword);

fun paren_args l r scan = position ($$$ l) -- !!! (scan true -- position ($$$ r))
  >> (fn (x, (ys, z)) => Args.mk_keyword x :: ys @ [Args.mk_keyword z]);

fun args is_symid blk x = Scan.optional (args1 is_symid blk) [] x
and args1 is_symid blk x =
  ((Scan.repeat1
    (Scan.repeat1 (atom_arg is_symid blk) ||
      paren_args "(" ")" (args is_symid) ||
      paren_args "[" "]" (args is_symid))) >> flat) x;

val arguments = args T.is_sid false;


(* targets *)

val target = ($$$ "(" -- $$$ "in") |-- !!! (xname --| $$$ ")");
val opt_target = Scan.option target;

end;
