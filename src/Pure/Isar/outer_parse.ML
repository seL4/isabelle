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
  val $$$ : string -> token list -> string * token list
  val position: (token list -> 'a * 'b) -> token list -> ('a * Position.T) * 'b
  val command: token list -> string * token list
  val keyword: token list -> string * token list
  val short_ident: token list -> string * token list
  val long_ident: token list -> string * token list
  val sym_ident: token list -> string * token list
  val term_var: token list -> string * token list
  val text_var: token list -> string * token list
  val type_ident: token list -> string * token list
  val type_var: token list -> string * token list
  val number: token list -> string * token list
  val string: token list -> string * token list
  val verbatim: token list -> string * token list
  val sync: token list -> string * token list
  val eof: token list -> string * token list
  val not_eof: token list -> token * token list
  val nat: token list -> int * token list
  val enum: string -> (token list -> 'a * token list) -> token list -> 'a list * token list
  val enum1: string -> (token list -> 'a * token list) -> token list -> 'a list * token list
  val list: (token list -> 'a * token list) -> token list -> 'a list * token list
  val list1: (token list -> 'a * token list) -> token list -> 'a list * token list
  val and_list: (token list -> 'a * token list) -> token list -> 'a list * token list
  val and_list1: (token list -> 'a * token list) -> token list -> 'a list * token list
  val name: token list -> bstring * token list
  val xname: token list -> xstring * token list
  val text: token list -> string * token list
  val comment: token list -> Comment.text * token list
  val marg_comment: token list -> Comment.text * token list
  val interest: token list -> Comment.interest * token list
  val sort: token list -> xsort * token list
  val arity: token list -> (xsort list * xsort) * token list
  val simple_arity: token list -> (xsort list * xclass) * token list
  val type_args: token list -> string list * token list
  val typ: token list -> string * token list
  val opt_infix: token list -> Syntax.mixfix * token list
  val opt_mixfix: token list -> Syntax.mixfix * token list
  val const: token list -> (bstring * string * Syntax.mixfix) * token list
  val term: token list -> string * token list
  val prop: token list -> string * token list
  val propp: token list -> (string * (string list * string list)) * token list
  val termp: token list -> (string * string list) * token list
  val attribs: token list -> Args.src list * token list
  val opt_attribs: token list -> Args.src list * token list
  val thm_name: string -> token list -> (bstring * Args.src list) * token list
  val opt_thm_name: string -> token list -> (bstring * Args.src list) * token list
  val spec_name: token list -> ((bstring * string) * Args.src list) * token list
  val spec_opt_name: token list -> ((bstring * string) * Args.src list) * token list
  val xthm: token list -> (xstring * Args.src list) * token list
  val xthms1: token list -> (xstring * Args.src list) list * token list
  val method: token list -> Method.text * token list
  val triple1: ('a * 'b) * 'c -> 'a * 'b * 'c
  val triple2: 'a * ('b * 'c) -> 'a * 'b * 'c
  val triple_swap: ('a * 'b) * 'c -> ('a * 'c) * 'b
end;

structure OuterParse: OUTER_PARSE =
struct

type token = OuterLex.token;


(** error handling **)

(* group atomic parsers (no cuts!) *)

fun fail_with s = Scan.fail_with
  (fn [] => s ^ " expected (past end-of-file!)"
    | (tok :: _) => s ^ " expected,\nbut " ^ OuterLex.name_of tok ^ " " ^
      quote (OuterLex.val_of tok) ^ OuterLex.pos_of tok ^ " was found");

fun group s scan = scan || fail_with s;


(* cut *)

fun !!! scan =
  let
    fun get_pos [] = " (past end-of-file!)"
      | get_pos (tok :: _) = OuterLex.pos_of tok;

    fun err (toks, None) = "Outer syntax error" ^ get_pos toks
      | err (toks, Some msg) = "Outer syntax error" ^ get_pos toks ^ ": " ^ msg;
  in Scan.!! err scan end;



(** basic parsers **)

(* utils *)

fun triple1 ((x, y), z) = (x, y, z);
fun triple2 (x, (y, z)) = (x, y, z);
fun triple_swap ((x, y), z) = ((x, z), y);


(* tokens *)

fun position scan =
  (Scan.ahead (Scan.one OuterLex.not_eof) >> OuterLex.position_of) -- scan >> Library.swap;

fun kind k =
  group (OuterLex.str_of_kind k)
    (Scan.one (OuterLex.is_kind k) >> OuterLex.val_of);

val command = kind OuterLex.Command;
val keyword = kind OuterLex.Keyword;
val short_ident = kind OuterLex.Ident;
val long_ident = kind OuterLex.LongIdent;
val sym_ident = kind OuterLex.SymIdent;
val term_var = kind OuterLex.Var;
val text_var = kind OuterLex.TextVar;
val type_ident = kind OuterLex.TypeIdent;
val type_var = kind OuterLex.TypeVar;
val number = kind OuterLex.Nat;
val string = kind OuterLex.String;
val verbatim = kind OuterLex.Verbatim;
val sync = kind OuterLex.Sync;
val eof = kind OuterLex.EOF;

fun $$$ x =
  group (OuterLex.str_of_kind OuterLex.Keyword ^ " " ^ quote x)
    (Scan.one (OuterLex.keyword_with (equal x)) >> OuterLex.val_of);

val nat = number >> (fst o Term.read_int o Symbol.explode);

val not_eof = Scan.one OuterLex.not_eof;


(* enumerations *)

fun enum1 sep scan = scan -- Scan.repeat ($$$ sep |-- !!! scan) >> op ::;
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun list1 scan = enum1 "," scan;
fun list scan = enum "," scan;

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;


(* names and text *)

val name = group "name declaration" (short_ident || sym_ident || string);
val xname = group "name reference" (short_ident || long_ident || sym_ident || string);
val text = group "text" (short_ident || long_ident || sym_ident || string || verbatim);


(* formal comments *)

val comment = text >> Comment.plain;
val marg_comment = Scan.optional ($$$ "--" |-- comment) Comment.none;

val interest = Scan.optional ($$$ "%%" >> K Comment.no_interest ||
  $$$ "%" |-- Scan.optional nat 1 >> Comment.interest) Comment.default_interest;


(* sorts and arities *)

val sort =
  xname >> single || $$$ "{" |-- !!! (list xname --| $$$ "}");

fun gen_arity cod =
  Scan.optional ($$$ "(" |-- !!! (Scan.repeat1 sort --| $$$ ")")) [] -- cod;

val arity = gen_arity sort;
val simple_arity = gen_arity name;


(* types *)

val typ =
  group "type" (short_ident || long_ident || sym_ident || type_ident || type_var || string);

val type_args =
  type_ident >> single ||
  $$$ "(" |-- !!! (list1 type_ident --| $$$ ")") ||
  Scan.succeed [];


(* mixfix annotations *)

val infxl = $$$ "infixl" |-- !!! (nat >> Syntax.Infixl || string -- nat >> Syntax.InfixlName);
val infxr = $$$ "infixr" |-- !!! (nat >> Syntax.Infixr || string -- nat >> Syntax.InfixrName);

val binder =
  $$$ "binder" |--
    !!! (string -- ($$$ "[" |-- nat --| $$$ "]" -- nat || nat >> (fn n => (n, n))))
  >> (Syntax.Binder o triple2);


val opt_pris = Scan.optional ($$$ "[" |-- !!! (list nat --| $$$ "]")) [];

val mixfix =
  string -- opt_pris -- Scan.optional nat Syntax.max_pri
  >> (Syntax.Mixfix o triple1);

fun opt_fix fix =
  Scan.optional ($$$ "(" |-- !!! (fix --| $$$ ")")) Syntax.NoSyn;

val opt_infix = opt_fix (infxl || infxr);
val opt_mixfix = opt_fix (mixfix || binder || infxl || infxr);


(* consts *)

val const =
  name -- ($$$ "::" |-- !!! (typ -- opt_mixfix)) >> triple2;


(* terms *)

val trm = short_ident || long_ident || sym_ident || term_var || text_var || number || string;

val term = group "term" trm;
val prop = group "proposition" trm;


(* patterns *)

val is_terms = Scan.repeat1 ($$$ "is" |-- term);
val is_props = Scan.repeat1 ($$$ "is" |-- prop);
val concl_props = $$$ "concl" |-- !!! is_props;
val any_props = is_props -- Scan.optional concl_props [] || concl_props >> pair [];

val propp = prop -- Scan.optional ($$$ "(" |-- !!! (any_props --| $$$ ")")) ([], []);
val termp = term -- Scan.optional ($$$ "(" |-- !!! (is_terms --| $$$ ")")) [];


(* arguments *)

fun keyword_symid is_symid = Scan.one (OuterLex.keyword_with is_symid) >> OuterLex.val_of;

fun atom_arg is_symid blk =
  group "argument"
    (position (short_ident || long_ident || sym_ident || term_var || text_var ||
        type_ident || type_var || number) >> Args.ident ||
      position (keyword_symid is_symid) >> Args.keyword ||
      position string >> Args.string ||
      position (if blk then $$$ "," else Scan.fail) >> Args.keyword);

fun paren_args l r scan = position ($$$ l) -- !!! (scan true -- position ($$$ r))
  >> (fn (x, (ys, z)) => Args.keyword x :: ys @ [Args.keyword z]);

fun args is_symid blk x = Scan.optional (args1 is_symid blk) [] x
and args1 is_symid blk x =
  ((Scan.repeat1
    (Scan.repeat1 (atom_arg is_symid blk) ||
      paren_args "(" ")" (args is_symid) ||
      paren_args "{" "}" (args is_symid) ||
      paren_args "[" "]" (args is_symid))) >> flat) x;


(* theorem specifications *)

val attrib = position (xname -- !!! (args OuterLex.is_sid false)) >> Args.src;
val attribs = $$$ "[" |-- !!! (list attrib --| $$$ "]");
val opt_attribs = Scan.optional attribs [];

fun thm_name s = name -- opt_attribs --| $$$ s;
fun opt_thm_name s =
  Scan.optional ((name -- opt_attribs || (attribs >> pair "")) --| $$$ s) ("", []);;

val spec_name = thm_name ":" -- prop >> (fn ((x, y), z) => ((x, z), y));
val spec_opt_name = opt_thm_name ":" -- prop >> (fn ((x, y), z) => ((x, z), y));

val xthm = xname -- opt_attribs;
val xthms1 = Scan.repeat1 xthm;


(* proof methods *)

fun is_symid_meth s =
  s <> "|" andalso s <> "?" andalso s <> "*" andalso s <> "+" andalso OuterLex.is_sid s;

fun meth4 x =
 (position (xname >> rpair []) >> (Method.Source o Args.src) ||
  $$$ "(" |-- !!! (meth0 --| $$$ ")")) x
and meth3 x =
 (meth4 --| $$$ "?" >> Method.Try ||
  meth4 --| $$$ "*" >> Method.Repeat ||
  meth4 --| $$$ "+" >> Method.Repeat1 ||
  meth4) x
and meth2 x =
 (position (xname -- args1 is_symid_meth false) >> (Method.Source o Args.src) ||
  meth3) x
and meth1 x = (enum1 "," meth2 >> (fn [m] => m | ms => Method.Then ms)) x
and meth0 x = (enum1 "|" meth1 >> (fn [m] => m | ms => Method.Orelse ms)) x;

val method = meth3;


end;
