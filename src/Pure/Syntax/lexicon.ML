(*  Title:      Pure/Syntax/lexicon.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Lexer for the inner Isabelle syntax (terms and types).
*)

signature LEXICON =
sig
  structure Syntax:
  sig
    val const: string -> term
    val free: string -> term
    val var: indexname -> term
  end
  val scan_id: Symbol_Pos.T list scanner
  val scan_longid: Symbol_Pos.T list scanner
  val scan_tid: Symbol_Pos.T list scanner
  val scan_hex: Symbol_Pos.T list scanner
  val scan_bin: Symbol_Pos.T list scanner
  val scan_var: Symbol_Pos.T list scanner
  val scan_tvar: Symbol_Pos.T list scanner
  val is_tid: string -> bool
  datatype token_kind =
    Literal | Ident | Long_Ident | Var | Type_Ident | Type_Var | Num | Float | Str |
    String | Cartouche | Space | Comment of Comment.kind | Dummy | EOF
  eqtype token
  val kind_of_token: token -> token_kind
  val str_of_token: token -> string
  val pos_of_token: token -> Position.T
  val end_pos_of_token: token -> Position.T
  val is_proper: token -> bool
  val dummy: token
  val literal: string -> token
  val is_literal: token -> bool
  val tokens_match_ord: token ord
  val mk_eof: Position.T -> token
  val eof: token
  val is_eof: token -> bool
  val stopper: token Scan.stopper
  val terminals: string list
  val is_terminal: string -> bool
  val get_terminal: string -> token option
  val suppress_literal_markup: string -> bool
  val suppress_markup: token -> bool
  val literal_markup: string -> Markup.T list
  val reports_of_token: token -> Position.report list
  val reported_token_range: Proof.context -> token -> string
  val valued_token: token -> bool
  val implode_string: Symbol.symbol list -> string
  val explode_string: string * Position.T -> Symbol_Pos.T list
  val implode_str: Symbol.symbol list -> string
  val explode_str: string * Position.T -> Symbol_Pos.T list
  val tokenize: Scan.lexicon -> bool -> Symbol_Pos.T list -> token list
  val read_indexname: string -> indexname
  val read_var: string -> term
  val read_variable: string -> indexname option
  val read_nat: string -> int option
  val read_int: string -> int option
  val read_num: string -> {radix: int, leading_zeros: int, value: int}
  val read_float: string -> {mant: int, exp: int}
  val mark_class: string -> string val unmark_class: string -> string
  val mark_type: string -> string val unmark_type: string -> string
  val mark_const: string -> string val unmark_const: string -> string
  val mark_fixed: string -> string val unmark_fixed: string -> string
  val unmark:
   {case_class: string -> 'a,
    case_type: string -> 'a,
    case_const: string -> 'a,
    case_fixed: string -> 'a,
    case_default: string -> 'a} -> string -> 'a
  val is_marked: string -> bool
  val dummy_type: term
  val fun_type: term
end;

structure Lexicon: LEXICON =
struct

(** syntactic terms **)

structure Syntax =
struct

fun const c = Const (c, dummyT);
fun free x = Free (x, dummyT);
fun var xi = Var (xi, dummyT);

end;



(** basic scanners **)

open Basic_Symbol_Pos;

val err_prefix = "Inner lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);

val scan_id = Symbol_Pos.scan_ident;
val scan_longid = scan_id @@@ Scan.repeats1 ($$$ "." @@@ scan_id);
val scan_tid = $$$ "'" @@@ scan_id;

val scan_hex = $$$ "0" @@@ $$$ "x" @@@ Scan.many1 (Symbol.is_ascii_hex o Symbol_Pos.symbol);
val scan_bin = $$$ "0" @@@ $$$ "b" @@@ Scan.many1 (fn (s, _) => s = "0" orelse s = "1");
val scan_num = scan_hex || scan_bin || Symbol_Pos.scan_nat;

val scan_id_nat = scan_id @@@ Scan.optional ($$$ "." @@@ Symbol_Pos.scan_nat) [];
val scan_var = $$$ "?" @@@ scan_id_nat;
val scan_tvar = $$$ "?" @@@ $$$ "'" @@@ scan_id_nat;

fun is_tid s =
  (case try (unprefix "'") s of
    SOME s' => Symbol_Pos.is_identifier s'
  | NONE => false);



(** tokens **)

(* datatype token_kind *)

datatype token_kind =
  Literal | Ident | Long_Ident | Var | Type_Ident | Type_Var | Num | Float | Str |
  String | Cartouche | Space | Comment of Comment.kind | Dummy | EOF;

val token_kinds =
  Vector.fromList
   [Literal, Ident, Long_Ident, Var, Type_Ident, Type_Var, Num, Float, Str,
    String, Cartouche, Space, Comment Comment.Comment, Comment Comment.Cancel,
    Comment Comment.Latex, Dummy, EOF];

fun token_kind i = Vector.sub (token_kinds, i);
fun token_kind_index k = #1 (the (Vector.findi (fn (_, k') => k = k') token_kinds));


(* datatype token *)

datatype token = Token of int * string * Position.range;

fun index_of_token (Token (i, _, _)) = i;
val kind_of_token = index_of_token #> token_kind;
fun str_of_token (Token (_, s, _)) = s;
fun pos_of_token (Token (_, _, (pos, _))) = pos;
fun end_pos_of_token (Token (_, _, (_, end_pos))) = end_pos;

val is_proper = kind_of_token #> (fn Space => false | Comment _ => false | _ => true);

val dummy = Token (token_kind_index Dummy, "", Position.no_range);


(* literals *)

val literal_index = token_kind_index Literal;
fun literal s = Token (literal_index, s, Position.no_range);
fun is_literal tok = index_of_token tok = literal_index;

fun tokens_match_ord toks =
  let val is = apply2 index_of_token toks in
    (case int_ord is of
      EQUAL => if #1 is = literal_index then fast_string_ord (apply2 str_of_token toks) else EQUAL
    | ord => ord)
  end;


(* stopper *)

val eof_index = token_kind_index EOF;
fun mk_eof pos = Token (eof_index, "", (pos, Position.none));
val eof = mk_eof Position.none;

fun is_eof tok = index_of_token tok = eof_index;
val stopper = Scan.stopper (K eof) is_eof;


(* terminal symbols *)

val terminal_symbols =
  [("id", Ident),
   ("longid", Long_Ident),
   ("var", Var),
   ("tid", Type_Ident),
   ("tvar", Type_Var),
   ("num_token", Num),
   ("float_token", Float),
   ("str_token", Str),
   ("string_token", String),
   ("cartouche", Cartouche)]
  |> map (apsnd token_kind_index)
  |> Symtab.make;

val terminals = Symtab.keys terminal_symbols;
val is_terminal = Symtab.defined terminal_symbols;
fun get_terminal s =
  (case Symtab.lookup terminal_symbols s of
    SOME i => SOME (Token (i, s, Position.no_range))
  | NONE => NONE);


(* markup *)

val suppress_literal_markup = Symbol.has_control_block o Symbol.explode;
fun suppress_markup tok = is_literal tok andalso suppress_literal_markup (str_of_token tok);

fun literal_markup s =
  let val syms = Symbol.explode s in
    if Symbol.has_control_block syms then []
    else if Symbol.is_ascii_identifier s orelse exists Symbol.is_letter syms
    then [Markup.literal]
    else [Markup.delimiter]
  end;

val token_kind_markup =
 fn Type_Ident => [Markup.tfree]
  | Type_Var => [Markup.tvar]
  | Num => [Markup.numeral]
  | Float => [Markup.numeral]
  | Str => [Markup.inner_string]
  | String => [Markup.inner_string]
  | Cartouche => [Markup.inner_cartouche]
  | Comment _ => [Markup.comment1]
  | _ => [];

fun reports_of_token tok =
  let
    val pos = pos_of_token tok;
    val markups =
      if is_literal tok then literal_markup (str_of_token tok)
      else token_kind_markup (kind_of_token tok);
  in map (pair pos) markups end;

fun reported_token_range ctxt tok =
  if is_proper tok
  then Context_Position.reported_text ctxt (pos_of_token tok) Markup.token_range ""
  else "";


(* valued_token *)

fun valued_token tok =
  not (is_literal tok orelse is_eof tok);



(** string literals **)

fun explode_literal scan_body (str, pos) =
  (case Scan.read Symbol_Pos.stopper scan_body (Symbol_Pos.explode (str, pos)) of
    SOME ss => ss
  | _ => error (err_prefix ^ "malformed string literal " ^ quote str ^ Position.here pos));


(* string *)

val scan_string = Scan.trace (Symbol_Pos.scan_string_qq err_prefix) >> #2;
val scan_string_body = Symbol_Pos.scan_string_qq err_prefix >> (#1 o #2);

fun implode_string ss = quote (implode (map (fn "\"" => "\\\"" | s => s) ss));
val explode_string = explode_literal scan_string_body;


(* str *)

val scan_chr =
  $$ "\\" |-- $$$ "'" ||
  Scan.one
    ((fn s => s <> "\\" andalso s <> "'" andalso Symbol.not_eof s) o
      Symbol_Pos.symbol) >> single ||
  $$$ "'" --| Scan.ahead (~$$ "'");

val scan_str =
  Scan.ahead ($$ "'" -- $$ "'") |--
    !!! "unclosed string literal"
      ($$$ "'" @@@ $$$ "'" @@@ Scan.repeats scan_chr @@@ $$$ "'" @@@ $$$ "'");

val scan_str_body =
  Scan.ahead ($$ "'" |-- $$ "'") |--
    !!! "unclosed string literal"
      ($$ "'" |-- $$ "'" |-- Scan.repeats scan_chr --| $$ "'" --| $$ "'");

fun implode_str ss = enclose "''" "''" (implode (map (fn "'" => "\\'" | s => s) ss));
val explode_str = explode_literal scan_str_body;



(** tokenize **)

val token_leq = op <= o apply2 str_of_token;

fun token kind =
  let val i = token_kind_index kind
  in fn ss => Token (i, Symbol_Pos.content ss, Symbol_Pos.range ss) end;

fun tokenize lex xids syms =
  let
    val scan_xid =
      (if xids then $$$ "_" @@@ scan_id || scan_id else scan_id) ||
      $$$ "_" @@@ $$$ "_";

    val scan_val =
      scan_tvar >> token Type_Var ||
      scan_var >> token Var ||
      scan_tid >> token Type_Ident ||
      Symbol_Pos.scan_float >> token Float ||
      scan_num >> token Num ||
      scan_longid >> token Long_Ident ||
      scan_xid >> token Ident;

    val scan_lit = Scan.literal lex >> token Literal;

    val scan =
      Symbol_Pos.scan_cartouche err_prefix >> token Cartouche ||
      Comment.scan_inner >> (fn (kind, ss) => token (Comment kind) ss) ||
      Scan.max token_leq scan_lit scan_val ||
      scan_string >> token String ||
      scan_str >> token Str ||
      Scan.many1 (Symbol.is_blank o Symbol_Pos.symbol) >> token Space;
  in
    (case Scan.error (Scan.finite Symbol_Pos.stopper (Scan.repeat scan)) syms of
      (toks, []) => toks
    | (_, ss) =>
        error ("Inner lexical error" ^ Position.here (#1 (Symbol_Pos.range ss)) ^
          Markup.markup Markup.no_report ("\nat " ^ quote (Symbol_Pos.content ss))))
  end;



(** scan variables **)

(* scan_indexname *)

local

val scan_vname =
  let
    fun nat n [] = n
      | nat n (c :: cs) = nat (n * 10 + (ord c - Char.ord #"0")) cs;

    fun idxname cs ds = (implode (rev cs), nat 0 ds);
    fun chop_idx [] ds = idxname [] ds
      | chop_idx (cs as (_ :: "\<^sub>" :: _)) ds = idxname cs ds
      | chop_idx (c :: cs) ds =
          if Symbol.is_digit c then chop_idx cs (c :: ds)
          else idxname (c :: cs) ds;

    val scan =
      (scan_id >> map Symbol_Pos.symbol) --
      Scan.optional ($$ "." |-- Symbol_Pos.scan_nat >> (nat 0 o map Symbol_Pos.symbol)) ~1;
  in
    scan >>
      (fn (cs, ~1) => chop_idx (rev cs) []
        | (cs, i) => (implode cs, i))
  end;

in

val scan_indexname = $$ "'" |-- scan_vname >> (fn (x, i) => ("'" ^ x, i)) || scan_vname;

end;


(* indexname *)

fun read_indexname s =
  (case Scan.read Symbol_Pos.stopper scan_indexname (Symbol_Pos.explode0 s) of
    SOME xi => xi
  | _ => error ("Lexical error in variable name: " ^ quote s));


(* read_var *)

fun read_var str =
  let
    val scan =
      $$ "?" |-- scan_indexname --| Scan.ahead (Scan.one Symbol_Pos.is_eof)
        >> Syntax.var ||
      Scan.many (Symbol.not_eof o Symbol_Pos.symbol)
        >> (Syntax.free o implode o map Symbol_Pos.symbol);
  in the (Scan.read Symbol_Pos.stopper scan (Symbol_Pos.explode0 str)) end;


(* read_variable *)

fun read_variable str =
  let val scan = $$ "?" |-- scan_indexname || scan_indexname
  in Scan.read Symbol_Pos.stopper scan (Symbol_Pos.explode0 str) end;


(* read numbers *)

local

fun nat cs =
  Option.map (#1 o Library.read_int o map Symbol_Pos.symbol)
    (Scan.read Symbol_Pos.stopper Symbol_Pos.scan_nat cs);

in

fun read_nat s = nat (Symbol_Pos.explode0 s);

fun read_int s =
  (case Symbol_Pos.explode0 s of
    ("-", _) :: cs => Option.map ~ (nat cs)
  | cs => nat cs);

end;


(* read_num: hex/bin/decimal *)

local

val ten = Char.ord #"0" + 10;
val a = Char.ord #"a";
val A = Char.ord #"A";
val _ = a > A orelse raise Fail "Bad ASCII";

fun remap_hex c =
  let val x = ord c in
    if x >= a then chr (x - a + ten)
    else if x >= A then chr (x - A + ten)
    else c
  end;

fun leading_zeros ["0"] = 0
  | leading_zeros ("0" :: cs) = 1 + leading_zeros cs
  | leading_zeros _ = 0;

in

fun read_num str =
  let
    val (radix, digs) =
      (case Symbol.explode str of
        "0" :: "x" :: cs => (16, map remap_hex cs)
      | "0" :: "b" :: cs => (2, cs)
      | cs => (10, cs));
  in
   {radix = radix,
    leading_zeros = leading_zeros digs,
    value = #1 (Library.read_radix_int radix digs)}
  end;

end;

fun read_float str =
  let
    val cs = Symbol.explode str;
    val (intpart, fracpart) =
      (case chop_prefix Symbol.is_digit cs of
        (intpart, "." :: fracpart) => (intpart, fracpart)
      | _ => raise Fail "read_float");
  in
   {mant = #1 (Library.read_int (intpart @ fracpart)),
    exp = length fracpart}
  end;


(* marked logical entities *)

fun marker s = (prefix s, unprefix s);

val (mark_class, unmark_class) = marker "\<^class>";
val (mark_type, unmark_type) = marker "\<^type>";
val (mark_const, unmark_const) = marker "\<^const>";
val (mark_fixed, unmark_fixed) = marker "\<^fixed>";

fun unmark {case_class, case_type, case_const, case_fixed, case_default} s =
  (case try unmark_class s of
    SOME c => case_class c
  | NONE =>
      (case try unmark_type s of
        SOME c => case_type c
      | NONE =>
          (case try unmark_const s of
            SOME c => case_const c
          | NONE =>
              (case try unmark_fixed s of
                SOME c => case_fixed c
              | NONE => case_default s))));

val is_marked =
  unmark {case_class = K true, case_type = K true, case_const = K true,
    case_fixed = K true, case_default = K false};

val dummy_type = Syntax.const (mark_type "dummy");
val fun_type = Syntax.const (mark_type "fun");


(* toplevel pretty printing *)

val _ =
  ML_system_pp (fn _ => fn _ =>
    Pretty.to_polyml o Pretty.str_list "{" "}" o map quote o Scan.dest_lexicon);

end;
