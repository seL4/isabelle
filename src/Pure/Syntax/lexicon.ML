(*  Title:      Pure/Syntax/lexicon.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Lexer for the inner Isabelle syntax (terms and types).
*)

signature LEXICON0 =
sig
  val is_identifier: string -> bool
  val is_ascii_identifier: string -> bool
  val is_tid: string -> bool
  val implode_xstr: string list -> string
  val explode_xstr: string -> string list
  val scan_id: string list -> string * string list
  val scan_longid: string list -> string * string list
  val scan_var: string list -> string * string list
  val scan_tid: string list -> string * string list
  val scan_tvar: string list -> string * string list
  val scan_nat: string list -> string * string list
  val scan_int: string list -> string * string list
  val scan_hex: string list -> string * string list
  val scan_bin: string list -> string * string list
  val read_indexname: string -> indexname
  val read_var: string -> term
  val read_variable: string -> indexname option
  val const: string -> term
  val free: string -> term
  val var: indexname -> term
  val read_nat: string -> int option
  val read_int: string -> int option
  val read_xnum: string -> {radix: int, leading_zeros: int, value: IntInf.int}
  val read_idents: string -> string list
  val fixedN: string
  val constN: string
end;

signature LEXICON =
sig
  include LEXICON0
  val is_xid: string -> bool
  datatype token =
    Token of string |
    IdentSy of string |
    LongIdentSy of string |
    VarSy of string |
    TFreeSy of string |
    TVarSy of string |
    NumSy of string |
    XNumSy of string |
    StrSy of string |
    EndToken
  val idT: typ
  val longidT: typ
  val varT: typ
  val tidT: typ
  val tvarT: typ
  val terminals: string list
  val is_terminal: string -> bool
  val str_of_token: token -> string
  val display_token: token -> string
  val matching_tokens: token * token -> bool
  val valued_token: token -> bool
  val predef_term: string -> token option
  val tokenize: Scan.lexicon -> bool -> string list -> token list
end;

structure Lexicon: LEXICON =
struct


(** is_identifier etc. **)

val is_identifier = Symbol.is_ident o Symbol.explode;

fun is_ascii_identifier s =
  let val cs = Symbol.explode s
  in forall Symbol.is_ascii cs andalso Symbol.is_ident cs end;

fun is_xid s =
  (case Symbol.explode s of
    "_" :: cs => Symbol.is_ident cs
  | cs => Symbol.is_ident cs);

fun is_tid s =
  (case Symbol.explode s of
    "'" :: cs => Symbol.is_ident cs
  | _ => false);



(** basic scanners **)

val scan_letter_letdigs = Scan.one Symbol.is_letter -- Scan.many Symbol.is_letdig >> op ::;
val scan_digits1 = Scan.many1 Symbol.is_digit;
val scan_hex1 = Scan.many1 Symbol.is_ascii_hex;
val scan_bin1 = Scan.many1 (fn s => s = "0" orelse s = "1");

val scan_id = scan_letter_letdigs >> implode;
val scan_longid = scan_id ^^ (Scan.repeat1 ($$ "." ^^ scan_id) >> implode);
val scan_tid = $$ "'" ^^ scan_id;

val scan_nat = scan_digits1 >> implode;
val scan_int = $$ "-" ^^ scan_nat || scan_nat;

val scan_hex = $$ "0" ^^ $$ "x" ^^ (scan_hex1 >> implode);
val scan_bin = $$ "0" ^^ $$ "b" ^^ (scan_bin1 >> implode);

val scan_id_nat = scan_id ^^ Scan.optional ($$ "." ^^ scan_nat) "";
val scan_var = $$ "?" ^^ scan_id_nat;
val scan_tvar = $$ "?" ^^ $$ "'" ^^ scan_id_nat;



(** datatype token **)

datatype token =
  Token of string |
  IdentSy of string |
  LongIdentSy of string |
  VarSy of string |
  TFreeSy of string |
  TVarSy of string |
  NumSy of string |
  XNumSy of string |
  StrSy of string |
  EndToken;


(* terminal arguments *)

val idT = Type ("id", []);
val longidT = Type ("longid", []);
val varT = Type ("var", []);
val tidT = Type ("tid", []);
val tvarT = Type ("tvar", []);

val terminals = ["id", "longid", "var", "tid", "tvar", "num", "xnum", "xstr"];
val is_terminal = member (op =) terminals;


(* str_of_token *)

fun str_of_token (Token s) = s
  | str_of_token (IdentSy s) = s
  | str_of_token (LongIdentSy s) = s
  | str_of_token (VarSy s) = s
  | str_of_token (TFreeSy s) = s
  | str_of_token (TVarSy s) = s
  | str_of_token (NumSy s) = s
  | str_of_token (XNumSy s) = s
  | str_of_token (StrSy s) = s
  | str_of_token EndToken = "EOF";


(* display_token *)

fun display_token (Token s) = quote s
  | display_token (IdentSy s) = "id(" ^ s ^ ")"
  | display_token (LongIdentSy s) = "longid(" ^ s ^ ")"
  | display_token (VarSy s) = "var(" ^ s ^ ")"
  | display_token (TFreeSy s) = "tid(" ^ s ^ ")"
  | display_token (TVarSy s) = "tvar(" ^ s ^ ")"
  | display_token (NumSy s) = "num(" ^ s ^ ")"
  | display_token (XNumSy s) = "xnum(" ^ s ^ ")"
  | display_token (StrSy s) = "xstr(" ^ s ^ ")"
  | display_token EndToken = "";


(* matching_tokens *)

fun matching_tokens (Token x, Token y) = (x = y)
  | matching_tokens (IdentSy _, IdentSy _) = true
  | matching_tokens (LongIdentSy _, LongIdentSy _) = true
  | matching_tokens (VarSy _, VarSy _) = true
  | matching_tokens (TFreeSy _, TFreeSy _) = true
  | matching_tokens (TVarSy _, TVarSy _) = true
  | matching_tokens (NumSy _, NumSy _) = true
  | matching_tokens (XNumSy _, XNumSy _) = true
  | matching_tokens (StrSy _, StrSy _) = true
  | matching_tokens (EndToken, EndToken) = true
  | matching_tokens _ = false;


(* valued_token *)

fun valued_token (Token _) = false
  | valued_token (IdentSy _) = true
  | valued_token (LongIdentSy _) = true
  | valued_token (VarSy _) = true
  | valued_token (TFreeSy _) = true
  | valued_token (TVarSy _) = true
  | valued_token (NumSy _) = true
  | valued_token (XNumSy _) = true
  | valued_token (StrSy _) = true
  | valued_token EndToken = false;


(* predef_term *)

fun predef_term "id" = SOME (IdentSy "id")
  | predef_term "longid" = SOME (LongIdentSy "longid")
  | predef_term "var" = SOME (VarSy "var")
  | predef_term "tid" = SOME (TFreeSy "tid")
  | predef_term "tvar" = SOME (TVarSy "tvar")
  | predef_term "num" = SOME (NumSy "num")
  | predef_term "xnum" = SOME (XNumSy "xnum")
  | predef_term "xstr" = SOME (StrSy "xstr")
  | predef_term _ = NONE;


(* xstr tokens *)

fun lex_err msg prfx (cs, _) =
  "Inner lexical error: " ^ msg ^ " at " ^ quote (prfx ^ Symbol.beginning 10 cs);

val scan_chr =
  $$ "\\" |-- $$ "'" ||
  Scan.one (fn s => s <> "\\" andalso s <> "'" andalso Symbol.is_regular s) ||
  $$ "'" --| Scan.ahead (~$$ "'");

val scan_str =
  $$ "'" |-- $$ "'" |-- !! (lex_err "missing end of string" "''")
    (Scan.repeat scan_chr --| $$ "'" --| $$ "'");


fun implode_xstr cs = enclose "''" "''" (implode (map (fn "'" => "\\'" | c => c) cs));

fun explode_xstr str =
  (case Scan.read Symbol.stopper scan_str (Symbol.explode str) of
    SOME cs => cs
  | _ => error ("Inner lexical error: literal string expected at " ^ quote str));


(* nested comments *)

val scan_cmt =
  Scan.depend (fn d => $$ "(" ^^ $$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$ "*" ^^ $$ ")" >> pair (d - 1)) ||
  Scan.lift ($$ "*" --| Scan.ahead (~$$ ")")) ||
  Scan.lift (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s));

val scan_comment =
  $$ "(" -- $$ "*" -- !! (lex_err "missing end of comment" "(*")
    (Scan.pass 0 (Scan.repeat scan_cmt) -- $$ "*" -- $$ ")")
  >> K ();



(** tokenize **)

fun tokenize lex xids chs =
  let
    val scan_xid =
      if xids then $$ "_" ^^ scan_id || scan_id
      else scan_id;

    val scan_num = scan_hex || scan_bin || scan_int;

    val scan_val =
      scan_tvar >> pair TVarSy ||
      scan_var >> pair VarSy ||
      scan_tid >> pair TFreeSy ||
      scan_num >> pair NumSy ||
      $$ "#" ^^ scan_num >> pair XNumSy ||
      scan_longid >> pair LongIdentSy ||
      scan_xid >> pair IdentSy;

    val scan_lit = Scan.literal lex >> (pair Token o implode);

    val scan_token =
      scan_comment >> K NONE ||
      Scan.max (op <= o pairself snd) scan_lit scan_val >> (fn (tk, s) => SOME (tk s)) ||
      scan_str >> (SOME o StrSy o implode_xstr) ||
      Scan.one Symbol.is_blank >> K NONE;
  in
    (case Scan.error (Scan.finite Symbol.stopper (Scan.repeat scan_token)) chs of
      (toks, []) => map_filter I toks
    | (_, cs) => error ("Inner lexical error at: " ^ quote (implode cs)))
  end;



(** scan variables **)

(* scan_indexname *)

local

fun scan_vname chrs =
  let
    fun nat n [] = n
      | nat n (c :: cs) = nat (n * 10 + (ord c - ord "0")) cs;

    fun idxname cs ds = (implode (rev cs), nat 0 ds);
    fun chop_idx [] ds = idxname [] ds
      | chop_idx (cs as (_ :: "\\<^isub>" :: _)) ds = idxname cs ds
      | chop_idx (cs as (_ :: "\\<^isup>" :: _)) ds = idxname cs ds
      | chop_idx (c :: cs) ds =
          if Symbol.is_digit c then chop_idx cs (c :: ds)
          else idxname (c :: cs) ds;

    val scan =
      scan_letter_letdigs -- Scan.optional ($$ "." |-- scan_digits1 >> nat 0) ~1;
  in
    (case scan chrs of
      ((cs, ~1), cs') => (chop_idx (rev cs) [], cs')
    | ((cs, i), cs') => ((implode cs, i), cs'))
  end;

in

val scan_indexname =
     $$ "'" |-- scan_vname >> (fn (x, i) => ("'" ^ x, i))
  || scan_vname;

end;


(* indexname *)

fun read_indexname s =
  (case Scan.read Symbol.stopper scan_indexname (Symbol.explode s) of
    SOME xi => xi
  | _ => error ("Lexical error in variable name: " ^ quote s));


(* read_var *)

fun const c = Const (c, dummyT);
fun free x = Free (x, dummyT);
fun var xi = Var (xi, dummyT);

fun read_var str =
  let
    val scan =
      $$ "?" |-- scan_indexname --| Scan.ahead (Scan.one Symbol.is_eof) >> var ||
      Scan.many Symbol.is_regular >> (free o implode);
  in the (Scan.read Symbol.stopper scan (Symbol.explode str)) end;


(* read_variable *)

fun read_variable str =
  let val scan = $$ "?" |-- scan_indexname || scan_indexname
  in Scan.read Symbol.stopper scan (Symbol.explode str) end;


(* specific identifiers *)

val constN = "\\<^const>";
val fixedN = "\\<^fixed>";


(* read numbers *)

local

fun nat cs =
  Option.map (#1 o Library.read_int)
    (Scan.read Symbol.stopper scan_digits1 cs);

in

val read_nat = nat o Symbol.explode;

fun read_int s =
  (case Symbol.explode s of
    "-" :: cs => Option.map ~ (nat cs)
  | cs => nat cs);

end;


(* read_xnum: hex/bin/decimal *)

local

val ten = ord "0" + 10;
val a = ord "a";
val A = ord "A";
val _ = a > A orelse sys_error "Bad ASCII";

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

fun read_xnum str =
  let
    val (sign, radix, digs) =
      (case Symbol.explode (perhaps (try (unprefix "#")) str) of
        "0" :: "x" :: cs => (1, 16, map remap_hex cs)
      | "0" :: "b" :: cs => (1, 2, cs)
      | "-" :: cs => (~1, 10, cs)
      | cs => (1, 10, cs));
    val value = IntInf.fromInt sign * #1 (Library.read_intinf radix digs);
  in {radix = radix, leading_zeros = leading_zeros digs, value = value} end;

end;


(* read_ident(s) *)

fun read_idents str =
  let
    val blanks = Scan.many Symbol.is_blank;
    val junk = Scan.many Symbol.is_regular;
    val idents = Scan.repeat1 (blanks |-- scan_id --| blanks) -- junk;
  in
    (case Scan.read Symbol.stopper idents (Symbol.explode str) of
      SOME (ids, []) => ids
    | SOME (_, bad) => error ("Bad identifier: " ^ quote (implode bad))
    | NONE => error ("No identifier found in: " ^ quote str))
  end;

end;
