(*  Title:      Pure/Syntax/lexicon.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Lexer for the inner Isabelle syntax (terms and types).
*)

signature LEXICON0 =
sig
  val is_identifier: string -> bool
  val is_ascii_identifier: string -> bool
  val implode_xstr: string list -> string
  val explode_xstr: string -> string list
  val scan_id: string list -> string * string list
  val scan_longid: string list -> string * string list
  val scan_var: string list -> string * string list
  val scan_tid: string list -> string * string list
  val scan_tvar: string list -> string * string list
  val scan_nat: string list -> string * string list
  val scan_int: string list -> string * string list
  val string_of_vname: indexname -> string
  val string_of_vname': indexname -> string
  val indexname: string list -> indexname
  val read_var: string -> term
  val const: string -> term
  val free: string -> term
  val var: indexname -> term
  val internal: string -> string
  val dest_internal: string -> string
  val skolem: string -> string
  val dest_skolem: string -> string
  val read_nat: string -> int option
  val read_xnum: string -> int
  val read_idents: string -> string list
end;

signature LEXICON =
sig
  include LEXICON0
  val is_xid: string -> bool
  val is_tid: string -> bool
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
  val token_assoc: (token option * 'a list) list * token -> 'a list
  val valued_token: token -> bool
  val predef_term: string -> token option
  val tokenize: Scan.lexicon -> bool -> string list -> token list
end;

structure Lexicon: LEXICON =
struct


(** is_identifier etc. **)

fun is_ident [] = false
  | is_ident (c :: cs) = Symbol.is_letter c andalso forall Symbol.is_letdig cs;

val is_identifier = is_ident o Symbol.explode;

fun is_ascii_identifier s =
  let val cs = Symbol.explode s
  in forall Symbol.is_ascii cs andalso is_ident cs end;

fun is_xid s =
  (case Symbol.explode s of
    "_" :: cs => is_ident cs
  | cs => is_ident cs);

fun is_tid s =
  (case Symbol.explode s of
    "'" :: cs => is_ident cs
  | _ => false);



(** basic scanners **)

val scan_letter_letdigs = Scan.one Symbol.is_letter -- Scan.any Symbol.is_letdig >> op ::;
val scan_digits1 = Scan.any1 Symbol.is_digit;

val scan_id = scan_letter_letdigs >> implode;
val scan_longid = scan_id ^^ (Scan.repeat1 ($$ "." ^^ scan_id) >> implode);
val scan_tid = $$ "'" ^^ scan_id;

val scan_nat = scan_digits1 >> implode;
val scan_int = $$ "-" ^^ scan_nat || scan_nat;

val scan_id_nat = scan_id ^^ Scan.optional ($$ "." ^^ scan_nat) "";
val scan_var = $$ "?" ^^ scan_id_nat;
val scan_tvar = $$ "?" ^^ $$ "'" ^^ scan_id_nat;



(** string_of_vname **)

val string_of_vname = Term.string_of_vname;
val string_of_vname' = Term.string_of_vname';



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

fun is_terminal s = s mem terminals;


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


(* token_assoc *)

fun token_assoc (list, key) =
  let
    fun assoc [] = []
      | assoc ((keyi, xi) :: pairs) =
          if is_none keyi orelse matching_tokens (the keyi, key) then
            assoc pairs @ xi
          else assoc pairs;
  in assoc list end;


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

fun predef_term "id" = Some (IdentSy "id")
  | predef_term "longid" = Some (LongIdentSy "longid")
  | predef_term "var" = Some (VarSy "var")
  | predef_term "tid" = Some (TFreeSy "tid")
  | predef_term "tvar" = Some (TVarSy "tvar")
  | predef_term "num" = Some (NumSy "num")
  | predef_term "xnum" = Some (XNumSy "xnum")
  | predef_term "xstr" = Some (StrSy "xstr")
  | predef_term _ = None;


(* xstr tokens *)

fun lex_err msg prfx (cs, _) =
  "Inner lexical error: " ^ msg ^ " at " ^ quote (prfx ^ Symbol.beginning 10 cs);

val scan_chr =
  $$ "\\" |-- Scan.one Symbol.not_eof ||
  Scan.one (not_equal "'" andf Symbol.not_eof) ||
  $$ "'" --| Scan.ahead (Scan.one (not_equal "'"));

val scan_str =
  $$ "'" |-- $$ "'" |-- !! (lex_err "missing end of string" "''")
    (Scan.repeat scan_chr --| $$ "'" --| $$ "'");


fun implode_xstr cs = enclose "''" "''" (implode (map (fn "'" => "\\'" | c => c) cs));

fun explode_xstr str =
  (case Scan.read Symbol.stopper scan_str (Symbol.explode str) of
    Some cs => cs
  | _ => error ("Inner lexical error: literal string expected at " ^ quote str));


(* nested comments *)

val scan_cmt =
  Scan.depend (fn d => $$ "(" ^^ $$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$ "*" ^^ $$ ")" >> pair (d - 1)) ||
  Scan.lift ($$ "*" --| Scan.ahead (Scan.one (not_equal ")"))) ||
  Scan.lift (Scan.one (not_equal "*" andf Symbol.not_eof));

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

    val scan_val =
      scan_tvar >> pair TVarSy ||
      scan_var >> pair VarSy ||
      scan_tid >> pair TFreeSy ||
      scan_int >> pair NumSy ||
      $$ "#" ^^ scan_int >> pair XNumSy ||
      scan_longid >> pair LongIdentSy ||
      scan_xid >> pair IdentSy;

    val scan_lit = Scan.literal lex >> (pair Token o implode);

    val scan_token =
      scan_comment >> K None ||
      Scan.max (op <= o pairself snd) scan_lit scan_val >> (fn (tk, s) => Some (tk s)) ||
      scan_str >> (Some o StrSy o implode_xstr) ||
      Scan.one Symbol.is_blank >> K None;
  in
    (case Scan.error (Scan.finite Symbol.stopper (Scan.repeat scan_token)) chs of
      (toks, []) => mapfilter I toks @ [EndToken]
    | (_, cs) => error ("Inner lexical error at: " ^ quote (implode cs)))
  end;



(** scan variables **)

(* scan_vname *)

fun scan_vname chrs =
  let
    fun nat_of_chs n [] = n
      | nat_of_chs n (c :: cs) = nat_of_chs (n * 10 + (ord c - ord "0")) cs;

    val nat = nat_of_chs 0;

    fun split_vname chs =
      let val (cs, ds) = take_suffix Symbol.is_digit chs
      in (implode cs, nat ds) end

    val scan =
      scan_letter_letdigs -- Scan.optional ($$ "." |-- scan_digits1 >> nat) ~1;
  in
    (case scan chrs of
      ((cs, ~1), cs') => (split_vname cs, cs')
    | ((cs, i), cs') => ((implode cs, i), cs'))
  end;


(* indexname *)

fun indexname cs =
  (case Scan.read Symbol.stopper scan_vname cs of
    Some xi => xi
  | _ => error ("Lexical error in variable name: " ^ quote (implode cs)));


(* read_var *)

fun const c = Const (c, dummyT);
fun free x = Free (x, dummyT);
fun var xi = Var (xi, dummyT);

fun read_var str =
  let
    fun tvar (x, i) = var ("'" ^ x, i);

    val scan =
      $$ "?" |-- $$ "'" |-- scan_vname >> tvar ||
      $$ "?" |-- scan_vname >> var ||
      Scan.any Symbol.not_eof >> (free o implode);
  in the (Scan.read Symbol.stopper scan (Symbol.explode str)) end;


(* variable kinds *)

val internal = suffix "_";
val dest_internal = unsuffix "_";

val skolem = suffix "__";
val dest_skolem = unsuffix "__";


(* read_nat *)

fun read_nat str =
  apsome (#1 o Library.read_int) (Scan.read Symbol.stopper scan_digits1 (Symbol.explode str));


(* read_xnum *)

fun read_xnum str =
  let
    val (sign, digs) =
      (case Symbol.explode str of
        "#" :: "-" :: cs => (~1, cs)
      | "#" :: cs => (1, cs)
      | "-" :: cs => (~1, cs)
      | cs => (1, cs));
  in sign * #1 (Library.read_int digs) end;


(* read_ident(s) *)

fun read_idents str =
  let
    val blanks = Scan.any Symbol.is_blank;
    val junk = Scan.any Symbol.not_eof;
    val idents = Scan.repeat1 (blanks |-- scan_id --| blanks) -- junk;
  in
    (case Scan.read Symbol.stopper idents (Symbol.explode str) of
      Some (ids, []) => ids
    | Some (_, bad) => error ("Bad identifier: " ^ quote (implode bad))
    | None => error ("No identifier found in: " ^ quote str))
  end;

end;
