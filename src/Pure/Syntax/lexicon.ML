(*  Title:      Pure/Syntax/lexicon.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Scanner combinators and the main lexer (for terms and types).
*)

infix 5 -- ^^;
infix 3 >>;
infix 0 ||;

signature SCANNER =
sig
  exception LEXICAL_ERROR
  val >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  val || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  val ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c
  val $$ : ''a -> ''a list -> ''a * ''a list
  val scan_empty: 'a list -> 'b list * 'a list
  val scan_one: ('a -> bool) -> 'a list -> 'a * 'a list
  val scan_any: ('a -> bool) -> 'a list -> 'a list * 'a list
  val scan_any1: ('a -> bool) -> 'a list -> 'a list * 'a list
  val scan_end: 'a list -> 'b list * 'a list
  val optional: ('a -> 'b * 'a) -> 'a -> 'b option * 'a
  val repeat: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val repeat1: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val max_of: ('a -> ('b * string) * 'a) -> ('a -> ('b * string) * 'a)
    -> 'a -> ('b * string) option * 'a
  val scan_id: string list -> string * string list
  val scan_longid: string list -> string * string list
  val scan_tid: string list -> string * string list
  val scan_nat: string list -> string * string list
  type lexicon
  val dest_lexicon: lexicon -> string list
  val empty_lexicon: lexicon
  val extend_lexicon: lexicon -> string list -> lexicon
  val make_lexicon: string list -> lexicon
  val merge_lexicons: lexicon -> lexicon -> lexicon
  val scan_literal: lexicon -> string list -> string * string list
end;

signature LEXICON0 =
sig
  val is_identifier: string -> bool
  val implode_xstr: string list -> string
  val explode_xstr: string -> string list
  val string_of_vname: indexname -> string
  val string_of_vname': indexname -> string
  val scan_varname: string list -> indexname * string list
  val scan_var: string -> term
  val const: string -> term
  val free: string -> term
  val var: indexname -> term
  val read_var: string -> string * int
end;

signature LEXICON =
sig
  include SCANNER
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
  val tokenize: lexicon -> bool -> string list -> token list
end;

structure Lexicon : LEXICON =
struct


(** is_identifier etc. **)

fun is_ident [] = false
  | is_ident (c :: cs) = is_letter c andalso forall is_letdig cs;

val is_identifier = is_ident o explode;

fun is_xid s =
  (case explode s of
    "_" :: cs => is_ident cs
  | cs => is_ident cs);

fun is_tid s =
  (case explode s of
    "'" :: cs => is_ident cs
  | _ => false);



(** string_of_vname **)

fun string_of_vname (x, i) =
  let
    val si = string_of_int i;
  in
    (if is_digit (last_elem (explode x)) then "?" ^ x ^ "." ^ si
     else if i = 0 then "?" ^ x
     else "?" ^ x ^ si)
    handle LIST _ => "?NULL_VARIABLE." ^ si
  end;

fun string_of_vname' (xi as (x, i)) =
  if i < 0 then x else string_of_vname xi;



(** datatype token **)

datatype token =
  Token of string |
  IdentSy of string |
  LongIdentSy of string |
  VarSy of string |
  TFreeSy of string |
  TVarSy of string |
  NumSy of string |
  StrSy of string |
  EndToken;


(* terminal arguments *)

val idT = Type ("id", []);
val longidT = Type ("longid", []);
val varT = Type ("var", []);
val tidT = Type ("tid", []);
val tvarT = Type ("tvar", []);

val terminals = ["id", "longid", "var", "tid", "tvar", "xnum", "xstr"];

fun is_terminal s = s mem terminals;


(* str_of_token *)

fun str_of_token (Token s) = s
  | str_of_token (IdentSy s) = s
  | str_of_token (LongIdentSy s) = s
  | str_of_token (VarSy s) = s
  | str_of_token (TFreeSy s) = s
  | str_of_token (TVarSy s) = s
  | str_of_token (NumSy s) = s
  | str_of_token (StrSy s) = s
  | str_of_token EndToken = "EOF";


(* display_token *)

fun display_token (Token s) = quote s
  | display_token (IdentSy s) = "id(" ^ s ^ ")"
  | display_token (LongIdentSy s) = "longid(" ^ s ^ ")"
  | display_token (VarSy s) = "var(" ^ s ^ ")"
  | display_token (TFreeSy s) = "tid(" ^ s ^ ")"
  | display_token (TVarSy s) = "tvar(" ^ s ^ ")"
  | display_token (NumSy s) = "xnum(" ^ s ^ ")"
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
  | valued_token (StrSy _) = true
  | valued_token EndToken = false;


(* predef_term *)

fun predef_term "id" = Some (IdentSy "id")
  | predef_term "longid" = Some (LongIdentSy "longid")
  | predef_term "var" = Some (VarSy "var")
  | predef_term "tid" = Some (TFreeSy "tid")
  | predef_term "tvar" = Some (TVarSy "tvar")
  | predef_term "xnum" = Some (NumSy "xnum")
  | predef_term "xstr" = Some (StrSy "xstr")
  | predef_term _ = None;


(*  xstr tokens *)

fun implode_xstr cs = enclose "''" "''" (implode cs);

fun explode_xstr str =
  rev (tl (tl (rev (tl (tl (explode str))))));



(** datatype lexicon **)

datatype lexicon =
  Empty |
  Branch of string * string * lexicon * lexicon * lexicon;

val no_token = "";


(* dest_lexicon *)

fun dest_lexicon Empty = []
  | dest_lexicon (Branch (_, "", lt, eq, gt)) =
      dest_lexicon eq @ dest_lexicon lt @ dest_lexicon gt
  | dest_lexicon (Branch (_, str, lt, eq, gt)) =
      str :: (dest_lexicon eq @ dest_lexicon lt @ dest_lexicon gt);


(* empty, extend, make, merge lexicons *)

val empty_lexicon = Empty;

fun extend_lexicon lexicon strs =
  let
    fun ext (lex, s) =
      let
        fun add (Branch (d, a, lt, eq, gt)) (chs as c :: cs) =
              if c < d then Branch (d, a, add lt chs, eq, gt)
              else if c > d then Branch (d, a, lt, eq, add gt chs)
              else Branch (d, if null cs then s else a, lt, add eq cs, gt)
          | add Empty [c] =
              Branch (c, s, Empty, Empty, Empty)
          | add Empty (c :: cs) =
              Branch (c, no_token, Empty, add Empty cs, Empty)
          | add lex [] = lex;

        val cs = explode s;
      in
        if exists is_blank cs then
          sys_error ("extend_lexicon: blank in delimiter " ^ quote s)
        else add lex cs
      end;
  in
    foldl ext (lexicon, strs \\ dest_lexicon lexicon)
  end;

val make_lexicon = extend_lexicon empty_lexicon;

fun merge_lexicons lex1 lex2 =
  let
    val strs1 = dest_lexicon lex1;
    val strs2 = dest_lexicon lex2;
  in
    if strs2 subset strs1 then lex1
    else if strs1 subset strs2 then lex2
    else extend_lexicon lex1 strs2
  end;



(** scanners **)

exception LEXICAL_ERROR;


(* scanner combinators *)

fun (scan >> f) cs = apfst f (scan cs);

fun (scan1 || scan2) cs = scan1 cs handle LEXICAL_ERROR => scan2 cs;

fun (scan1 -- scan2) cs =
  let
    val (x, cs') = scan1 cs;
    val (y, cs'') = scan2 cs';
  in
    ((x, y), cs'')
  end;

fun (scan1 ^^ scan2) = scan1 -- scan2 >> op ^;


(* generic scanners *)

fun $$ _ [] = raise LEXICAL_ERROR
  | $$ a (c :: cs) =
      if a = c then (c, cs) else raise LEXICAL_ERROR;

fun scan_empty cs = ([], cs);

fun scan_one _ [] = raise LEXICAL_ERROR
  | scan_one pred (c :: cs) =
      if pred c then (c, cs) else raise LEXICAL_ERROR;

fun scan_any _ [] = ([], [])
  | scan_any pred (chs as c :: cs) =
      if pred c then apfst (cons c) (scan_any pred cs)
      else ([], chs);

fun scan_any1 pred = scan_one pred -- scan_any pred >> op ::;

fun scan_rest cs = (cs, []);

fun scan_end [] = ([], [])
  | scan_end _ = raise LEXICAL_ERROR;

fun optional scan = scan >> Some || scan_empty >> K None;

fun repeat scan cs = (scan -- repeat scan >> op :: || scan_empty) cs;

fun repeat1 scan = scan -- repeat scan >> op ::;

fun max_of scan1 scan2 cs =
  (case (optional scan1 cs, optional scan2 cs) of
    (tok1, (None, _)) => tok1
  | ((None, _), tok2) => tok2
  | (tok1 as (Some (_, s1), _), tok2 as (Some (_, s2), _)) =>
      if size s1 >= size s2 then tok1 else tok2);


(* other scanners *)

val scan_letter_letdigs = scan_one is_letter -- scan_any is_letdig >> op ::;

val scan_digits1 = scan_any1 is_digit;

val scan_id = scan_letter_letdigs >> implode;

val scan_longid = scan_id ^^ (repeat1 ($$ "." ^^ scan_id) >> implode);

val scan_id_nat =
  scan_id ^^ ($$ "." ^^ (scan_digits1 >> implode) || scan_empty >> K "");

val scan_tid = $$ "'" ^^ scan_id;

val scan_nat = scan_digits1 >> implode;

val scan_int = $$ "~" ^^ scan_nat || scan_nat;


(* scan_literal *)

fun scan_literal lex chrs =
  let
    fun scan_lit _ s_cs [] = s_cs
      | scan_lit Empty s_cs _ = s_cs
      | scan_lit (Branch (d, a, lt, eq, gt)) s_cs (chs as c :: cs) =
          if c < d then scan_lit lt s_cs chs
          else if c > d then scan_lit gt s_cs chs
          else scan_lit eq (if a = no_token then s_cs else Some (a, cs)) cs;
  in
    (case scan_lit lex None chrs of
      None => raise LEXICAL_ERROR
    | Some s_cs => s_cs)
  end;



(** tokenize **)

fun tokenize lex xids chs =
  let
    val scan_xid =
      if xids then $$ "_" ^^ scan_id || scan_id
      else scan_id;

    val scan_lit = scan_literal lex >> pair Token;

    val scan_val =
      $$ "?" ^^ $$ "'" ^^ scan_id_nat >> pair TVarSy ||
      $$ "?" ^^ scan_id_nat >> pair VarSy ||
      $$ "'" ^^ scan_id >> pair TFreeSy ||
      $$ "#" ^^ scan_int >> pair NumSy ||
      scan_longid >> pair LongIdentSy ||
      scan_xid >> pair IdentSy;

    fun scan_str ("'" :: "'" :: cs) = ([], cs)
      | scan_str ("\\" :: c :: cs) = apfst (cons c) (scan_str cs)
      | scan_str (c :: cs) = apfst (cons c) (scan_str cs)
      | scan_str [] = raise ERROR;


    fun scan (rev_toks, []) = rev (EndToken :: rev_toks)
      | scan (rev_toks, chs as "'" :: "'" :: cs) =
          let
            val (cs', cs'') = scan_str cs handle ERROR =>
              error ("Lexical error: missing quotes at end of string " ^
                quote (implode chs));
          in
            scan (StrSy (implode_xstr cs') :: rev_toks, cs'')
          end
      | scan (rev_toks, chs as c :: cs) =
          if is_blank c then scan (rev_toks, cs)
          else
            (case max_of scan_lit scan_val chs of
              (None, _) => error ("Lexical error at: " ^ quote (implode chs))
            | (Some (tk, s), chs') => scan (tk s :: rev_toks, chs'));
  in
    scan ([], chs)
  end;



(** scan variables **)

(* scan_vname *)

fun scan_vname chrs =
  let
    fun nat_of_chs n [] = n
      | nat_of_chs n (c :: cs) = nat_of_chs (n * 10 + (ord c - ord "0")) cs;

    val nat_of = nat_of_chs 0;

    fun split_vname chs =
      let val (cs, ds) = take_suffix is_digit chs
      in (implode cs, nat_of ds) end

    val scan =
      scan_letter_letdigs --
        ($$ "." -- scan_digits1 >> (nat_of o #2) || scan_empty >> K ~1);
  in
    (case scan chrs of
      ((cs, ~1), cs') => (split_vname cs, cs')
    | ((cs, i), cs') => ((implode cs, i), cs'))
  end;


(* scan_varname *)

fun scan_varname chs =
  scan_vname chs handle LEXICAL_ERROR
    => error ("scan_varname: bad varname " ^ quote (implode chs));


(* scan_var *)

fun const c = Const (c, dummyT);
fun free x = Free (x, dummyT);
fun var xi = Var (xi, dummyT);

fun scan_var str =
  let
    fun tvar (x, i) = var ("'" ^ x, i);

    val scan =
      $$ "?" -- $$ "'" -- scan_vname -- scan_end >> (tvar o #2 o #1) ||
      $$ "?" -- scan_vname -- scan_end >> (var o #2 o #1) ||
      scan_rest >> (free o implode);
  in
    #1 (scan (explode str))
  end;


(* read_var *)

fun read_var str =
  let val scan = $$ "?" -- scan_vname -- scan_end >> (#2 o #1) in
    #1 (scan (explode str)) handle LEXICAL_ERROR
      => error ("Bad variable " ^ quote str)
  end;


end;
