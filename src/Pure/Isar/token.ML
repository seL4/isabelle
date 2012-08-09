(*  Title:      Pure/Isar/token.ML
    Author:     Markus Wenzel, TU Muenchen

Outer token syntax for Isabelle/Isar.
*)

signature TOKEN =
sig
  datatype kind =
    Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar |
    Nat | Float | String | AltString | Verbatim | Space | Comment | InternalValue |
    Error of string | Sync | EOF
  datatype value =
    Text of string | Typ of typ | Term of term | Fact of thm list |
    Attribute of morphism -> attribute
  type T
  val str_of_kind: kind -> string
  val position_of: T -> Position.T
  val end_position_of: T -> Position.T
  val pos_of: T -> string
  val range: T list -> Position.range
  val eof: T
  val is_eof: T -> bool
  val not_eof: T -> bool
  val not_sync: T -> bool
  val stopper: T Scan.stopper
  val kind_of: T -> kind
  val is_kind: kind -> T -> bool
  val keyword_with: (string -> bool) -> T -> bool
  val ident_with: (string -> bool) -> T -> bool
  val is_command: T -> bool
  val is_proper: T -> bool
  val is_semicolon: T -> bool
  val is_comment: T -> bool
  val is_begin_ignore: T -> bool
  val is_end_ignore: T -> bool
  val is_blank: T -> bool
  val is_newline: T -> bool
  val source_of: T -> string
  val source_position_of: T -> Symbol_Pos.text * Position.T
  val content_of: T -> string
  val unparse: T -> string
  val text_of: T -> string * string
  val get_value: T -> value option
  val map_value: (value -> value) -> T -> T
  val mk_text: string -> T
  val mk_typ: typ -> T
  val mk_term: term -> T
  val mk_fact: thm list -> T
  val mk_attribute: (morphism -> attribute) -> T
  val assignable: T -> T
  val assign: value option -> T -> unit
  val closure: T -> T
  val ident_or_symbolic: string -> bool
  val source_proper: (T, 'a) Source.source -> (T, (T, 'a) Source.source) Source.source
  val source': {do_recover: bool option} -> (unit -> Scan.lexicon * Scan.lexicon) ->
    (Symbol_Pos.T, 'a) Source.source -> (T, (Symbol_Pos.T, 'a) Source.source) Source.source
  val source: {do_recover: bool option} -> (unit -> Scan.lexicon * Scan.lexicon) ->
    Position.T -> (Symbol.symbol, 'a) Source.source -> (T,
      (Symbol_Pos.T, Position.T * (Symbol.symbol, 'a) Source.source) Source.source) Source.source
  val read_antiq: Scan.lexicon -> (T list -> 'a * T list) -> Symbol_Pos.T list * Position.T -> 'a
end;

structure Token: TOKEN =
struct

(** tokens **)

(* token values *)

(*The value slot assigns an (optional) internal value to a token,
  usually as a side-effect of special scanner setup (see also
  args.ML).  Note that an assignable ref designates an intermediate
  state of internalization -- it is NOT meant to persist.*)

datatype value =
  Text of string |
  Typ of typ |
  Term of term |
  Fact of thm list |
  Attribute of morphism -> attribute;

datatype slot =
  Slot |
  Value of value option |
  Assignable of value option Unsynchronized.ref;


(* datatype token *)

datatype kind =
  Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar |
  Nat | Float | String | AltString | Verbatim | Space | Comment | InternalValue |
  Error of string | Sync | EOF;

datatype T = Token of (Symbol_Pos.text * Position.range) * (kind * string) * slot;

val str_of_kind =
 fn Command => "command"
  | Keyword => "keyword"
  | Ident => "identifier"
  | LongIdent => "long identifier"
  | SymIdent => "symbolic identifier"
  | Var => "schematic variable"
  | TypeIdent => "type variable"
  | TypeVar => "schematic type variable"
  | Nat => "natural number"
  | Float => "floating-point number"
  | String => "string"
  | AltString => "back-quoted string"
  | Verbatim => "verbatim text"
  | Space => "white space"
  | Comment => "comment text"
  | InternalValue => "internal value"
  | Error _ => "bad input"
  | Sync => "sync marker"
  | EOF => "end-of-file";


(* position *)

fun position_of (Token ((_, (pos, _)), _, _)) = pos;
fun end_position_of (Token ((_, (_, pos)), _, _)) = pos;

val pos_of = Position.str_of o position_of;

fun range [] = (Position.none, Position.none)
  | range toks =
      let
        val start_pos = position_of (hd toks);
        val end_pos = end_position_of (List.last toks);
      in (start_pos, end_pos) end;


(* control tokens *)

fun mk_eof pos = Token (("", (pos, Position.none)), (EOF, ""), Slot);
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _), _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

fun not_sync (Token (_, (Sync, _), _)) = false
  | not_sync _ = true;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_position_of (List.last toks))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _), _)) = k;
fun is_kind k (Token (_, (k', _), _)) = k = k';

val is_command = is_kind Command;

fun keyword_with pred (Token (_, (Keyword, x), _)) = pred x
  | keyword_with _ _ = false;

fun ident_with pred (Token (_, (Ident, x), _)) = pred x
  | ident_with _ _ = false;

fun is_proper (Token (_, (Space, _), _)) = false
  | is_proper (Token (_, (Comment, _), _)) = false
  | is_proper _ = true;

fun is_semicolon (Token (_, (Keyword, ";"), _)) = true
  | is_semicolon _ = false;

fun is_comment (Token (_, (Comment, _), _)) = true
  | is_comment _ = false;

fun is_begin_ignore (Token (_, (Comment, "<"), _)) = true
  | is_begin_ignore _ = false;

fun is_end_ignore (Token (_, (Comment, ">"), _)) = true
  | is_end_ignore _ = false;


(* blanks and newlines -- space tokens obey lines *)

fun is_blank (Token (_, (Space, x), _)) = not (String.isSuffix "\n" x)
  | is_blank _ = false;

fun is_newline (Token (_, (Space, x), _)) = String.isSuffix "\n" x
  | is_newline _ = false;


(* token content *)

fun source_of (Token ((source, (pos, _)), (_, x), _)) =
  if YXML.detect x then x
  else
    YXML.string_of
      (XML.Elem (Isabelle_Markup.token (Position.properties_of pos), [XML.Text source]));

fun source_position_of (Token ((source, (pos, _)), _, _)) = (source, pos);

fun content_of (Token (_, (_, x), _)) = x;


(* unparse *)

fun unparse (Token (_, (kind, x), _)) =
  (case kind of
    String => Symbol_Pos.quote_string_qq x
  | AltString => Symbol_Pos.quote_string_bq x
  | Verbatim => enclose "{*" "*}" x
  | Comment => enclose "(*" "*)" x
  | Sync => ""
  | EOF => ""
  | _ => x);

fun text_of tok =
  if is_semicolon tok then ("terminator", "")
  else
    let
      val k = str_of_kind (kind_of tok);
      val s = unparse tok;
    in
      if s = "" then (k, "")
      else if size s < 40 andalso not (exists_string (fn c => c = "\n") s) then (k ^ " " ^ s, "")
      else (k, s)
    end;



(** associated values **)

(* access values *)

fun get_value (Token (_, _, Value v)) = v
  | get_value _ = NONE;

fun map_value f (Token (x, y, Value (SOME v))) = Token (x, y, Value (SOME (f v)))
  | map_value _ tok = tok;


(* make values *)

fun mk_value k v = Token ((k, Position.no_range), (InternalValue, k), Value (SOME v));

val mk_text = mk_value "<text>" o Text;
val mk_typ = mk_value "<typ>" o Typ;
val mk_term = mk_value "<term>" o Term;
val mk_fact = mk_value "<fact>" o Fact;
val mk_attribute = mk_value "<attribute>" o Attribute;


(* static binding *)

(*1st stage: make empty slots assignable*)
fun assignable (Token (x, y, Slot)) = Token (x, y, Assignable (Unsynchronized.ref NONE))
  | assignable tok = tok;

(*2nd stage: assign values as side-effect of scanning*)
fun assign v (Token (_, _, Assignable r)) = r := v
  | assign _ _ = ();

(*3rd stage: static closure of final values*)
fun closure (Token (x, y, Assignable (Unsynchronized.ref v))) = Token (x, y, Value v)
  | closure tok = tok;



(** scanners **)

open Basic_Symbol_Pos;

fun !!! msg = Symbol_Pos.!!! (fn () => "Outer lexical error: " ^ msg);


(* scan symbolic idents *)

val is_sym_char = member (op =) (raw_explode "!#$%&*+-/<=>?@^_|~");

val scan_symid =
  Scan.many1 (is_sym_char o Symbol_Pos.symbol) ||
  Scan.one (Symbol.is_symbolic o Symbol_Pos.symbol) >> single;

fun is_symid str =
  (case try Symbol.explode str of
    SOME [s] => Symbol.is_symbolic s orelse is_sym_char s
  | SOME ss => forall is_sym_char ss
  | _ => false);

fun ident_or_symbolic "begin" = false
  | ident_or_symbolic ":" = true
  | ident_or_symbolic "::" = true
  | ident_or_symbolic s = Lexicon.is_identifier s orelse is_symid s;


(* scan verbatim text *)

val scan_verb =
  $$$ "*" --| Scan.ahead (~$$$ "}") ||
  Scan.one (fn (s, _) => s <> "*" andalso Symbol.is_regular s) >> single;

val scan_verbatim =
  (Symbol_Pos.scan_pos --| $$$ "{" --| $$$ "*") -- !!! "missing end of verbatim text"
    (Symbol_Pos.change_prompt
      ((Scan.repeat scan_verb >> flat) -- ($$$ "*" |-- $$$ "}" |-- Symbol_Pos.scan_pos)));

val recover_verbatim =
  $$$ "{" @@@ $$$ "*" @@@ (Scan.repeat scan_verb >> flat);


(* scan space *)

fun is_space s = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  Scan.many1 (is_space o Symbol_Pos.symbol) @@@ Scan.optional ($$$ "\n") [] ||
  Scan.many (is_space o Symbol_Pos.symbol) @@@ $$$ "\n";


(* scan comment *)

val scan_comment =
  Symbol_Pos.scan_pos -- (Symbol_Pos.scan_comment_body !!! -- Symbol_Pos.scan_pos);



(** token sources **)

fun source_proper src = src |> Source.filter is_proper;

local

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun token k ss =
  Token ((Symbol_Pos.implode ss, Symbol_Pos.range ss), (k, Symbol_Pos.content ss), Slot);

fun token_range k (pos1, (ss, pos2)) =
  Token (Symbol_Pos.implode_range pos1 pos2 ss, (k, Symbol_Pos.content ss), Slot);

fun scan (lex1, lex2) = !!! "bad input"
  (Symbol_Pos.scan_string_qq >> token_range String ||
    Symbol_Pos.scan_string_bq >> token_range AltString ||
    scan_verbatim >> token_range Verbatim ||
    scan_comment >> token_range Comment ||
    scan_space >> token Space ||
    Scan.one (Symbol.is_sync o Symbol_Pos.symbol) >> (token Sync o single) ||
    (Scan.max token_leq
      (Scan.max token_leq
        (Scan.literal lex2 >> pair Command)
        (Scan.literal lex1 >> pair Keyword))
      (Lexicon.scan_longid >> pair LongIdent ||
        Lexicon.scan_id >> pair Ident ||
        Lexicon.scan_var >> pair Var ||
        Lexicon.scan_tid >> pair TypeIdent ||
        Lexicon.scan_tvar >> pair TypeVar ||
        Lexicon.scan_float >> pair Float ||
        Lexicon.scan_nat >> pair Nat ||
        scan_symid >> pair SymIdent) >> uncurry token));

fun recover msg =
  (Symbol_Pos.recover_string_qq ||
    Symbol_Pos.recover_string_bq ||
    recover_verbatim ||
    Symbol_Pos.recover_comment ||
    Scan.one (Symbol.is_regular o Symbol_Pos.symbol) >> single)
  >> (single o token (Error msg));

in

fun source' {do_recover} get_lex =
  Source.source Symbol_Pos.stopper (Scan.bulk (fn xs => scan (get_lex ()) xs))
    (Option.map (rpair recover) do_recover);

fun source do_recover get_lex pos src =
  Symbol_Pos.source pos src
  |> source' do_recover get_lex;

end;


(* read_antiq *)

fun read_antiq lex scan (syms, pos) =
  let
    fun err msg = cat_error msg ("Malformed antiquotation" ^ Position.str_of pos ^ ":\n" ^
      "@{" ^ Symbol_Pos.content syms ^ "}");

    val res =
      Source.of_list syms
      |> source' {do_recover = NONE} (K (lex, Scan.empty_lexicon))
      |> source_proper
      |> Source.source stopper (Scan.error (Scan.bulk scan)) NONE
      |> Source.exhaust;
  in (case res of [x] => x | _ => err "") handle ERROR msg => err msg end;

end;
