(*  Title:      Pure/Isar/token.ML
    Author:     Markus Wenzel, TU Muenchen

Outer token syntax for Isabelle/Isar.
*)

signature TOKEN =
sig
  datatype kind =
    (*immediate source*)
    Command | Keyword | Ident | Long_Ident | Sym_Ident | Var | Type_Ident | Type_Var | Nat |
    Float | Space |
    (*delimited content*)
    String | Alt_String | Cartouche |
    Control of Antiquote.control |
    Comment of Comment.kind option |
    (*special content*)
    Error of string | EOF
  val control_kind: kind
  val str_of_kind: kind -> string
  type file = {src_path: Path.T, lines: string list, digest: SHA1.digest, pos: Position.T}
  type T
  type src = T list
  type name_value = {name: string, kind: string, print: Proof.context -> Markup.T * xstring}
  datatype value =
    Source of src |
    Literal of bool * Markup.T |
    Name of name_value * morphism |
    Typ of typ |
    Term of term |
    Fact of string option * thm list |
    Attribute of attribute Morphism.entity |
    Declaration of Morphism.declaration_entity |
    Files of file Exn.result list |
    Output of XML.body option
  val pos_of: T -> Position.T
  val adjust_offsets: (int -> int option) -> T -> T
  val input_position: src -> string option
  val context_input_position: Context.generic * src -> string option
  val eof: T
  val is_eof: T -> bool
  val not_eof: T -> bool
  val stopper: T Scan.stopper
  val kind_of: T -> kind
  val is_kind: kind -> T -> bool
  val get_control: T -> Antiquote.control option
  val is_command: T -> bool
  val keyword_with: (string -> bool) -> T -> bool
  val is_command_modifier: T -> bool
  val ident_with: (string -> bool) -> T -> bool
  val is_proper: T -> bool
  val is_comment: T -> bool
  val is_informal_comment: T -> bool
  val is_formal_comment: T -> bool
  val is_document_marker: T -> bool
  val is_ignored: T -> bool
  val is_begin_ignore: T -> bool
  val is_end_ignore: T -> bool
  val is_error: T -> bool
  val is_space: T -> bool
  val is_blank: T -> bool
  val is_newline: T -> bool
  val range_of: T list -> Position.range
  val core_range_of: T list -> Position.range
  val content_of: T -> string
  val source_of: T -> string
  val input_of: T -> Input.source
  val inner_syntax_of: T -> string
  val keyword_markup: bool * Markup.T -> string -> Markup.T
  val completion_report: T -> Position.report_text list
  val reports: Keyword.keywords -> T -> Position.report_text list
  val markups: Keyword.keywords -> T -> Markup.T list
  val unparse: T -> string
  val print: T -> string
  val text_of: T -> string * string
  val file_source: file -> Input.source
  val get_files: T -> file Exn.result list
  val put_files: file Exn.result list -> T -> T
  val get_output: T -> XML.body option
  val put_output: XML.body -> T -> T
  val get_value: T -> value option
  val reports_of_value: T -> Position.report list
  val name_value: name_value -> value
  val get_name: T -> name_value option
  val declare_maxidx: T -> Proof.context -> Proof.context
  val map_facts: (string option -> thm list -> thm list) -> T -> T
  val trim_context: T -> T
  val transfer: theory -> T -> T
  val transform: morphism -> T -> T
  val init_assignable: T -> T
  val assign: value option -> T -> T
  val evaluate: ('a -> value) -> (T -> 'a) -> T -> 'a
  val closure: T -> T
  val pretty_value: Proof.context -> T -> Pretty.T
  val name_of_src: src -> string * Position.T
  val args_of_src: src -> T list
  val checked_src: src -> bool
  val check_src: Proof.context -> (Proof.context -> 'a Name_Space.table) -> src -> src * 'a
  val pretty_src: Proof.context -> src -> Pretty.T
  val ident_or_symbolic: string -> bool
  val read_cartouche: Symbol_Pos.T list -> T
  val tokenize: Keyword.keywords -> {strict: bool} -> Symbol_Pos.T list -> T list
  val explode: Keyword.keywords -> Position.T -> string -> T list
  val explode0: Keyword.keywords -> string -> T list
  val print_name: Keyword.keywords -> string -> string
  val print_properties: Keyword.keywords -> Properties.T -> string
  val make: (int * int) * string -> Position.T -> T * Position.T
  val make_string: string * Position.T -> T
  val make_string0: string -> T
  val make_int: int -> T list
  val make_src: string * Position.T -> T list -> src
  type 'a parser = T list -> 'a * T list
  type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)
  val syntax_generic: 'a context_parser -> src -> Context.generic -> 'a * Context.generic
  val syntax: 'a context_parser -> src -> Proof.context -> 'a * Proof.context
  val read: Proof.context -> 'a parser -> src -> 'a
end;

structure Token: TOKEN =
struct

(** tokens **)

(* token kind *)

datatype kind =
  (*immediate source*)
  Command | Keyword | Ident | Long_Ident | Sym_Ident | Var | Type_Ident | Type_Var | Nat |
  Float | Space |
  (*delimited content*)
  String | Alt_String | Cartouche |
  Control of Antiquote.control |
  Comment of Comment.kind option |
  (*special content*)
  Error of string | EOF;

val control_kind = Control Antiquote.no_control;

fun equiv_kind kind kind' =
  (case (kind, kind') of
    (Control _, Control _) => true
  | (Error _, Error _) => true
  | _ => kind = kind');

val str_of_kind =
 fn Command => "command"
  | Keyword => "keyword"
  | Ident => "identifier"
  | Long_Ident => "long identifier"
  | Sym_Ident => "symbolic identifier"
  | Var => "schematic variable"
  | Type_Ident => "type variable"
  | Type_Var => "schematic type variable"
  | Nat => "natural number"
  | Float => "floating-point number"
  | Space => "white space"
  | String => "quoted string"
  | Alt_String => "back-quoted string"
  | Cartouche => "text cartouche"
  | Control _ => "control cartouche"
  | Comment NONE => "informal comment"
  | Comment (SOME _) => "formal comment"
  | Error _ => "bad input"
  | EOF => "end-of-input";

val immediate_kinds =
  Vector.fromList
    [Command, Keyword, Ident, Long_Ident, Sym_Ident, Var, Type_Ident, Type_Var, Nat, Float, Space];

val delimited_kind =
  (fn String => true
    | Alt_String => true
    | Cartouche => true
    | Control _ => true
    | Comment _ => true
    | _ => false);


(* datatype token *)

(*The value slot assigns an (optional) internal value to a token,
  usually as a side-effect of special scanner setup (see also
  args.ML).  Note that an assignable ref designates an intermediate
  state of internalization -- it is NOT meant to persist.*)

type file = {src_path: Path.T, lines: string list, digest: SHA1.digest, pos: Position.T};

type name_value = {name: string, kind: string, print: Proof.context -> Markup.T * xstring};

datatype T = Token of (Symbol_Pos.text * Position.range) * (kind * string) * slot

and slot =
  Slot |
  Value of value option |
  Assignable of value option Unsynchronized.ref

and value =
  Source of T list |
  Literal of bool * Markup.T |
  Name of name_value * morphism |
  Typ of typ |
  Term of term |
  Fact of string option * thm list |  (*optional name for dynamic fact, i.e. fact "variable"*)
  Attribute of attribute Morphism.entity |
  Declaration of Morphism.declaration_entity |
  Files of file Exn.result list |
  Output of XML.body option;

type src = T list;


(* position *)

fun pos_of (Token ((_, (pos, _)), _, _)) = pos;
fun end_pos_of (Token ((_, (_, pos)), _, _)) = pos;

fun adjust_offsets adjust (Token ((x, range), y, z)) =
  Token ((x, apply2 (Position.adjust_offsets adjust) range), y, z);

fun input_position [] = NONE
  | input_position (tok :: _) = SOME (Position.here (pos_of tok));

fun context_input_position (_: Context.generic, []) = NONE
  | context_input_position (_, tok :: _) = SOME (Position.here (pos_of tok));


(* stopper *)

fun mk_eof pos = Token (("", (pos, Position.none)), (EOF, ""), Slot);
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _), _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _), _)) = k;
fun is_kind k (Token (_, (k', _), _)) = equiv_kind k k';

fun get_control tok =
  (case kind_of tok of Control control => SOME control | _ => NONE);

val is_command = is_kind Command;

fun keyword_with pred (Token (_, (Keyword, x), _)) = pred x
  | keyword_with _ _ = false;

val is_command_modifier = keyword_with (fn x => x = "private" orelse x = "qualified");

fun ident_with pred (Token (_, (Ident, x), _)) = pred x
  | ident_with _ _ = false;

fun is_ignored (Token (_, (Space, _), _)) = true
  | is_ignored (Token (_, (Comment NONE, _), _)) = true
  | is_ignored _ = false;

fun is_proper (Token (_, (Space, _), _)) = false
  | is_proper (Token (_, (Comment _, _), _)) = false
  | is_proper _ = true;

fun is_comment (Token (_, (Comment _, _), _)) = true
  | is_comment _ = false;

fun is_informal_comment (Token (_, (Comment NONE, _), _)) = true
  | is_informal_comment _ = false;

fun is_formal_comment (Token (_, (Comment (SOME _), _), _)) = true
  | is_formal_comment _ = false;

fun is_document_marker (Token (_, (Comment (SOME Comment.Marker), _), _)) = true
  | is_document_marker _ = false;

fun is_begin_ignore (Token (_, (Comment NONE, "<"), _)) = true
  | is_begin_ignore _ = false;

fun is_end_ignore (Token (_, (Comment NONE, ">"), _)) = true
  | is_end_ignore _ = false;

fun is_error (Token (_, (Error _, _), _)) = true
  | is_error _ = false;


(* blanks and newlines -- space tokens obey lines *)

fun is_space (Token (_, (Space, _), _)) = true
  | is_space _ = false;

fun is_blank (Token (_, (Space, x), _)) = not (String.isSuffix "\n" x)
  | is_blank _ = false;

fun is_newline (Token (_, (Space, x), _)) = String.isSuffix "\n" x
  | is_newline _ = false;


(* range of tokens *)

fun range_of (toks as tok :: _) =
      let val pos' = end_pos_of (List.last toks)
      in Position.range (pos_of tok, pos') end
  | range_of [] = Position.no_range;

val core_range_of =
  drop_prefix is_ignored #> drop_suffix is_ignored #> range_of;


(* token content *)

fun content_of (Token (_, (_, x), _)) = x;
fun source_of (Token ((source, _), _, _)) = source;

fun input_of (Token ((source, range), (kind, _), _)) =
  Input.source (delimited_kind kind) source range;

fun inner_syntax_of tok =
  let val x = content_of tok
  in if YXML.detect x then x else Syntax.implode_input (input_of tok) end;


(* markup reports *)

local

val token_kind_markup =
 fn Var => (Markup.var, "")
  | Type_Ident => (Markup.tfree, "")
  | Type_Var => (Markup.tvar, "")
  | String => (Markup.string, "")
  | Alt_String => (Markup.alt_string, "")
  | Cartouche => (Markup.cartouche, "")
  | Control _ => (Markup.cartouche, "")
  | Comment _ => (Markup.comment, "")
  | Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun keyword_reports tok = map (fn markup => ((pos_of tok, markup), ""));

fun command_markups keywords x =
  if Keyword.is_theory_end keywords x then [Markup.keyword2 |> Markup.keyword_properties]
  else
    (if Keyword.is_proof_asm keywords x then [Markup.keyword3]
     else if Keyword.is_improper keywords x then [Markup.keyword1, Markup.improper]
     else [Markup.keyword1])
    |> map Markup.command_properties;

in

fun keyword_markup (important, keyword) x =
  if important orelse Symbol.is_ascii_identifier x then keyword else Markup.delimiter;

fun completion_report tok =
  if is_kind Keyword tok
  then map (fn m => ((pos_of tok, m), "")) (Completion.suppress_abbrevs (content_of tok))
  else [];

fun reports keywords tok =
  if is_command tok then
    keyword_reports tok (command_markups keywords (content_of tok))
  else if is_kind Keyword tok then
    keyword_reports tok
      [keyword_markup (false, Markup.keyword2 |> Markup.keyword_properties) (content_of tok)]
  else
    let
      val pos = pos_of tok;
      val (m, text) = token_kind_markup (kind_of tok);
      val deleted = Symbol_Pos.explode_deleted (source_of tok, pos);
    in ((pos, m), text) :: map (fn p => ((p, Markup.delete), "")) deleted end;

fun markups keywords = map (#2 o #1) o reports keywords;

end;


(* unparse *)

fun unparse (Token (_, (kind, x), _)) =
  (case kind of
    String => Symbol_Pos.quote_string_qq x
  | Alt_String => Symbol_Pos.quote_string_bq x
  | Cartouche => cartouche x
  | Control control => Symbol_Pos.content (Antiquote.control_symbols control)
  | Comment NONE => enclose "(*" "*)" x
  | EOF => ""
  | _ => x);

fun print tok = Markup.markups (markups Keyword.empty_keywords tok) (unparse tok);

fun text_of tok =
  let
    val k = str_of_kind (kind_of tok);
    val ms = markups Keyword.empty_keywords tok;
    val s = unparse tok;
  in
    if s = "" then (k, "")
    else if size s < 40 andalso not (exists_string (fn c => c = "\n") s)
    then (k ^ " " ^ Markup.markups ms s, "")
    else (k, Markup.markups ms s)
  end;



(** associated values **)

(* inlined file content *)

fun file_source (file: file) =
  let
    val text = cat_lines (#lines file);
    val end_pos = Position.symbol_explode text (#pos file);
  in Input.source true text (Position.range (#pos file, end_pos)) end;

fun get_files (Token (_, _, Value (SOME (Files files)))) = files
  | get_files _ = [];

fun put_files [] tok = tok
  | put_files files (Token (x, y, Slot)) = Token (x, y, Value (SOME (Files files)))
  | put_files _ tok = raise Fail ("Cannot put inlined files here" ^ Position.here (pos_of tok));


(* document output *)

fun get_output (Token (_, _, Value (SOME (Output output)))) = output
  | get_output _ = NONE;

fun put_output output (Token (x, y, Slot)) = Token (x, y, Value (SOME (Output (SOME output))))
  | put_output _ tok = raise Fail ("Cannot put document output here" ^ Position.here (pos_of tok));


(* access values *)

fun get_value (Token (_, _, Value v)) = v
  | get_value _ = NONE;

fun map_value f (Token (x, y, Value (SOME v))) = Token (x, y, Value (SOME (f v)))
  | map_value _ tok = tok;


(* reports of value *)

fun get_assignable_value (Token (_, _, Assignable r)) = ! r
  | get_assignable_value (Token (_, _, Value v)) = v
  | get_assignable_value _ = NONE;

fun reports_of_value tok =
  (case get_assignable_value tok of
    SOME (Literal markup) =>
      let
        val pos = pos_of tok;
        val x = content_of tok;
      in
        if Position.is_reported pos then
          map (pair pos) (keyword_markup markup x :: Completion.suppress_abbrevs x)
        else []
      end
  | _ => []);


(* name value *)

fun name_value a = Name (a, Morphism.identity);

fun get_name tok =
  (case get_assignable_value tok of
    SOME (Name (a, _)) => SOME a
  | _ => NONE);


(* maxidx *)

fun declare_maxidx tok =
  (case get_value tok of
    SOME (Source src) => fold declare_maxidx src
  | SOME (Typ T) => Variable.declare_maxidx (Term.maxidx_of_typ T)
  | SOME (Term t) => Variable.declare_maxidx (Term.maxidx_of_term t)
  | SOME (Fact (_, ths)) => fold (Variable.declare_maxidx o Thm.maxidx_of) ths
  | SOME (Attribute _) => I  (* FIXME !? *)
  | SOME (Declaration decl) =>
      (fn ctxt =>
        let val ctxt' = Context.proof_map (Morphism.form decl) ctxt
        in Variable.declare_maxidx (Variable.maxidx_of ctxt') ctxt end)
  | _ => I);


(* fact values *)

fun map_facts f =
  map_value (fn v =>
    (case v of
      Source src => Source (map (map_facts f) src)
    | Fact (a, ths) => Fact (a, f a ths)
    | _ => v));


(* implicit context *)

local

fun context thm_context morphism_context attribute_context declaration_context =
  let
    fun token_context tok = map_value
      (fn Source src => Source (map token_context src)
        | Fact (a, ths) => Fact (a, map thm_context ths)
        | Name (a, phi) => Name (a, morphism_context phi)
        | Attribute a => Attribute (attribute_context a)
        | Declaration a => Declaration (declaration_context a)
        | v => v) tok;
  in token_context end;

in

val trim_context =
  context Thm.trim_context Morphism.reset_context
    Morphism.entity_reset_context Morphism.entity_reset_context;

fun transfer thy =
  context (Thm.transfer thy) (Morphism.set_context thy)
    (Morphism.entity_set_context thy) (Morphism.entity_set_context thy);

end;


(* transform *)

fun transform phi =
  map_value (fn v =>
    (case v of
      Source src => Source (map (transform phi) src)
    | Literal _ => v
    | Name (a, psi) => Name (a, psi $> phi)
    | Typ T => Typ (Morphism.typ phi T)
    | Term t => Term (Morphism.term phi t)
    | Fact (a, ths) => Fact (a, Morphism.fact phi ths)
    | Attribute att => Attribute (Morphism.transform phi att)
    | Declaration decl => Declaration (Morphism.transform phi decl)
    | Files _ => v
    | Output _ => v));


(* static binding *)

(*1st stage: initialize assignable slots*)
fun init_assignable tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Assignable (Unsynchronized.ref NONE))
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := NONE; tok));

(*2nd stage: assign values as side-effect of scanning*)
fun assign v tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Value v)
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := v; tok));

fun evaluate mk eval arg =
  let val x = eval arg in (assign (SOME (mk x)) arg; x) end;

(*3rd stage: static closure of final values*)
fun closure (Token (x, y, Assignable (Unsynchronized.ref v))) = Token (x, y, Value v)
  | closure tok = tok;


(* pretty *)

fun pretty_keyword3 tok =
  let val props = Position.properties_of (pos_of tok)
  in Pretty.mark_str (Markup.properties props Markup.keyword3, unparse tok) end;

fun pretty_value ctxt tok =
  (case get_value tok of
    SOME (Literal markup) =>
      let val x = content_of tok
      in Pretty.mark_str (keyword_markup markup x, x) end
  | SOME (Name ({print, ...}, _)) => Pretty.quote (Pretty.mark_str (print ctxt))
  | SOME (Typ T) => Syntax.pretty_typ ctxt T
  | SOME (Term t) => Syntax.pretty_term ctxt t
  | SOME (Fact (_, ths)) =>
      Pretty.enclose "(" ")" (Pretty.breaks (map (Pretty.cartouche o Thm.pretty_thm ctxt) ths))
  | SOME (Attribute _) => pretty_keyword3 tok
  | SOME (Declaration _) => pretty_keyword3 tok
  | _ => Pretty.marks_str (markups Keyword.empty_keywords tok, unparse tok));


(* src *)

fun dest_src ([]: src) = raise Fail "Empty token source"
  | dest_src (head :: args) = (head, args);

fun name_of_src src =
  let
    val head = #1 (dest_src src);
    val name =
      (case get_name head of
        SOME {name, ...} => name
      | NONE => content_of head);
  in (name, pos_of head) end;

val args_of_src = #2 o dest_src;

fun pretty_src ctxt src =
  let
    val (head, args) = dest_src src;
    val prt_name =
      (case get_name head of
        SOME {print, ...} => Pretty.mark_str (print ctxt)
      | NONE => Pretty.str (content_of head));
  in Pretty.block (Pretty.breaks (Pretty.quote prt_name :: map (pretty_value ctxt) args)) end;

fun checked_src (head :: _) = is_some (get_name head)
  | checked_src [] = true;

fun check_src ctxt get_table src =
  let
    val (head, args) = dest_src src;
    val table = get_table ctxt;
  in
    (case get_name head of
      SOME {name, ...} => (src, Name_Space.get table name)
    | NONE =>
        let
          val pos = pos_of head;
          val (name, x) = Name_Space.check (Context.Proof ctxt) table (content_of head, pos);
          val _ = Context_Position.report ctxt pos Markup.operator;
          val kind = Name_Space.kind_of (Name_Space.space_of_table table);
          fun print ctxt' =
            Name_Space.markup_extern ctxt' (Name_Space.space_of_table (get_table ctxt')) name;
          val value = name_value {name = name, kind = kind, print = print};
          val head' = closure (assign (SOME value) head);
        in (head' :: args, x) end)
  end;



(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "Outer lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);


(* scan symbolic idents *)

val scan_symid =
  Scan.many1 (Symbol.is_symbolic_char o Symbol_Pos.symbol) ||
  Scan.one (Symbol.is_symbolic o Symbol_Pos.symbol) >> single;

fun is_symid str =
  (case try Symbol.explode str of
    SOME [s] => Symbol.is_symbolic s orelse Symbol.is_symbolic_char s
  | SOME ss => forall Symbol.is_symbolic_char ss
  | _ => false);

fun ident_or_symbolic "begin" = false
  | ident_or_symbolic ":" = true
  | ident_or_symbolic "::" = true
  | ident_or_symbolic s = Symbol_Pos.is_identifier s orelse is_symid s;


(* scan cartouche *)

val scan_cartouche =
  Symbol_Pos.scan_pos --
    ((Symbol_Pos.scan_cartouche err_prefix >> Symbol_Pos.cartouche_content) -- Symbol_Pos.scan_pos);


(* scan space *)

fun space_symbol (s, _) = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  Scan.many1 space_symbol @@@ Scan.optional ($$$ "\n") [] ||
  Scan.many space_symbol @@@ $$$ "\n";


(* scan comment *)

val scan_comment =
  Symbol_Pos.scan_pos -- (Symbol_Pos.scan_comment_body err_prefix -- Symbol_Pos.scan_pos);



(** token sources **)

local

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun token k ss =
  Token ((Symbol_Pos.implode ss, Symbol_Pos.range ss), (k, Symbol_Pos.content ss), Slot);

fun token_range k (pos1, (ss, pos2)) =
  Token (Symbol_Pos.implode_range (pos1, pos2) ss, (k, Symbol_Pos.content ss), Slot);

fun scan_token keywords = !!! "bad input"
  (Symbol_Pos.scan_string_qq err_prefix >> token_range String ||
    Symbol_Pos.scan_string_bq err_prefix >> token_range Alt_String ||
    scan_comment >> token_range (Comment NONE) ||
    Comment.scan_outer >> (fn (k, ss) => token (Comment (SOME k)) ss) ||
    scan_cartouche >> token_range Cartouche ||
    Antiquote.scan_control err_prefix >> (fn control =>
      token (Control control) (Antiquote.control_symbols control)) ||
    scan_space >> token Space ||
    (Scan.max token_leq
      (Scan.max token_leq
        (Scan.literal (Keyword.major_keywords keywords) >> pair Command)
        (Scan.literal (Keyword.minor_keywords keywords) >> pair Keyword))
      (Lexicon.scan_longid >> pair Long_Ident ||
        Lexicon.scan_id >> pair Ident ||
        Lexicon.scan_var >> pair Var ||
        Lexicon.scan_tid >> pair Type_Ident ||
        Lexicon.scan_tvar >> pair Type_Var ||
        Symbol_Pos.scan_float >> pair Float ||
        Symbol_Pos.scan_nat >> pair Nat ||
        scan_symid >> pair Sym_Ident) >> uncurry token));

fun recover msg =
  (Symbol_Pos.recover_string_qq ||
    Symbol_Pos.recover_string_bq ||
    Symbol_Pos.recover_cartouche ||
    Symbol_Pos.recover_comment ||
    Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Error msg));

in

fun make_source keywords {strict} =
  let
    val scan_strict = Scan.bulk (scan_token keywords);
    val scan = if strict then scan_strict else Scan.recover scan_strict recover;
  in Source.source Symbol_Pos.stopper scan end;

fun read_cartouche syms =
  (case Scan.read Symbol_Pos.stopper (scan_cartouche >> token_range Cartouche) syms of
    SOME tok => tok
  | NONE => error ("Single cartouche expected" ^ Position.here (#1 (Symbol_Pos.range syms))));

end;


(* explode *)

fun tokenize keywords strict syms =
  Source.of_list syms |> make_source keywords strict |> Source.exhaust;

fun explode keywords pos text =
  Symbol_Pos.explode (text, pos) |> tokenize keywords {strict = false};

fun explode0 keywords = explode keywords Position.none;


(* print names in parsable form *)

fun print_name keywords name =
  ((case explode keywords Position.none name of
    [tok] => not (member (op =) [Ident, Long_Ident, Sym_Ident, Nat] (kind_of tok))
  | _ => true) ? Symbol_Pos.quote_string_qq) name;

fun print_properties keywords =
  map (apply2 (print_name keywords) #> (fn (a, b) => a ^ " = " ^ b)) #> commas #> enclose "[" "]";


(* make *)

fun make ((k, n), s) pos =
  let
    val pos' = Position.shift_offsets {remove_id = false} n pos;
    val range = Position.range (pos, pos');
    val tok =
      if 0 <= k andalso k < Vector.length immediate_kinds then
        Token ((s, range), (Vector.nth immediate_kinds k, s), Slot)
      else
        (case explode Keyword.empty_keywords pos s of
          [tok] => tok
        | _ => Token ((s, range), (Error (err_prefix ^ "exactly one token expected"), s), Slot))
  in (tok, pos') end;

fun make_string (s, pos) =
  let
    val Token ((x, _), y, z) = #1 (make ((~1, 0), Symbol_Pos.quote_string_qq s) Position.none);
    val pos' = Position.no_range_position pos;
  in Token ((x, (pos', pos')), y, z) end;

fun make_string0 s = make_string (s, Position.none);

val make_int = explode Keyword.empty_keywords Position.none o signed_string_of_int;

fun make_src a args = make_string a :: args;



(** parsers **)

type 'a parser = T list -> 'a * T list;
type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list);


(* wrapped syntax *)

fun syntax_generic scan src0 context =
  let
    val src = map (transfer (Context.theory_of context)) src0;
    val (name, pos) = name_of_src src;
    val old_reports = maps reports_of_value src;
    val args1 = map init_assignable (args_of_src src);
    fun reported_text () =
      if Context_Position.reports_enabled_generic context then
        let val new_reports = maps (reports_of_value o closure) args1 in
          if old_reports <> new_reports then
            map (fn (p, m) => Position.reported_text p m "") new_reports
          else []
        end
      else [];
  in
    (case Scan.error (Scan.finite' stopper (Scan.option scan)) (context, args1) of
      (SOME x, (context', [])) =>
        let val _ = Output.report (reported_text ())
        in (x, context') end
    | (_, (context', args2)) =>
        let
          val print_name =
            (case get_name (hd src) of
              NONE => quote name
            | SOME {kind, print, ...} =>
                let
                  val ctxt' = Context.proof_of context';
                  val (markup, xname) = print ctxt';
                in plain_words kind ^ " " ^ quote (Markup.markup markup xname) end);
          val print_args =
            if null args2 then "" else ":\n  " ^ implode_space (map print args2);
        in
          error ("Bad arguments for " ^ print_name ^ Position.here pos ^ print_args ^
            Markup.markup_report (implode (reported_text ())))
        end)
  end;

fun syntax scan src = apsnd Context.the_proof o syntax_generic scan src o Context.Proof;

fun read ctxt scan src = syntax (Scan.lift scan) src ctxt |> #1;

end;

type 'a parser = 'a Token.parser;
type 'a context_parser = 'a Token.context_parser;
