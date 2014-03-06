(*  Title:      Pure/Isar/args.ML
    Author:     Markus Wenzel, TU Muenchen

Parsing with implicit value assignment.  Concrete argument syntax of
attributes, methods etc.
*)

signature ARGS =
sig
  type src
  val src: (string * Token.T list) * Position.T -> src
  val dest_src: src -> (string * Token.T list) * Position.T
  val pretty_src: Proof.context -> src -> Pretty.T
  val map_name: (string -> string) -> src -> src
  val transform_values: morphism -> src -> src
  val init_assignable: src -> src
  val closure: src -> src
  val context: Proof.context context_parser
  val theory: theory context_parser
  val $$$ : string -> string parser
  val add: string parser
  val del: string parser
  val colon: string parser
  val query: string parser
  val bang: string parser
  val query_colon: string parser
  val bang_colon: string parser
  val parens: 'a parser -> 'a parser
  val bracks: 'a parser -> 'a parser
  val mode: string -> bool parser
  val maybe: 'a parser -> 'a option parser
  val cartouche_inner_syntax: string parser
  val cartouche_source_position: Symbol_Pos.source parser
  val name_inner_syntax: string parser
  val name_source_position: Symbol_Pos.source parser
  val name: string parser
  val binding: binding parser
  val alt_name: string parser
  val symbol: string parser
  val liberal_name: string parser
  val var: indexname parser
  val internal_text: string parser
  val internal_typ: typ parser
  val internal_term: term parser
  val internal_fact: thm list parser
  val internal_attribute: (morphism -> attribute) parser
  val named_text: (string -> string) -> string parser
  val named_typ: (string -> typ) -> typ parser
  val named_term: (string -> term) -> term parser
  val named_fact: (string -> thm list) -> thm list parser
  val named_attribute:
    (string * Position.T -> morphism -> attribute) -> (morphism -> attribute) parser
  val typ_abbrev: typ context_parser
  val typ: typ context_parser
  val term: term context_parser
  val term_pattern: term context_parser
  val term_abbrev: term context_parser
  val prop: term context_parser
  val type_name: {proper: bool, strict: bool} -> string context_parser
  val const: {proper: bool, strict: bool} -> string context_parser
  val goal_spec: ((int -> tactic) -> tactic) context_parser
  val parse: Token.T list parser
  val parse1: (string -> bool) -> Token.T list parser
  val attribs: (string -> string) -> src list parser
  val opt_attribs: (string -> string) -> src list parser
  val thm_name: (string -> string) -> string -> (binding * src list) parser
  val opt_thm_name: (string -> string) -> string -> (binding * src list) parser
  val syntax: string -> 'a context_parser -> src -> Context.generic -> 'a * Context.generic
  val context_syntax: string -> 'a context_parser -> src -> Proof.context -> 'a * Proof.context
end;

structure Args: ARGS =
struct

(** datatype src **)

datatype src = Src of (string * Token.T list) * Position.T;

val src = Src;
fun dest_src (Src src) = src;

fun pretty_src ctxt src =
  let
    val prt_thm = Pretty.backquote o Display.pretty_thm ctxt;
    fun prt arg =
      (case Token.get_value arg of
        SOME (v as Token.Literal s) => Pretty.marks_str (Token.value_markup v, s)
      | SOME (Token.Text s) => Pretty.str (quote s)
      | SOME (Token.Typ T) => Syntax.pretty_typ ctxt T
      | SOME (Token.Term t) => Syntax.pretty_term ctxt t
      | SOME (Token.Fact ths) => Pretty.enclose "(" ")" (Pretty.breaks (map prt_thm ths))
      | _ => Pretty.mark_str (Token.markup arg, Token.unparse arg));
    val (s, args) = #1 (dest_src src);
  in Pretty.block (Pretty.breaks (Pretty.str s :: map prt args)) end;

fun map_name f (Src ((s, args), pos)) = Src ((f s, args), pos);
fun map_args f (Src ((s, args), pos)) = Src ((s, map f args), pos);


(* values *)

fun transform_values phi = map_args (Token.map_value
  (fn Token.Typ T => Token.Typ (Morphism.typ phi T)
    | Token.Term t => Token.Term (Morphism.term phi t)
    | Token.Fact ths => Token.Fact (Morphism.fact phi ths)
    | Token.Attribute att => Token.Attribute (Morphism.transform phi att)
    | tok => tok));

val init_assignable = map_args Token.init_assignable;
val closure = map_args Token.closure;



(** argument scanners **)

(* context *)

fun context x = (Scan.state >> Context.proof_of) x;
fun theory x = (Scan.state >> Context.theory_of) x;


(* basic *)

fun token atom = Scan.ahead Parse.not_eof --| atom;

val ident = token
  (Parse.short_ident || Parse.long_ident || Parse.sym_ident || Parse.term_var ||
    Parse.type_ident || Parse.type_var || Parse.number);

val string = token (Parse.string || Parse.verbatim);
val alt_string = token Parse.alt_string;
val symbolic = token Parse.keyword_ident_or_symbolic;

fun $$$ x =
  (ident || token Parse.keyword) :|-- (fn tok =>
    let val y = Token.content_of tok
    in if x = y then (Token.assign (SOME (Token.Literal x)) tok; Scan.succeed x) else Scan.fail end);


val named = ident || string;

val add = $$$ "add";
val del = $$$ "del";
val colon = $$$ ":";
val query = $$$ "?";
val bang = $$$ "!";
val query_colon = $$$ "?" ^^ $$$ ":";
val bang_colon = $$$ "!" ^^ $$$ ":";

fun parens scan = $$$ "(" |-- scan --| $$$ ")";
fun bracks scan = $$$ "[" |-- scan --| $$$ "]";
fun mode s = Scan.optional (parens ($$$ s) >> K true) false;
fun maybe scan = $$$ "_" >> K NONE || scan >> SOME;

val cartouche = token Parse.cartouche;
val cartouche_inner_syntax = cartouche >> Token.inner_syntax_of;
val cartouche_source_position = cartouche >> Token.source_position_of;

val name_inner_syntax = named >> Token.inner_syntax_of;
val name_source_position = named >> Token.source_position_of;

val name = named >> Token.content_of;
val binding = Parse.position name >> Binding.make;
val alt_name = alt_string >> Token.content_of;
val symbol = symbolic >> Token.content_of;
val liberal_name = symbol || name;

val var = (ident >> Token.content_of) :|-- (fn x =>
  (case Lexicon.read_variable x of SOME v => Scan.succeed v | NONE => Scan.fail));


(* values *)

fun value dest = Scan.some (fn arg =>
  (case Token.get_value arg of SOME v => (SOME (dest v) handle Match => NONE) | NONE => NONE));

fun evaluate mk eval arg =
  let val x = eval arg in (Token.assign (SOME (mk x)) arg; x) end;

val internal_text = value (fn Token.Text s => s);
val internal_typ = value (fn Token.Typ T => T);
val internal_term = value (fn Token.Term t => t);
val internal_fact = value (fn Token.Fact ths => ths);
val internal_attribute = value (fn Token.Attribute att => att);

fun named_text intern = internal_text || named >> evaluate Token.Text (intern o Token.content_of);
fun named_typ readT = internal_typ || named >> evaluate Token.Typ (readT o Token.inner_syntax_of);
fun named_term read = internal_term || named >> evaluate Token.Term (read o Token.inner_syntax_of);

fun named_fact get = internal_fact || named >> evaluate Token.Fact (get o Token.content_of) ||
  alt_string >> evaluate Token.Fact (get o Token.inner_syntax_of);

fun named_attribute att =
  internal_attribute ||
  named >> evaluate Token.Attribute (fn tok => att (Token.content_of tok, Token.pos_of tok));


(* terms and types *)

val typ_abbrev = Scan.peek (named_typ o Proof_Context.read_typ_abbrev o Context.proof_of);
val typ = Scan.peek (named_typ o Syntax.read_typ o Context.proof_of);
val term = Scan.peek (named_term o Syntax.read_term o Context.proof_of);
val term_pattern = Scan.peek (named_term o Proof_Context.read_term_pattern o Context.proof_of);
val term_abbrev = Scan.peek (named_term o Proof_Context.read_term_abbrev o Context.proof_of);
val prop = Scan.peek (named_term o Syntax.read_prop o Context.proof_of);


(* type and constant names *)

fun type_name flags =
  Scan.peek (fn ctxt => named_typ (Proof_Context.read_type_name (Context.proof_of ctxt) flags))
  >> (fn Type (c, _) => c | TFree (a, _) => a | _ => "");

fun const flags =
  Scan.peek (fn ctxt => named_term (Proof_Context.read_const (Context.proof_of ctxt) flags dummyT))
  >> (fn Const (c, _) => c | Free (x, _) => x | _ => "");


(* improper method arguments *)

val from_to =
  Parse.nat -- ($$$ "-" |-- Parse.nat) >> (fn (i, j) => fn tac => Seq.INTERVAL tac i j) ||
  Parse.nat --| $$$ "-" >> (fn i => fn tac => fn st => Seq.INTERVAL tac i (Thm.nprems_of st) st) ||
  Parse.nat >> (fn i => fn tac => tac i) ||
  $$$ "!" >> K ALLGOALS;

val goal = $$$ "[" |-- Parse.!!! (from_to --| $$$ "]");
fun goal_spec x = Scan.lift (Scan.optional goal (fn tac => tac 1)) x;


(* arguments within outer syntax *)

val argument_kinds =
 [Token.Ident, Token.LongIdent, Token.SymIdent, Token.Var, Token.TypeIdent, Token.TypeVar,
  Token.Nat, Token.Float, Token.String, Token.AltString, Token.Cartouche, Token.Verbatim];

fun parse_args is_symid =
  let
    fun argument blk =
      Parse.group (fn () => "argument")
        (Scan.one (fn tok =>
          let val kind = Token.kind_of tok in
            member (op =) argument_kinds kind orelse
            Token.keyword_with is_symid tok orelse
            (blk andalso Token.keyword_with (fn s => s = ",") tok)
          end));

    fun args blk x = Scan.optional (args1 blk) [] x
    and args1 blk x =
      ((Scan.repeat1
        (Scan.repeat1 (argument blk) ||
          argsp "(" ")" ||
          argsp "[" "]")) >> flat) x
    and argsp l r x =
      (token (Parse.$$$ l) ::: Parse.!!! (args true @@@ (token (Parse.$$$ r) >> single))) x;
  in (args, args1) end;

val parse = #1 (parse_args Token.ident_or_symbolic) false;
fun parse1 is_symid = #2 (parse_args is_symid) false;


(* attributes *)

fun attribs intern =
  let
    val attrib_name = internal_text || (symbolic || named)
      >> evaluate Token.Text (intern o Token.content_of);
    val attrib = Parse.position (attrib_name -- Parse.!!! parse) >> src;
  in $$$ "[" |-- Parse.!!! (Parse.list attrib --| $$$ "]") end;

fun opt_attribs intern = Scan.optional (attribs intern) [];


(* theorem specifications *)

fun thm_name intern s = binding -- opt_attribs intern --| $$$ s;

fun opt_thm_name intern s =
  Scan.optional
    ((binding -- opt_attribs intern || attribs intern >> pair Binding.empty) --| $$$ s)
    (Binding.empty, []);



(** syntax wrapper **)

fun syntax kind scan (Src ((s, args0), pos)) context =
  let
    val args1 = map Token.init_assignable args0;
    fun reported_text () =
      if Context_Position.is_visible_generic context then
        maps (Token.reports_of_value o Token.closure) args1
        |> map (fn (p, m) => Position.reported_text p m "")
        |> implode
      else "";
  in
    (case Scan.error (Scan.finite' Token.stopper (Scan.option scan)) (context, args1) of
      (SOME x, (context', [])) => (Output.report (reported_text ()); (x, context'))
    | (_, (_, args2)) =>
        error ("Bad arguments for " ^ kind ^ " " ^ quote s ^ Position.here pos ^
          (if null args2 then "" else ":\n  " ^ space_implode " " (map Token.print args2)) ^
          Markup.markup Markup.report (reported_text ())))
  end;

fun context_syntax kind scan src =
  apsnd Context.the_proof o syntax kind scan src o Context.Proof;

end;
