(*  Title:      Pure/Isar/args.ML
    Author:     Markus Wenzel, TU Muenchen

Parsing with implicit value assigment.  Concrete argument syntax of
attributes, methods etc.
*)

signature ARGS =
sig
  type T = OuterLex.token
  type src
  val src: (string * T list) * Position.T -> src
  val dest_src: src -> (string * T list) * Position.T
  val pretty_src: Proof.context -> src -> Pretty.T
  val map_name: (string -> string) -> src -> src
  val morph_values: morphism -> src -> src
  val maxidx_values: src -> int -> int
  val assignable: src -> src
  val closure: src -> src
  val context: Context.generic * T list -> Context.proof * (Context.generic * T list)
  val theory: Context.generic * T list -> Context.theory * (Context.generic * T list)
  val $$$ : string -> T list -> string * T list
  val add: T list -> string * T list
  val del: T list -> string * T list
  val colon: T list -> string * T list
  val query: T list -> string * T list
  val bang: T list -> string * T list
  val query_colon: T list -> string * T list
  val bang_colon: T list -> string * T list
  val parens: (T list -> 'a * T list) -> T list -> 'a * T list
  val bracks: (T list -> 'a * T list) -> T list -> 'a * T list
  val mode: string -> 'a * T list -> bool * ('a * T list)
  val maybe: (T list -> 'a * T list) -> T list -> 'a option * T list
  val name_source: T list -> string * T list
  val name_source_position: T list -> (SymbolPos.text * Position.T) * T list
  val name: T list -> string * T list
  val binding: T list -> binding * T list
  val alt_name: T list -> string * T list
  val symbol: T list -> string * T list
  val liberal_name: T list -> string * T list
  val var: T list -> indexname * T list
  val internal_text: T list -> string * T list
  val internal_typ: T list -> typ * T list
  val internal_term: T list -> term * T list
  val internal_fact: T list -> thm list * T list
  val internal_attribute: T list -> (morphism -> attribute) * T list
  val named_text: (string -> string) -> T list -> string * T list
  val named_typ: (string -> typ) -> T list -> typ * T list
  val named_term: (string -> term) -> T list -> term * T list
  val named_fact: (string -> thm list) -> T list -> thm list * T list
  val named_attribute: (string -> morphism -> attribute) -> T list ->
    (morphism -> attribute) * T list
  val typ_abbrev: Context.generic * T list -> typ * (Context.generic * T list)
  val typ: Context.generic * T list -> typ * (Context.generic * T list)
  val term: Context.generic * T list -> term * (Context.generic * T list)
  val term_abbrev: Context.generic * T list -> term * (Context.generic * T list)
  val prop: Context.generic * T list -> term * (Context.generic * T list)
  val tyname: Context.generic * T list -> string * (Context.generic * T list)
  val const: Context.generic * T list -> string * (Context.generic * T list)
  val const_proper: Context.generic * T list -> string * (Context.generic * T list)
  val bang_facts: Context.generic * T list -> thm list * (Context.generic * T list)
  val goal_spec: ((int -> tactic) -> tactic) -> ('a * T list)
    -> ((int -> tactic) -> tactic) * ('a * T list)
  val parse: OuterLex.token list -> T list * OuterLex.token list
  val parse1: (string -> bool) -> OuterLex.token list -> T list * OuterLex.token list
  val attribs: (string -> string) -> T list -> src list * T list
  val opt_attribs: (string -> string) -> T list -> src list * T list
  val thm_name: (string -> string) -> string -> T list -> (binding * src list) * T list
  val opt_thm_name: (string -> string) -> string -> T list -> (binding * src list) * T list
  val syntax: string -> ('b * T list -> 'a * ('b * T list)) -> src -> 'b -> 'a * 'b
  val context_syntax: string -> (Context.generic * T list -> 'a * (Context.generic * T list)) ->
    src -> Proof.context -> 'a * Proof.context
end;

structure Args: ARGS =
struct

structure T = OuterLex;
structure P = OuterParse;



(** datatype src **)

type T = T.token;

datatype src = Src of (string * T list) * Position.T;

val src = Src;
fun dest_src (Src src) = src;

fun pretty_src ctxt src =
  let
    val prt_thm = Pretty.backquote o ProofContext.pretty_thm ctxt;
    fun prt arg =
      (case T.get_value arg of
        SOME (T.Text s) => Pretty.str (quote s)
      | SOME (T.Typ T) => Syntax.pretty_typ ctxt T
      | SOME (T.Term t) => Syntax.pretty_term ctxt t
      | SOME (T.Fact ths) => Pretty.enclose "(" ")" (Pretty.breaks (map prt_thm ths))
      | _ => Pretty.str (T.unparse arg));
    val (s, args) = #1 (dest_src src);
  in Pretty.block (Pretty.breaks (Pretty.str s :: map prt args)) end;

fun map_name f (Src ((s, args), pos)) = Src ((f s, args), pos);
fun map_args f (Src ((s, args), pos)) = Src ((s, map f args), pos);


(* values *)

fun morph_values phi = map_args (T.map_value
  (fn T.Text s => T.Text s
    | T.Typ T => T.Typ (Morphism.typ phi T)
    | T.Term t => T.Term (Morphism.term phi t)
    | T.Fact ths => T.Fact (Morphism.fact phi ths)
    | T.Attribute att => T.Attribute (Morphism.transform phi att)));

fun maxidx_values (Src ((_, args), _)) = args |> fold (fn arg =>
  (case T.get_value arg of
    SOME (T.Typ T) => Term.maxidx_typ T
  | SOME (T.Term t) => Term.maxidx_term t
  | SOME (T.Fact ths) => fold Thm.maxidx_thm ths
  | _ => I));

val assignable = map_args T.assignable;
val closure = map_args T.closure;



(** argument scanners **)

(* context *)

fun context x = (Scan.state >> Context.proof_of) x;
fun theory x = (Scan.state >> Context.theory_of) x;


(* basic *)

fun token atom = Scan.ahead P.not_eof --| atom;

val ident = token
  (P.short_ident || P.long_ident || P.sym_ident || P.term_var ||
    P.type_ident || P.type_var || P.number);

val string = token (P.string || P.verbatim);
val alt_string = token P.alt_string;
val symbolic = token P.keyword_ident_or_symbolic;

fun $$$ x = (ident >> T.content_of || P.keyword)
  :|-- (fn y => if x = y then Scan.succeed x else Scan.fail);


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
fun mode s = Scan.lift (Scan.optional (parens ($$$ s) >> K true) false);
fun maybe scan = $$$ "_" >> K NONE || scan >> SOME;

val name_source = named >> T.source_of;
val name_source_position = named >> T.source_position_of;

val name = named >> T.content_of;
val binding = P.position name >> Binding.make;
val alt_name = alt_string >> T.content_of;
val symbol = symbolic >> T.content_of;
val liberal_name = symbol || name;

val var = (ident >> T.content_of) :|-- (fn x =>
  (case Lexicon.read_variable x of SOME v => Scan.succeed v | NONE => Scan.fail));


(* values *)

fun value dest = Scan.some (fn arg =>
  (case T.get_value arg of SOME v => (SOME (dest v) handle Match => NONE) | NONE => NONE));

fun evaluate mk eval arg =
  let val x = eval arg in (T.assign (SOME (mk x)) arg; x) end;

val internal_text = value (fn T.Text s => s);
val internal_typ = value (fn T.Typ T => T);
val internal_term = value (fn T.Term t => t);
val internal_fact = value (fn T.Fact ths => ths);
val internal_attribute = value (fn T.Attribute att => att);

fun named_text intern = internal_text || named >> evaluate T.Text (intern o T.content_of);
fun named_typ readT = internal_typ || named >> evaluate T.Typ (readT o T.source_of);
fun named_term read = internal_term || named >> evaluate T.Term (read o T.source_of);
fun named_fact get = internal_fact || named >> evaluate T.Fact (get o T.content_of) ||
  alt_string >> evaluate T.Fact (get o T.source_of);
fun named_attribute att = internal_attribute || named >> evaluate T.Attribute (att o T.content_of);


(* terms and types *)

val typ_abbrev = Scan.peek (named_typ o ProofContext.read_typ_abbrev o Context.proof_of);
val typ = Scan.peek (named_typ o Syntax.read_typ o Context.proof_of);
val term = Scan.peek (named_term o Syntax.read_term o Context.proof_of);
val term_abbrev = Scan.peek (named_term o ProofContext.read_term_abbrev o Context.proof_of);
val prop = Scan.peek (named_term o Syntax.read_prop o Context.proof_of);


(* type and constant names *)

val tyname = Scan.peek (named_typ o ProofContext.read_tyname o Context.proof_of)
  >> (fn Type (c, _) => c | TFree (a, _) => a | _ => "");

val const = Scan.peek (named_term o ProofContext.read_const o Context.proof_of)
  >> (fn Const (c, _) => c | Free (x, _) => x | _ => "");

val const_proper = Scan.peek (named_term o ProofContext.read_const_proper o Context.proof_of)
  >> (fn Const (c, _) => c | _ => "");


(* improper method arguments *)

val bang_facts = Scan.peek (fn context =>
  P.position ($$$ "!") >> (fn (_, pos) =>
    (warning ("use of prems in proof method" ^ Position.str_of pos);
      Assumption.all_prems_of (Context.proof_of context))) || Scan.succeed []);

val from_to =
  P.nat -- ($$$ "-" |-- P.nat) >> (fn (i, j) => fn tac => Seq.INTERVAL tac i j) ||
  P.nat --| $$$ "-" >> (fn i => fn tac => fn st => Seq.INTERVAL tac i (Thm.nprems_of st) st) ||
  P.nat >> (fn i => fn tac => tac i) ||
  $$$ "!" >> K ALLGOALS;

val goal = $$$ "[" |-- P.!!! (from_to --| $$$ "]");
fun goal_spec def = Scan.lift (Scan.optional goal def);


(* arguments within outer syntax *)

fun parse_args is_symid =
  let
    val keyword_symid = token (P.keyword_with is_symid);
    fun atom blk = P.group "argument"
      (ident || keyword_symid || string || alt_string ||
        (if blk then token (P.$$$ ",") else Scan.fail));

    fun args blk x = Scan.optional (args1 blk) [] x
    and args1 blk x =
      ((Scan.repeat1
        (Scan.repeat1 (atom blk) ||
          argsp "(" ")" ||
          argsp "[" "]")) >> flat) x
    and argsp l r x = (token (P.$$$ l) ::: P.!!! (args true @@@ (token (P.$$$ r) >> single))) x;
  in (args, args1) end;

val parse = #1 (parse_args T.ident_or_symbolic) false;
fun parse1 is_symid = #2 (parse_args is_symid) false;


(* attributes *)

fun attribs intern =
  let
    val attrib_name = internal_text || (symbolic || named)
      >> evaluate T.Text (intern o T.content_of);
    val attrib = P.position (attrib_name -- P.!!! parse) >> src;
  in $$$ "[" |-- P.!!! (P.list attrib --| $$$ "]") end;

fun opt_attribs intern = Scan.optional (attribs intern) [];


(* theorem specifications *)

fun thm_name intern s = binding -- opt_attribs intern --| $$$ s;

fun opt_thm_name intern s =
  Scan.optional
    ((binding -- opt_attribs intern || attribs intern >> pair Binding.empty) --| $$$ s)
    (Binding.empty, []);



(** syntax wrapper **)

fun syntax kind scan (src as Src ((s, args), pos)) st =
  (case Scan.error (Scan.finite' T.stopper (Scan.option scan)) (st, args) of
    (SOME x, (st', [])) => (x, st')
  | (_, (_, args')) =>
      error (kind ^ " " ^ quote s ^ Position.str_of pos ^ ": bad arguments\n  " ^
        space_implode " " (map T.unparse args')));

fun context_syntax kind scan src = apsnd Context.the_proof o syntax kind scan src o Context.Proof;

end;
