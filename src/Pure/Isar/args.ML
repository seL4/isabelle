(*  Title:      Pure/Isar/args.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Concrete argument syntax of attributes, methods etc. -- with special
support for embedded values and static binding.
*)

signature ARGS =
sig
  datatype value = Name of string | Typ of typ | Term of term | Fact of thm list |
    Attribute of theory attribute * ProofContext.context attribute
  type T
  val string_of: T -> string
  val mk_ident: string * Position.T -> T
  val mk_string: string * Position.T -> T
  val mk_keyword: string * Position.T -> T
  val mk_name: string -> T
  val mk_typ: typ -> T
  val mk_term: term -> T
  val mk_fact: thm list -> T
  val mk_attribute: theory attribute * ProofContext.context attribute -> T
  val stopper: T * (T -> bool)
  val not_eof: T -> bool
  type src
  val src: (string * T list) * Position.T -> src
  val dest_src: src -> (string * T list) * Position.T
  val map_name: (string -> string) -> src -> src
  val map_values: (string -> string) -> (typ -> typ) -> (term -> term) -> (thm -> thm)
    -> src -> src
  val assignable: src -> src
  val assign: value option -> T -> unit
  val closure: src -> src
  val position: (T list -> 'a * 'b) -> T list -> ('a * Position.T) * 'b
  val !!! : (T list -> 'a) -> T list -> 'a
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
  val name: T list -> string * T list
  val symbol: T list -> string * T list
  val nat: T list -> int * T list
  val int: T list -> int * T list
  val var: T list -> indexname * T list
  val list: (T list -> 'a * T list) -> T list -> 'a list * T list
  val list1: (T list -> 'a * T list) -> T list -> 'a list * T list
  val enum: string -> ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val enum1: string -> ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val and_list: ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val and_list1: ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val ahead: T list -> T * T list
  val internal_name: T list -> string * T list
  val internal_typ: T list -> typ * T list
  val internal_term: T list -> term * T list
  val internal_fact: T list -> thm list * T list
  val internal_attribute: T list ->
    (theory attribute * ProofContext.context attribute) * T list
  val named_name: (string -> string) -> T list -> string * T list
  val named_typ: (string -> typ) -> T list -> typ * T list
  val named_term: (string -> term) -> T list -> term * T list
  val named_fact: (string -> thm list) -> T list -> thm list * T list
  val global_typ_abbrev: theory * T list -> typ * (theory * T list)
  val global_typ: theory * T list -> typ * (theory * T list)
  val global_term: theory * T list -> term * (theory * T list)
  val global_prop: theory * T list -> term * (theory * T list)
  val local_typ_abbrev: ProofContext.context * T list -> typ * (ProofContext.context * T list)
  val local_typ: ProofContext.context * T list -> typ * (ProofContext.context * T list)
  val local_term: ProofContext.context * T list -> term * (ProofContext.context * T list)
  val local_prop: ProofContext.context * T list -> term * (ProofContext.context * T list)
  val global_tyname: theory * T list -> string * (theory * T list)
  val global_const: theory * T list -> string * (theory * T list)
  val local_tyname: ProofContext.context * T list -> string * (ProofContext.context * T list)
  val local_const: ProofContext.context * T list -> string * (ProofContext.context * T list)
  val thm_sel: T list -> PureThy.interval list * T list
  val bang_facts: ProofContext.context * T list -> thm list * (ProofContext.context * T list)
  val goal_spec: ((int -> tactic) -> tactic) -> ('a * T list)
    -> ((int -> tactic) -> tactic) * ('a * T list)
  val attribs: (string -> string) -> T list -> src list * T list
  val opt_attribs: (string -> string) -> T list -> src list * T list
  val syntax: string -> ('a * T list -> 'b * ('a * T list)) -> src -> 'a -> 'a * 'b
  val pretty_src: ProofContext.context -> src -> Pretty.T
  val pretty_attribs: ProofContext.context -> src list -> Pretty.T list
end;

structure Args: ARGS =
struct


(** datatype T **)

(*An argument token is a symbol (with raw string value), together with
  an optional assigned internal value.  Note that an assignable ref
  designates an intermediate state of internalization -- it is NOT
  meant to persist.*)

datatype kind = Ident | String | Keyword | EOF;

type symbol = kind * string * Position.T;

datatype value =
  Name of string |
  Typ of typ |
  Term of term |
  Fact of thm list |
  Attribute of theory attribute * ProofContext.context attribute;

datatype slot =
  Empty |
  Value of value option |
  Assignable of value option ref;

datatype T = Arg of symbol * slot;

fun string_of (Arg ((Ident, x, _), _)) = x
  | string_of (Arg ((String, x, _), _)) = Library.quote x
  | string_of (Arg ((Keyword, x, _), _)) = x
  | string_of (Arg ((EOF, _, _), _)) = "";

fun sym_of (Arg ((_, x, _), _)) = x;
fun pos_of (Arg ((_, _, pos), _)) = pos;


(* basic constructors *)

fun mk_symbol k (x, p) = Arg ((k, x, p), Empty);
fun mk_value k v = Arg ((Keyword, k, Position.none), Value (SOME v));

val mk_ident = mk_symbol Ident;
val mk_string = mk_symbol String;
val mk_keyword = mk_symbol Keyword;
val mk_name = mk_value "<name>" o Name;
val mk_typ = mk_value "<typ>" o Typ;
val mk_term = mk_value "<term>" o Term;
val mk_fact = mk_value "<fact>" o Fact;
val mk_attribute = mk_value "<attribute>" o Attribute;


(* eof *)

val eof = mk_symbol EOF ("", Position.none);

fun is_eof (Arg ((EOF, _, _), _)) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;



(** datatype src **)

datatype src = Src of (string * T list) * Position.T;

val src = Src;
fun dest_src (Src src) = src;

fun map_name f (Src ((s, args), pos)) = Src ((f s, args), pos);
fun map_args f (Src ((s, args), pos)) = Src ((s, map f args), pos);


(* values *)

fun map_value f (Arg (s, Value (SOME v))) = Arg (s, Value (SOME (f v)))
  | map_value _ arg = arg;

fun map_values f g h i = map_args (map_value
  (fn Name s => Name (f s)
    | Typ T => Typ (g T)
    | Term t => Term (h t)
    | Fact ths => Fact (map i ths)
    | Attribute att => Attribute att));


(* static binding *)

(*1st stage: make empty slots assignable*)
val assignable =
  map_args (fn Arg (s, Empty) => Arg (s, Assignable (ref NONE)) | arg => arg);

(*2nd stage: assign values as side-effect of scanning*)
fun assign v (arg as Arg (_, Assignable r)) = r := v
  | assign _ _ = ();

val ahead = Scan.ahead (Scan.one not_eof);
fun touch scan = ahead -- scan >> (fn (arg, y) => (assign NONE arg; y));

(*3rd stage: static closure of final values*)
val closure =
  map_args (fn Arg (s, Assignable (ref v)) => Arg (s, Value v) | arg => arg);



(** scanners **)

(* position *)

fun position scan =
  (Scan.ahead (Scan.one not_eof) >> pos_of) -- scan >> Library.swap;


(* cut *)

fun !!! scan =
  let
    fun get_pos [] = " (past end-of-text!)"
      | get_pos (arg :: _) = Position.str_of (pos_of arg);

    fun err (args, NONE) = "Argument syntax error" ^ get_pos args
      | err (args, SOME msg) = "Argument syntax error" ^ get_pos args ^ ": " ^ msg;
  in Scan.!! err scan end;


(* basic *)

fun some_ident f =
  touch (Scan.some (fn Arg ((Ident, x, _), _) => f x | _ => NONE));

val named =
  touch (Scan.one (fn Arg ((k, _, _), _) => k = Ident orelse k = String));

val symbolic =
  touch (Scan.one (fn Arg ((k, x, _), _) => k = Keyword andalso OuterLex.is_sid x));

fun &&& x =
  touch (Scan.one (fn Arg ((k, y, _), _) => k = Keyword andalso x = y));

fun $$$ x =
  touch (Scan.one (fn Arg ((k, y, _), _) => (k = Ident orelse k = Keyword) andalso x = y))
  >> sym_of;

val add = $$$ "add";
val del = $$$ "del";
val colon = $$$ ":";
val query = $$$ "?";
val bang = $$$ "!";
val query_colon = $$$ "?:";
val bang_colon = $$$ "!:";

fun parens scan = $$$ "(" |-- scan --| $$$ ")";
fun bracks scan = $$$ "[" |-- scan --| $$$ "]";
fun mode s = Scan.lift (Scan.optional (parens ($$$ s) >> K true) false);
fun maybe scan = $$$ "_" >> K NONE || scan >> SOME;

val name = named >> sym_of;
val symbol = symbolic >> sym_of;

val nat = some_ident Syntax.read_nat;
val int = Scan.optional ($$$ "-" >> K ~1) 1 -- nat >> op *;
val var = some_ident Syntax.read_variable;


(* enumerations *)

fun list1 scan = scan -- Scan.repeat ($$$ "," |-- scan) >> op ::;
fun list scan = list1 scan || Scan.succeed [];

fun enum1 sep scan = scan -- Scan.repeat (Scan.lift ($$$ sep) |-- scan) >> op ::;
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;


(* values *)

fun value dest = Scan.some  (*no touch here*)
  (fn Arg (_, Value (SOME v)) => (SOME (dest v) handle Match => NONE)
    | Arg _ => NONE);

fun evaluate mk eval arg =
  let val x = eval (sym_of arg) in (assign (SOME (mk x)) arg; x) end;

val internal_name = value (fn Name s => s);
val internal_typ = value (fn Typ T => T);
val internal_term = value (fn Term t => t);
val internal_fact = value (fn Fact ths => ths);
val internal_attribute = value (fn Attribute att => att);

fun named_name intern = internal_name || named >> evaluate Name intern;
fun named_typ readT = internal_typ || named >> evaluate Typ readT;
fun named_term read = internal_term || named >> evaluate Term read;
fun named_fact get = internal_fact || named >> evaluate Fact get;


(* terms and types *)

val global_typ_abbrev = Scan.peek (named_typ o ProofContext.read_typ_abbrev o ProofContext.init);
val global_typ = Scan.peek (named_typ o ProofContext.read_typ o ProofContext.init);
val global_term = Scan.peek (named_term o ProofContext.read_term o ProofContext.init);
val global_prop = Scan.peek (named_term o ProofContext.read_prop o ProofContext.init);

val local_typ_abbrev = Scan.peek (named_typ o ProofContext.read_typ_abbrev);
val local_typ = Scan.peek (named_typ o ProofContext.read_typ);
val local_term = Scan.peek (named_term o ProofContext.read_term);
val local_prop = Scan.peek (named_term o ProofContext.read_prop);


(* type and constant names *)

val dest_tyname = fn Type (c, _) => c | TFree (a, _) => a | _ => "";
val dest_const = fn Const (c, _) => c | Free (x, _) => x | _ => "";

val global_tyname = Scan.peek (named_typ o Sign.read_tyname o Theory.sign_of) >> dest_tyname;
val global_const = Scan.peek (named_term o Sign.read_const o Theory.sign_of) >> dest_const;
val local_tyname = Scan.peek (named_typ o ProofContext.read_tyname) >> dest_tyname;
val local_const = Scan.peek (named_term o ProofContext.read_const) >> dest_const;


(* misc *)

val thm_sel = parens (list1
 (nat --| $$$ "-" -- nat >> PureThy.FromTo ||
  nat --| $$$ "-" >> PureThy.From ||
  nat >> PureThy.Single));

val bang_facts = Scan.peek (fn ctxt =>
  $$$ "!" >> K (ProofContext.prems_of ctxt) || Scan.succeed []);


(* goal specification *)

(* range *)

val from_to =
  nat -- ($$$ "-" |-- nat) >> (fn (i, j) => fn tac => Seq.INTERVAL tac i j) ||
  nat --| $$$ "-" >> (fn i => fn tac => fn st => Seq.INTERVAL tac i (Thm.nprems_of st) st) ||
  nat >> (fn i => fn tac => tac i) ||
  $$$ "!" >> K ALLGOALS;

val goal = $$$ "[" |-- !!! (from_to --| $$$ "]");
fun goal_spec def = Scan.lift (Scan.optional goal def);



(* attribs *)

local

val exclude = explode "()[],";

fun atomic blk = touch (Scan.one (fn Arg ((k, x, _), _) =>
    k <> Keyword orelse not (x mem exclude) orelse blk andalso x = ","));

fun args blk x = Scan.optional (args1 blk) [] x
and args1 blk x =
  ((Scan.repeat1
    (Scan.repeat1 (atomic blk) ||
      argsp "(" ")" ||
      argsp "[" "]")) >> List.concat) x
and argsp l r x =
  (Scan.trace (&&& l -- !!! (args true -- &&& r)) >> #2) x;

in

fun attribs intern =
  let
    val attrib_name = internal_name || (symbolic || named) >> evaluate Name intern;
    val attrib = position (attrib_name -- !!! (args false)) >> src;
  in $$$ "[" |-- !!! (list attrib --| $$$ "]") end;

fun opt_attribs intern = Scan.optional (attribs intern) [];

end;


(* syntax interface *)

fun syntax kind scan (src as Src ((s, args), pos)) st =
  (case Scan.error (Scan.finite' stopper (Scan.option scan)) (st, args) of
    (SOME x, (st', [])) => (st', x)
  | (_, (_, args')) =>
      error (kind ^ " " ^ quote s ^ Position.str_of pos ^ ": bad arguments\n  " ^
        space_implode " " (map string_of args')));



(** pretty printing **)

fun pretty_src ctxt src =
  let
    fun prt (Arg (_, Value (SOME (Name s)))) = Pretty.str (quote s)
      | prt (Arg (_, Value (SOME (Typ T)))) = ProofContext.pretty_typ ctxt T
      | prt (Arg (_, Value (SOME (Term t)))) = ProofContext.pretty_term ctxt t
      | prt (Arg (_, Value (SOME (Fact ths)))) = ProofContext.pretty_thms ctxt ths
      | prt arg = Pretty.str (string_of arg);
    val (s, args) = #1 (dest_src src);
  in Pretty.block (Pretty.breaks (Pretty.str s :: map prt args)) end;

fun pretty_attribs _ [] = []
  | pretty_attribs ctxt srcs =
      [Pretty.enclose "[" "]" (Pretty.commas (map (pretty_src ctxt) srcs))];

end;
