(*  Title:      Pure/Isar/args.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Concrete argument syntax (of attributes and methods).
*)

signature ARGS =
sig
  type T
  val val_of: T -> string
  val pos_of: T -> Position.T
  val str_of: T -> string
  val string_of: T -> string
  val ident: string * Position.T -> T
  val string: string * Position.T -> T
  val keyword: string * Position.T -> T
  val stopper: T * (T -> bool)
  val not_eof: T -> bool
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
  val name: T list -> string * T list
  val name_dummy: T list -> string option * T list
  val nat: T list -> int * T list
  val int: T list -> int * T list
  val var: T list -> indexname * T list
  val enum: string -> ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val enum1: string -> ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val and_list: ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val and_list1: ('a * T list -> 'b * ('a * T list)) -> 'a * T list -> 'b list * ('a * T list)
  val global_typ_no_norm: theory * T list -> typ * (theory * T list)
  val global_typ: theory * T list -> typ * (theory * T list)
  val global_term: theory * T list -> term * (theory * T list)
  val global_prop: theory * T list -> term * (theory * T list)
  val local_typ_no_norm: Proof.context * T list -> typ * (Proof.context * T list)
  val local_typ: Proof.context * T list -> typ * (Proof.context * T list)
  val local_term: Proof.context * T list -> term * (Proof.context * T list)
  val local_prop: Proof.context * T list -> term * (Proof.context * T list)
  val bang_facts: Proof.context * T list -> thm list * (Proof.context * T list)
  val goal_spec: ((int -> tactic) -> tactic) -> ('a * T list)
    -> ((int -> tactic) -> tactic) * ('a * T list)
  type src
  val src: (string * T list) * Position.T -> src
  val dest_src: src -> (string * T list) * Position.T
  val attribs: T list -> src list * T list
  val opt_attribs: T list -> src list * T list
  val syntax: string -> ('a * T list -> 'b * ('a * T list)) -> src -> 'a -> 'a * 'b
end;

structure Args: ARGS =
struct


(** datatype T **)

datatype kind = Ident | String | Keyword | EOF;
datatype T = Arg of kind * (string * Position.T);

fun val_of (Arg (_, (x, _))) = x;
fun pos_of (Arg (_, (_, pos))) = pos;

fun str_of (Arg (Ident, (x, _))) = x
  | str_of (Arg (String, (x, _))) = quote x
  | str_of (Arg (Keyword, (x, _))) = x
  | str_of (Arg (EOF, _)) = "end-of-text";

fun string_of (Arg (Ident, (x, _))) = x
  | string_of (Arg (String, (x, _))) = quote x
  | string_of (Arg (Keyword, (x, _))) = x
  | string_of (Arg (EOF, _)) = "";

fun arg kind x_pos = Arg (kind, x_pos);
val ident = arg Ident;
val string = arg String;
val keyword = arg Keyword;


(* eof *)

val eof = arg EOF ("", Position.none);

fun is_eof (Arg (EOF, _)) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;



(** scanners **)

(* position *)

fun position scan = (Scan.ahead (Scan.one not_eof) >> pos_of) -- scan >> Library.swap;


(* cut *)

fun !!! scan =
  let
    fun get_pos [] = " (past end-of-text!)"
      | get_pos (Arg (_, (_, pos)) :: _) = Position.str_of pos;

    fun err (args, None) = "Argument syntax error" ^ get_pos args
      | err (args, Some msg) = "Argument syntax error" ^ get_pos args ^ ": " ^ msg;
  in Scan.!! err scan end;


(* basic *)

fun $$$$ x = Scan.one (fn Arg (k, (y, _)) => (k = Ident orelse k = Keyword) andalso x = y);
fun $$$ x = $$$$ x >> val_of;

val add = $$$ "add";
val del = $$$ "del";
val colon = $$$ ":";
val query = $$$ "?";
val bang = $$$ "!";
val query_colon = $$$ "?:";
val bang_colon = $$$ "!:";

fun parens scan = $$$ "(" |-- scan --| $$$ ")";
fun bracks scan = $$$ "[" |-- scan --| $$$ "]";
fun mode s = Scan.lift (Scan.optional (parens ($$$$ s) >> K true) false);

val name = Scan.one (fn Arg (k, (x, _)) => k = Ident orelse k = String) >> val_of;
val name_dummy = $$$ "_" >> K None || name >> Some;

val keyword_symid =
  Scan.one (fn Arg (k, (x, _)) => k = Keyword andalso OuterLex.is_sid x) >> val_of;

fun kind f = Scan.one (K true) :--
  (fn Arg (Ident, (x, _)) =>
    (case f x of Some y => Scan.succeed y | _ => Scan.fail)
  | _ => Scan.fail) >> #2;

val nat = kind Syntax.read_nat;
val int = Scan.optional ($$$ "-" >> K ~1) 1 -- nat >> op *;
val var = kind (apsome #1 o try Term.dest_Var o Syntax.read_var);


(* enumerations *)

fun enum1 sep scan = scan -- Scan.repeat (Scan.lift ($$$ sep) |-- scan) >> op ::;
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;


(* terms and types *)

fun gen_item read = Scan.depend (fn st => name >> (pair st o read st));

val global_typ_no_norm = gen_item (ProofContext.read_typ_no_norm o ProofContext.init);
val global_typ = gen_item (ProofContext.read_typ o ProofContext.init);
val global_term = gen_item (ProofContext.read_term o ProofContext.init);
val global_prop = gen_item (ProofContext.read_prop o ProofContext.init);

val local_typ_no_norm = gen_item ProofContext.read_typ_no_norm;
val local_typ = gen_item ProofContext.read_typ;
val local_term = gen_item ProofContext.read_term;
val local_prop = gen_item ProofContext.read_prop;


(* bang facts *)

val bang_facts = Scan.depend (fn ctxt =>
  ($$$ "!" >> K (ProofContext.prems_of ctxt) || Scan.succeed []) >> pair ctxt);


(* goal specification *)

(* range *)

val from_to =
  nat -- ($$$$ "-" |-- nat) >> (fn (i, j) => fn tac => Seq.INTERVAL tac i j) ||
  nat --| $$$$ "-" >> (fn i => fn tac => fn st => Seq.INTERVAL tac i (Thm.nprems_of st) st) ||
  nat >> (fn i => fn tac => tac i) ||
  $$$$ "!" >> K ALLGOALS;

val goal = $$$$ "[" |-- !!! (from_to --| $$$$ "]");
fun goal_spec def = Scan.lift (Scan.optional goal def);


(* args *)

val exclude = explode "()[],";

fun atom_arg blk = Scan.one (fn Arg (k, (x, _)) =>
  k <> Keyword orelse not (x mem exclude) orelse blk andalso x = ",");

fun paren_args l r scan = $$$$ l -- !!! (scan true -- $$$$ r)
  >> (fn (x, (ys, z)) => x :: ys @ [z]);

fun args blk x = Scan.optional (args1 blk) [] x
and args1 blk x =
  ((Scan.repeat1
    (Scan.repeat1 (atom_arg blk) ||
      paren_args "(" ")" args ||
      paren_args "[" "]" args)) >> flat) x;



(** type src **)

datatype src = Src of (string * T list) * Position.T;

val src = Src;
fun dest_src (Src src) = src;

fun err_in_src kind msg (Src ((s, args), pos)) =
  error (kind ^ " " ^ s ^ Position.str_of pos ^ ": " ^ msg ^ "\n  " ^
    space_implode " " (map str_of args));


(* argument syntax *)

fun syntax kind scan (src as Src ((s, args), pos)) st =
  (case Scan.error (Scan.finite' stopper (Scan.option scan)) (st, args) of
    (Some x, (st', [])) => (st', x)
  | (_, (_, args')) => err_in_src kind "bad arguments" (Src ((s, args'), pos)));


(* attribs *)

fun list1 scan = scan -- Scan.repeat ($$$ "," |-- scan) >> op ::;
fun list scan = list1 scan || Scan.succeed [];

val attrib = position ((keyword_symid || name) -- !!! (args false)) >> src;
val attribs = $$$ "[" |-- !!! (list attrib --| $$$ "]");
val opt_attribs = Scan.optional attribs [];


end;
