(*  Title:      Tools/Argo/argo_rewr.ML
    Author:     Sascha Boehme

Bottom-up rewriting of expressions based on rewrite rules and rewrite functions.
*)

signature ARGO_REWR =
sig
  (* patterns *)
  datatype pattern =
    V of int |
    E of Argo_Expr.expr |
    A of Argo_Expr.kind |
    P of Argo_Expr.kind * pattern list |
    M of pattern |
    X

  (* scanning patterns from strings *)
  val scan: string -> pattern

  (* pattern matching *)
  type env
  val get_all: env -> Argo_Expr.expr list
  val get: env -> int -> Argo_Expr.expr

  (* conversions *)
  type conv = Argo_Expr.expr -> Argo_Expr.expr * Argo_Proof.conv
  val keep: conv
  val seq: conv list -> conv
  val args: conv -> conv
  val rewr: Argo_Proof.rewrite -> Argo_Expr.expr -> conv

  (* context *)
  type context
  val context: context
  val flat: string ->
    (int -> Argo_Expr.expr list -> (Argo_Proof.rewrite * Argo_Expr.expr) option) ->
    context -> context
  val func: string -> (env -> (Argo_Proof.rewrite * pattern) option) -> context -> context
  val rule: Argo_Proof.rewrite -> string -> string -> context -> context

  (* rewriting *)
  val rewrite: context -> conv
  val rewrite_top: context -> conv
  val with_proof: conv -> Argo_Expr.expr * Argo_Proof.proof -> Argo_Proof.context ->
    (Argo_Expr.expr * Argo_Proof.proof) * Argo_Proof.context
end

structure Argo_Rewr: ARGO_REWR =
struct

(* patterns *)

(*
  Patterns are used for matching against expressions and as a schema to construct
  expressions. For matching, only V, E, A and P must be used. For the schema,
  additionally M and X can be used.
*)

datatype pattern =
  V of int | (* indexed placeholder where the index must be greater than 0 *)
  E of Argo_Expr.expr | (* expression without placeholders *)
  A of Argo_Expr.kind | (* placeholder for the arguments of an n-ary expression *)
  P of Argo_Expr.kind * pattern list | (* expression with optional placeholders *)
  M of pattern | (* mapping operator to iterate over an argument list of an n-ary expression *)
  X (* closure argument under a mapping operator representing an expression *)

fun int_of_pattern (E _) = 0
  | int_of_pattern (P _) = 1
  | int_of_pattern (A _) = 2
  | int_of_pattern (V _) = 3
  | int_of_pattern _ = raise Fail "bad pattern"

(*
  Specific patterns are ordered before generic patterns, since pattern matching
  performs a linear search for the most suitable pattern.
*)

fun pattern_ord (E e1, E e2) = Argo_Expr.expr_ord (e1, e2)
  | pattern_ord (P (k1, ps1), P (k2, ps2)) =
      (case Argo_Expr.kind_ord (k1, k2) of EQUAL => list_ord pattern_ord (ps1, ps2) | x => x)
  | pattern_ord (A k1, A k2) = Argo_Expr.kind_ord (k1, k2)
  | pattern_ord (V i1, V i2) = int_ord (i1, i2)
  | pattern_ord (p1, p2) = int_ord (int_of_pattern p1, int_of_pattern p2)


(* scanning patterns from strings *)

(*
  The pattern language is cumbersome to use in other structures. Strings are a more
  lightweight representation. Scanning patterns from strings should be performed at
  compile time to avoid the parsing overhead at runtime.
*)

val kind = Scan.many1 Symbol.is_ascii_letter >> (Argo_Expr.kind_of_string o implode)
val num = Scan.many1 Symbol.is_ascii_digit >> (the o Int.fromString o implode)
val integer = $$ "-" |-- num >> ~ || num
val blank = Scan.many1 Symbol.is_ascii_blank >> K ()

fun pattern xs = (
  kind >> (P o rpair []) ||
  $$ "!" >> K X ||
  $$ "(" -- $$ "#" -- blank |-- pattern --| $$ ")" >> M ||
  $$ "(" -- $$ "?" -- blank |-- num --| $$ ")" >> V ||
  $$ "(" -- Scan.this_string "num" -- blank |-- integer --| $$ ")" >>
    (E o Argo_Expr.mk_num o Rat.of_int) ||
  $$ "(" |-- kind --| blank --| $$ "_" --| $$ ")" >> A ||
  $$ "(" |-- kind -- Scan.repeat1 (blank |-- pattern) --| $$ ")" >> P) xs

fun scan s = fst (pattern (map str (String.explode s) @ [""]))


(* pattern matching *)

exception PATTERN of unit

(*
  The environment stores the matched expressions for the pattern placeholders.
  The expression for an indexed placeholder (V i) can be retrieved by "get env i".
  The argument expressions for an n-ary placeholder (A k) can be retrieved by "get_all env".
*)

type env = Argo_Expr.expr list Inttab.table

val empty_env: env = Inttab.empty
fun get_all env = Inttab.lookup_list env 0
fun get env i = hd (Inttab.lookup_list env i)

fun depth_of (V _) = 0
  | depth_of (E _) = 0
  | depth_of (A _) = 1
  | depth_of (P (_, ps)) = 1 + fold (Integer.max o depth_of) ps 0
  | depth_of (M p) = depth_of p
  | depth_of X = 0

fun match_list f k k' env = if k = k' then f env else raise PATTERN ()

fun match (V i) e env = Inttab.update_new (i, [e]) env
  | match (A k) (Argo_Expr.E (k', es)) env = match_list (Inttab.update_new (0, es)) k k' env
  | match (P (k, ps)) (Argo_Expr.E (k', es)) env = match_list (fold2 match ps es) k k' env
  | match _ _ _ = raise Fail "bad pattern"

fun unfold_index env (V i) _ = get env i
  | unfold_index _ (E e) _ = e
  | unfold_index env (P (k, ps)) e = Argo_Expr.E (k, map (fn p => unfold_index env p e) ps)
  | unfold_index _ X e = e
  | unfold_index _ _ _ = raise Fail "bad pattern"

fun unfold_pattern env (V i) = get env i
  | unfold_pattern _ (E e) = e
  | unfold_pattern env (A k) = Argo_Expr.E (k, get_all env)
  | unfold_pattern env (P (k, [M p])) = Argo_Expr.E (k, map (unfold_index env p) (get_all env))
  | unfold_pattern env (P (k, ps)) = Argo_Expr.E (k, map (unfold_pattern env) ps)
  | unfold_pattern _ _ = raise Fail "bad pattern"


(* conversions *)

(*
  Conversions are atomic rewrite steps. For every conversion there is a corresponding
  inference step.
*)

type conv = Argo_Expr.expr -> Argo_Expr.expr * Argo_Proof.conv

fun keep e = (e, Argo_Proof.keep_conv)

fun seq [] e = keep e
  | seq [cv] e = cv e
  | seq (cv :: cvs) e =
      let val ((e, c2), c1) = cv e |>> seq cvs
      in (e, Argo_Proof.mk_then_conv c1 c2) end

fun args cv (Argo_Expr.E (k, es)) =
  let val (es, cs) = split_list (map cv es)
  in (Argo_Expr.E (k, es), Argo_Proof.mk_args_conv cs) end

fun rewr r e _ = (e, Argo_Proof.mk_rewr_conv r)


(* context *)

(*
  The context stores functions to flatten expressions and functions to rewrite expressions.
  Flattening an n-ary expression of kind k produces an expression whose arguments are not
  of kind k. For instance, flattening (and p (and q r)) produces (and p q r) where p, q and r
  are not conjunctions.
*)

structure Pattab = Table(type key = pattern val ord = pattern_ord)

type context = {
  flats:
    (Argo_Expr.kind * (int -> Argo_Expr.expr list -> (Argo_Proof.rewrite * Argo_Expr.expr) option))
      list, (* expressions that should be flattened before rewriting *)
  rewrs: (env -> (Argo_Proof.rewrite * pattern) option) list Pattab.table}
    (* Looking up matching rules is O(n). This could be optimized. *)

fun mk_context flats rewrs: context = {flats=flats, rewrs=rewrs}
val context = mk_context [] Pattab.empty

fun map_context map_flats map_rewrs ({flats, rewrs}: context) =
  mk_context (map_flats flats) (map_rewrs rewrs)

fun flat lhs f =
  (case scan lhs of
    A k => map_context (cons (k, f)) I
  | _ => raise Fail "bad pattern")

fun func lhs f = map_context I (Pattab.map_default (scan lhs, []) (fn fs => fs @ [f]))
fun rule r lhs rhs = func lhs (K (SOME (r, scan rhs)))


(* rewriting *)

(*
  Rewriting proceeds bottom-up. Whenever a rewrite rule with placeholders is used,
  the arguments are again rewritten, but only up to depth of the placeholders within the
  matched pattern.
*)

fun rewr_rule r env p = rewr r (unfold_pattern env p)

fun try_apply p e f =
  let val env = match p e empty_env
  in (case f env of NONE => NONE | SOME (r, p) => SOME (r, env, p)) end
  handle PATTERN () => NONE

fun all_args cv k (e as Argo_Expr.E (k', _)) = if k = k' then args (all_args cv k) e else cv e
fun all_args_of k (e as Argo_Expr.E (k', es)) = if k = k' then maps (all_args_of k) es else [e]
fun kind_depth_of k (Argo_Expr.E (k', es)) =
  if k = k' then 1 + fold (Integer.max o kind_depth_of k) es 0 else 0

fun descend cv flats (e as Argo_Expr.E (k, _)) =
  if AList.defined Argo_Expr.eq_kind flats k then all_args cv k e
  else args cv e

fun flatten flats (e as Argo_Expr.E (k, _)) =
  (case AList.lookup Argo_Expr.eq_kind flats k of
    NONE => keep e
  | SOME f =>
      (case f (kind_depth_of k e) (all_args_of k e) of
        NONE => keep e
      | SOME (r, e') => rewr r e' e))

fun exhaust cv rewrs e =
  (case Pattab.get_first (fn (p, fs) => get_first (try_apply p e) fs) rewrs of
    NONE => keep e
  | SOME (r, env, p) => seq [rewr_rule r env p, cv (depth_of p)] e)

fun norm (cx as {flats, rewrs}: context) d e =
  seq [
    if d = 0 then keep else descend (norm cx (d - 1)) flats,
    flatten flats,
    exhaust (norm cx) rewrs] e

fun rewrite cx = norm cx ~1   (* bottom-up rewriting *)
fun rewrite_top cx = norm cx 0   (* top-down rewriting *)

fun with_proof cv (e, p) prf =
  let
    val (e, c) = cv e
    val (p, prf) = Argo_Proof.mk_rewrite c p prf
  in ((e, p), prf) end

end
