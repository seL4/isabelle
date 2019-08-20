(*  Title:      Tools/Argo/argo_term.ML
    Author:     Sascha Boehme

Internal language of the Argo solver.

Terms are fully-shared via hash-consing. Alpha-equivalent terms have the same identifier.
*)

signature ARGO_TERM =
sig
  (* data types *)
  type meta
  datatype term = T of meta * Argo_Expr.kind * term list

  (* term operations *)
  val id_of: term -> int
  val expr_of: term -> Argo_Expr.expr
  val type_of: term -> Argo_Expr.typ
  val eq_term: term * term -> bool
  val term_ord: term ord

  (* context *)
  type context
  val context: context

  (* identifying expressions *)
  datatype item = Expr of Argo_Expr.expr | Term of term
  datatype identified = New of term | Known of term
  val identify_item: item -> context -> identified * context
end

structure Argo_Term: ARGO_TERM =
struct

(* data types *)

(*
  The type meta is intentionally hidden to prevent that functions outside of this structure
  are able to build terms. Meta stores the identifier of the term as well as the complete
  expression underlying the term.
*)

datatype meta = M of int * Argo_Expr.expr
datatype term = T of meta * Argo_Expr.kind * term list


(* term operations *)

fun id_of (T (M (id, _), _, _)) = id
fun expr_of (T (M (_, e), _, _)) = e
fun type_of t = Argo_Expr.type_of (expr_of t)

(*
  Comparing terms is fast as only the identifiers are compared. No expressions need to
  be taken into account.
*)

fun eq_term (t1, t2) = (id_of t1 = id_of t2)
fun term_ord (t1, t2) = int_ord (id_of t1, id_of t2)


(* sharing of terms *)

(*
  Kinds are short representation of expressions. Constants and numbers carry additional
  information and have no arguments. Their kind is hence similar to them. All other expressions
  are stored in a flat way with identifiers of shared terms as arguments instead of expression
  as arguments.
*)

datatype kind =
  Con of string * Argo_Expr.typ |
  Num of Rat.rat |
  Exp of int list

fun kind_of (Argo_Expr.E (Argo_Expr.Con c, _)) _ = Con c
  | kind_of (Argo_Expr.E (Argo_Expr.Num n, _)) _ = Num n
  | kind_of (Argo_Expr.E (k, _)) is = Exp (Argo_Expr.int_of_kind k :: is)

fun int_of_kind (Con _) = 1
  | int_of_kind (Num _) = 2
  | int_of_kind (Exp _) = 3

fun kind_ord (Con c1, Con c2) = Argo_Expr.con_ord (c1, c2)
  | kind_ord (Num n1, Num n2) = Rat.ord (n1, n2)
  | kind_ord (Exp is1, Exp is2) = dict_ord int_ord (is1, is2)
  | kind_ord (k1, k2) = int_ord (int_of_kind k1, int_of_kind k2)

structure Kindtab = Table(type key = kind val ord = kind_ord)

(*
  The context keeps track of the next unused identifier as well as all shared terms,
  which are indexed by their unique kind. For each term, a boolean marker flag is stored.
  When set to true on an atom, the atom is already asserted to the solver core. When set to
  true on an if-then-else term, the term has already been lifted.

  Zero is intentionally avoided as identifier, since literals use term identifiers
  with a sign as literal identifiers.
*)

type context = {
  next_id: int,
  terms: (term * bool) Kindtab.table}

fun mk_context next_id terms: context = {next_id=next_id, terms=terms}

val context = mk_context 1 Kindtab.empty

fun note_atom true kind (t, false) ({next_id, terms}: context) =
      mk_context next_id (Kindtab.update (kind, (t, true)) terms)
  | note_atom _ _ _ cx = cx

fun with_unique_id kind is_atom (e as Argo_Expr.E (k, _)) ts ({next_id, terms}: context) =
  let val t = T (M (next_id, e), k, ts)
  in ((t, false), mk_context (next_id + 1) (Kindtab.update (kind, (t, is_atom)) terms)) end

fun unique kind is_atom e ts (cx as {terms, ...}: context) =
  (case Kindtab.lookup terms kind of
    SOME tp => (tp, note_atom is_atom kind tp cx)
  | NONE => with_unique_id kind is_atom e ts cx)


(* identifying expressions *)

(*
  Only atoms, i.e., boolean propositons, and if-then-else expressions need to be identified.
  Other terms are identified implicitly. The identification process works bottom-up.

  The solver core needs to know whether an atom has already been added. Likewise, the clausifier
  needs to know whether an if-then-else expression has already been lifted. Therefore,
  the identified term is marked as either "new" when identified for the first time or
  "known" when it has already been identified before.
*)

datatype item = Expr of Argo_Expr.expr | Term of term
datatype identified = New of term | Known of term

fun identify_head is_atom e (ts, cx) = unique (kind_of e (map id_of ts)) is_atom e ts cx

fun identify is_atom (e as Argo_Expr.E (_, es)) cx =
  identify_head is_atom e (fold_map (apfst fst oo identify false) es cx)

fun identified (t, true) = Known t
  | identified (t, false) = New t

fun identify_item (Expr e) cx = identify true e cx |>> identified
  | identify_item (Term (t as T (_, _, ts))) cx =
      identify_head true (expr_of t) (ts, cx) |>> identified

end

structure Argo_Termtab = Table(type key = Argo_Term.term val ord = Argo_Term.term_ord)
