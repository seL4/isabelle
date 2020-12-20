(*  Title:      Tools/Argo/argo_thy.ML
    Author:     Sascha Boehme

Combination of all theory solvers.

Currently, it is assumed that theories have distinct domains. Theory solvers do not
exchange knowledge among each other. This should be changed in the future. Relevant work is:

  Greg Nelson and Derek C. Oppen. Simplification by cooperating decision procedures. In ACM
  Transactions on Programming Languages and Systems, 1(2):245-257, 1979.

  Leonardo de Moura and Nikolaj Bjørner. Model-based Theory Combination. In Electronic Notes
  in Theoretical Computer Science, volume 198(2), pages 37-49, 2008.
*)

signature ARGO_THY =
sig
  (* context *)
  type context
  val context: context

  (* enriching the context *)
  val add_atom: Argo_Term.term -> context -> Argo_Lit.literal option * context

  (* main operations *)
  val prepare: context -> context
  val assume: Argo_Common.literal -> context -> Argo_Lit.literal Argo_Common.implied * context
  val check: context -> Argo_Lit.literal Argo_Common.implied * context
  val explain: Argo_Lit.literal -> context -> Argo_Cls.clause * context
  val add_level: context -> context
  val backtrack: context -> context
end

structure Argo_Thy: ARGO_THY =
struct

(* context *)

type context = Argo_Cc.context * Argo_Simplex.context

val context = (Argo_Cc.context, Argo_Simplex.context)

fun map_cc f (cc, simplex) =
  let val (x, cc) = f cc
  in (x, (cc, simplex)) end

fun map_simplex f (cc, simplex) =
  let val (x, simplex) = f simplex
  in (x, (cc, simplex)) end


(* enriching the context *)

fun add_atom t (cc, simplex) =
  let
    val (lit1, cc) = Argo_Cc.add_atom t cc
    val (lit2, simplex) = Argo_Simplex.add_atom t simplex
  in
    (case fold (union Argo_Lit.eq_lit o the_list) [lit1, lit2] [] of
      [] => (NONE, (cc, simplex))
    | [lit] => (SOME lit, (cc, simplex))
    | _ => raise Fail "unsynchronized theory solvers")
  end
    


(* main operations *)

fun prepare (cc, simplex) = (cc, Argo_Simplex.prepare simplex)

local

exception CONFLICT of Argo_Cls.clause * context

datatype tag = All | Cc | Simplex

fun apply f cx =
  (case f cx of
    (Argo_Common.Conflict cls, cx) => raise CONFLICT (cls, cx)
  | (Argo_Common.Implied lits, cx) => (lits, cx))

fun with_lits tag f (txs, lits, cx) =
  let val (lits', cx) = f cx
  in (fold (fn l => cons (tag, (l, NONE))) lits' txs, union Argo_Lit.eq_lit lits' lits, cx) end

fun apply0 (tag, f) = with_lits tag (apply f)
fun apply1 (tag, f) (tag', x) = if tag <> tag' then with_lits tag (apply (f x)) else I

val assumes = [(Cc, map_cc o Argo_Cc.assume), (Simplex, map_simplex o Argo_Simplex.assume)]
val checks = [(Cc, map_cc Argo_Cc.check), (Simplex, map_simplex Argo_Simplex.check)]

fun propagate ([], lits, cx) = (Argo_Common.Implied lits, cx)
  | propagate (txs, lits, cx) = propagate (fold_product apply1 assumes txs ([], lits, cx))

in

fun assume lp cx = propagate ([(All, lp)], [], cx)
  handle CONFLICT (cls, cx) => (Argo_Common.Conflict cls, cx)

fun check cx = propagate (fold apply0 checks ([], [], cx))
  handle CONFLICT (cls, cx) => (Argo_Common.Conflict cls, cx)

end

fun explain lit (cc, simplex) =
  (case Argo_Cc.explain lit cc of
    SOME (cls, cc) => (cls, (cc, simplex))
  | NONE =>
      (case Argo_Simplex.explain lit simplex of
        SOME (cls, simplex) => (cls, (cc, simplex))
      | NONE => raise Fail "bad literal without explanation"))

fun add_level (cc, simplex) = (Argo_Cc.add_level cc, Argo_Simplex.add_level simplex)

fun backtrack (cc, simplex) = (Argo_Cc.backtrack cc, Argo_Simplex.backtrack simplex)

end
