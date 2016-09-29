(*  Title:      Tools/Argo/argo_clausify.ML
    Author:     Sascha Boehme

Conversion of propositional formulas to definitional CNF.

The clausification implementation is based on:

  G. S. Tseitin. On the complexity of derivation in propositional
  calculus.  In A. O. Slisenko (editor) Structures in Constructive
  Mathematics and Mathematical Logic, Part II, Seminars in Mathematics,
  pages 115-125. Steklov Mathematic Institute, 1968.

  D. A. Plaisted and S. Greenbaum. A Structure-Preserving Clause Form
  Translation. Journal of Symbolic Computation, 1986.

  L. de Moura and N. Bj\orner. Proofs and Refutations, and Z3. In
  P. Rudnicki and G. Sutcliffe and B. Konev and R. A. Schmidt and
  S. Schulz (editors) International Workshop on the Implementation of
  Logics. CEUR Workshop Proceedings, 2008.
*)

signature ARGO_CLAUSIFY =
sig
  val clausify: Argo_Rewr.context -> Argo_Expr.expr * Argo_Proof.proof ->
    Argo_Proof.context * Argo_Core.context -> Argo_Proof.context * Argo_Core.context
end

structure Argo_Clausify: ARGO_CLAUSIFY =
struct

(* lifting of if-then-else expressions *)

(*
  It is assumed that expressions are free of if-then-else expressions whose then- and else-branch
  have boolean type. Such if-then-else expressions can be rewritten to expressions using only
  negation, conjunction and disjunction.

  All other modules treat if-then-else expressions as constant expressions. They do not analyze or
  decend into sub-expressions of an if-then-else expression.

  Lifting an if-then-else expression (ite P t u) introduces two new clauses
    (or (not P) (= (ite P t u) t)) and
    (or P (= (ite P t u) u))
*)

fun ite_clause simp k es (eps, (prf, core)) =
  let
    val e = Argo_Expr.mk_or es
    val (p, prf) = Argo_Proof.mk_taut k e prf 
    val (ep, prf) = Argo_Rewr.with_proof (Argo_Rewr.args (Argo_Rewr.rewrite_top simp)) (e, p) prf
  in (ep :: eps, (prf, core)) end

fun check_ite simp t (e as Argo_Expr.E (Argo_Expr.Ite, [e1, e2, e3])) (eps, (prf, core)) =
      (case Argo_Core.identify (Argo_Term.Term t) core of
        (Argo_Term.Known _, core) => (eps, (prf, core))
      | (Argo_Term.New _, core) =>
          (eps, (prf, core))
          |> ite_clause simp Argo_Proof.Taut_Ite_Then [Argo_Expr.mk_not e1, Argo_Expr.mk_eq e e2]
          |> ite_clause simp Argo_Proof.Taut_Ite_Else [e1, Argo_Expr.mk_eq e e3])
  | check_ite _ _ _ cx = cx

fun lift_ites simp (t as Argo_Term.T (_, _, ts)) =
  check_ite simp t (Argo_Term.expr_of t) #>
  fold (lift_ites simp) ts


(* tagged expressions and terms *)

fun pos x = (true, x)
fun neg x = (false, x)

fun mk_lit true t = Argo_Lit.Pos t
  | mk_lit false t = Argo_Lit.Neg t

fun expr_of (true, t) = Argo_Term.expr_of t
  | expr_of (false, t) = Argo_Expr.mk_not (Argo_Term.expr_of t)


(* adding literals *)

fun lit_for (polarity, x) (new_atoms, core) =
  (case Argo_Core.add_atom x core of
    (Argo_Term.Known t, core) => (mk_lit polarity t, (new_atoms, core))
  | (Argo_Term.New t, core) => (mk_lit polarity t, (t :: new_atoms, core)))

fun lit_of (Argo_Expr.E (Argo_Expr.Not, [e])) = lit_for (neg (Argo_Term.Expr e))
  | lit_of e = lit_for (pos (Argo_Term.Expr e))

fun lit_of' (pol, Argo_Term.T (_, Argo_Expr.Not, [t])) = lit_for (not pol, Argo_Term.Term t)
  | lit_of' (pol, t) = lit_for (pol, Argo_Term.Term t)


(* adding clauses *)

fun add_clause f xs p (new_atoms, (prf, core)) =
  let val (lits, (new_atoms, core)) = fold_map f xs (new_atoms, core)
  in (new_atoms, (prf, Argo_Core.add_axiom (lits, p) core)) end

fun simp_lit (e as Argo_Expr.E (Argo_Expr.Not, [Argo_Expr.E (Argo_Expr.Not, [e'])])) =
      Argo_Rewr.rewr Argo_Proof.Rewr_Not_Not e' e
  | simp_lit e = Argo_Rewr.keep e

fun simp_clause (e as Argo_Expr.E (Argo_Expr.Or, _)) = Argo_Rewr.args simp_lit e
  | simp_clause e = Argo_Rewr.keep e

fun new_clause k ls (new_atoms, (prf, core)) =
  let
    val e = Argo_Expr.mk_or (map expr_of ls)
    val (p, prf) = Argo_Proof.mk_taut k e prf
    val ((_, p), prf) = Argo_Rewr.with_proof simp_clause (e, p) prf
  in add_clause lit_of' ls p (new_atoms, (prf, core)) end


(* clausifying propositions *)

fun clausify_and t ts cx =
  let
    val n = length ts
    val k1 = Argo_Proof.Taut_And_1 n and k2 = Argo_Proof.Taut_And_2 o rpair n
  in
    cx
    |> new_clause k1 (pos t :: map neg ts)
    |> fold_index (fn (i, t') => new_clause (k2 i) [neg t, pos t']) ts
  end

fun clausify_or t ts cx =
  let
    val n = length ts
    val k1 = Argo_Proof.Taut_Or_1 o rpair n and k2 = Argo_Proof.Taut_Or_2 n
  in
    cx
    |> fold_index (fn (i, t') => new_clause (k1 i) [pos t, neg t']) ts
    |> new_clause k2 (neg t :: map pos ts)
  end

fun clausify_iff t t1 t2 cx =
  cx
  |> new_clause Argo_Proof.Taut_Iff_1 [pos t, pos t1, pos t2]
  |> new_clause Argo_Proof.Taut_Iff_2 [pos t, neg t1, neg t2]
  |> new_clause Argo_Proof.Taut_Iff_3 [neg t, neg t1, pos t2]
  |> new_clause Argo_Proof.Taut_Iff_4 [neg t, pos t1, neg t2]

fun clausify_lit (t as Argo_Term.T (_, Argo_Expr.And, ts)) = clausify_and t ts
  | clausify_lit (t as Argo_Term.T (_, Argo_Expr.Or, ts)) = clausify_or t ts
  | clausify_lit (t as Argo_Term.T (_, Argo_Expr.Iff, [t1, t2])) = clausify_iff t t1 t2
  | clausify_lit _ = I

fun exhaust_new_atoms ([], cx) = cx
  | exhaust_new_atoms (t :: new_atoms, cx) = exhaust_new_atoms (clausify_lit t (new_atoms, cx))

fun clausify_expr _ (Argo_Expr.E (Argo_Expr.True, _), _) cx = cx
  | clausify_expr _ (Argo_Expr.E (Argo_Expr.False, _), p) _ = Argo_Proof.unsat p
  | clausify_expr f (Argo_Expr.E (Argo_Expr.And, es), p) cx =
      fold_index (clausify_conj f (length es) p) es cx
  | clausify_expr f (Argo_Expr.E (Argo_Expr.Or, es), p) cx = add_clausify f es p cx
  | clausify_expr f (e, p) cx = add_clausify f [e] p cx

and clausify_conj f n p (i, e) (prf, core) =
  let val (p, prf) = Argo_Proof.mk_conj i n p prf
  in clausify_expr f (e, p) (prf, core) end

and add_clausify f es p cx =
  let val ecx as (new_atoms, _) = add_clause lit_of es p ([], cx)
  in fold f new_atoms ([], exhaust_new_atoms ecx) |-> fold (clausify_expr (K I)) end

fun clausify simp ep cx = clausify_expr (lift_ites simp) ep cx

end
