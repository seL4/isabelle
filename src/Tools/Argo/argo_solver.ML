(*  Title:      Tools/Argo/argo_solver.ML
    Author:     Sascha Boehme

The main interface to the Argo solver.

The solver performs satisfiability checking for a given set of assertions. If these assertions
are unsatisfiable, a proof trace is returned. If these assertions are satisfiable, the computed
model can be queried or further assertions may be added.
*)

signature ARGO_SOLVER =
sig
  type context
  val context: context
  val assert: Argo_Expr.expr list -> context -> context (* raises Argo_Expr.TYPE, Argo_Expr.EXPR
    and Argo_Proof.UNSAT *)
  val model_of: context -> string * Argo_Expr.typ -> bool option
end

structure Argo_Solver: ARGO_SOLVER =
struct

(* context *)

type context = {
  next_axiom: int,
  prf: Argo_Proof.context,
  core: Argo_Core.context}

fun mk_context next_axiom prf core: context = {next_axiom=next_axiom, prf=prf, core=core}

val context = mk_context 0 Argo_Proof.solver_context Argo_Core.context


(* negation normal form *)

fun nnf_nary r rhs env = SOME (r (length (Argo_Rewr.get_all env)), rhs)

val not_and_rhs = Argo_Rewr.scan "(or (# (not !)))"
val not_or_rhs = Argo_Rewr.scan "(and (# (not !)))"

val nnf =
  Argo_Rewr.rule Argo_Proof.Rewr_Not_True "(not true)" "false" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Not_False "(not false)" "true" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Not_Not "(not (not (? 1)))" "(? 1)" #>
  Argo_Rewr.func "(not (and _))" (nnf_nary Argo_Proof.Rewr_Not_And not_and_rhs) #>
  Argo_Rewr.func "(not (or _))" (nnf_nary Argo_Proof.Rewr_Not_Or not_or_rhs) #>
  Argo_Rewr.rule Argo_Proof.Rewr_Not_Iff "(not (iff (not (? 1)) (? 2)))" "(iff (? 1) (? 2))" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Not_Iff "(not (iff (? 1) (not (? 2))))" "(iff (? 1) (? 2))" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Not_Iff "(not (iff (? 1) (? 2)))" "(iff (not (? 1)) (? 2))"


(* propositional normalization *)

(*
  Propositional expressions are transformed into literals in the clausifier. Having
  fewer literals results in faster solver execution. Normalizing propositional expressions
  turns similar expressions into equal expressions, for which the same literal can be used.
  The clausifier expects that only negation, disjunction, conjunction and equivalence form
  propositional expressions. Expressions may be simplified to truth or falsity, but both
  truth and falsity eventually occur nowhere inside expressions.
*)

val e_true = Argo_Expr.true_expr
val e_false = Argo_Expr.false_expr

fun first_index pred xs =
  let val i = find_index pred xs
  in if i >= 0 then SOME i else NONE end

fun find_zero r_zero zero es =
  Option.map (fn i => (r_zero i, zero)) (first_index (curry Argo_Expr.eq_expr zero) es)

fun find_duals _ _ _ [] = NONE
  | find_duals _ _ _ [_] = NONE
  | find_duals r_dual zero i (e :: es) =
      (case first_index (Argo_Expr.dual_expr e) es of
        SOME i' => SOME (r_dual (i, i + i' + 1), zero)
      | NONE => find_duals r_dual zero (i + 1) es)

fun sort_nary r_sort one mk l es =
  let
    val n = length es
    fun add (i, e) = if Argo_Expr.eq_expr (e, one) then I else Argo_Exprtab.cons_list (e, i)
    fun dest (e, i) (es, is) = (e :: es, i :: is)
    val (es, iss) = Argo_Exprtab.fold_rev dest (fold_index add es Argo_Exprtab.empty) ([], [])
    fun identity is = length is = n andalso forall (op =) (map_index I is)
  in if l = 1 andalso identity (map hd iss) then NONE else (SOME (r_sort (n, iss), mk es)) end

fun apply_first fs es = get_first (fn f => f es) fs

fun norm_nary r_zero r_dual r_sort zero one mk l =
  apply_first [find_zero r_zero zero, find_duals r_dual zero 0, sort_nary r_sort one mk l]

val norm_and = norm_nary Argo_Proof.Rewr_And_False Argo_Proof.Rewr_And_Dual Argo_Proof.Rewr_And_Sort
  e_false e_true Argo_Expr.mk_and
val norm_or = norm_nary Argo_Proof.Rewr_Or_True Argo_Proof.Rewr_Or_Dual Argo_Proof.Rewr_Or_Sort
  e_true e_false Argo_Expr.mk_or

fun norm_iff env =
  let val e1 = Argo_Rewr.get env 1 and e2 = Argo_Rewr.get env 2
  in
    if Argo_Expr.dual_expr e1 e2 then SOME (Argo_Proof.Rewr_Iff_Dual, Argo_Rewr.E e_false)
    else
      (case Argo_Expr.expr_ord (e1, e2) of
        EQUAL => SOME (Argo_Proof.Rewr_Iff_Refl, Argo_Rewr.E e_true)
      | LESS => NONE
      | GREATER => SOME (Argo_Proof.Rewr_Iff_Symm, Argo_Rewr.E (Argo_Expr.mk_iff e2 e1)))
  end

val norm_prop =
  Argo_Rewr.flat "(and _)" norm_and #>
  Argo_Rewr.flat "(or _)" norm_or #>
  Argo_Rewr.rule Argo_Proof.Rewr_Imp "(imp (? 1) (? 2))" "(or (not (? 1)) (? 2))" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Iff_True "(iff true (? 1))" "(? 1)" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Iff_False "(iff false (? 1))" "(not (? 1))" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Iff_True "(iff (? 1) true)" "(? 1)" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Iff_False "(iff (? 1) false)" "(not (? 1))" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Iff_Not_Not "(iff (not (? 1)) (not (? 2)))" "(iff (? 1) (? 2))" #>
  Argo_Rewr.func "(iff (? 1) (? 2))" norm_iff


(* normalization of if-then-else expressions *)

val simp_prop_ite_result =
  Argo_Rewr.scan "(and (or (not (? 1)) (? 2)) (or (? 1) (? 3)) (or (? 2) (? 3)))"

val simp_ite_eq_result = Argo_Rewr.scan "(? 2)"

fun simp_ite env =
  if Argo_Expr.type_of (Argo_Rewr.get env 2) = Argo_Expr.Bool then
    SOME (Argo_Proof.Rewr_Ite_Prop, simp_prop_ite_result)
  else if Argo_Expr.eq_expr (Argo_Rewr.get env 2, Argo_Rewr.get env 3) then
    SOME (Argo_Proof.Rewr_Ite_Eq, simp_ite_eq_result)
  else NONE

val norm_ite =
  Argo_Rewr.rule Argo_Proof.Rewr_Ite_True "(ite true (? 1) (? 2))" "(? 1)" #>
  Argo_Rewr.rule Argo_Proof.Rewr_Ite_False "(ite false (? 1) (? 2))" "(? 2)" #>
  Argo_Rewr.func "(ite (? 1) (? 2) (? 3))" simp_ite


(* rewriting and normalizing axioms *)

val simp_context = Argo_Rewr.context |> nnf |> norm_prop |> norm_ite |> Argo_Thy.simplify
val simp_axiom = Argo_Rewr.with_proof (Argo_Rewr.rewrite simp_context)


(* asserting axioms *)

fun add_axiom e ({next_axiom, prf, core}: context) =
  let
    val _ = Argo_Expr.check e
    val (p, prf) = Argo_Proof.mk_axiom next_axiom prf
    val (ep, prf) = simp_axiom (e, p) prf 
    val (prf, core) = Argo_Clausify.clausify simp_context ep (prf, core)
  in mk_context (next_axiom + 1) prf core end

fun assert es cx =
  let val {next_axiom, prf, core}: context = fold add_axiom es cx
  in mk_context next_axiom prf (Argo_Core.run core) end


(* models *)

fun model_of ({core, ...}: context) = Argo_Core.model_of core

end
