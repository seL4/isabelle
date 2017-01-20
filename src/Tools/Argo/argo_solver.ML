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


(* rewriting and normalizing axioms *)

val simp_context =
  Argo_Rewr.context
  |> Argo_Rewr.nnf
  |> Argo_Rewr.norm_prop
  |> Argo_Rewr.norm_ite
  |> Argo_Rewr.norm_eq
  |> Argo_Rewr.norm_arith

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
