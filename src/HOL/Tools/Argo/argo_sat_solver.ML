(*  Title:      HOL/Tools/Argo/argo_sat_solver.ML
    Author:     Sascha Boehme

A SAT solver based on the Argo solver.
This SAT solver produces models. For proofs use Argo_Tactic.prove instead.
*)

structure Argo_SAT_Solver: sig end =
struct

fun con_of i = (string_of_int i, Argo_Expr.Bool)

fun expr_of Prop_Logic.True = Argo_Expr.true_expr
  | expr_of Prop_Logic.False = Argo_Expr.false_expr
  | expr_of (Prop_Logic.Not p) = Argo_Expr.mk_not (expr_of p)
  | expr_of (Prop_Logic.Or (p1, p2)) = Argo_Expr.mk_or2 (expr_of p1) (expr_of p2)
  | expr_of (Prop_Logic.And (p1, p2)) = Argo_Expr.mk_and2 (expr_of p1) (expr_of p2)
  | expr_of (Prop_Logic.BoolVar i) = Argo_Expr.mk_con (con_of i)

fun argo_solver p =
  let val argo = Argo_Solver.assert [expr_of p] Argo_Solver.context
  in SAT_Solver.SATISFIABLE (Argo_Solver.model_of argo o con_of) end
  handle Argo_Proof.UNSAT _ => SAT_Solver.UNSATISFIABLE NONE

val () = SAT_Solver.add_solver ("argo", argo_solver)

end
