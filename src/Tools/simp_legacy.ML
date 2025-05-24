(*  Title:      Tools/simp_legacy.ML

Legacy simplifier configuration interfaces -- to be phased out eventually.
*)

infix 4
  addsimps delsimps addsimprocs delsimprocs
  setloop addloop delloop
  setSSolver addSSolver setSolver addSolver;

local

open Simplifier

in

fun ctxt addsimps thms = ctxt |> add_simps thms;
fun ctxt delsimps thms = ctxt |> del_simps thms;

fun ctxt addsimprocs procs = ctxt |> fold add_proc procs;
fun ctxt delsimprocs procs = ctxt |> fold del_proc procs;

fun ctxt setloop looper = ctxt |> set_loop looper;
fun ctxt addloop looper = ctxt |> add_loop looper;
fun ctxt delloop looper = ctxt |> del_loop looper;

fun ctxt setSSolver solver = ctxt |> set_safe_solver solver;
fun ctxt addSSolver solver = ctxt |> add_safe_solver solver;

fun ctxt setSolver solver = ctxt |> set_unsafe_solver solver;
fun ctxt addSolver solver = ctxt |> add_unsafe_solver solver;

end
