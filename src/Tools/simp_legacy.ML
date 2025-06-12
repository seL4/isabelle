(*  Title:      Tools/simp_legacy.ML

Legacy simplifier configuration interfaces -- to be phased out eventually.
*)

infix 4 addsimps delsimps addsimprocs delsimprocs;

fun ctxt addsimps thms = ctxt |> Simplifier.add_simps thms;
fun ctxt delsimps thms = ctxt |> Simplifier.del_simps thms;

fun ctxt addsimprocs procs = ctxt |> fold Simplifier.add_proc procs;
fun ctxt delsimprocs procs = ctxt |> fold Simplifier.del_proc procs;
