theory MutabelleExtra
imports Complex_Main SML_Quickcheck
(*
  "~/Downloads/Jinja/J/TypeSafe"
  "~/Downloads/Jinja/J/Annotate"
  (* FIXME "Example" *)
  "~/Downloads/Jinja/J/execute_Bigstep"
  "~/Downloads/Jinja/J/execute_WellType"
  "~/Downloads/Jinja/JVM/JVMDefensive"
  "~/Downloads/Jinja/JVM/JVMListExample"
  "~/Downloads/Jinja/BV/BVExec"
  "~/Downloads/Jinja/BV/LBVJVM"
  "~/Downloads/Jinja/BV/BVNoTypeError"
  "~/Downloads/Jinja/BV/BVExample"
  "~/Downloads/Jinja/Compiler/TypeComp"
*)
(*"~/Downloads/NormByEval/NBE"*)
uses "mutabelle.ML"
     "mutabelle_extra.ML"
begin

ML {* val old_tr = !Output.tracing_fn *}
ML {* val old_wr = !Output.writeln_fn *}
ML {* val old_pr = !Output.priority_fn *}
ML {* val old_wa = !Output.warning_fn *}

quickcheck_params [size = 5, iterations = 1000]
(*
nitpick_params [timeout = 5 s, sat_solver = MiniSat, no_overlord, verbose, card = 1-5, iter = 1,2,4,8,12]
refute_params [maxtime = 10, minsize = 1, maxsize = 5, satsolver = jerusat]
*)
ML {* Auto_Counterexample.time_limit := 10 *}


text {* Uncomment the following ML code to check the counterexample generation with all theorems of Complex_Main. *}

ML {*
(*
      MutabelleExtra.random_seed := 1.0;
      MutabelleExtra.thms_of true @{theory Complex_Main}
      |> MutabelleExtra.take_random 1000000
      |> (fn thms => List.drop (thms, 1000))
      |> (fn thms => MutabelleExtra.mutate_theorems_and_write_report
             @{theory} [MutabelleExtra.quickcheck_mtd "SML",
                        MutabelleExtra.quickcheck_mtd "code"
                        (*MutabelleExtra.refute_mtd,
                        MutabelleExtra.nitpick_mtd*)] thms "/tmp/muta.out")
*)
 *}

ML {* Output.tracing_fn := old_tr *}
ML {* Output.writeln_fn := old_wr *}
ML {* Output.priority_fn := old_pr *}
ML {* Output.warning_fn := old_wa *}

end