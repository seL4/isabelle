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

(* FIXME !?!?! *)
ML {* val old_tr = !Output.Private_Hooks.tracing_fn *}
ML {* val old_wr = !Output.Private_Hooks.writeln_fn *}
ML {* val old_ur = !Output.Private_Hooks.urgent_message_fn *}
ML {* val old_wa = !Output.Private_Hooks.warning_fn *}

quickcheck_params [size = 5, iterations = 1000]
(*
nitpick_params [timeout = 5, sat_solver = MiniSat, no_overlord, verbose, card = 1-5, iter = 1,2,4,8,12]
refute_params [maxtime = 10, minsize = 1, maxsize = 5, satsolver = jerusat]
*)
ML {* Auto_Tools.time_limit := 10 *}


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

(* FIXME !?!?! *)
ML {* Output.Private_Hooks.tracing_fn := old_tr *}
ML {* Output.Private_Hooks.writeln_fn := old_wr *}
ML {* Output.Private_Hooks.urgent_message_fn := old_ur *}
ML {* Output.Private_Hooks.warning_fn := old_wa *}

end
