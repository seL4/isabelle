(* 
    File:        ProcedureInterface.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Procedure interface (theorems and proofs)
*)

Addsimps [slice_def];
val mem_css = (claset(), simpset());

(* ---------------------------------------------------------------------------- *)

val Procedure_defs = [caller_def, rtrner_def, Calling_def, 
                      Call_def, Return_def,
		      PLegalCaller_def, LegalCaller_def,
		      PLegalReturner_def, LegalReturner_def];

(* sample theorems (not used in the proof):
   1. calls and returns are mutually exclusive

qed_goal "CallNotReturn" ProcedureInterface.thy
     "|- Call ch p v --> ~ Return ch p w"
  (fn prems => [ auto_tac (temp_css addsimps2 [Call_def,Return_def]) ]);


  2. enabledness of calls and returns

qed_goal "Call_enabled" ProcedureInterface.thy
   "!!p. basevars ((caller ch)!p) ==> |- ~ Calling ch p --> Enabled (Call ch p v)"
   (fn _ => [action_simp_tac (simpset() addsimps [caller_def, Call_def]) 
                             [] [base_enabled,Pair_inject] 1
            ]);

qed_goal "Call_enabled_rew" ProcedureInterface.thy
   "basevars ((caller ch)!p) ==> |- Enabled (Call ch p v) = (~Calling ch p)"
   (fn [prem] => [auto_tac (mem_css addsimps2 [Call_def]),
                  force_tac (mem_css addsimps2 [enabled_def]) 1,
                  enabled_tac prem 1,
                  action_simp_tac (simpset() addsimps [caller_def]) [] [Pair_inject] 1
            ]);

qed_goal "Return_enabled" ProcedureInterface.thy
   "!!p. basevars ((rtrner ch)!p) ==> |- Calling ch p --> Enabled (Return ch p v)"
   (fn _ => [action_simp_tac (simpset() addsimps [rtrner_def, Return_def]) 
                             [] [base_enabled,Pair_inject] 1
            ]);

*)

(* Calls and returns change their subchannel *)
qed_goal "Call_changed" ProcedureInterface.thy
   "|- Call ch p v --> <Call ch p v>_((caller ch)!p)"
   (fn _ => [ auto_tac (mem_css addsimps2 [angle_def,Call_def,caller_def,Calling_def]) ]);

qed_goal "Return_changed" ProcedureInterface.thy
   "|- Return ch p v --> <Return ch p v>_((rtrner ch)!p)"
   (fn _ => [ auto_tac (mem_css addsimps2 [angle_def,Return_def,rtrner_def,Calling_def]) ]);


