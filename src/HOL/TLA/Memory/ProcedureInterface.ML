(* 
    File:        ProcedureInterface.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Procedure interface (ML file)
*)

Addsimps [slice_def];

(* ---------------------------------------------------------------------------- *)

val Procedure_defs = [caller_def, rtrner_def, action_rewrite Calling_def, 
                      Call_def, Return_def,
		      PLegalCaller_def, LegalCaller_def,
		      PLegalReturner_def, LegalReturner_def];

(* sample theorems (not used in the proof):
   1. calls and returns are mutually exclusive

qed_goal "CallReturnMutex" ProcedureInterface.thy
     "Call ch p v .-> .~ Return ch p w"
  (fn prems => [ auto_tac (action_css addsimps2 [Call_def,Return_def]) ]);


  2. enabledness of calls and returns
     NB: action_simp_tac is significantly faster than auto_tac

qed_goal "Call_enabled" ProcedureInterface.thy
   "!!p. base_var ((caller ch)@p) ==> (.~ $(Calling ch p) .-> $(Enabled (Call ch p (#v))))"
   (fn _ => [action_simp_tac (!simpset addsimps [caller_def, Call_def]) 
                             [] [base_enabled,Pair_inject] 1
            ]);

qed_goal "Return_enabled" ProcedureInterface.thy
   "!!p. base_var ((rtrner ch)@p) ==> $(Calling ch p) .-> $(Enabled (Return ch p (#v)))"
   (fn _ => [action_simp_tac (!simpset addsimps [rtrner_def, Return_def]) 
                             [] [base_enabled,Pair_inject] 1
            ]);

*)

(* Calls and returns change their subchannel *)
qed_goal "Call_changed" ProcedureInterface.thy
   "Call ch p v .-> <Call ch p v>_((caller ch)@p)"
   (fn _ => [auto_tac (!claset,
		       !simpset addsimps [angle_def,Call_def,caller_def,
					  action_rewrite Calling_def])
	    ]);

qed_goal "Return_changed" ProcedureInterface.thy
   "Return ch p v .-> <Return ch p v>_((rtrner ch)@p)"
   (fn _ => [auto_tac (!claset,
		       !simpset addsimps [angle_def,Return_def,rtrner_def,
					  action_rewrite Calling_def])
	    ]);

(* For convenience, generate elimination rules. 
   These rules loop if angle_def is active! *)
bind_thm("Call_changedE", action_impE Call_changed);
bind_thm("Return_changedE", action_impE Return_changed);

