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

(* Calls and returns change their subchannel *)
Goal "|- Call ch p v --> <Call ch p v>_((caller ch)!p)";
by (auto_tac (mem_css addsimps2 [angle_def,Call_def,caller_def,Calling_def]));
qed "Call_changed";

Goal "|- Return ch p v --> <Return ch p v>_((rtrner ch)!p)";
by (auto_tac (mem_css addsimps2 [angle_def,Return_def,rtrner_def,Calling_def]));
qed "Return_changed";

