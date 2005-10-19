(* ID: $Id$
   Author: Jia Meng, NICTA
*)


structure ResAtpMethods =

struct
  

val vampire_time = ref 60;
val eprover_time = ref 60;

fun run_vampire time =  
    if (time >0) then vampire_time:= time
    else vampire_time:=60;

fun run_eprover time = 
    if (time > 0) then eprover_time:= time
    else eprover_time:=60;

fun vampireLimit () = !vampire_time;
fun eproverLimit () = !eprover_time;



(* convert the negated 1st subgoal into CNF, write to files and call an ATP oracle *)
fun res_atp_tac res_atp_oracle timeLimit ctxt files tfrees n thm =
    SELECT_GOAL
	((EVERY1 [rtac ccontr,ObjectLogic.atomize_tac, skolemize_tac, 
		  METAHYPS(fn negs =>
			      HEADGOAL(Tactic.rtac 
					   (res_atp_oracle (ProofContext.theory_of ctxt) 
							   ((ResAtpSetup.tptp_form (make_clauses (map make_nnf negs)) n tfrees)::files, timeLimit))))]) handle Fail _ => no_tac) n thm;


(* vampire_tac and eprover_tac *)
val vampire_tac = res_atp_tac vampire_oracle (!vampire_time);

val eprover_tac = res_atp_tac eprover_oracle (!eprover_time);


val ResAtps_setup = [Method.add_methods 
		 [("vampire", ResAtpSetup.atp_method vampire_tac, "A Vampire method"),
		   ("eprover", ResAtpSetup.atp_method eprover_tac, "A E prover method")]];




end
