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
fun res_atp_tac res_atp_oracle mode timeLimit ctxt user_thms n thm =
    (SELECT_GOAL
	(EVERY1 [rtac ccontr,ObjectLogic.atomize_tac, skolemize_tac, 
		  METAHYPS(fn negs =>
			      HEADGOAL(Tactic.rtac 
					   (res_atp_oracle (ProofContext.theory_of ctxt) 
							   (ResAtpSetup.prep_atp_input mode ctxt negs user_thms n, timeLimit))))]) n thm) handle (Fail _) => Seq.empty;

(* vampire and eprover tactics *)

fun vampire_tac st = res_atp_tac vampire_oracle ResAtpSetup.Auto (!vampire_time) st;
fun eprover_tac st = res_atp_tac eprover_oracle ResAtpSetup.Auto (!eprover_time) st;

fun vampireF_tac st = res_atp_tac vampire_oracle ResAtpSetup.Fol (!vampire_time) st;

fun vampireH_tac st = res_atp_tac vampire_oracle ResAtpSetup.Hol (!vampire_time) st;

fun eproverF_tac st = res_atp_tac eprover_oracle ResAtpSetup.Fol (!eprover_time) st;

fun eproverH_tac st = res_atp_tac eprover_oracle ResAtpSetup.Hol (!eprover_time) st;

val ResAtps_setup =
  Method.add_methods 
    [("vampireF", ResAtpSetup.atp_method vampireF_tac, "Vampire for FOL problems"),
     ("eproverF", ResAtpSetup.atp_method eproverF_tac, "E prover for FOL problems"),
     ("vampireH", ResAtpSetup.atp_method vampireH_tac, "Vampire for HOL problems"),
     ("eproverH", ResAtpSetup.atp_method eproverH_tac, "E prover for HOL problems"),
     ("eprover", ResAtpSetup.atp_method eprover_tac, "E prover for FOL and HOL problems"),
     ("vampire", ResAtpSetup.atp_method vampire_tac, "Vampire for FOL and HOL problems")];

end
