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
fun res_atp_tac res_atp_oracle tptp_form make_nnf timeLimit ctxt files tfrees n thm =
    SELECT_GOAL
	((EVERY1 [rtac ccontr,ObjectLogic.atomize_tac, skolemize_tac, 
		  METAHYPS(fn negs =>
			      HEADGOAL(Tactic.rtac 
					   (res_atp_oracle (ProofContext.theory_of ctxt) 
							   ((tptp_form (make_clauses (map make_nnf negs)) n tfrees)::files, timeLimit))))]) handle Fail _ => no_tac) n thm;

(* vampire and eprover tactics *)
val vampireF_tac = res_atp_tac vampire_oracle ResAtpSetup.tptp_form make_nnf (!vampire_time);

val vampireH_tac = res_atp_tac vampire_oracle ResAtpSetup.tptp_formH make_nnf1 (!vampire_time);

val eproverF_tac = res_atp_tac eprover_oracle ResAtpSetup.tptp_form make_nnf (!eprover_time);

val eproverH_tac = res_atp_tac eprover_oracle ResAtpSetup.tptp_formH make_nnf1 (!eprover_time);

val ResAtps_setup = [Method.add_methods 
		 [("vampireF", ResAtpSetup.atp_method_F vampireF_tac, "A Vampire method for FOL problems"),
		   ("eproverF", ResAtpSetup.atp_method_F eproverF_tac, "A E prover method for FOL problems"),
			("vampireH",ResAtpSetup.atp_method_H vampireH_tac, "A Vampire method for HOL problems"),
				("eproverH",ResAtpSetup.atp_method_H eproverH_tac,"A E prover method for HOL problems")]];




end
