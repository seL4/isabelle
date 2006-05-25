(* ID: $Id$
   Author: Jia Meng, NICTA
*)


structure ResAtpMethods =

struct
  
(* convert the negated 1st subgoal into CNF, write to file and call an ATP oracle *)
fun res_atp_tac dfg res_atp_oracle mode timeLimit ctxt user_thms n thm =
    (EVERY' [rtac ccontr,ObjectLogic.atomize_tac, skolemize_tac, 
		  METAHYPS(fn negs =>
			      HEADGOAL(Tactic.rtac 
					   (res_atp_oracle (ProofContext.theory_of ctxt) 
							   (ResAtp.write_subgoal_file dfg mode ctxt negs user_thms n, timeLimit))))] n thm) handle (Fail _) => Seq.empty;

(* vampire, eprover and spass tactics *)

fun vampire_tac st = res_atp_tac false vampire_oracle ResAtp.Auto (!ResAtp.vampire_time) st;
fun eprover_tac st = res_atp_tac false eprover_oracle ResAtp.Auto (!ResAtp.eprover_time) st;
fun spass_tac st = res_atp_tac true spass_oracle ResAtp.Auto (!ResAtp.spass_time) st;


fun vampireF_tac st = res_atp_tac false vampire_oracle ResAtp.Fol (!ResAtp.vampire_time) st;

fun vampireH_tac st = res_atp_tac false vampire_oracle ResAtp.Hol (!ResAtp.vampire_time) st;

fun eproverF_tac st = res_atp_tac false eprover_oracle ResAtp.Fol (!ResAtp.eprover_time) st;

fun eproverH_tac st = res_atp_tac false eprover_oracle ResAtp.Hol (!ResAtp.eprover_time) st;

fun spassF_tac st = res_atp_tac true spass_oracle ResAtp.Fol (!ResAtp.spass_time) st;

fun spassH_tac st = res_atp_tac true spass_oracle ResAtp.Hol (!ResAtp.spass_time) st;

val ResAtps_setup =
  Method.add_methods 
    [("vampireF", ResAtp.atp_method vampireF_tac, "Vampire for FOL problems"),
     ("eproverF", ResAtp.atp_method eproverF_tac, "E prover for FOL problems"),
     ("vampireH", ResAtp.atp_method vampireH_tac, "Vampire for HOL problems"),
     ("eproverH", ResAtp.atp_method eproverH_tac, "E prover for HOL problems"),
     ("eprover", ResAtp.atp_method eprover_tac, "E prover for FOL and HOL problems"),
     ("vampire", ResAtp.atp_method vampire_tac, "Vampire for FOL and HOL problems"),
     ("spassF", ResAtp.atp_method spassF_tac, "SPASS for FOL problems"),
     ("spassH", ResAtp.atp_method spassH_tac, "SPASS for HOL problems"),
     ("spass", ResAtp.atp_method spass_tac, "SPASS for FOL and HOL problems")];

end
