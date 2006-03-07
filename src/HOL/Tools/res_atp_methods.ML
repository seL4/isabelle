(* ID: $Id$
   Author: Jia Meng, NICTA
*)


structure ResAtpMethods =

struct
  
(* convert the negated 1st subgoal into CNF, write to file and call an ATP oracle *)
fun res_atp_tac res_atp_oracle mode timeLimit ctxt user_thms n thm =
    (EVERY' [rtac ccontr,ObjectLogic.atomize_tac, skolemize_tac, 
		  METAHYPS(fn negs =>
			      HEADGOAL(Tactic.rtac 
					   (res_atp_oracle (ProofContext.theory_of ctxt) 
							   (ResAtp.write_subgoal_file mode ctxt negs user_thms n, timeLimit))))] n thm) handle (Fail _) => Seq.empty;

(* vampire and eprover tactics *)

fun vampire_tac st = res_atp_tac vampire_oracle ResAtp.Auto (!ResAtp.vampire_time) st;
fun eprover_tac st = res_atp_tac eprover_oracle ResAtp.Auto (!ResAtp.eprover_time) st;

fun vampireF_tac st = res_atp_tac vampire_oracle ResAtp.Fol (!ResAtp.vampire_time) st;

fun vampireH_tac st = res_atp_tac vampire_oracle ResAtp.Hol (!ResAtp.vampire_time) st;

fun eproverF_tac st = res_atp_tac eprover_oracle ResAtp.Fol (!ResAtp.eprover_time) st;

fun eproverH_tac st = res_atp_tac eprover_oracle ResAtp.Hol (!ResAtp.eprover_time) st;

val ResAtps_setup =
  Method.add_methods 
    [("vampireF", ResAtp.atp_method vampireF_tac, "Vampire for FOL problems"),
     ("eproverF", ResAtp.atp_method eproverF_tac, "E prover for FOL problems"),
     ("vampireH", ResAtp.atp_method vampireH_tac, "Vampire for HOL problems"),
     ("eproverH", ResAtp.atp_method eproverH_tac, "E prover for HOL problems"),
     ("eprover", ResAtp.atp_method eprover_tac, "E prover for FOL and HOL problems"),
     ("vampire", ResAtp.atp_method vampire_tac, "Vampire for FOL and HOL problems")];

end
