(* ID: $Id$
   Author: Jia Meng, NICTA
*)

signature RES_ATP_METHODS =
sig
  val vampire_tac: Proof.context -> thm list -> int -> tactic
  val eprover_tac: Proof.context -> thm list -> int -> tactic
  val spass_tac: Proof.context -> thm list -> int -> tactic
  val vampireF_tac: Proof.context -> thm list -> int -> tactic
  val vampireH_tac: Proof.context -> thm list -> int -> tactic
  val eproverF_tac: Proof.context -> thm list -> int -> tactic
  val eproverH_tac: Proof.context -> thm list -> int -> tactic
  val spassF_tac: Proof.context -> thm list -> int -> tactic
  val spassH_tac: Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end

structure ResAtpMethods =
struct

(* convert the negated 1st subgoal into CNF, write to file and call an ATP oracle *)
fun res_atp_tac dfg res_atp_oracle mode timeLimit ctxt user_thms i st =
  (EVERY'
   [rtac ccontr,
    ObjectLogic.atomize_prems_tac,
    Meson.skolemize_tac,
    METAHYPS (fn negs =>
      HEADGOAL (Tactic.rtac
        (res_atp_oracle (ProofContext.theory_of ctxt)
          (ResAtp.write_subgoal_file dfg mode ctxt negs user_thms i, timeLimit))))] i st) handle Fail _ => Seq.empty;


(* vampire, eprover and spass tactics *)

fun vampire_tac st = res_atp_tac false vampire_oracle ResAtp.Auto (!ResAtp.time_limit) st;
fun eprover_tac st = res_atp_tac false eprover_oracle ResAtp.Auto (!ResAtp.time_limit) st;
fun spass_tac st = res_atp_tac true spass_oracle ResAtp.Auto (!ResAtp.time_limit) st;


fun vampireF_tac st = res_atp_tac false vampire_oracle ResAtp.Fol (!ResAtp.time_limit) st;

fun vampireH_tac st = res_atp_tac false vampire_oracle ResAtp.Hol (!ResAtp.time_limit) st;

fun eproverF_tac st = res_atp_tac false eprover_oracle ResAtp.Fol (!ResAtp.time_limit) st;

fun eproverH_tac st = res_atp_tac false eprover_oracle ResAtp.Hol (!ResAtp.time_limit) st;

fun spassF_tac st = res_atp_tac true spass_oracle ResAtp.Fol (!ResAtp.time_limit) st;

fun spassH_tac st = res_atp_tac true spass_oracle ResAtp.Hol (!ResAtp.time_limit) st;


fun atp_method tac =
  Method.thms_ctxt_args (fn ths => fn ctxt => Method.SIMPLE_METHOD' (tac ctxt ths));

val setup =
  Method.add_methods
    [("vampireF", atp_method vampireF_tac, "Vampire for FOL problems"),
     ("eproverF", atp_method eproverF_tac, "E prover for FOL problems"),
     ("vampireH", atp_method vampireH_tac, "Vampire for HOL problems"),
     ("eproverH", atp_method eproverH_tac, "E prover for HOL problems"),
     ("eprover", atp_method eprover_tac, "E prover for FOL and HOL problems"),
     ("vampire", atp_method vampire_tac, "Vampire for FOL and HOL problems"),
     ("spassF", atp_method spassF_tac, "SPASS for FOL problems"),
     ("spassH", atp_method spassH_tac, "SPASS for HOL problems"),
     ("spass", atp_method spass_tac, "SPASS for FOL and HOL problems")];

end;
