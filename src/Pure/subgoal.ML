(*  Title:      Pure/subgoal.ML
    ID:         $Id$
    Author:     Makarius

Tactical operations depending on local subgoal structure.
*)

signature BASIC_SUBGOAL =
sig
  val SUBPROOF: Proof.context ->
    ({context: Proof.context, asms: cterm list, concl: cterm,
      params: (string * typ) list, prems: thm list} -> tactic) -> int -> tactic
end

signature SUBGOAL =
sig
  include BASIC_SUBGOAL
  val focus: Proof.context -> int -> thm ->
   {context: Proof.context, asms: cterm list, concl: cterm,
    params: (string * typ) list, prems: thm list} * thm

end;

structure Subgoal: SUBGOAL =
struct

(* canonical proof decomposition -- similar to fix/assume/show *)

fun focus ctxt i st =
  let
    val ([st'], ctxt') = Variable.import true [Goal.norm_hhf st] ctxt;
    val ((params, goal), ctxt'') = Variable.focus (Thm.cprem_of st' i) ctxt';
    val asms = Drule.strip_imp_prems goal;
    val concl = Drule.strip_imp_concl goal;
    val (prems, context) = ProofContext.add_assumes asms ctxt'';
  in
    ({context = context, asms = asms, concl = concl, params = params, prems = prems},
      Goal.init concl)
  end;

fun SUBPROOF ctxt tac i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let
      val (args as {context, ...}, st') = focus ctxt i st
      val result = Goal.conclude #> Seq.singleton (ProofContext.goal_exports context ctxt);
    in Seq.lifts (fn res => Proof.goal_tac res i) (Seq.maps result (tac args st')) st end

end;

structure BasicSubgoal: BASIC_SUBGOAL = Subgoal;
open BasicSubgoal;
