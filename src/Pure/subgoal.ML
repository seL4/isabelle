(*  Title:      Pure/subgoal.ML
    Author:     Makarius

Tactical operations depending on local subgoal structure.
*)

signature BASIC_SUBGOAL =
sig
  val SUBPROOF:
    ({context: Proof.context, schematics: ctyp list * cterm list,
      params: cterm list, asms: cterm list, concl: cterm,
      prems: thm list} -> tactic) -> Proof.context -> int -> tactic
end

signature SUBGOAL =
sig
  include BASIC_SUBGOAL
  val focus: Proof.context -> int -> thm ->
   {context: Proof.context, schematics: ctyp list * cterm list,
    params: cterm list, asms: cterm list, concl: cterm, prems: thm list} * thm

end;

structure Subgoal: SUBGOAL =
struct

(* canonical proof decomposition -- similar to fix/assume/show *)

fun focus ctxt i st =
  let
    val ((schematics, [st']), ctxt') =
      Variable.import_thms true [Simplifier.norm_hhf_protect st] ctxt;
    val ((params, goal), ctxt'') = Variable.focus_subgoal i st' ctxt';
    val asms = Drule.strip_imp_prems goal;
    val concl = Drule.strip_imp_concl goal;
    val (prems, context) = Assumption.add_assumes asms ctxt'';
  in
    ({context = context, schematics = schematics, params = params,
      asms = asms, concl = concl, prems = prems}, Goal.init concl)
  end;

fun SUBPROOF tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let
      val (args as {context, params, ...}, st') = focus ctxt i st;
      fun export_closed th =
        let
          val (th' :: params') = ProofContext.export context ctxt (th :: map Drule.mk_term params);
          val vs = map (Thm.dest_arg o Drule.strip_imp_concl o Thm.cprop_of) params';
        in Drule.forall_intr_list vs th' end;
      fun retrofit th = Thm.compose_no_flatten false (th, 0) i;
    in Seq.lifts retrofit (Seq.map (Goal.finish #> export_closed) (tac args st')) st end

end;

structure BasicSubgoal: BASIC_SUBGOAL = Subgoal;
open BasicSubgoal;
