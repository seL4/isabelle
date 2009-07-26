(*  Title:      Pure/subgoal.ML
    Author:     Makarius

Tactical operations with explicit subgoal focus, based on
canonical proof decomposition (similar to fix/assume/show).
*)

signature SUBGOAL =
sig
  type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
    asms: cterm list, concl: cterm, schematics: ctyp list * cterm list}
  val focus: Proof.context -> int -> thm -> focus * thm
  val retrofit: Proof.context -> (string * cterm) list -> cterm list ->
    int -> thm -> thm -> thm Seq.seq
  val FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF: (focus -> tactic) -> Proof.context -> int -> tactic
end;

structure Subgoal: SUBGOAL =
struct

(* focus *)

type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
  asms: cterm list, concl: cterm, schematics: ctyp list * cterm list};

fun focus ctxt i st =
  let
    val ((schematics, [st']), ctxt') =
      Variable.import true [Simplifier.norm_hhf_protect st] ctxt;
    val ((params, goal), ctxt'') = Variable.focus_subgoal i st' ctxt';
    val asms = Drule.strip_imp_prems goal;
    val concl = Drule.strip_imp_concl goal;
    val (prems, context) = Assumption.add_assumes asms ctxt'';
  in
    ({context = context, params = params, prems = prems,
      asms = asms, concl = concl, schematics = schematics}, Goal.init concl)
  end;


(* lift and retrofit *)

(*
     B [?'b, ?y]
  ----------------
  B ['b, y params]
*)
fun lift_import params th ctxt =
  let
    val cert = Thm.cterm_of (Thm.theory_of_thm th);
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;

    val Ts = map (#T o Thm.rep_cterm) params;
    val ts = map Thm.term_of params;

    val vars = rev (Term.add_vars (Thm.full_prop_of th') []);
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';
    fun var_inst (v as (_, T)) y =
      (cert (Var v), cert (list_comb (Free (y, Ts ---> T), ts)));
    val th'' = Thm.instantiate ([], map2 var_inst vars ys) th';
  in (th'', ctxt'') end;

(*
        [A x]
          :
      B x ==> C
  ------------------
  [!!x. A x ==> B x]
         :
         C
*)
fun lift_subgoals params asms th =
  let
    val lift = fold_rev Thm.all_name params o curry Drule.list_implies asms;
    val unlift =
      fold (Thm.elim_implies o Thm.assume) asms o
      Drule.forall_elim_list (map #2 params) o Thm.assume;
    val subgoals = map lift (Drule.strip_imp_prems (Thm.cprop_of th));
    val th' = fold (Thm.elim_implies o unlift) subgoals th;
  in (subgoals, th') end;

fun retrofit ctxt params asms i th =
  let
    val ps = map #2 params;
    val res0 = Goal.conclude th;
    val (res1, ctxt1) = lift_import ps res0 ctxt;
    val (subgoals, res2) = lift_subgoals params asms res1;
    val result = res2
      |> Drule.implies_intr_list asms
      |> Drule.forall_intr_list ps
      |> Drule.implies_intr_list subgoals
      |> singleton (Variable.export ctxt1 ctxt);
  in Thm.compose_no_flatten false (result, Thm.nprems_of res0) i end;


(* tacticals *)

fun FOCUS tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val (args as {context, params, asms, ...}, st') = focus ctxt i st;
    in Seq.lifts (retrofit context params asms i) (tac args st') st end;

fun SUBPROOF tac = FOCUS (FILTER Thm.no_prems o tac);

end;

val FOCUS = Subgoal.FOCUS;
val SUBPROOF = Subgoal.SUBPROOF;

