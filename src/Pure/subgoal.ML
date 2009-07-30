(*  Title:      Pure/subgoal.ML
    Author:     Makarius

Tactical operations with explicit subgoal focus, based on canonical
proof decomposition.  The "visible" part of the text within the
context is fixed, the remaining goal may be schematic.
*)

signature SUBGOAL =
sig
  type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
    asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list}
  val focus_params: Proof.context -> int -> thm -> focus * thm
  val focus_prems: Proof.context -> int -> thm -> focus * thm
  val focus: Proof.context -> int -> thm -> focus * thm
  val retrofit: Proof.context -> Proof.context -> (string * cterm) list -> cterm list ->
    int -> thm -> thm -> thm Seq.seq
  val FOCUS_PARAMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF: (focus -> tactic) -> Proof.context -> int -> tactic
end;

structure Subgoal: SUBGOAL =
struct

(* focus *)

type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
  asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list};

fun gen_focus (do_prems, do_concl) ctxt i raw_st =
  let
    val st = Simplifier.norm_hhf_protect raw_st;
    val ((schematic_types, [st']), ctxt1) = Variable.importT [st] ctxt;
    val ((params, goal), ctxt2) = Variable.focus (Thm.cprem_of st' i) ctxt1;

    val (asms, concl) =
      if do_prems then (Drule.strip_imp_prems goal, Drule.strip_imp_concl goal)
      else ([], goal);
    val text = asms @ (if do_concl then [concl] else []);

    val ((_, schematic_terms), ctxt3) =
      Variable.import_inst true (map Thm.term_of text) ctxt2
      |>> Thm.certify_inst (Thm.theory_of_thm raw_st);

    val schematics = (schematic_types, schematic_terms);
    val asms' = map (Thm.instantiate_cterm schematics) asms;
    val concl' = Thm.instantiate_cterm schematics concl;
    val (prems, context) = Assumption.add_assumes asms' ctxt3;
  in
    ({context = context, params = params, prems = prems,
      asms = asms', concl = concl', schematics = schematics}, Goal.init concl')
  end;

val focus_params = gen_focus (false, false);
val focus_prems = gen_focus (true, false);
val focus = gen_focus (true, true);


(* lift and retrofit *)

(*
     B [?'b, ?y]
  ----------------
  B ['b, y params]
*)
fun lift_import params th ctxt =
  let
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;

    val Ts = map (#T o Thm.rep_cterm) params;
    val ts = map Thm.term_of params;

    val prop = Thm.full_prop_of th';
    val concl_vars = Term.add_vars (Logic.strip_imp_concl prop) [];
    val vars = rev (Term.add_vars prop []);
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';
    fun var_inst (v as (_, T)) y =
      if member (op =) concl_vars v then (v, Free (y, T))
      else (v, list_comb (Free (y, Ts ---> T), ts));
    val th'' = Thm.certify_instantiate ([], map2 var_inst vars ys) th';
  in (th'', ctxt'') end;

(*
       [x, A x]
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

fun retrofit ctxt1 ctxt0 params asms i st1 st0 =
  let
    val ps = map #2 params;
    val (st2, ctxt2) = lift_import ps st1 ctxt1;
    val (subgoals, st3) = lift_subgoals params asms st2;
    val result = st3
      |> Goal.conclude
      |> Drule.implies_intr_list asms
      |> Drule.forall_intr_list ps
      |> Drule.implies_intr_list subgoals
      |> singleton (Variable.export ctxt2 ctxt0)
      |> Drule.zero_var_indexes
      |> Drule.incr_indexes st0;
  in Thm.compose_no_flatten false (result, Thm.nprems_of st1) i st0 end;


(* tacticals *)

fun GEN_FOCUS flags tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val (args as {context, params, asms, ...}, st') = gen_focus flags ctxt i st;
    in Seq.lifts (retrofit context ctxt params asms i) (tac args st') st end;

val FOCUS_PARAMS = GEN_FOCUS (false, false);
val FOCUS_PREMS = GEN_FOCUS (true, false);
val FOCUS = GEN_FOCUS (true, true);

fun SUBPROOF tac = FOCUS (FILTER Thm.no_prems o tac);

end;

val FOCUS_PARAMS = Subgoal.FOCUS_PARAMS;
val FOCUS_PREMS = Subgoal.FOCUS_PREMS;
val FOCUS = Subgoal.FOCUS;
val SUBPROOF = Subgoal.SUBPROOF;

