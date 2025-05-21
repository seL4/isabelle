(*  Title:      HOL/Nonstandard_Analysis/transfer_principle.ML
    Author:     Brian Huffman

Transfer principle tactic for nonstandard analysis.
*)

signature TRANSFER_PRINCIPLE =
sig
  val transfer_tac: Proof.context -> thm list -> int -> tactic
  val add_const: string -> theory -> theory
end;

structure Transfer_Principle: TRANSFER_PRINCIPLE =
struct

structure Data = Generic_Data
(
  type T = {
    intros: thm list,
    unfolds: thm list,
    refolds: thm list,
    consts: string list
  };
  val empty = {intros = [], unfolds = [], refolds = [], consts = []};
  fun merge
    ({intros = intros1, unfolds = unfolds1,
      refolds = refolds1, consts = consts1},
     {intros = intros2, unfolds = unfolds2,
      refolds = refolds2, consts = consts2}) : T =
   {intros = Thm.merge_thms (intros1, intros2),
    unfolds = Thm.merge_thms (unfolds1, unfolds2),
    refolds = Thm.merge_thms (refolds1, refolds2),
    consts = Library.merge (op =) (consts1, consts2)};
);

fun unstar_typ (Type (\<^type_name>\<open>star\<close>, [t])) = unstar_typ t
  | unstar_typ (Type (a, Ts)) = Type (a, map unstar_typ Ts)
  | unstar_typ T = T

fun unstar_term consts term =
  let
    fun unstar (Const(a,T) $ t) = if member (op =) consts a then (unstar t)
          else (Const(a,unstar_typ T) $ unstar t)
      | unstar (f $ t) = unstar f $ unstar t
      | unstar (Const(a,T)) = Const(a,unstar_typ T)
      | unstar (Abs(a,T,t)) = Abs(a,unstar_typ T,unstar t)
      | unstar t = t
  in
    unstar term
  end

local exception MATCH
in
fun transfer_star_tac ctxt =
  let
    fun thm_of (Const (\<^const_name>\<open>Ifun\<close>, _) $ t $ u) = @{thm transfer_Ifun} OF [thm_of t, thm_of u]
      | thm_of (Const (\<^const_name>\<open>star_of\<close>, _) $ _) = @{thm star_of_def}
      | thm_of (Const (\<^const_name>\<open>star_n\<close>, _) $ _) = @{thm Pure.reflexive}
      | thm_of _ = raise MATCH;

    fun thm_of_goal (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t $ (Const (\<^const_name>\<open>star_n\<close>, _) $ _)) =
          thm_of t
      | thm_of_goal _ = raise MATCH;
  in
    SUBGOAL (fn (t, i) =>
      resolve_tac ctxt [thm_of_goal (strip_all_body t |> Logic.strip_imp_concl)] i
      handle MATCH => no_tac)
  end;
end;

fun transfer_thm_of ctxt ths t =
  let
    val {intros,unfolds,refolds,consts} = Data.get (Context.Proof ctxt);
    val meta = Local_Defs.meta_rewrite_rule ctxt;
    val ths' = map meta ths;
    val unfolds' = map meta unfolds and refolds' = map meta refolds;
    val (_$_$t') = Thm.concl_of (Simplifier.rewrite_wrt ctxt true unfolds' (Thm.cterm_of ctxt t))
    val u = unstar_term consts t'
    val tac =
      rewrite_goals_tac ctxt (ths' @ refolds' @ unfolds') THEN
      ALLGOALS (Object_Logic.full_atomize_tac ctxt) THEN
      match_tac ctxt [transitive_thm] 1 THEN
      resolve_tac ctxt [@{thm transfer_start}] 1 THEN
      REPEAT_ALL_NEW (resolve_tac ctxt intros ORELSE' transfer_star_tac ctxt) 1 THEN
      match_tac ctxt [reflexive_thm] 1
  in Goal.prove ctxt [] [] (Logic.mk_equals (t,u)) (K tac) end;

fun transfer_tac ctxt ths = SUBGOAL (fn (t, _) => (fn th =>
  let
    val tr = transfer_thm_of ctxt ths t
    val (_$ l $ r) = Thm.concl_of tr;
    val trs = if l aconv r then [] else [tr];
  in rewrite_goals_tac ctxt trs th end));

local

fun map_intros f = Data.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=f intros, unfolds=unfolds, refolds=refolds, consts=consts})

fun map_unfolds f = Data.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=f unfolds, refolds=refolds, consts=consts})

fun map_refolds f = Data.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=unfolds, refolds=f refolds, consts=consts})
in

val intro_add = Thm.declaration_attribute (map_intros o Thm.add_thm o Thm.trim_context);
val intro_del = Thm.declaration_attribute (map_intros o Thm.del_thm);

val unfold_add = Thm.declaration_attribute (map_unfolds o Thm.add_thm o Thm.trim_context);
val unfold_del = Thm.declaration_attribute (map_unfolds o Thm.del_thm);

val refold_add = Thm.declaration_attribute (map_refolds o Thm.add_thm o Thm.trim_context);
val refold_del = Thm.declaration_attribute (map_refolds o Thm.del_thm);

end

fun add_const c = Context.theory_map (Data.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=unfolds, refolds=refolds, consts=c::consts}))

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>transfer_intro\<close> (Attrib.add_del intro_add intro_del)
      "declaration of transfer introduction rule" #>
    Attrib.setup \<^binding>\<open>transfer_unfold\<close> (Attrib.add_del unfold_add unfold_del)
      "declaration of transfer unfolding rule" #>
    Attrib.setup \<^binding>\<open>transfer_refold\<close> (Attrib.add_del refold_add refold_del)
      "declaration of transfer refolding rule")

end;
