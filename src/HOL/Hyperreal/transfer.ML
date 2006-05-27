(*  Title       : HOL/Hyperreal/transfer.ML
    ID          : $Id$
    Author      : Brian Huffman

Transfer principle tactic for nonstandard analysis.
*)

signature TRANSFER =
sig
  val transfer_tac: Proof.context -> thm list -> int -> tactic
  val add_const: string -> theory -> theory
  val setup: theory -> theory
end;

structure Transfer: TRANSFER =
struct

structure TransferData = GenericDataFun
(struct
  val name = "HOL/transfer";
  type T = {
    intros: thm list,
    unfolds: thm list,
    refolds: thm list,
    consts: string list
  };
  val empty = {intros = [], unfolds = [], refolds = [], consts = []};
  val extend = I;
  fun merge _
    ({intros = intros1, unfolds = unfolds1,
      refolds = refolds1, consts = consts1},
     {intros = intros2, unfolds = unfolds2,
      refolds = refolds2, consts = consts2}) =
   {intros = Drule.merge_rules (intros1, intros2),
    unfolds = Drule.merge_rules (unfolds1, unfolds2),
    refolds = Drule.merge_rules (refolds1, refolds2),
    consts = Library.merge (op =) (consts1, consts2)} : T;
  fun print _ _ = ();
end);

val transfer_start = thm "transfer_start"

fun unstar_typ (Type ("StarDef.star",[t])) = unstar_typ t
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

fun transfer_thm_of ctxt ths t =
  let
    val thy = ProofContext.theory_of ctxt;
    val {intros,unfolds,refolds,consts} = TransferData.get (Context.Proof ctxt)
    val meta = LocalDefs.meta_rewrite_rule (Context.Proof ctxt)
    val unfolds' = map meta unfolds and refolds' = map meta refolds;
    val (_$_$t') = concl_of (Tactic.rewrite true unfolds' (cterm_of thy t))
    val u = unstar_term consts t'
    val tac =
      rewrite_goals_tac (ths @ refolds' @ unfolds') THEN
      ALLGOALS ObjectLogic.full_atomize_tac THEN
      match_tac [transitive_thm] 1 THEN
      resolve_tac [transfer_start] 1 THEN
      REPEAT_ALL_NEW (resolve_tac intros) 1 THEN
      match_tac [reflexive_thm] 1
  in Goal.prove thy [] [] (Logic.mk_equals (t,u)) (K tac) end

fun transfer_tac ctxt ths =
    SUBGOAL (fn (t,i) =>
        (fn th =>
            let val tr = transfer_thm_of ctxt ths t
            in rewrite_goals_tac [tr] th end))

local

fun map_intros f = TransferData.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=f intros, unfolds=unfolds, refolds=refolds, consts=consts})

fun map_unfolds f = TransferData.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=f unfolds, refolds=refolds, consts=consts})

fun map_refolds f = TransferData.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=unfolds, refolds=f refolds, consts=consts})
in
val intro_add = Thm.declaration_attribute (map_intros o Drule.add_rule);
val intro_del = Thm.declaration_attribute (map_intros o Drule.del_rule);

val unfold_add = Thm.declaration_attribute (map_unfolds o Drule.add_rule);
val unfold_del = Thm.declaration_attribute (map_unfolds o Drule.del_rule);

val refold_add = Thm.declaration_attribute (map_refolds o Drule.add_rule);
val refold_del = Thm.declaration_attribute (map_refolds o Drule.del_rule);
end

fun add_const c = Context.theory_map (TransferData.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=unfolds, refolds=refolds, consts=c::consts}))

val transfer_method = Method.thms_ctxt_args (fn ths => fn ctxt =>
  Method.SIMPLE_METHOD' HEADGOAL (transfer_tac ctxt ths));

val setup =
  TransferData.init #>
  Attrib.add_attributes
    [("transfer_intro", Attrib.add_del_args intro_add intro_del,
      "declaration of transfer introduction rule"),
     ("transfer_unfold", Attrib.add_del_args unfold_add unfold_del,
      "declaration of transfer unfolding rule"),
     ("transfer_refold", Attrib.add_del_args refold_add refold_del,
      "declaration of transfer refolding rule")] #>
  Method.add_method ("transfer", transfer_method, "transfer principle");

end;
