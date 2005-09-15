(*  Title       : HOL/Hyperreal/transfer.ML
    ID          : $Id$
    Author      : Brian Huffman

Transfer principle tactic for nonstandard analysis
*)

signature TRANSFER_TAC =
sig
  val transfer_tac: thm list -> int -> tactic
  val add_const: string -> theory -> theory
  val setup: (theory -> theory) list
end;

structure Transfer: TRANSFER_TAC =
struct

structure TransferData = TheoryDataFun
(struct
  val name = "HOL/transfer";
  type T = {
    intros: thm list,
    unfolds: thm list,
    refolds: thm list,
    consts: string list
  };
  val empty = {intros = [], unfolds = [], refolds = [], consts = []};
  val copy = I;
  val extend = I;
  fun merge _
    ({intros = intros1, unfolds = unfolds1,
      refolds = refolds1, consts = consts1},
     {intros = intros2, unfolds = unfolds2,
      refolds = refolds2, consts = consts2}) =
   {intros = Drule.merge_rules (intros1, intros2),
    unfolds = Drule.merge_rules (unfolds1, unfolds2),
    refolds = Drule.merge_rules (refolds1, refolds2),
    consts = merge_lists consts1 consts2};
  fun print _ _ = ();
end);

val transfer_start = thm "transfer_start"

fun unstar_typ (Type ("StarDef.star",[t])) = unstar_typ t
  | unstar_typ (Type (a, Ts)) = Type (a, map unstar_typ Ts)
  | unstar_typ T = T

fun unstar_term consts term =
  let
    fun delete a = exists (fn x => x = a) consts
    fun unstar (Const(a,T) $ t) = if (delete a) then (unstar t)
          else (Const(a,unstar_typ T) $ unstar t)
      | unstar (f $ t) = unstar f $ unstar t
      | unstar (Const(a,T)) = Const(a,unstar_typ T)
      | unstar (Abs(a,T,t)) = Abs(a,unstar_typ T,unstar t) 
      | unstar t = t
  in
    unstar term
  end

val atomizers = map thm ["atomize_all", "atomize_imp", "atomize_eq"]

fun transfer_thm_of thy ths t =
  let
    val {intros,unfolds,refolds,consts} = TransferData.get thy
    val (_$_$t') = concl_of (Tactic.rewrite true unfolds (cterm_of thy t))
    val u = unstar_term consts t'
    val ct = cterm_of thy (Logic.mk_equals (t,u))
    val tacs =
      [ rewrite_goals_tac atomizers
      , match_tac [transitive_thm] 1
      , resolve_tac [transfer_start] 1
      , REPEAT_ALL_NEW (resolve_tac intros) 1
      , match_tac [reflexive_thm] 1 ]
  in
    prove_goalw_cterm (ths @ refolds @ unfolds) ct (fn _ => tacs)
  end

fun transfer_tac ths =
    SUBGOAL (fn (t,i) =>
        (fn th =>
            let val thy = theory_of_thm th
                val tr = transfer_thm_of thy ths t
            in rewrite_goals_tac [tr] th
            end
        )
    )

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
fun intro_add_global (thy, thm) = (map_intros (Drule.add_rule thm) thy, thm);
fun intro_del_global (thy, thm) = (map_intros (Drule.del_rule thm) thy, thm);

fun unfold_add_global (thy, thm) = (map_unfolds (Drule.add_rule thm) thy, thm);
fun unfold_del_global (thy, thm) = (map_unfolds (Drule.del_rule thm) thy, thm);

fun refold_add_global (thy, thm) = (map_refolds (Drule.add_rule thm) thy, thm);
fun refold_del_global (thy, thm) = (map_refolds (Drule.del_rule thm) thy, thm);
end

fun add_const c = TransferData.map
  (fn {intros,unfolds,refolds,consts} =>
    {intros=intros, unfolds=unfolds, refolds=refolds, consts=c::consts})

local
  val undef_local =
    Attrib.add_del_args
      Attrib.undef_local_attribute
      Attrib.undef_local_attribute;
in
  val intro_attr =
   (Attrib.add_del_args intro_add_global intro_del_global, undef_local);
  val unfold_attr =
   (Attrib.add_del_args unfold_add_global unfold_del_global, undef_local);
  val refold_attr =
   (Attrib.add_del_args refold_add_global refold_del_global, undef_local);
end

val transfer_method = Method.SIMPLE_METHOD' HEADGOAL o transfer_tac;

val setup =
  [ TransferData.init,
    Attrib.add_attributes
    [ ("transfer_intro", intro_attr,
       "declaration of transfer introduction rule"),
      ("transfer_unfold", unfold_attr,
       "declaration of transfer unfolding rule"),
      ("transfer_refold", refold_attr,
       "declaration of transfer refolding rule")
    ],
    Method.add_method
    ("transfer", Method.thms_args transfer_method, "transfer principle")
  ];

end;
