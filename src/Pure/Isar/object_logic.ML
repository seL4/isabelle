(*  Title:      Pure/Isar/object_logic.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Specifics about common object-logics.
*)

signature OBJECT_LOGIC =
sig
  val add_judgment: bstring * string * mixfix -> theory -> theory
  val add_judgment_i: bstring * typ * mixfix -> theory -> theory
  val judgment_name: Sign.sg -> string
  val is_judgment: Sign.sg -> term -> bool
  val drop_judgment: Sign.sg -> term -> term
  val fixed_judgment: Sign.sg -> string -> term
  val assert_propT: Sign.sg -> term -> term
  val declare_atomize: theory attribute
  val declare_rulify: theory attribute
  val atomize_term: Sign.sg -> term -> term
  val atomize_rule: Sign.sg -> cterm -> thm
  val atomize_tac: int -> tactic
  val full_atomize_tac: int -> tactic
  val atomize_goal: int -> thm -> thm
  val rulify: thm -> thm
  val rulify_no_asm: thm -> thm
  val rule_format: 'a attribute
  val rule_format_no_asm: 'a attribute
  val setup: (theory -> theory) list
end;

structure ObjectLogic: OBJECT_LOGIC =
struct


(** object-logic theory data **)

(* data kind 'Pure/object-logic' *)

structure ObjectLogicDataArgs =
struct
  val name = "Pure/object-logic";
  type T = string option * (thm list * thm list);

  val empty = (None, ([], [Drule.norm_hhf_eq]));
  val copy = I;
  val prep_ext = I;

  fun merge_judgment (Some x, Some y) =
        if x = y then Some x else error "Attempt to merge different object-logics"
    | merge_judgment (j1, j2) = if is_some j1 then j1 else j2;

  fun merge ((judgment1, (atomize1, rulify1)), (judgment2, (atomize2, rulify2))) =
    (merge_judgment (judgment1, judgment2),
      (Drule.merge_rules (atomize1, atomize2), Drule.merge_rules (rulify1, rulify2)));

  fun print _ _ = ();
end;

structure ObjectLogicData = TheoryDataFun(ObjectLogicDataArgs);


(** generic treatment of judgments -- with a single argument only **)

(* add_judgment(_i) *)

local

fun new_judgment name (None, rules) = (Some name, rules)
  | new_judgment _ (Some _, _) = error "Attempt to redeclare object-logic judgment";

fun gen_add_judgment add_consts (name, T, syn) thy =
  thy
  |> add_consts [(name, T, syn)]
  |> ObjectLogicData.map (new_judgment (Sign.full_name (Theory.sign_of thy) name));

in

val add_judgment = gen_add_judgment Theory.add_consts;
val add_judgment_i = gen_add_judgment Theory.add_consts_i;

end;


(* term operations *)

fun judgment_name sg =
  (case ObjectLogicData.get_sg sg of
    (Some name, _) => name
  | _ => raise TERM ("Unknown object-logic judgment", []));

fun is_judgment sg (Const (c, _) $ _) = c = judgment_name sg
  | is_judgment _ _ = false;

fun drop_judgment sg (Abs (x, T, t)) = Abs (x, T, drop_judgment sg t)
  | drop_judgment sg (tm as (Const (c, _) $ t)) =
      if (c = judgment_name sg handle TERM _ => false) then t else tm
  | drop_judgment _ tm = tm;

fun fixed_judgment sg x =
  let  (*be robust wrt. low-level errors*)
    val c = judgment_name sg;
    val aT = TFree ("'a", logicS);
    val T =
      if_none (Sign.const_type sg c) (aT --> propT)
      |> Term.map_type_tvar (fn ((x, _), S) => TFree (x, S));
    val U = Term.domain_type T handle Match => aT;
  in Const (c, T) $ Free (x, U) end;

fun assert_propT sg t =
  let val T = Term.fastype_of t
  in if T = propT then t else Const (judgment_name sg, T --> propT) $ t end;



(** treatment of meta-level connectives **)

(* maintain rules *)

val get_atomize = #1 o #2 o ObjectLogicData.get_sg;
val get_rulify = #2 o #2 o ObjectLogicData.get_sg;

val add_atomize = ObjectLogicData.map o Library.apsnd o Library.apfst o Drule.add_rule;
val add_rulify = ObjectLogicData.map o Library.apsnd o Library.apsnd o Drule.add_rule;

fun declare_atomize (thy, th) = (add_atomize th thy, th);
fun declare_rulify (thy, th) = (add_rulify th thy, th);


(* atomize *)

fun rewrite_prems_tac rews i = PRIMITIVE (MetaSimplifier.fconv_rule
  (MetaSimplifier.goals_conv (Library.equal i)
    (MetaSimplifier.forall_conv
      (MetaSimplifier.goals_conv (K true) (Tactic.rewrite true rews)))));

fun atomize_term sg =
  drop_judgment sg o MetaSimplifier.rewrite_term sg (get_atomize sg) [];

fun atomize_rule sg = Tactic.rewrite true (get_atomize sg);

fun atomize_tac i st =
  if Logic.has_meta_prems (Thm.prop_of st) i then
    (rewrite_prems_tac (get_atomize (Thm.sign_of_thm st)) i) st
  else all_tac st;

fun full_atomize_tac i st =
  rewrite_goal_tac (get_atomize (Thm.sign_of_thm st)) i st;

fun atomize_goal i st =
  (case Seq.pull (atomize_tac i st) of None => st | Some (st', _) => st');


(* rulify *)

fun gen_rulify full thm =
  Tactic.simplify full (get_rulify (Thm.sign_of_thm thm)) thm
  |> Drule.gen_all |> Drule.strip_shyps_warning |> Drule.zero_var_indexes;

val rulify = gen_rulify true;
val rulify_no_asm = gen_rulify false;

fun rule_format x = Drule.rule_attribute (fn _ => rulify) x;
fun rule_format_no_asm x = Drule.rule_attribute (fn _ => rulify_no_asm) x;



(** theory setup **)

val setup = [ObjectLogicData.init];


end;
