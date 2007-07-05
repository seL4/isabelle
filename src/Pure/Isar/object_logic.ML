(*  Title:      Pure/Isar/object_logic.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Specifics about common object-logics.
*)

signature OBJECT_LOGIC =
sig
  val add_judgment: bstring * string * mixfix -> theory -> theory
  val add_judgment_i: bstring * typ * mixfix -> theory -> theory
  val judgment_name: theory -> string
  val is_judgment: theory -> term -> bool
  val drop_judgment: theory -> term -> term
  val fixed_judgment: theory -> string -> term
  val ensure_propT: theory -> term -> term
  val dest_judgment: cterm -> cterm
  val judgment_conv: conv -> conv
  val is_elim: thm -> bool
  val declare_atomize: attribute
  val declare_rulify: attribute
  val atomize_term: theory -> term -> term
  val atomize: conv
  val atomize_prems: conv
  val atomize_prems_tac: int -> tactic
  val full_atomize_tac: int -> tactic
  val rulify_term: theory -> term -> term
  val rulify_tac: int -> tactic
  val rulify: thm -> thm
  val rulify_no_asm: thm -> thm
  val rule_format: attribute
  val rule_format_no_asm: attribute
end;

structure ObjectLogic: OBJECT_LOGIC =
struct


(** theory data **)

structure ObjectLogicData = TheoryDataFun
(
  type T = string option * (thm list * thm list);
  val empty = (NONE, ([], []));
  val copy = I;
  val extend = I;

  fun merge_judgment (SOME x, SOME y) =
        if (x: string) = y then SOME x else error "Attempt to merge different object-logics"
    | merge_judgment (j1, j2) = if is_some j1 then j1 else j2;

  fun merge _ ((judgment1, (atomize1, rulify1)), (judgment2, (atomize2, rulify2))) =
    (merge_judgment (judgment1, judgment2),
      (Drule.merge_rules (atomize1, atomize2), Drule.merge_rules (rulify1, rulify2)));
);



(** generic treatment of judgments -- with a single argument only **)

(* add judgment *)

local

fun new_judgment name (NONE, rules) = (SOME name, rules)
  | new_judgment _ (SOME _, _) = error "Attempt to redeclare object-logic judgment";

fun gen_add_judgment add_consts (bname, T, mx) thy =
  let val c = Sign.full_name thy (Syntax.const_name bname mx) in
    thy
    |> add_consts [(bname, T, mx)]
    |> (fn thy' => Theory.add_finals_i false [(Const (c, Sign.the_const_type thy' c))] thy')
    |> ObjectLogicData.map (new_judgment c)
  end;

in

val add_judgment = gen_add_judgment Sign.add_consts;
val add_judgment_i = gen_add_judgment Sign.add_consts_i;

end;


(* judgments *)

fun judgment_name thy =
  (case ObjectLogicData.get thy of
    (SOME name, _) => name
  | _ => raise TERM ("Unknown object-logic judgment", []));

fun is_judgment thy (Const (c, _) $ _) = c = judgment_name thy
  | is_judgment _ _ = false;

fun drop_judgment thy (Abs (x, T, t)) = Abs (x, T, drop_judgment thy t)
  | drop_judgment thy (tm as (Const (c, _) $ t)) =
      if (c = judgment_name thy handle TERM _ => false) then t else tm
  | drop_judgment _ tm = tm;

fun fixed_judgment thy x =
  let  (*be robust wrt. low-level errors*)
    val c = judgment_name thy;
    val aT = TFree ("'a", []);
    val T =
      the_default (aT --> propT) (Sign.const_type thy c)
      |> Term.map_type_tvar (fn ((x, _), S) => TFree (x, S));
    val U = Term.domain_type T handle Match => aT;
  in Const (c, T) $ Free (x, U) end;

fun ensure_propT thy t =
  let val T = Term.fastype_of t
  in if T = propT then t else Const (judgment_name thy, T --> propT) $ t end;

fun dest_judgment ct =
  if is_judgment (Thm.theory_of_cterm ct) (Thm.term_of ct)
  then Thm.dest_arg ct
  else raise CTERM ("dest_judgment", [ct]);

fun judgment_conv cv ct =
  if is_judgment (Thm.theory_of_cterm ct) (Thm.term_of ct)
  then Conv.arg_conv cv ct
  else raise CTERM ("judgment_conv", [ct]);


(* elimination rules *)

fun is_elim rule =
  let
    val thy = Thm.theory_of_thm rule;
    val concl = Thm.concl_of rule;
  in
    Term.is_Var (drop_judgment thy concl) andalso
      exists (fn prem => concl aconv Logic.strip_assums_concl prem) (Thm.prems_of rule)
  end;



(** treatment of meta-level connectives **)

(* maintain rules *)

val get_atomize = #1 o #2 o ObjectLogicData.get;
val get_rulify = #2 o #2 o ObjectLogicData.get;

val add_atomize = ObjectLogicData.map o apsnd o apfst o Drule.add_rule;
val add_rulify = ObjectLogicData.map o apsnd o apsnd o Drule.add_rule;

val declare_atomize = Thm.declaration_attribute (fn th => Context.mapping (add_atomize th) I);
val declare_rulify = Thm.declaration_attribute (fn th => Context.mapping (add_rulify th) I);

val _ = Context.add_setup (add_rulify Drule.norm_hhf_eq);


(* atomize *)

fun atomize_term thy =
  drop_judgment thy o MetaSimplifier.rewrite_term thy (get_atomize thy) [];

fun atomize ct =
  MetaSimplifier.rewrite true (get_atomize (Thm.theory_of_cterm ct)) ct;

fun atomize_prems ct =
  if Logic.has_meta_prems (Thm.term_of ct) then
    Conv.forall_conv ~1 (Conv.prems_conv ~1 atomize) ct
  else Conv.all_conv ct;

val atomize_prems_tac = CONVERSION atomize_prems;
val full_atomize_tac = CONVERSION atomize;


(* rulify *)

fun rulify_term thy = MetaSimplifier.rewrite_term thy (get_rulify thy) [];
fun rulify_tac i st = MetaSimplifier.rewrite_goal_tac (get_rulify (Thm.theory_of_thm st)) i st;

fun gen_rulify full thm =
  MetaSimplifier.simplify full (get_rulify (Thm.theory_of_thm thm)) thm
  |> Drule.gen_all |> Thm.strip_shyps |> Drule.zero_var_indexes;

val rulify = gen_rulify true;
val rulify_no_asm = gen_rulify false;

fun rule_format x = Thm.rule_attribute (fn _ => rulify) x;
fun rule_format_no_asm x = Thm.rule_attribute (fn _ => rulify_no_asm) x;

end;
