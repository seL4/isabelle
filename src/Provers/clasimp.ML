(*  Title:      Provers/clasimp.ML
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier (depends on
splitter.ML, classical.ML, blast.ML).
*)

signature CLASIMP_DATA =
sig
  structure Splitter: SPLITTER
  structure Classical: CLASSICAL
  structure Blast: BLAST
  val notE: thm
  val iffD1: thm
  val iffD2: thm
end;

signature CLASIMP =
sig
  val addSss: Proof.context -> Proof.context
  val addss: Proof.context -> Proof.context
  val clarsimp_tac: Proof.context -> int -> tactic
  val mk_auto_tac: Proof.context -> int -> int -> tactic
  val auto_tac: Proof.context -> tactic
  val force_tac: Proof.context -> int -> tactic
  val fast_force_tac: Proof.context -> int -> tactic
  val slow_simp_tac: Proof.context -> int -> tactic
  val best_simp_tac: Proof.context -> int -> tactic
  val iff_add: attribute
  val iff_add': attribute
  val iff_del: attribute
  val iff_modifiers: Method.modifier parser list
  val clasimp_modifiers: Method.modifier parser list
  val clasimp_setup: theory -> theory
end;

functor Clasimp(Data: CLASIMP_DATA): CLASIMP =
struct

structure Splitter = Data.Splitter;
structure Classical = Data.Classical;
structure Blast = Data.Blast;


(* simp as classical wrapper *)

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = Simplifier.generic_simp_tac true (true, true, true);

fun clasimp f name tac ctxt =
  Classical.map_claset (fn cs => f (cs, (name, CHANGED o tac (simpset_of ctxt)))) ctxt;

(*Add a simpset to the claset!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
val addSss = clasimp Classical.addSafter "safe_asm_full_simp_tac" safe_asm_full_simp_tac;
val addss = clasimp Classical.addbefore "asm_full_simp_tac" Simplifier.asm_full_simp_tac;


(* iffs: addition of rules to simpsets and clasets simultaneously *)

local

(*Takes (possibly conditional) theorems of the form A<->B to
        the Safe Intr     rule B==>A and
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)

fun add_iff safe unsafe =
  Thm.declaration_attribute (fn th =>
    let
      val n = nprems_of th;
      val (elim, intro) = if n = 0 then safe else unsafe;
      val zero_rotate = zero_var_indexes o rotate_prems n;
    in
      Thm.attribute_declaration intro (zero_rotate (th RS Data.iffD2)) #>
      Thm.attribute_declaration elim (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
      handle THM _ =>
        (Thm.attribute_declaration elim (zero_rotate (th RS Data.notE))
          handle THM _ => Thm.attribute_declaration intro th)
    end);

fun del_iff del = Thm.declaration_attribute (fn th =>
  let val zero_rotate = zero_var_indexes o rotate_prems (nprems_of th) in
    Thm.attribute_declaration del (zero_rotate (th RS Data.iffD2)) #>
    Thm.attribute_declaration del (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
    handle THM _ =>
      (Thm.attribute_declaration del (zero_rotate (th RS Data.notE))
        handle THM _ => Thm.attribute_declaration del th)
  end);

in

val iff_add =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (add_iff
      (Classical.safe_elim NONE, Classical.safe_intro NONE)
      (Classical.haz_elim NONE, Classical.haz_intro NONE)) th
    #> Thm.attribute_declaration Simplifier.simp_add th);

val iff_add' =
  add_iff
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE)
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE);

val iff_del =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (del_iff Classical.rule_del) th #>
    Thm.attribute_declaration (del_iff Context_Rules.rule_del) th #>
    Thm.attribute_declaration Simplifier.simp_del th);

end;


(* tactics *)

fun clarsimp_tac ctxt =
  safe_asm_full_simp_tac (simpset_of ctxt) THEN_ALL_NEW
  Classical.clarify_tac (addSss ctxt);


(* auto_tac *)

(* a variant of depth_tac that avoids interference of the simplifier
   with dup_step_tac when they are combined by auto_tac *)
local

fun slow_step_tac' ctxt =
  Classical.appWrappers ctxt
    (Classical.instp_step_tac ctxt APPEND' Classical.haz_step_tac ctxt);

in

fun nodup_depth_tac ctxt m i st =
  SELECT_GOAL
    (Classical.safe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (nodup_depth_tac ctxt m 1),
        Classical.inst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (slow_step_tac' ctxt 1 THEN DEPTH_SOLVE (nodup_depth_tac ctxt (m - 1) 1)))) i st;

end;

(*Designed to be idempotent, except if Blast.depth_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac ctxt m n =
  let
    val main_tac =
      Blast.depth_tac ctxt m  (* fast but can't use wrappers *)
      ORELSE'
      (CHANGED o nodup_depth_tac (addss ctxt) n);  (* slower but more general *)
  in
    PARALLEL_GOALS (ALLGOALS (Simplifier.asm_full_simp_tac (simpset_of ctxt))) THEN
    TRY (Classical.safe_tac ctxt) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (Classical.safe_tac (addSss ctxt)) THEN
    prune_params_tac
  end;

fun auto_tac ctxt = mk_auto_tac ctxt 4 2;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac ctxt =
  let val ctxt' = addss ctxt in
    SELECT_GOAL
     (Classical.clarify_tac ctxt' 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac (simpset_of ctxt) 1) THEN
      ALLGOALS (Classical.first_best_tac ctxt'))
  end;


(* basic combinations *)

val fast_force_tac = Classical.fast_tac o addss;
val slow_simp_tac = Classical.slow_tac o addss;
val best_simp_tac = Classical.best_tac o addss;



(** concrete syntax **)

(* attributes *)

fun iff_att x = (Scan.lift
 (Args.del >> K iff_del ||
  Scan.option Args.add -- Args.query >> K iff_add' ||
  Scan.option Args.add >> K iff_add)) x;


(* method modifiers *)

val iffN = "iff";

val iff_modifiers =
 [Args.$$$ iffN -- Scan.option Args.add -- Args.colon >> K ((I, iff_add): Method.modifier),
  Args.$$$ iffN -- Scan.option Args.add -- Args.query_colon >> K (I, iff_add'),
  Args.$$$ iffN -- Args.del -- Args.colon >> K (I, iff_del)];

val clasimp_modifiers =
  Simplifier.simp_modifiers @ Splitter.split_modifiers @
  Classical.cla_modifiers @ iff_modifiers;


(* methods *)

fun clasimp_method' tac =
  Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o tac);

val auto_method =
  Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
    Method.sections clasimp_modifiers >>
  (fn NONE => SIMPLE_METHOD o CHANGED_PROP o auto_tac
    | SOME (m, n) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));


(* theory setup *)

val clasimp_setup =
  Attrib.setup @{binding iff} iff_att "declaration of Simplifier / Classical rules" #>
  Method.setup @{binding fastforce} (clasimp_method' fast_force_tac) "combined fast and simp" #>
  Method.setup @{binding slowsimp} (clasimp_method' slow_simp_tac) "combined slow and simp" #>
  Method.setup @{binding bestsimp} (clasimp_method' best_simp_tac) "combined best and simp" #>
  Method.setup @{binding force} (clasimp_method' force_tac) "force" #>
  Method.setup @{binding auto} auto_method "auto" #>
  Method.setup @{binding clarsimp} (clasimp_method' (CHANGED_PROP oo clarsimp_tac))
    "clarify simplified goal";

end;
