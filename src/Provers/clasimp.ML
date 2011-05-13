(*  Title:      Provers/clasimp.ML
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier (depends on
splitter.ML, classical.ML, blast.ML).
*)

infix 4 addSss addss addss';

signature CLASIMP_DATA =
sig
  structure Splitter: SPLITTER
  structure Classical: CLASSICAL
  structure Blast: BLAST
  sharing type Classical.claset = Blast.claset
  val notE: thm
  val iffD1: thm
  val iffD2: thm
end;

signature CLASIMP =
sig
  type claset
  type clasimpset
  val clasimpset_of: Proof.context -> clasimpset
  val addSss: claset * simpset -> claset
  val addss: claset * simpset -> claset
  val addss': claset * simpset -> claset
  val clarsimp_tac: clasimpset -> int -> tactic
  val mk_auto_tac: clasimpset -> int -> int -> tactic
  val auto_tac: clasimpset -> tactic
  val force_tac: clasimpset  -> int -> tactic
  val fast_simp_tac: clasimpset -> int -> tactic
  val slow_simp_tac: clasimpset -> int -> tactic
  val best_simp_tac: clasimpset -> int -> tactic
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


(* type clasimpset *)

type claset = Classical.claset;
type clasimpset = claset * simpset;

fun clasimpset_of ctxt = (Classical.claset_of ctxt, Simplifier.simpset_of ctxt);


(* simp as classical wrapper *)

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = Simplifier.generic_simp_tac true (true, true, true);

(*Add a simpset to a classical set!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
fun cs addSss ss =
  Classical.addSafter (cs, ("safe_asm_full_simp_tac", CHANGED o safe_asm_full_simp_tac ss));

fun cs addss ss =
  Classical.addbefore (cs, ("asm_full_simp_tac", CHANGED o Simplifier.asm_full_simp_tac ss));

fun cs addss' ss =
  Classical.addbefore (cs, ("asm_full_simp_tac", CHANGED o Simplifier.asm_lr_simp_tac ss));


(* iffs: addition of rules to simpsets and clasets simultaneously *)

local

(*Takes (possibly conditional) theorems of the form A<->B to
        the Safe Intr     rule B==>A and
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)

fun app (att: attribute) th context = #1 (att (context, th));

fun add_iff safe unsafe =
  Thm.declaration_attribute (fn th =>
    let
      val n = nprems_of th;
      val (elim, intro) = if n = 0 then safe else unsafe;
      val zero_rotate = zero_var_indexes o rotate_prems n;
    in
      app intro (zero_rotate (th RS Data.iffD2)) #>
      app elim (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
      handle THM _ => (app elim (zero_rotate (th RS Data.notE)) handle THM _ => app intro th)
    end);

fun del_iff del = Thm.declaration_attribute (fn th =>
  let val zero_rotate = zero_var_indexes o rotate_prems (nprems_of th) in
    app del (zero_rotate (th RS Data.iffD2)) #>
    app del (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
    handle THM _ => (app del (zero_rotate (th RS Data.notE)) handle THM _ => app del th)
  end);

in

val iff_add =
  add_iff
    (Classical.safe_elim NONE, Classical.safe_intro NONE)
    (Classical.haz_elim NONE, Classical.haz_intro NONE)
  #> Simplifier.simp_add;

val iff_add' =
  add_iff
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE)
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE);

val iff_del =
  del_iff Classical.rule_del #>
  del_iff Context_Rules.rule_del #>
  Simplifier.simp_del;

end;


(* tactics *)

fun clarsimp_tac (cs, ss) =
  safe_asm_full_simp_tac ss THEN_ALL_NEW
  Classical.clarify_tac (cs addSss ss);


(* auto_tac *)

fun blast_depth_tac cs m i thm =
  Blast.depth_tac cs m i thm
    handle Blast.TRANS s => (warning ("Blast_tac: " ^ s); Seq.empty);

(* a variant of depth_tac that avoids interference of the simplifier
   with dup_step_tac when they are combined by auto_tac *)
local

fun slow_step_tac' cs =
  Classical.appWrappers cs
    (Classical.instp_step_tac cs APPEND' Classical.haz_step_tac cs);

in

fun nodup_depth_tac cs m i st =
  SELECT_GOAL
    (Classical.safe_steps_tac cs 1 THEN_ELSE
      (DEPTH_SOLVE (nodup_depth_tac cs m 1),
        Classical.inst0_step_tac cs 1 APPEND COND (K (m = 0)) no_tac
          (slow_step_tac' cs 1 THEN DEPTH_SOLVE (nodup_depth_tac cs (m - 1) 1)))) i st;

end;

(*Designed to be idempotent, except if blast_depth_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac (cs, ss) m n =
  let
    val cs' = cs addss ss;
    val main_tac =
      blast_depth_tac cs m               (* fast but can't use wrappers *)
      ORELSE'
      (CHANGED o nodup_depth_tac cs' n); (* slower but more general *)
  in
    PARALLEL_GOALS (ALLGOALS (Simplifier.asm_full_simp_tac ss)) THEN
    TRY (Classical.safe_tac cs) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (Classical.safe_tac (cs addSss ss)) THEN
    prune_params_tac
  end;

fun auto_tac css = mk_auto_tac css 4 2;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac (cs, ss) =
  let val cs' = cs addss ss in
    SELECT_GOAL
     (Classical.clarify_tac cs' 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac ss 1) THEN
      ALLGOALS (Classical.first_best_tac cs'))
  end;


(* basic combinations *)

fun ADDSS tac (cs, ss) = let val cs' = cs addss ss in tac cs' end;

val fast_simp_tac = ADDSS Classical.fast_tac;
val slow_simp_tac = ADDSS Classical.slow_tac;
val best_simp_tac = ADDSS Classical.best_tac;



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

fun clasimp_meth tac ctxt = METHOD (fn facts =>
  ALLGOALS (Method.insert_tac facts) THEN tac (clasimpset_of ctxt));

fun clasimp_meth' tac ctxt = METHOD (fn facts =>
  HEADGOAL (Method.insert_tac facts THEN' tac (clasimpset_of ctxt)));


fun clasimp_method' tac =
  Method.sections clasimp_modifiers >> K (clasimp_meth' tac);

val auto_method =
  Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
    Method.sections clasimp_modifiers >>
  (fn NONE => clasimp_meth (CHANGED_PROP o auto_tac)
    | SOME (m, n) => clasimp_meth (CHANGED_PROP o (fn css => mk_auto_tac css m n)));


(* theory setup *)

val clasimp_setup =
  Attrib.setup @{binding iff} iff_att "declaration of Simplifier / Classical rules" #>
  Method.setup @{binding fastsimp} (clasimp_method' fast_simp_tac) "combined fast and simp" #>
  Method.setup @{binding slowsimp} (clasimp_method' slow_simp_tac) "combined slow and simp" #>
  Method.setup @{binding bestsimp} (clasimp_method' best_simp_tac) "combined best and simp" #>
  Method.setup @{binding force} (clasimp_method' force_tac) "force" #>
  Method.setup @{binding auto} auto_method "auto" #>
  Method.setup @{binding clarsimp} (clasimp_method' (CHANGED_PROP oo clarsimp_tac))
    "clarify simplified goal";

end;
