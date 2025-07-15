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
  val iff_add_pure: attribute
  val iff_del: attribute
  val iff_modifiers: Method.modifier parser list
  val clasimp_modifiers: Method.modifier parser list
end;

functor Clasimp(Data: CLASIMP_DATA): CLASIMP =
struct

structure Splitter = Data.Splitter;
structure Classical = Data.Classical;
structure Blast = Data.Blast;


(* simp as classical wrapper *)

(* FIXME !? *)
fun clasimp f name tac ctxt = f (ctxt, (name, fn _ => CHANGED o tac ctxt));

(*Add a simpset to the claset!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
val addSss = clasimp Classical.addSafter "safe_asm_full_simp_tac" Simplifier.safe_asm_full_simp_tac;
val addss = clasimp Classical.addbefore "asm_full_simp_tac" Simplifier.asm_full_simp_tac;


(* iffs: addition of rules to simpsets and clasets simultaneously *)

local

val safe_atts =
 {intro = Classical.safe_intro NONE,
  elim = Classical.safe_elim NONE,
  dest = Classical.safe_dest NONE};

val unsafe_atts =
 {intro = Classical.unsafe_intro NONE,
  elim = Classical.unsafe_elim NONE,
  dest = Classical.unsafe_dest NONE};

val pure_atts =
 {intro = Context_Rules.intro_query NONE,
  elim = Context_Rules.elim_query NONE,
  dest = Context_Rules.dest_query NONE};

val del_atts =
 {intro = Classical.rule_del,
  elim = Classical.rule_del,
  dest = Classical.rule_del};

(*Takes (possibly conditional) theorems of the form A<->B to
        the Safe Intr     rule B==>A and
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)

fun iff_decl safe unsafe =
  Thm.declaration_attribute (fn th => fn context =>
    let
      val n = Thm.nprems_of th;
      val {intro, elim, dest} = if n = 0 then safe else unsafe;
      val zero_rotate = zero_var_indexes o rotate_prems n;
      val decls =
        [(intro, zero_rotate (th RS Data.iffD2)),
         (dest, zero_rotate (th RS Data.iffD1))]
        handle THM _ => [(elim, zero_rotate (th RS Data.notE))]
        handle THM _ => [(intro, th)];
    in fold (uncurry Thm.attribute_declaration) decls context end);

in

val iff_add =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (iff_decl safe_atts unsafe_atts) th #>
    Thm.attribute_declaration Simplifier.simp_add th);

val iff_add_pure = iff_decl pure_atts pure_atts;

val iff_del =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (iff_decl del_atts del_atts) th #>
    Thm.attribute_declaration Simplifier.simp_del th);

end;


(* tactics *)

fun clarsimp_tac ctxt =
  Simplifier.safe_asm_full_simp_tac ctxt THEN_ALL_NEW
  Classical.clarify_tac (addSss ctxt);


(* auto_tac *)

(* a variant of depth_tac that avoids interference of the simplifier
   with dup_step_tac when they are combined by auto_tac *)
local

fun slow_step_tac' ctxt =
  Classical.appWrappers ctxt
    (Classical.instp_step_tac ctxt APPEND' Classical.unsafe_step_tac ctxt);

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
    PARALLEL_ALLGOALS (Simplifier.asm_full_simp_tac ctxt) THEN
    TRY (Classical.safe_tac ctxt) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (Classical.safe_tac (addSss ctxt)) THEN
    prune_params_tac ctxt
  end;

fun auto_tac ctxt = mk_auto_tac ctxt 4 2;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac ctxt =
  let val ctxt' = addss ctxt in
    SELECT_GOAL
     (Classical.clarify_tac ctxt' 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac ctxt 1) THEN
      ALLGOALS (Classical.first_best_tac ctxt'))
  end;


(* basic combinations *)

val fast_force_tac = Classical.fast_tac o addss;
val slow_simp_tac = Classical.slow_tac o addss;
val best_simp_tac = Classical.best_tac o addss;



(** concrete syntax **)

(* attributes *)

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>iff\<close>
      (Scan.lift
        (Args.del >> K iff_del ||
          Scan.option Args.add -- Args.query >> K iff_add_pure ||
          Scan.option Args.add >> K iff_add))
      "declaration of Simplifier / Classical rules");


(* method modifiers *)

val iffN = "iff";

val iff_modifiers =
 [Args.$$$ iffN -- Scan.option Args.add -- Args.colon >> K (Method.modifier iff_add \<^here>),
  Args.$$$ iffN -- Scan.option Args.add -- Args.query_colon >> K (Method.modifier iff_add_pure \<^here>),
  Args.$$$ iffN -- Args.del -- Args.colon >> K (Method.modifier iff_del \<^here>)];

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

val _ =
  Theory.setup
   (Method.setup \<^binding>\<open>fastforce\<close> (clasimp_method' fast_force_tac) "combined fast and simp" #>
    Method.setup \<^binding>\<open>slowsimp\<close> (clasimp_method' slow_simp_tac) "combined slow and simp" #>
    Method.setup \<^binding>\<open>bestsimp\<close> (clasimp_method' best_simp_tac) "combined best and simp" #>
    Method.setup \<^binding>\<open>force\<close> (clasimp_method' force_tac) "force" #>
    Method.setup \<^binding>\<open>auto\<close> auto_method "auto" #>
    Method.setup \<^binding>\<open>clarsimp\<close> (clasimp_method' (CHANGED_PROP oo clarsimp_tac))
      "clarify simplified goal");

end;
