(*  Title:      Provers/clasimp.ML
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier (depends on
simplifier.ML, splitter.ML classical.ML, blast.ML).
*)

infix 4 addSIs2 addSEs2 addSDs2 addIs2 addEs2 addDs2 addsimps2 delsimps2;
infix 4 addSss addss;

signature CLASIMP_DATA =
sig
  structure Simplifier: SIMPLIFIER
  structure Splitter: SPLITTER
  structure Classical: CLASSICAL
  structure Blast: BLAST
  sharing type Classical.claset = Blast.claset
end

signature CLASIMP =
sig
  include CLASIMP_DATA
  type claset
  type simpset
  type clasimpset
  val addSIs2   : clasimpset * thm list -> clasimpset
  val addSEs2   : clasimpset * thm list -> clasimpset
  val addSDs2   : clasimpset * thm list -> clasimpset
  val addIs2    : clasimpset * thm list -> clasimpset
  val addEs2    : clasimpset * thm list -> clasimpset
  val addDs2    : clasimpset * thm list -> clasimpset
  val addsimps2 : clasimpset * thm list -> clasimpset
  val delsimps2 : clasimpset * thm list -> clasimpset
  val addSss    : claset * simpset -> claset
  val addss     : claset * simpset -> claset
  val CLASIMPSET  :(clasimpset -> tactic) -> tactic
  val CLASIMPSET' :(clasimpset -> 'a -> tactic) -> 'a -> tactic
  val clarsimp_tac: clasimpset -> int -> tactic
  val Clarsimp_tac:               int -> tactic
  val mk_auto_tac : clasimpset -> int -> int -> tactic
  val auto_tac    : clasimpset -> tactic
  val Auto_tac    : tactic
  val auto        : unit -> unit
  val force_tac   : clasimpset  -> int -> tactic
  val Force_tac   : int -> tactic
  val force       : int -> unit
  val fast_simp_tac : clasimpset  -> int -> tactic
  val change_global_css: (clasimpset * thm list -> clasimpset) -> theory attribute
  val change_local_css: (clasimpset * thm list -> clasimpset) -> Proof.context attribute
  val get_local_clasimpset: Proof.context -> clasimpset
  val clasimp_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val setup       : (theory -> theory) list
end;

functor ClasimpFun(Data: CLASIMP_DATA): CLASIMP =
struct

open Data;

type claset = Classical.claset;
type simpset = Simplifier.simpset;
type clasimpset = claset * simpset;


(* clasimpset operations *)

(*this interface for updating a clasimpset is rudimentary and just for
  convenience for the most common cases*)

fun pair_upd1 f ((a,b),x) = (f(a,x), b);
fun pair_upd2 f ((a,b),x) = (a, f(b,x));

fun op addSIs2   arg = pair_upd1 Classical.addSIs arg;
fun op addSEs2   arg = pair_upd1 Classical.addSEs arg;
fun op addSDs2   arg = pair_upd1 Classical.addSDs arg;
fun op addIs2    arg = pair_upd1 Classical.addIs arg;
fun op addEs2    arg = pair_upd1 Classical.addEs arg;
fun op addDs2    arg = pair_upd1 Classical.addDs arg;
fun op addsimps2 arg = pair_upd2 Simplifier.addsimps arg;
fun op delsimps2 arg = pair_upd2 Simplifier.delsimps arg;

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = Simplifier.generic_simp_tac true (true,true,true);

(*Add a simpset to a classical set!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
fun cs addSss ss = Classical.addSaltern (cs, ("safe_asm_full_simp_tac",
                            CHANGED o safe_asm_full_simp_tac ss));
fun cs addss  ss = Classical.addbefore  (cs, ("asm_full_simp_tac",
                            CHANGED o Simplifier.asm_full_simp_tac ss));

(* tacticals *)

fun CLASIMPSET tacf state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss))) state;

fun CLASIMPSET' tacf i state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss) i)) state;


fun clarsimp_tac (cs, ss) = safe_asm_full_simp_tac ss THEN_ALL_NEW
                            Classical.clarify_tac (cs addSss ss);
fun Clarsimp_tac i = clarsimp_tac (Classical.claset(), Simplifier.simpset()) i;


(* auto_tac *)

fun blast_depth_tac cs m i thm =
    Blast.depth_tac cs m i thm
      handle Blast.TRANS s => (warning ("Blast_tac: " ^ s); Seq.empty);

(* a variant of depth_tac that avoids interference of the simplifier
   with dup_step_tac when they are combined by auto_tac *)
local
fun slow_step_tac' cs = Classical.appWrappers cs
        (Classical.instp_step_tac cs APPEND' Classical.haz_step_tac cs);
in fun nodup_depth_tac cs m i state = SELECT_GOAL
   (Classical.safe_steps_tac cs 1 THEN_ELSE
        (DEPTH_SOLVE (nodup_depth_tac cs m 1),
         Classical.inst0_step_tac cs 1 APPEND COND (K (m=0)) no_tac
             (slow_step_tac' cs 1 THEN DEPTH_SOLVE (nodup_depth_tac cs (m-1) 1))
        )) i state;
end;

(*Designed to be idempotent, except if blast_depth_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac (cs, ss) m n =
    let val cs' = cs addss ss
        val maintac =
          blast_depth_tac cs m               (* fast but can't use wrappers *)
          ORELSE'
          (CHANGED o nodup_depth_tac cs' n); (* slower but more general *)
    in  EVERY [ALLGOALS (Simplifier.asm_full_simp_tac ss),
               TRY (Classical.safe_tac cs),
               REPEAT (FIRSTGOAL maintac),
               TRY (Classical.safe_tac (cs addSss ss)),
               prune_params_tac]
    end;

fun auto_tac css = mk_auto_tac css 4 2;

fun Auto_tac st = auto_tac (Classical.claset(), Simplifier.simpset()) st;

fun auto () = by Auto_tac;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac (cs,ss) = let val cs' = cs addss ss in SELECT_GOAL (EVERY [
        Classical.clarify_tac cs' 1,
        IF_UNSOLVED (Simplifier.asm_full_simp_tac ss 1),
        ALLGOALS (Classical.first_best_tac cs')]) end;
fun Force_tac i = force_tac (Classical.claset(), Simplifier.simpset()) i;
fun force i = by (Force_tac i);


(* fast_simp_tac *)

fun fast_simp_tac (cs, ss) = let val cs' = cs addss ss in Classical.fast_tac cs' end;


(* change clasimpset *)

fun change_global_css f (thy, th) =
  let
    val cs_ref = Classical.claset_ref_of thy;
    val ss_ref = Simplifier.simpset_ref_of thy;
    val (cs', ss') = f ((! cs_ref, ! ss_ref), [th]);
  in cs_ref := cs'; ss_ref := ss'; (thy, th) end;

fun change_local_css f (ctxt, th) =
  let
    val cs = Classical.get_local_claset ctxt;
    val ss = Simplifier.get_local_simpset ctxt;
    val (cs', ss') = f ((cs, ss), [th]);
    val ctxt' =
      ctxt
      |> Classical.put_local_claset cs'
      |> Simplifier.put_local_simpset ss';
  in (ctxt', th) end;


(* methods *)

fun get_local_clasimpset ctxt =
  (Classical.get_local_claset ctxt, Simplifier.get_local_simpset ctxt);

val clasimp_modifiers =
  Simplifier.simp_modifiers @ Splitter.split_modifiers @ Classical.cla_modifiers;

fun clasimp_meth tac prems ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (get_local_clasimpset ctxt));

fun clasimp_meth' tac prems ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' tac (get_local_clasimpset ctxt)));

val clasimp_method = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth;
val clasimp_method' = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth';


fun auto_args m =
  Method.bang_sectioned_args' clasimp_modifiers (Scan.lift (Scan.option (Args.nat -- Args.nat))) m;

fun auto_meth None = clasimp_meth (CHANGED o auto_tac)
  | auto_meth (Some (m, n)) = clasimp_meth (CHANGED o (fn css => mk_auto_tac css m n));


(* theory setup *)

val setup =
 [Method.add_methods
   [("fastsimp", clasimp_method' fast_simp_tac, "combined fast and simp"),
    ("force", clasimp_method' force_tac, "force"),
    ("auto", auto_args auto_meth, "auto"),
    ("clarsimp", clasimp_method' (CHANGED oo clarsimp_tac), "clarify simplified goal")]];


end;
