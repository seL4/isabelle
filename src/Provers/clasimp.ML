(*  Title: 	Provers/clasimp.ML
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier (depends on
simplifier.ML, classical.ML, blast.ML).
*)

infix 4 addSIs2 addSEs2 addSDs2 addIs2 addEs2 addDs2 addsimps2 delsimps2;
infix 4 addSss addss;

signature CLASIMP_DATA =
sig
  structure Simplifier: SIMPLIFIER
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
  val addSIs2	: clasimpset * thm list -> clasimpset
  val addSEs2	: clasimpset * thm list -> clasimpset
  val addSDs2	: clasimpset * thm list -> clasimpset
  val addIs2	: clasimpset * thm list -> clasimpset
  val addEs2	: clasimpset * thm list -> clasimpset
  val addDs2	: clasimpset * thm list -> clasimpset
  val addsimps2	: clasimpset * thm list -> clasimpset
  val delsimps2	: clasimpset * thm list -> clasimpset
  val addSss	: claset * simpset -> claset
  val addss	: claset * simpset -> claset
  val CLASIMPSET  :(clasimpset -> tactic) -> tactic
  val CLASIMPSET' :(clasimpset -> 'a -> tactic) -> 'a -> tactic
  val clarsimp_tac: clasimpset -> int -> tactic
  val Clarsimp_tac:               int -> tactic
  val mk_auto_tac : clasimpset -> int -> int -> tactic
  val auto_tac	  : clasimpset -> tactic
  val Auto_tac	  : tactic
  val auto	  : unit -> unit
  val force_tac	  : clasimpset  -> int -> tactic
  val Force_tac	  : int -> tactic
  val force	  : int -> unit
  val setup	  : (theory -> theory) list
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

(*Add a simpset to a classical set!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
fun cs addSss ss = Classical.addSaltern (cs, ("safe_asm_full_simp_tac",
			    CHANGED o Simplifier.safe_asm_full_simp_tac ss));
fun cs addss  ss = Classical.addbefore  (cs, ("asm_full_simp_tac", 
			    CHANGED o Simplifier.asm_full_simp_tac ss));

(* tacticals *)

fun CLASIMPSET tacf state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss))) state;

fun CLASIMPSET' tacf i state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss) i)) state;


fun clarsimp_tac (cs, ss) = Simplifier.safe_asm_full_simp_tac ss THEN_MAYBE'
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

(*Designed to be idempotent, except if best_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac (cs, ss) m n =
    let val cs' = cs addss ss
        val maintac = 
          blast_depth_tac cs m		     (* fast but can't use wrappers *)
          ORELSE'
          (CHANGED o nodup_depth_tac cs' n); (* slower but more general *)
    in  EVERY [ALLGOALS (Simplifier.asm_full_simp_tac ss),
	       TRY (Classical.safe_tac cs),
	       REPEAT (FIRSTGOAL maintac),
               TRY (Classical.safe_tac (cs addSss ss)),
	       prune_params_tac] 
    end;

fun auto_tac (cs,ss) = mk_auto_tac (cs,ss) 4 2;

fun Auto_tac st = auto_tac (Classical.claset(), Simplifier.simpset()) st;

fun auto () = by Auto_tac;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac (cs,ss) = let val cs' = cs addss ss in SELECT_GOAL (EVERY [
	Classical.clarify_tac cs' 1,
	IF_UNSOLVED (Simplifier.asm_full_simp_tac ss 1),
	ALLGOALS (Classical.best_tac cs')]) end;
fun Force_tac i = force_tac (Classical.claset(), Simplifier.simpset()) i;
fun force i = by (Force_tac i);


(* methods *)

fun get_local_clasimpset ctxt =
  (Classical.get_local_claset ctxt, Simplifier.get_local_simpset ctxt);

val clasimp_modifiers = Classical.cla_modifiers @ Simplifier.simp_modifiers;

fun clasimp_meth tac prems ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (get_local_clasimpset ctxt));

fun clasimp_meth' tac prems ctxt = Method.METHOD (fn facts =>
  FIRSTGOAL (Method.insert_tac (prems @ facts) THEN' tac (get_local_clasimpset ctxt)));

val clasimp_method = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth;
val clasimp_method' = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth';


val setup =
 [Method.add_methods
   [("clarsimp_tac", clasimp_method' clarsimp_tac, "clarsimp (improper!)"),
    ("auto", clasimp_method (CHANGED o auto_tac), "auto"),
    ("force", clasimp_method' force_tac, "force")]];
    


end;
