(*  Title: 	Provers/clasimp.ML
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier
to be used after installing both of them
*)

type clasimpset = claset * simpset;

infix 4 addSIs2 addSEs2 addSDs2 addIs2 addEs2 addDs2
	addsimps2 delsimps2 addcongs2 delcongs2;
infix 4 addSss addss;

signature CLASIMP =
sig
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
  val mk_auto_tac:clasimpset -> int -> int -> tactic
  val auto_tac	: clasimpset -> tactic
  val Auto_tac	: tactic
  val auto	: unit -> unit
  val force_tac	: clasimpset  -> int -> tactic
  val Force_tac	: int -> tactic
  val force	: int -> unit
end;

structure Clasimp: CLASIMP =
struct

(* this interface for updating a clasimpset is rudimentary and just for 
   convenience for the most common cases. 
   In other cases a clasimpset may be dealt with componentwise. *)
local 
  fun pair_upd1 f ((a,b),x) = (f(a,x), b);
  fun pair_upd2 f ((a,b),x) = (a, f(b,x));
in
  fun op addSIs2   arg = pair_upd1 (op addSIs) arg;
  fun op addSEs2   arg = pair_upd1 (op addSEs) arg;
  fun op addSDs2   arg = pair_upd1 (op addSDs) arg;
  fun op addIs2    arg = pair_upd1 (op addIs ) arg;
  fun op addEs2    arg = pair_upd1 (op addEs ) arg;
  fun op addDs2    arg = pair_upd1 (op addDs ) arg;
  fun op addsimps2 arg = pair_upd2 (op addsimps) arg;
  fun op delsimps2 arg = pair_upd2 (op delsimps) arg;
  fun op addcongs2 arg = pair_upd2 (op addcongs) arg;
  fun op delcongs2 arg = pair_upd2 (op delcongs) arg;
end;

(*an unsatisfactory fix for the incomplete safe_asm_full_simp_tac!
  better: asm_really_full_simp_tac, a yet to be implemented version of
			asm_full_simp_tac that applies all equalities in the
			premises to all the premises *)
fun safe_asm_more_full_simp_tac ss = TRY o rot_eq_tac THEN' 
				     safe_asm_full_simp_tac ss;

(*Add a simpset to a classical set!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
fun cs addSss ss = cs addSaltern ("safe_asm_more_full_simp_tac",
			CHANGED o (safe_asm_more_full_simp_tac ss));
fun cs addss  ss = cs addbefore  (     "asm_full_simp_tac",
					asm_full_simp_tac ss);


local

	fun blast_depth_tac cs m i thm = Blast.depth_tac cs m i thm 
		handle Blast.TRANS s => (warning ("Blast_tac: " ^ s); Seq.empty);

	(* a variant of depth_tac that avoids interference of the simplifier 
	   with dup_step_tac when they are combined by auto_tac *)
	fun nodup_depth_tac cs m i state = 
	  SELECT_GOAL 
	   (appWrappers cs
	    (fn i => REPEAT_DETERM1 (COND (has_fewer_prems i) no_tac
	                             (safe_step_tac cs i)) THEN_ELSE
	     (DEPTH_SOLVE (nodup_depth_tac cs m i),
	      inst0_step_tac cs i  APPEND
	      COND (K(m=0)) no_tac
	        ((instp_step_tac cs i APPEND step_tac cs i)
	         THEN DEPTH_SOLVE (nodup_depth_tac cs (m-1) i)))) 1)
	  i state;

in

(*Designed to be idempotent, except if best_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac (cs, ss) m n =
    let val cs' = cs addss ss 
        val maintac = 
          blast_depth_tac cs m		(*fast but can't use addss*)
          ORELSE'
          nodup_depth_tac cs' n;	(*slower but more general*)
    in  EVERY [ALLGOALS (asm_full_simp_tac ss),
	       TRY (safe_tac cs'),
	       REPEAT (FIRSTGOAL maintac),
               TRY (safe_tac (cs addSss ss)),
	       prune_params_tac] 
    end;
end;

fun auto_tac (cs,ss) = mk_auto_tac (cs,ss) 4 2;

fun Auto_tac st = auto_tac (claset(), simpset()) st;

fun auto () = by Auto_tac;

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac (cs,ss) = let val cs' = cs addss ss in SELECT_GOAL (EVERY [
	clarify_tac cs' 1,
	IF_UNSOLVED (asm_full_simp_tac ss 1),
	ALLGOALS (fast_tac cs')]) end;
fun Force_tac i = force_tac (claset(), simpset()) i;
fun force i = by (Force_tac i);

end;
