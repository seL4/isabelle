(*  Title:      FOL/int-prover
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

A naive prover for intuitionistic logic

BEWARE OF NAME CLASHES WITH CLASSICAL TACTICS -- use Int.fast_tac ...

Completeness (for propositional logic) is proved in 

Roy Dyckhoff.
Contraction-Free Sequent Calculi for Intuitionistic Logic.
J. Symbolic Logic  57(3), 1992, pages 795-807.

The approach was developed independently by Roy Dyckhoff and L C Paulson.
*)

signature INT_PROVER = 
  sig
  val best_tac: int -> tactic
  val fast_tac: int -> tactic
  val inst_step_tac: int -> tactic
  val safe_step_tac: int -> tactic
  val safe_brls: (bool * thm) list
  val safe_tac: tactic
  val step_tac: int -> tactic
  val haz_brls: (bool * thm) list
  end;


structure Int : INT_PROVER   = 
struct

(*Negation is treated as a primitive symbol, with rules notI (introduction),
  not_to_imp (converts the assumption ~P to P-->False), and not_impE
  (handles double negations).  Could instead rewrite by not_def as the first
  step of an intuitionistic proof.
*)
val safe_brls = sort lessb 
    [ (true,FalseE), (false,TrueI), (false,refl),
      (false,impI), (false,notI), (false,allI),
      (true,conjE), (true,exE),
      (false,conjI), (true,conj_impE),
      (true,disj_impE), (true,ex_impE),
      (true,disjE), (false,iffI), (true,iffE), (true,not_to_imp) ];

val haz_brls =
    [ (false,disjI1), (false,disjI2), (false,exI), 
      (true,allE), (true,not_impE), (true,imp_impE), (true,iff_impE),
      (true,all_impE), (true,impE) ];

(*0 subgoals vs 1 or more: the p in safep is for positive*)
val (safe0_brls, safep_brls) =
    partition (apl(0,op=) o subgoals_of_brl) safe_brls;

(*Attack subgoals using safe inferences -- matching, not resolution*)
val safe_step_tac = FIRST' [eq_assume_tac,
                            eq_mp_tac,
                            bimatch_tac safe0_brls,
                            hyp_subst_tac,
                            bimatch_tac safep_brls] ;

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
val safe_tac = REPEAT_DETERM_FIRST safe_step_tac;

(*These steps could instantiate variables and are therefore unsafe.*)
val inst_step_tac =
  assume_tac APPEND' mp_tac APPEND' 
  biresolve_tac (safe0_brls @ safep_brls);

(*One safe or unsafe step. *)
fun step_tac i = FIRST [safe_tac, inst_step_tac i, biresolve_tac haz_brls i];

(*Dumb but fast*)
val fast_tac = SELECT_GOAL (DEPTH_SOLVE (step_tac 1));

(*Slower but smarter than fast_tac*)
val best_tac = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, size_of_thm) (step_tac 1));

end;

