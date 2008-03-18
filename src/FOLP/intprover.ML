(*  Title:      FOLP/intprover.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

A naive prover for intuitionistic logic

BEWARE OF NAME CLASHES WITH CLASSICAL TACTICS -- use IntPr.fast_tac ...

Completeness (for propositional logic) is proved in 

Roy Dyckhoff.
Contraction-Free Sequent Calculi for IntPruitionistic Logic.
J. Symbolic Logic (in press)
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


structure IntPr : INT_PROVER   = 
struct

(*Negation is treated as a primitive symbol, with rules notI (introduction),
  not_to_imp (converts the assumption ~P to P-->False), and not_impE
  (handles double negations).  Could instead rewrite by not_def as the first
  step of an intuitionistic proof.
*)
val safe_brls = sort (make_ord lessb)
    [ (true, @{thm FalseE}), (false, @{thm TrueI}), (false, @{thm refl}),
      (false, @{thm impI}), (false, @{thm notI}), (false, @{thm allI}),
      (true, @{thm conjE}), (true, @{thm exE}),
      (false, @{thm conjI}), (true, @{thm conj_impE}),
      (true, @{thm disj_impE}), (true, @{thm disjE}), 
      (false, @{thm iffI}), (true, @{thm iffE}), (true, @{thm not_to_imp}) ];

val haz_brls =
    [ (false, @{thm disjI1}), (false, @{thm disjI2}), (false, @{thm exI}), 
      (true, @{thm allE}), (true, @{thm not_impE}), (true, @{thm imp_impE}), (true, @{thm iff_impE}),
      (true, @{thm all_impE}), (true, @{thm ex_impE}), (true, @{thm impE}) ];

(*0 subgoals vs 1 or more: the p in safep is for positive*)
val (safe0_brls, safep_brls) =
    List.partition (curry (op =) 0 o subgoals_of_brl) safe_brls;

(*Attack subgoals using safe inferences*)
val safe_step_tac = FIRST' [uniq_assume_tac,
                            int_uniq_mp_tac,
                            biresolve_tac safe0_brls,
                            hyp_subst_tac,
                            biresolve_tac safep_brls] ;

(*Repeatedly attack subgoals using safe inferences*)
val safe_tac = DETERM (REPEAT_FIRST safe_step_tac);

(*These steps could instantiate variables and are therefore unsafe.*)
val inst_step_tac = assume_tac APPEND' mp_tac;

(*One safe or unsafe step. *)
fun step_tac i = FIRST [safe_tac, inst_step_tac i, biresolve_tac haz_brls i];

(*Dumb but fast*)
val fast_tac = SELECT_GOAL (DEPTH_SOLVE (step_tac 1));

(*Slower but smarter than fast_tac*)
val best_tac = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, size_of_thm) (step_tac 1));

end;
