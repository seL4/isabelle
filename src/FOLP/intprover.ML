(*  Title:      FOLP/intprover.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

A naive prover for intuitionistic logic

BEWARE OF NAME CLASHES WITH CLASSICAL TACTICS -- use IntPr.fast_tac ...

Completeness (for propositional logic) is proved in 

Roy Dyckhoff.
Contraction-Free Sequent Calculi for Intuitionistic Logic.
J. Symbolic Logic (in press)
*)

signature INT_PROVER = 
  sig
  val best_tac: Proof.context -> int -> tactic
  val fast_tac: Proof.context -> int -> tactic
  val inst_step_tac: Proof.context -> int -> tactic
  val safe_step_tac: Proof.context -> int -> tactic
  val safe_brls: (bool * thm) list
  val safe_tac: Proof.context -> tactic
  val step_tac: Proof.context -> int -> tactic
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
fun safe_step_tac ctxt = FIRST' [uniq_assume_tac ctxt,
                            int_uniq_mp_tac ctxt,
                            biresolve_tac ctxt safe0_brls,
                            hyp_subst_tac ctxt,
                            biresolve_tac ctxt safep_brls] ;

(*Repeatedly attack subgoals using safe inferences*)
fun safe_tac ctxt = DETERM (REPEAT_FIRST (safe_step_tac ctxt));

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac ctxt = assume_tac ctxt APPEND' mp_tac ctxt;

(*One safe or unsafe step. *)
fun step_tac ctxt i = FIRST [safe_tac ctxt, inst_step_tac ctxt i, biresolve_tac ctxt haz_brls i];

(*Dumb but fast*)
fun fast_tac ctxt = SELECT_GOAL (DEPTH_SOLVE (step_tac ctxt 1));

(*Slower but smarter than fast_tac*)
fun best_tac ctxt =
  SELECT_GOAL (BEST_FIRST (Thm.no_prems, size_of_thm) (step_tac ctxt 1));

end;
