(*  Title:      FOLP/FOLP.thy
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Classical First-Order Logic with Proofs *}

theory FOLP
imports IFOLP
uses
  ("classical.ML") ("simp.ML") ("simpdata.ML")
begin

consts
  cla :: "[p=>p]=>p"
axioms
  classical: "(!!x. x:~P ==> f(x):P) ==> cla(f):P"


(*** Classical introduction rules for | and EX ***)

lemma disjCI:
  assumes "!!x. x:~Q ==> f(x):P"
  shows "?p : P|Q"
  apply (rule classical)
  apply (assumption | rule assms disjI1 notI)+
  apply (assumption | rule disjI2 notE)+
  done

(*introduction rule involving only EX*)
lemma ex_classical:
  assumes "!!u. u:~(EX x. P(x)) ==> f(u):P(a)"
  shows "?p : EX x. P(x)"
  apply (rule classical)
  apply (rule exI, rule assms, assumption)
  done

(*version of above, simplifying ~EX to ALL~ *)
lemma exCI:
  assumes "!!u. u:ALL x. ~P(x) ==> f(u):P(a)"
  shows "?p : EX x. P(x)"
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN assms])
  apply (erule notE)
  apply (erule exI)
  done

lemma excluded_middle: "?p : ~P | P"
  apply (rule disjCI)
  apply assumption
  done


(*** Special elimination rules *)

(*Classical implies (-->) elimination. *)
lemma impCE:
  assumes major: "p:P-->Q"
    and r1: "!!x. x:~P ==> f(x):R"
    and r2: "!!y. y:Q ==> g(y):R"
  shows "?p : R"
  apply (rule excluded_middle [THEN disjE])
   apply (tactic {* DEPTH_SOLVE (atac 1 ORELSE
       resolve_tac [@{thm r1}, @{thm r2}, @{thm major} RS @{thm mp}] 1) *})
  done

(*Double negation law*)
lemma notnotD: "p:~~P ==> ?p : P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done


(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in
    ~P ==> ~Q    and    P ==> Q  *)
lemma iffCE:
  assumes major: "p:P<->Q"
    and r1: "!!x y.[| x:P; y:Q |] ==> f(x,y):R"
    and r2: "!!x y.[| x:~P; y:~Q |] ==> g(x,y):R"
  shows "?p : R"
  apply (insert major)
  apply (unfold iff_def)
  apply (rule conjE)
  apply (tactic {* DEPTH_SOLVE_1 (etac @{thm impCE} 1 ORELSE
      eresolve_tac [@{thm notE}, @{thm impE}] 1 THEN atac 1 ORELSE atac 1 ORELSE
      resolve_tac [@{thm r1}, @{thm r2}] 1) *})+
  done


(*Should be used as swap since ~P becomes redundant*)
lemma swap:
  assumes major: "p:~P"
    and r: "!!x. x:~Q ==> f(x):P"
  shows "?p : Q"
  apply (rule classical)
  apply (rule major [THEN notE])
  apply (rule r)
  apply assumption
  done

use "classical.ML"      (* Patched 'cos matching won't instantiate proof *)
use "simp.ML"           (* Patched 'cos matching won't instantiate proof *)

ML {*
(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data =
struct
  val sizef = size_of_thm
  val mp = @{thm mp}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val hyp_subst_tacs = [hyp_subst_tac]
end;

structure Cla = ClassicalFun(Classical_Data);
open Cla;

(*Propositional rules
  -- iffCE might seem better, but in the examples in ex/cla
     run about 7% slower than with iffE*)
val prop_cs =
  empty_cs addSIs [@{thm refl}, @{thm TrueI}, @{thm conjI}, @{thm disjCI},
      @{thm impI}, @{thm notI}, @{thm iffI}]
    addSEs [@{thm conjE}, @{thm disjE}, @{thm impCE}, @{thm FalseE}, @{thm iffE}];

(*Quantifier rules*)
val FOLP_cs =
  prop_cs addSIs [@{thm allI}] addIs [@{thm exI}, @{thm ex1I}]
    addSEs [@{thm exE}, @{thm ex1E}] addEs [@{thm allE}];

val FOLP_dup_cs =
  prop_cs addSIs [@{thm allI}] addIs [@{thm exCI}, @{thm ex1I}]
    addSEs [@{thm exE}, @{thm ex1E}] addEs [@{thm all_dupE}];
*}

lemma cla_rews:
  "?p1 : P | ~P"
  "?p2 : ~P | P"
  "?p3 : ~ ~ P <-> P"
  "?p4 : (~P --> P) <-> P"
  apply (tactic {* ALLGOALS (Cla.fast_tac FOLP_cs) *})
  done

use "simpdata.ML"

end
