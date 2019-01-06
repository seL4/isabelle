(*  Title:      FOLP/FOLP.thy
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>Classical First-Order Logic with Proofs\<close>

theory FOLP
imports IFOLP
begin

axiomatization cla :: "[p=>p]=>p"
  where classical: "(!!x. x:~P ==> f(x):P) ==> cla(f):P"


(*** Classical introduction rules for | and EX ***)

schematic_goal disjCI:
  assumes "!!x. x:~Q ==> f(x):P"
  shows "?p : P|Q"
  apply (rule classical)
  apply (assumption | rule assms disjI1 notI)+
  apply (assumption | rule disjI2 notE)+
  done

(*introduction rule involving only EX*)
schematic_goal ex_classical:
  assumes "!!u. u:~(EX x. P(x)) ==> f(u):P(a)"
  shows "?p : EX x. P(x)"
  apply (rule classical)
  apply (rule exI, rule assms, assumption)
  done

(*version of above, simplifying ~EX to ALL~ *)
schematic_goal exCI:
  assumes "!!u. u:ALL x. ~P(x) ==> f(u):P(a)"
  shows "?p : EX x. P(x)"
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN assms])
  apply (erule notE)
  apply (erule exI)
  done

schematic_goal excluded_middle: "?p : ~P | P"
  apply (rule disjCI)
  apply assumption
  done


(*** Special elimination rules *)

(*Classical implies (-->) elimination. *)
schematic_goal impCE:
  assumes major: "p:P-->Q"
    and r1: "!!x. x:~P ==> f(x):R"
    and r2: "!!y. y:Q ==> g(y):R"
  shows "?p : R"
  apply (rule excluded_middle [THEN disjE])
   apply (tactic \<open>DEPTH_SOLVE (assume_tac \<^context> 1 ORELSE
       resolve_tac \<^context> [@{thm r1}, @{thm r2}, @{thm major} RS @{thm mp}] 1)\<close>)
  done

(*Double negation law*)
schematic_goal notnotD: "p:~~P ==> ?p : P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done


(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in
    ~P ==> ~Q    and    P ==> Q  *)
schematic_goal iffCE:
  assumes major: "p:P<->Q"
    and r1: "!!x y.[| x:P; y:Q |] ==> f(x,y):R"
    and r2: "!!x y.[| x:~P; y:~Q |] ==> g(x,y):R"
  shows "?p : R"
  apply (insert major)
  apply (unfold iff_def)
  apply (rule conjE)
  apply (tactic \<open>DEPTH_SOLVE_1 (eresolve_tac \<^context> @{thms impCE} 1 ORELSE
      eresolve_tac \<^context> [@{thm notE}, @{thm impE}] 1 THEN assume_tac \<^context> 1 ORELSE
      assume_tac \<^context> 1 ORELSE
      resolve_tac \<^context> [@{thm r1}, @{thm r2}] 1)\<close>)+
  done


(*Should be used as swap since ~P becomes redundant*)
schematic_goal swap:
  assumes major: "p:~P"
    and r: "!!x. x:~Q ==> f(x):P"
  shows "?p : Q"
  apply (rule classical)
  apply (rule major [THEN notE])
  apply (rule r)
  apply assumption
  done

ML_file \<open>classical.ML\<close>      (* Patched because matching won't instantiate proof *)
ML_file \<open>simp.ML\<close>           (* Patched because matching won't instantiate proof *)

ML \<open>
structure Cla = Classical
(
  val sizef = size_of_thm
  val mp = @{thm mp}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  fun hyp_subst_tacs ctxt = [hyp_subst_tac ctxt]
);
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
\<close>

schematic_goal cla_rews:
  "?p1 : P | ~P"
  "?p2 : ~P | P"
  "?p3 : ~ ~ P <-> P"
  "?p4 : (~P --> P) <-> P"
  apply (tactic \<open>ALLGOALS (Cla.fast_tac \<^context> FOLP_cs)\<close>)
  done

ML_file \<open>simpdata.ML\<close>

end
