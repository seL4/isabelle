(*  Title:      CTT/ex/Synthesis.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header "Synthesis examples, using a crude form of narrowing"

theory Synthesis
imports Arith
begin

text "discovery of predecessor function"
lemma "?a : SUM pred:?A . Eq(N, pred`0, 0)
                  *  (PROD n:N. Eq(N, pred ` succ(n), n))"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule_tac [3] reduction_rls)
apply (rule_tac [5] comp_rls)
apply (tactic "rew_tac []")
done

text "the function fst as an element of a function type"
lemma [folded basic_defs]:
  "A type ==> ?a: SUM f:?B . PROD i:A. PROD j:A. Eq(A, f ` <i,j>, i)"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule_tac [2] reduction_rls)
apply (rule_tac [4] comp_rls)
apply (tactic "typechk_tac []")
txt "now put in A everywhere"
apply assumption+
done

text "An interesting use of the eliminator, when"
(*The early implementation of unification caused non-rigid path in occur check
  See following example.*)
lemma "?a : PROD i:N. Eq(?A, ?b(inl(i)), <0    ,   i>)
                   * Eq(?A, ?b(inr(i)), <succ(0), i>)"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule comp_rls)
apply (tactic "rew_tac []")
done

(*Here we allow the type to depend on i.
 This prevents the cycle in the first unification (no longer needed).
 Requires flex-flex to preserve the dependence.
 Simpler still: make ?A into a constant type N*N.*)
lemma "?a : PROD i:N. Eq(?A(i), ?b(inl(i)), <0   ,   i>)
                  *  Eq(?A(i), ?b(inr(i)), <succ(0),i>)"
oops

text "A tricky combination of when and split"
(*Now handled easily, but caused great problems once*)
lemma [folded basic_defs]:
  "?a : PROD i:N. PROD j:N. Eq(?A, ?b(inl(<i,j>)), i)
                           *  Eq(?A, ?b(inr(<i,j>)), j)"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule PlusC_inl [THEN trans_elem])
apply (rule_tac [4] comp_rls)
apply (rule_tac [7] reduction_rls)
apply (rule_tac [10] comp_rls)
apply (tactic "typechk_tac []")
done

(*similar but allows the type to depend on i and j*)
lemma "?a : PROD i:N. PROD j:N. Eq(?A(i,j), ?b(inl(<i,j>)), i)
                          *   Eq(?A(i,j), ?b(inr(<i,j>)), j)"
oops

(*similar but specifying the type N simplifies the unification problems*)
lemma "?a : PROD i:N. PROD j:N. Eq(N, ?b(inl(<i,j>)), i)
                          *   Eq(N, ?b(inr(<i,j>)), j)"
oops


text "Deriving the addition operator"
lemma [folded arith_defs]:
  "?c : PROD n:N. Eq(N, ?f(0,n), n)
                  *  (PROD m:N. Eq(N, ?f(succ(m), n), succ(?f(m,n))))"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule comp_rls)
apply (tactic "rew_tac []")
done

text "The addition function -- using explicit lambdas"
lemma [folded arith_defs]:
  "?c : SUM plus : ?A .
         PROD x:N. Eq(N, plus`0`x, x)
                *  (PROD y:N. Eq(N, plus`succ(y)`x, succ(plus`y`x)))"
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (tactic "resolve_tac [TSimp.split_eqn] 3")
apply (tactic "SELECT_GOAL (rew_tac []) 4")
apply (tactic "resolve_tac [TSimp.split_eqn] 3")
apply (tactic "SELECT_GOAL (rew_tac []) 4")
apply (rule_tac [3] p = "y" in NC_succ)
  (**  by (resolve_tac comp_rls 3);  caused excessive branching  **)
apply (tactic "rew_tac []")
done

end

