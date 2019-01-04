(*  Title:      CTT/ex/Synthesis.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Synthesis examples, using a crude form of narrowing"

theory Synthesis
imports "../CTT"
begin

text "discovery of predecessor function"
schematic_goal "?a : \<Sum>pred:?A . Eq(N, pred`0, 0) \<times> (\<Prod>n:N. Eq(N, pred ` succ(n), n))"
apply intr
apply eqintr
apply (rule_tac [3] reduction_rls)
apply (rule_tac [5] comp_rls)
apply rew
done

text "the function fst as an element of a function type"
schematic_goal [folded basic_defs]:
  "A type \<Longrightarrow> ?a: \<Sum>f:?B . \<Prod>i:A. \<Prod>j:A. Eq(A, f ` <i,j>, i)"
apply intr
apply eqintr
apply (rule_tac [2] reduction_rls)
apply (rule_tac [4] comp_rls)
apply typechk
txt "now put in A everywhere"
apply assumption+
done

text "An interesting use of the eliminator, when"
(*The early implementation of unification caused non-rigid path in occur check
  See following example.*)
schematic_goal "?a : \<Prod>i:N. Eq(?A, ?b(inl(i)), <0    ,   i>)
                   \<times> Eq(?A, ?b(inr(i)), <succ(0), i>)"
apply intr
apply eqintr
apply (rule comp_rls)
apply rew
done

(*Here we allow the type to depend on i.
 This prevents the cycle in the first unification (no longer needed).
 Requires flex-flex to preserve the dependence.
 Simpler still: make ?A into a constant type N \<times> N.*)
schematic_goal "?a : \<Prod>i:N. Eq(?A(i), ?b(inl(i)), <0   ,   i>)
                  \<times>  Eq(?A(i), ?b(inr(i)), <succ(0),i>)"
oops

text "A tricky combination of when and split"
(*Now handled easily, but caused great problems once*)
schematic_goal [folded basic_defs]:
  "?a : \<Prod>i:N. \<Prod>j:N. Eq(?A, ?b(inl(<i,j>)), i)
                           \<times>  Eq(?A, ?b(inr(<i,j>)), j)"
apply intr
apply eqintr
apply (rule PlusC_inl [THEN trans_elem])
apply (rule_tac [4] comp_rls)
apply (rule_tac [7] reduction_rls)
apply (rule_tac [10] comp_rls)
apply typechk
done

(*similar but allows the type to depend on i and j*)
schematic_goal "?a : \<Prod>i:N. \<Prod>j:N. Eq(?A(i,j), ?b(inl(<i,j>)), i)
                          \<times>   Eq(?A(i,j), ?b(inr(<i,j>)), j)"
oops

(*similar but specifying the type N simplifies the unification problems*)
schematic_goal "?a : \<Prod>i:N. \<Prod>j:N. Eq(N, ?b(inl(<i,j>)), i)
                          \<times>   Eq(N, ?b(inr(<i,j>)), j)"
oops


text "Deriving the addition operator"
schematic_goal [folded arith_defs]:
  "?c : \<Prod>n:N. Eq(N, ?f(0,n), n)
                  \<times>  (\<Prod>m:N. Eq(N, ?f(succ(m), n), succ(?f(m,n))))"
apply intr
apply eqintr
apply (rule comp_rls)
apply rew
done

text "The addition function -- using explicit lambdas"
schematic_goal [folded arith_defs]:
  "?c : \<Sum>plus : ?A .
         \<Prod>x:N. Eq(N, plus`0`x, x)
                \<times>  (\<Prod>y:N. Eq(N, plus`succ(y)`x, succ(plus`y`x)))"
apply intr
apply eqintr
apply (tactic "resolve_tac \<^context> [TSimp.split_eqn] 3")
apply (tactic "SELECT_GOAL (rew_tac \<^context> []) 4")
apply (tactic "resolve_tac \<^context> [TSimp.split_eqn] 3")
apply (tactic "SELECT_GOAL (rew_tac \<^context> []) 4")
apply (rule_tac [3] p = "y" in NC_succ)
  (**  by (resolve_tac @{context} comp_rls 3);  caused excessive branching  **)
apply rew
done

end

