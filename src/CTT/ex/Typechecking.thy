(*  Title:      CTT/ex/Typechecking.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Easy examples: type checking and type deduction"

theory Typechecking
imports "../CTT"
begin

subsection \<open>Single-step proofs: verifying that a type is well-formed\<close>

schematic_goal "?A type"
apply (rule form_rls)
done

schematic_goal "?A type"
apply (rule form_rls)
back
apply (rule form_rls)
apply (rule form_rls)
done

schematic_goal "PROD z:?A . N + ?B(z) type"
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
done


subsection \<open>Multi-step proofs: Type inference\<close>

lemma "PROD w:N. N + N type"
apply form
done

schematic_goal "<0, succ(0)> : ?A"
apply intr
done

schematic_goal "PROD w:N . Eq(?A,w,w) type"
apply typechk
done

schematic_goal "PROD x:N . PROD y:N . Eq(?A,x,y) type"
apply typechk
done

text "typechecking an application of fst"
schematic_goal "(lam u. split(u, \<lambda>v w. v)) ` <0, succ(0)> : ?A"
apply typechk
done

text "typechecking the predecessor function"
schematic_goal "lam n. rec(n, 0, \<lambda>x y. x) : ?A"
apply typechk
done

text "typechecking the addition function"
schematic_goal "lam n. lam m. rec(n, m, \<lambda>x y. succ(y)) : ?A"
apply typechk
done

(*Proofs involving arbitrary types.
  For concreteness, every type variable left over is forced to be N*)
method_setup N =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (TRYALL (resolve_tac ctxt @{thms NF})))\<close>

schematic_goal "lam w. <w,w> : ?A"
apply typechk
apply N
done

schematic_goal "lam x. lam y. x : ?A"
apply typechk
apply N
done

text "typechecking fst (as a function object)"
schematic_goal "lam i. split(i, \<lambda>j k. j) : ?A"
apply typechk
apply N
done

end
