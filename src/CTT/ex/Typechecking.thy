(*  Title:      CTT/ex/Typechecking.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Easy examples: type checking and type deduction"

theory Typechecking
imports "../CTT"
begin

subsection {* Single-step proofs: verifying that a type is well-formed *}

schematic_lemma "?A type"
apply (rule form_rls)
done

schematic_lemma "?A type"
apply (rule form_rls)
back
apply (rule form_rls)
apply (rule form_rls)
done

schematic_lemma "PROD z:?A . N + ?B(z) type"
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
apply (rule form_rls)
done


subsection {* Multi-step proofs: Type inference *}

lemma "PROD w:N. N + N type"
apply form
done

schematic_lemma "<0, succ(0)> : ?A"
apply intr
done

schematic_lemma "PROD w:N . Eq(?A,w,w) type"
apply typechk
done

schematic_lemma "PROD x:N . PROD y:N . Eq(?A,x,y) type"
apply typechk
done

text "typechecking an application of fst"
schematic_lemma "(lam u. split(u, \<lambda>v w. v)) ` <0, succ(0)> : ?A"
apply typechk
done

text "typechecking the predecessor function"
schematic_lemma "lam n. rec(n, 0, \<lambda>x y. x) : ?A"
apply typechk
done

text "typechecking the addition function"
schematic_lemma "lam n. lam m. rec(n, m, \<lambda>x y. succ(y)) : ?A"
apply typechk
done

(*Proofs involving arbitrary types.
  For concreteness, every type variable left over is forced to be N*)
method_setup N = {* Scan.succeed (fn _ => SIMPLE_METHOD (TRYALL (resolve_tac @{thms NF}))) *}

schematic_lemma "lam w. <w,w> : ?A"
apply typechk
apply N
done

schematic_lemma "lam x. lam y. x : ?A"
apply typechk
apply N
done

text "typechecking fst (as a function object)"
schematic_lemma "lam i. split(i, \<lambda>j k. j) : ?A"
apply typechk
apply N
done

end
