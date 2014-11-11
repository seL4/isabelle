(*  Title:      CTT/ex/Equality.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Equality reasoning by rewriting"

theory Equality
imports "../CTT"
begin

lemma split_eq: "p : Sum(A,B) \<Longrightarrow> split(p,pair) = p : Sum(A,B)"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply rew
done

lemma when_eq: "\<lbrakk>A type; B type; p : A+B\<rbrakk> \<Longrightarrow> when(p,inl,inr) = p : A + B"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply rew
done

(*in the "rec" formulation of addition, 0+n=n *)
lemma "p:N \<Longrightarrow> rec(p,0, \<lambda>y z. succ(y)) = p : N"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply rew
done

(*the harder version, n+0=n: recursive, uses induction hypothesis*)
lemma "p:N \<Longrightarrow> rec(p,0, \<lambda>y z. succ(z)) = p : N"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply hyp_rew
done

(*Associativity of addition*)
lemma "\<lbrakk>a:N; b:N; c:N\<rbrakk>
  \<Longrightarrow> rec(rec(a, b, \<lambda>x y. succ(y)), c, \<lambda>x y. succ(y)) =
    rec(a, rec(b, c, \<lambda>x y. succ(y)), \<lambda>x y. succ(y)) : N"
apply (NE a)
apply hyp_rew
done

(*Martin-Lof (1984) page 62: pairing is surjective*)
lemma "p : Sum(A,B) \<Longrightarrow> <split(p,\<lambda>x y. x), split(p,\<lambda>x y. y)> = p : Sum(A,B)"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic {* DEPTH_SOLVE_1 (rew_tac @{context} []) *}) (*!!!!!!!*)
done

lemma "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (lam u. split(u, \<lambda>v w.<w,v>)) ` <a,b> = <b,a> : SUM x:B. A"
apply rew
done

(*a contrived, complicated simplication, requires sum-elimination also*)
lemma "(lam f. lam x. f`(f`x)) ` (lam u. split(u, \<lambda>v w.<w,v>)) =
      lam x. x  :  PROD x:(SUM y:N. N). (SUM y:N. N)"
apply (rule reduction_rls)
apply (rule_tac [3] intrL_rls)
apply (rule_tac [4] EqE)
apply (erule_tac [4] SumE)
(*order of unifiers is essential here*)
apply rew
done

end
