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

text \<open>in the "rec" formulation of addition, $0+n=n$\<close>
lemma "p:N \<Longrightarrow> rec(p,0, \<lambda>y z. succ(y)) = p : N"
  apply (rule EqE)
  apply (rule elim_rls, assumption)
   apply rew
  done

text \<open>the harder version, $n+0=n$: recursive, uses induction hypothesis\<close>
lemma "p:N \<Longrightarrow> rec(p,0, \<lambda>y z. succ(z)) = p : N"
  apply (rule EqE)
  apply (rule elim_rls, assumption)
   apply hyp_rew
  done

text \<open>Associativity of addition\<close>
lemma "\<lbrakk>a:N; b:N; c:N\<rbrakk>
  \<Longrightarrow> rec(rec(a, b, \<lambda>x y. succ(y)), c, \<lambda>x y. succ(y)) =
    rec(a, rec(b, c, \<lambda>x y. succ(y)), \<lambda>x y. succ(y)) : N"
  apply (NE a)
    apply hyp_rew
  done

text \<open>Martin-Löf (1984) page 62: pairing is surjective\<close>
lemma "p : Sum(A,B) \<Longrightarrow> <split(p,\<lambda>x y. x), split(p,\<lambda>x y. y)> = p : Sum(A,B)"
  apply (rule EqE)
  apply (rule elim_rls, assumption)
  apply (tactic \<open>DEPTH_SOLVE_1 (rew_tac \<^context> [])\<close>) (*!!!!!!!*)
  done

lemma "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>u. split(u, \<lambda>v w.<w,v>)) ` <a,b> = <b,a> : \<Sum>x:B. A"
  by rew

text \<open>a contrived, complicated simplication, requires sum-elimination also\<close>
lemma "(\<^bold>\<lambda>f. \<^bold>\<lambda>x. f`(f`x)) ` (\<^bold>\<lambda>u. split(u, \<lambda>v w.<w,v>)) =
      \<^bold>\<lambda>x. x  :  \<Prod>x:(\<Sum>y:N. N). (\<Sum>y:N. N)"
  apply (rule reduction_rls)
    apply (rule_tac [3] intrL_rls)
     apply (rule_tac [4] EqE)
     apply (erule_tac [4] SumE)
    (*order of unifiers is essential here*)
     apply rew
  done

end
