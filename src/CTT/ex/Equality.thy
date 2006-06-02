(*  Title:      CTT/ex/Equality.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header "Equality reasoning by rewriting"

theory Equality
imports CTT
begin

lemma split_eq: "p : Sum(A,B) ==> split(p,pair) = p : Sum(A,B)"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic "rew_tac []")
done

lemma when_eq: "[| A type;  B type;  p : A+B |] ==> when(p,inl,inr) = p : A + B"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic "rew_tac []")
done

(*in the "rec" formulation of addition, 0+n=n *)
lemma "p:N ==> rec(p,0, %y z. succ(y)) = p : N"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic "rew_tac []")
done

(*the harder version, n+0=n: recursive, uses induction hypothesis*)
lemma "p:N ==> rec(p,0, %y z. succ(z)) = p : N"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic "hyp_rew_tac []")
done

(*Associativity of addition*)
lemma "[| a:N;  b:N;  c:N |]
      ==> rec(rec(a, b, %x y. succ(y)), c, %x y. succ(y)) =
          rec(a, rec(b, c, %x y. succ(y)), %x y. succ(y)) : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic "hyp_rew_tac []")
done

(*Martin-Lof (1984) page 62: pairing is surjective*)
lemma "p : Sum(A,B) ==> <split(p,%x y. x), split(p,%x y. y)> = p : Sum(A,B)"
apply (rule EqE)
apply (rule elim_rls, assumption)
apply (tactic {* DEPTH_SOLVE_1 (rew_tac []) *}) (*!!!!!!!*)
done

lemma "[| a : A;  b : B |] ==>
     (lam u. split(u, %v w.<w,v>)) ` <a,b> = <b,a> : SUM x:B. A"
apply (tactic "rew_tac []")
done

(*a contrived, complicated simplication, requires sum-elimination also*)
lemma "(lam f. lam x. f`(f`x)) ` (lam u. split(u, %v w.<w,v>)) =
      lam x. x  :  PROD x:(SUM y:N. N). (SUM y:N. N)"
apply (rule reduction_rls)
apply (rule_tac [3] intrL_rls)
apply (rule_tac [4] EqE)
apply (rule_tac [4] SumE, tactic "assume_tac 4")
(*order of unifiers is essential here*)
apply (tactic "rew_tac []")
done

end
