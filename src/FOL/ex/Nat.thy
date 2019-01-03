(*  Title:      FOL/ex/Nat.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>Theory of the natural numbers: Peano's axioms, primitive recursion\<close>

theory Nat
imports FOL
begin

typedecl nat
instance nat :: \<open>term\<close> ..

axiomatization
  Zero :: \<open>nat\<close>  (\<open>0\<close>) and
  Suc :: \<open>nat => nat\<close> and
  rec :: \<open>[nat, 'a, [nat, 'a] => 'a] => 'a\<close>
where
  induct: \<open>[| P(0);  !!x. P(x) ==> P(Suc(x)) |]  ==> P(n)\<close> and
  Suc_inject: \<open>Suc(m)=Suc(n) ==> m=n\<close> and
  Suc_neq_0: \<open>Suc(m)=0 ==> R\<close> and
  rec_0: \<open>rec(0,a,f) = a\<close> and
  rec_Suc: \<open>rec(Suc(m), a, f) = f(m, rec(m,a,f))\<close>

definition add :: \<open>[nat, nat] => nat\<close>  (infixl \<open>+\<close> 60)
  where \<open>m + n == rec(m, n, %x y. Suc(y))\<close>


subsection \<open>Proofs about the natural numbers\<close>

lemma Suc_n_not_n: \<open>Suc(k) \<noteq> k\<close>
apply (rule_tac n = \<open>k\<close> in induct)
apply (rule notI)
apply (erule Suc_neq_0)
apply (rule notI)
apply (erule notE)
apply (erule Suc_inject)
done

lemma \<open>(k+m)+n = k+(m+n)\<close>
apply (rule induct)
back
back
back
back
back
back
oops

lemma add_0 [simp]: \<open>0+n = n\<close>
apply (unfold add_def)
apply (rule rec_0)
done

lemma add_Suc [simp]: \<open>Suc(m)+n = Suc(m+n)\<close>
apply (unfold add_def)
apply (rule rec_Suc)
done

lemma add_assoc: \<open>(k+m)+n = k+(m+n)\<close>
apply (rule_tac n = \<open>k\<close> in induct)
apply simp
apply simp
done

lemma add_0_right: \<open>m+0 = m\<close>
apply (rule_tac n = \<open>m\<close> in induct)
apply simp
apply simp
done

lemma add_Suc_right: \<open>m+Suc(n) = Suc(m+n)\<close>
apply (rule_tac n = \<open>m\<close> in induct)
apply simp_all
done

lemma
  assumes prem: \<open>!!n. f(Suc(n)) = Suc(f(n))\<close>
  shows \<open>f(i+j) = i+f(j)\<close>
apply (rule_tac n = \<open>i\<close> in induct)
apply simp
apply (simp add: prem)
done

end
