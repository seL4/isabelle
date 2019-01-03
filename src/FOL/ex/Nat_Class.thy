(*  Title:      FOL/ex/Nat_Class.thy
    Author:     Markus Wenzel, TU Muenchen
*)

theory Nat_Class
imports FOL
begin

text \<open>
  This is an abstract version of theory \<open>Nat\<close>. Instead of axiomatizing a
  single type \<open>nat\<close> we define the class of all these types (up to
  isomorphism).

  Note: The \<open>rec\<close> operator had to be made \<^emph>\<open>monomorphic\<close>, because class axioms
  may not contain more than one type variable.
\<close>

class nat =
  fixes Zero :: \<open>'a\<close>  (\<open>0\<close>)
    and Suc :: \<open>'a \<Rightarrow> 'a\<close>
    and rec :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a\<close>
  assumes induct: \<open>P(0) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> P(Suc(x))) \<Longrightarrow> P(n)\<close>
    and Suc_inject: \<open>Suc(m) = Suc(n) \<Longrightarrow> m = n\<close>
    and Suc_neq_Zero: \<open>Suc(m) = 0 \<Longrightarrow> R\<close>
    and rec_Zero: \<open>rec(0, a, f) = a\<close>
    and rec_Suc: \<open>rec(Suc(m), a, f) = f(m, rec(m, a, f))\<close>
begin

definition add :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>+\<close> 60)
  where \<open>m + n = rec(m, n, \<lambda>x y. Suc(y))\<close>

lemma Suc_n_not_n: \<open>Suc(k) \<noteq> (k::'a)\<close>
  apply (rule_tac n = \<open>k\<close> in induct)
   apply (rule notI)
   apply (erule Suc_neq_Zero)
  apply (rule notI)
  apply (erule notE)
  apply (erule Suc_inject)
  done

lemma \<open>(k + m) + n = k + (m + n)\<close>
  apply (rule induct)
  back
  back
  back
  back
  back
  oops

lemma add_Zero [simp]: \<open>0 + n = n\<close>
  apply (unfold add_def)
  apply (rule rec_Zero)
  done

lemma add_Suc [simp]: \<open>Suc(m) + n = Suc(m + n)\<close>
  apply (unfold add_def)
  apply (rule rec_Suc)
  done

lemma add_assoc: \<open>(k + m) + n = k + (m + n)\<close>
  apply (rule_tac n = \<open>k\<close> in induct)
   apply simp
  apply simp
  done

lemma add_Zero_right: \<open>m + 0 = m\<close>
  apply (rule_tac n = \<open>m\<close> in induct)
   apply simp
  apply simp
  done

lemma add_Suc_right: \<open>m + Suc(n) = Suc(m + n)\<close>
  apply (rule_tac n = \<open>m\<close> in induct)
   apply simp_all
  done

lemma
  assumes prem: \<open>\<And>n. f(Suc(n)) = Suc(f(n))\<close>
  shows \<open>f(i + j) = i + f(j)\<close>
  apply (rule_tac n = \<open>i\<close> in induct)
   apply simp
  apply (simp add: prem)
  done

end

end
