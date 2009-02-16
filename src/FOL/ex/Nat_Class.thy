(*  Title:      FOL/ex/Nat_Class.thy
    Author:     Markus Wenzel, TU Muenchen
*)

theory Nat_Class
imports FOL
begin

text {*
  This is an abstract version of theory @{text "Nat"}. Instead of
  axiomatizing a single type @{text nat} we define the class of all
  these types (up to isomorphism).

  Note: The @{text rec} operator had to be made \emph{monomorphic},
  because class axioms may not contain more than one type variable.
*}

class nat =
  fixes Zero :: 'a  ("0")
    and Suc :: "'a => 'a"
    and rec :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"
  assumes induct: "P(0) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> P(Suc(x))) \<Longrightarrow> P(n)"
    and Suc_inject: "Suc(m) = Suc(n) \<Longrightarrow> m = n"
    and Suc_neq_Zero: "Suc(m) = 0 \<Longrightarrow> R"
    and rec_Zero: "rec(0, a, f) = a"
    and rec_Suc: "rec(Suc(m), a, f) = f(m, rec(m, a, f))"
begin

definition
  add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 60) where
  "m + n = rec(m, n, \<lambda>x y. Suc(y))"

lemma Suc_n_not_n: "Suc(k) ~= (k::'a)"
  apply (rule_tac n = k in induct)
   apply (rule notI)
   apply (erule Suc_neq_Zero)
  apply (rule notI)
  apply (erule notE)
  apply (erule Suc_inject)
  done

lemma "(k + m) + n = k + (m + n)"
  apply (rule induct)
  back
  back
  back
  back
  back
  oops

lemma add_Zero [simp]: "0 + n = n"
  apply (unfold add_def)
  apply (rule rec_Zero)
  done

lemma add_Suc [simp]: "Suc(m) + n = Suc(m + n)"
  apply (unfold add_def)
  apply (rule rec_Suc)
  done

lemma add_assoc: "(k + m) + n = k + (m + n)"
  apply (rule_tac n = k in induct)
   apply simp
  apply simp
  done

lemma add_Zero_right: "m + 0 = m"
  apply (rule_tac n = m in induct)
   apply simp
  apply simp
  done

lemma add_Suc_right: "m + Suc(n) = Suc(m + n)"
  apply (rule_tac n = m in induct)
   apply simp_all
  done

lemma
  assumes prem: "\<And>n. f(Suc(n)) = Suc(f(n))"
  shows "f(i + j) = i + f(j)"
  apply (rule_tac n = i in induct)
   apply simp
  apply (simp add: prem)
  done

end

end
