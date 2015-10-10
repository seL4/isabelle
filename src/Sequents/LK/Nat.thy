(*  Title:      Sequents/LK/Nat.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

section \<open>Theory of the natural numbers: Peano's axioms, primitive recursion\<close>

theory Nat
imports "../LK"
begin

typedecl nat
instance nat :: "term" ..

axiomatization
  Zero :: nat      ("0") and
  Suc :: "nat \<Rightarrow> nat" and
  rec :: "[nat, 'a, [nat,'a] \<Rightarrow> 'a] \<Rightarrow> 'a"
where
  induct:  "\<lbrakk>$H |- $E, P(0), $F;
             \<And>x. $H, P(x) |- $E, P(Suc(x)), $F\<rbrakk> \<Longrightarrow> $H |- $E, P(n), $F" and

  Suc_inject:  "|- Suc(m) = Suc(n) \<longrightarrow> m = n" and
  Suc_neq_0:   "|- Suc(m) \<noteq> 0" and
  rec_0:       "|- rec(0,a,f) = a" and
  rec_Suc:     "|- rec(Suc(m), a, f) = f(m, rec(m,a,f))"

definition add :: "[nat, nat] \<Rightarrow> nat"  (infixl "+" 60)
  where "m + n == rec(m, n, \<lambda>x y. Suc(y))"


declare Suc_neq_0 [simp]

lemma Suc_inject_rule: "$H, $G, m = n |- $E \<Longrightarrow> $H, Suc(m) = Suc(n), $G |- $E"
  by (rule L_of_imp [OF Suc_inject])

lemma Suc_n_not_n: "|- Suc(k) \<noteq> k"
  apply (rule_tac n = k in induct)
  apply simp
  apply (fast add!: Suc_inject_rule)
  done

lemma add_0: "|- 0 + n = n"
  apply (unfold add_def)
  apply (rule rec_0)
  done

lemma add_Suc: "|- Suc(m) + n = Suc(m + n)"
  apply (unfold add_def)
  apply (rule rec_Suc)
  done

declare add_0 [simp] add_Suc [simp]

lemma add_assoc: "|- (k + m) + n = k + (m + n)"
  apply (rule_tac n = "k" in induct)
  apply simp_all
  done

lemma add_0_right: "|- m + 0 = m"
  apply (rule_tac n = "m" in induct)
  apply simp_all
  done

lemma add_Suc_right: "|- m + Suc(n) = Suc(m + n)"
  apply (rule_tac n = "m" in induct)
  apply simp_all
  done

lemma "(\<And>n. |- f(Suc(n)) = Suc(f(n))) \<Longrightarrow> |- f(i + j) = i + f(j)"
  apply (rule_tac n = "i" in induct)
  apply simp_all
  done

end
