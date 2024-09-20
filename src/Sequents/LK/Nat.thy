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
  Zero :: nat      (\<open>0\<close>) and
  Suc :: "nat \<Rightarrow> nat" and
  rec :: "[nat, 'a, [nat,'a] \<Rightarrow> 'a] \<Rightarrow> 'a"
where
  induct:  "\<lbrakk>$H \<turnstile> $E, P(0), $F;
             \<And>x. $H, P(x) \<turnstile> $E, P(Suc(x)), $F\<rbrakk> \<Longrightarrow> $H \<turnstile> $E, P(n), $F" and

  Suc_inject:  "\<turnstile> Suc(m) = Suc(n) \<longrightarrow> m = n" and
  Suc_neq_0:   "\<turnstile> Suc(m) \<noteq> 0" and
  rec_0:       "\<turnstile> rec(0,a,f) = a" and
  rec_Suc:     "\<turnstile> rec(Suc(m), a, f) = f(m, rec(m,a,f))"

definition add :: "[nat, nat] \<Rightarrow> nat"  (infixl \<open>+\<close> 60)
  where "m + n == rec(m, n, \<lambda>x y. Suc(y))"


declare Suc_neq_0 [simp]

lemma Suc_inject_rule: "$H, $G, m = n \<turnstile> $E \<Longrightarrow> $H, Suc(m) = Suc(n), $G \<turnstile> $E"
  by (rule L_of_imp [OF Suc_inject])

lemma Suc_n_not_n: "\<turnstile> Suc(k) \<noteq> k"
  apply (rule_tac n = k in induct)
  apply simp
  apply (fast add!: Suc_inject_rule)
  done

lemma add_0: "\<turnstile> 0 + n = n"
  apply (unfold add_def)
  apply (rule rec_0)
  done

lemma add_Suc: "\<turnstile> Suc(m) + n = Suc(m + n)"
  apply (unfold add_def)
  apply (rule rec_Suc)
  done

declare add_0 [simp] add_Suc [simp]

lemma add_assoc: "\<turnstile> (k + m) + n = k + (m + n)"
  apply (rule_tac n = "k" in induct)
  apply simp_all
  done

lemma add_0_right: "\<turnstile> m + 0 = m"
  apply (rule_tac n = "m" in induct)
  apply simp_all
  done

lemma add_Suc_right: "\<turnstile> m + Suc(n) = Suc(m + n)"
  apply (rule_tac n = "m" in induct)
  apply simp_all
  done

lemma "(\<And>n. \<turnstile> f(Suc(n)) = Suc(f(n))) \<Longrightarrow> \<turnstile> f(i + j) = i + f(j)"
  apply (rule_tac n = "i" in induct)
  apply simp_all
  done

end
