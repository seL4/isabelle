(*  Title:      Sequents/LK/Nat.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Theory of the natural numbers: Peano's axioms, primitive recursion *}

theory Nat
imports "../LK"
begin

typedecl nat
arities nat :: "term"

axiomatization
  Zero :: nat      ("0") and
  Suc :: "nat=>nat" and
  rec :: "[nat, 'a, [nat,'a]=>'a] => 'a"
where
  induct:  "[| $H |- $E, P(0), $F;
              !!x. $H, P(x) |- $E, P(Suc(x)), $F |] ==> $H |- $E, P(n), $F" and

  Suc_inject:  "|- Suc(m)=Suc(n) --> m=n" and
  Suc_neq_0:   "|- Suc(m) ~= 0" and
  rec_0:       "|- rec(0,a,f) = a" and
  rec_Suc:     "|- rec(Suc(m), a, f) = f(m, rec(m,a,f))"

definition add :: "[nat, nat] => nat"  (infixl "+" 60)
  where "m + n == rec(m, n, %x y. Suc(y))"


declare Suc_neq_0 [simp]

lemma Suc_inject_rule: "$H, $G, m = n |- $E \<Longrightarrow> $H, Suc(m) = Suc(n), $G |- $E"
  by (rule L_of_imp [OF Suc_inject])

lemma Suc_n_not_n: "|- Suc(k) ~= k"
  apply (rule_tac n = k in induct)
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms Suc_neq_0}) 1 *})
  apply (fast add!: Suc_inject_rule)
  done

lemma add_0: "|- 0+n = n"
  apply (unfold add_def)
  apply (rule rec_0)
  done

lemma add_Suc: "|- Suc(m)+n = Suc(m+n)"
  apply (unfold add_def)
  apply (rule rec_Suc)
  done

declare add_0 [simp] add_Suc [simp]

lemma add_assoc: "|- (k+m)+n = k+(m+n)"
  apply (rule_tac n = "k" in induct)
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_0}) 1 *})
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_Suc}) 1 *})
  done

lemma add_0_right: "|- m+0 = m"
  apply (rule_tac n = "m" in induct)
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_0}) 1 *})
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_Suc}) 1 *})
  done

lemma add_Suc_right: "|- m+Suc(n) = Suc(m+n)"
  apply (rule_tac n = "m" in induct)
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_0}) 1 *})
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_Suc}) 1 *})
  done

lemma "(!!n. |- f(Suc(n)) = Suc(f(n))) ==> |- f(i+j) = i+f(j)"
  apply (rule_tac n = "i" in induct)
  apply (tactic {* simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_0}) 1 *})
  apply (tactic {* asm_simp_tac (put_simpset LK_ss @{context} addsimps @{thms add_Suc}) 1 *})
  done

end
