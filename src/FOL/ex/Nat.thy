(*  Title:      FOL/ex/Nat.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Theory of the natural numbers: Peano's axioms, primitive recursion *}

theory Nat
imports FOL
begin

typedecl nat
arities nat :: "term"

consts
  0 :: nat    ("0")
  Suc :: "nat => nat"
  rec :: "[nat, 'a, [nat, 'a] => 'a] => 'a"
  add :: "[nat, nat] => nat"    (infixl "+" 60)

axioms
  induct:      "[| P(0);  !!x. P(x) ==> P(Suc(x)) |]  ==> P(n)"
  Suc_inject:  "Suc(m)=Suc(n) ==> m=n"
  Suc_neq_0:   "Suc(m)=0      ==> R"
  rec_0:       "rec(0,a,f) = a"
  rec_Suc:     "rec(Suc(m), a, f) = f(m, rec(m,a,f))"

defs
  add_def:     "m+n == rec(m, n, %x y. Suc(y))"


subsection {* Proofs about the natural numbers *}

lemma Suc_n_not_n: "Suc(k) ~= k"
apply (rule_tac n = k in induct)
apply (rule notI)
apply (erule Suc_neq_0)
apply (rule notI)
apply (erule notE)
apply (erule Suc_inject)
done

lemma "(k+m)+n = k+(m+n)"
apply (rule induct)
back
back
back
back
back
back
oops

lemma add_0 [simp]: "0+n = n"
apply (unfold add_def)
apply (rule rec_0)
done

lemma add_Suc [simp]: "Suc(m)+n = Suc(m+n)"
apply (unfold add_def)
apply (rule rec_Suc)
done

lemma add_assoc: "(k+m)+n = k+(m+n)"
apply (rule_tac n = k in induct)
apply simp
apply simp
done

lemma add_0_right: "m+0 = m"
apply (rule_tac n = m in induct)
apply simp
apply simp
done

lemma add_Suc_right: "m+Suc(n) = Suc(m+n)"
apply (rule_tac n = m in induct)
apply simp_all
done

lemma
  assumes prem: "!!n. f(Suc(n)) = Suc(f(n))"
  shows "f(i+j) = i+f(j)"
apply (rule_tac n = i in induct)
apply simp
apply (simp add: prem)
done

end
