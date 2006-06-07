(*  Title:      FOL/ex/NatClass.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory NatClass
imports FOL
begin

text {*
  This is an abstract version of theory @{text "Nat"}. Instead of
  axiomatizing a single type @{text nat} we define the class of all
  these types (up to isomorphism).

  Note: The @{text rec} operator had to be made \emph{monomorphic},
  because class axioms may not contain more than one type variable.
*}

consts
  0 :: 'a    ("0")
  Suc :: "'a => 'a"
  rec :: "['a, 'a, ['a, 'a] => 'a] => 'a"

axclass
  nat < "term"
  induct:        "[| P(0); !!x. P(x) ==> P(Suc(x)) |] ==> P(n)"
  Suc_inject:    "Suc(m) = Suc(n) ==> m = n"
  Suc_neq_0:     "Suc(m) = 0 ==> R"
  rec_0:         "rec(0, a, f) = a"
  rec_Suc:       "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

definition
  add :: "['a::nat, 'a] => 'a"    (infixl "+" 60)
  "m + n = rec(m, n, %x y. Suc(y))"

lemma Suc_n_not_n: "Suc(k) ~= (k::'a::nat)"
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
