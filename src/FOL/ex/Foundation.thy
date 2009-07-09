(*  Title:      FOL/ex/Foundation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header "Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover"

theory Foundation
imports IFOL
begin

lemma "A&B  --> (C-->A&C)"
apply (rule impI)
apply (rule impI)
apply (rule conjI)
prefer 2 apply assumption
apply (rule conjunct1)
apply assumption
done

text {*A form of conj-elimination*}
lemma
  assumes "A & B"
    and "A ==> B ==> C"
  shows C
apply (rule assms)
apply (rule conjunct1)
apply (rule assms)
apply (rule conjunct2)
apply (rule assms)
done

lemma
  assumes "!!A. ~ ~A ==> A"
  shows "B | ~B"
apply (rule assms)
apply (rule notI)
apply (rule_tac P = "~B" in notE)
apply (rule_tac [2] notI)
apply (rule_tac [2] P = "B | ~B" in notE)
prefer 2 apply assumption
apply (rule_tac [2] disjI1)
prefer 2 apply assumption
apply (rule notI)
apply (rule_tac P = "B | ~B" in notE)
apply assumption
apply (rule disjI2)
apply assumption
done

lemma
  assumes "!!A. ~ ~A ==> A"
  shows "B | ~B"
apply (rule assms)
apply (rule notI)
apply (rule notE)
apply (rule_tac [2] notI)
apply (erule_tac [2] notE)
apply (erule_tac [2] disjI1)
apply (rule notI)
apply (erule notE)
apply (erule disjI2)
done


lemma
  assumes "A | ~A"
    and "~ ~A"
  shows A
apply (rule disjE)
apply (rule assms)
apply assumption
apply (rule FalseE)
apply (rule_tac P = "~A" in notE)
apply (rule assms)
apply assumption
done


subsection "Examples with quantifiers"

lemma
  assumes "ALL z. G(z)"
  shows "ALL z. G(z)|H(z)"
apply (rule allI)
apply (rule disjI1)
apply (rule assms [THEN spec])
done

lemma "ALL x. EX y. x=y"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma "EX y. ALL x. x=y"
apply (rule exI)
apply (rule allI)
apply (rule refl)?
oops

text {* Parallel lifting example. *}
lemma "EX u. ALL x. EX v. ALL y. EX w. P(u,x,v,y,w)"
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
oops

lemma
  assumes "(EX z. F(z)) & B"
  shows "EX z. F(z) & B"
apply (rule conjE)
apply (rule assms)
apply (rule exE)
apply assumption
apply (rule exI)
apply (rule conjI)
apply assumption
apply assumption
done

text {* A bigger demonstration of quantifiers -- not in the paper. *}
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
apply (rule impI)
apply (rule allI)
apply (rule exE, assumption)
apply (rule exI)
apply (rule allE, assumption)
apply assumption
done

end
