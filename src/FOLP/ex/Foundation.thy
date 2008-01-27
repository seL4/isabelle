(*  Title:      FOLP/ex/Foundation.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header "Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover"

theory Foundation
imports IFOLP
begin

lemma "?p : A&B  --> (C-->A&C)"
apply (rule impI)
apply (rule impI)
apply (rule conjI)
prefer 2 apply assumption
apply (rule conjunct1)
apply assumption
done

text {*A form of conj-elimination*}
lemma
  assumes "p : A & B"
    and "!!x y. x : A ==> y : B ==> f(x, y) : C"
  shows "?p : C"
apply (rule prems)
apply (rule conjunct1)
apply (rule prems)
apply (rule conjunct2)
apply (rule prems)
done

lemma
  assumes "!!A x. x : ~ ~A ==> cla(x) : A"
  shows "?p : B | ~B"
apply (rule prems)
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
  assumes "!!A x. x : ~ ~A ==> cla(x) : A"
  shows "?p : B | ~B"
apply (rule prems)
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
  assumes "p : A | ~A"
    and "q : ~ ~A"
  shows "?p : A"
apply (rule disjE)
apply (rule prems)
apply assumption
apply (rule FalseE)
apply (rule_tac P = "~A" in notE)
apply (rule prems)
apply assumption
done


subsection "Examples with quantifiers"

lemma
  assumes "p : ALL z. G(z)"
  shows "?p : ALL z. G(z)|H(z)"
apply (rule allI)
apply (rule disjI1)
apply (rule prems [THEN spec])
done

lemma "?p : ALL x. EX y. x=y"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma "?p : EX y. ALL x. x=y"
apply (rule exI)
apply (rule allI)
apply (rule refl)?
oops

text {* Parallel lifting example. *}
lemma "?p : EX u. ALL x. EX v. ALL y. EX w. P(u,x,v,y,w)"
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
oops

lemma
  assumes "p : (EX z. F(z)) & B"
  shows "?p : EX z. F(z) & B"
apply (rule conjE)
apply (rule prems)
apply (rule exE)
apply assumption
apply (rule exI)
apply (rule conjI)
apply assumption
apply assumption
done

text {* A bigger demonstration of quantifiers -- not in the paper. *}
lemma "?p : (EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
apply (rule impI)
apply (rule allI)
apply (rule exE, assumption)
apply (rule exI)
apply (rule allE, assumption)
apply assumption
done

end
