(*  Title:      FOLP/ex/Intro.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Derives some inference rules, illustrating the use of definitions.
*)

section {* Examples for the manual ``Introduction to Isabelle'' *}

theory Intro
imports FOLP
begin

subsubsection {* Some simple backward proofs *}

schematic_lemma mythm: "?p : P|P --> P"
apply (rule impI)
apply (rule disjE)
prefer 3 apply (assumption)
prefer 2 apply (assumption)
apply assumption
done

schematic_lemma "?p : (P & Q) | R --> (P | R)"
apply (rule impI)
apply (erule disjE)
apply (drule conjunct1)
apply (rule disjI1)
apply (rule_tac [2] disjI2)
apply assumption+
done

(*Correct version, delaying use of "spec" until last*)
schematic_lemma "?p : (ALL x y. P(x,y)) --> (ALL z w. P(w,z))"
apply (rule impI)
apply (rule allI)
apply (rule allI)
apply (drule spec)
apply (drule spec)
apply assumption
done


subsubsection {* Demonstration of @{text "fast"} *}

schematic_lemma "?p : (EX y. ALL x. J(y,x) <-> ~J(x,x))
        -->  ~ (ALL x. EX y. ALL z. J(z,y) <-> ~ J(z,x))"
apply (tactic {* fast_tac FOLP_cs 1 *})
done


schematic_lemma "?p : ALL x. P(x,f(x)) <->
        (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
apply (tactic {* fast_tac FOLP_cs 1 *})
done


subsubsection {* Derivation of conjunction elimination rule *}

schematic_lemma
  assumes major: "p : P&Q"
    and minor: "!!x y. [| x : P; y : Q |] ==> f(x, y) : R"
  shows "?p : R"
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done


subsection {* Derived rules involving definitions *}

text {* Derivation of negation introduction *}

schematic_lemma
  assumes "!!x. x : P ==> f(x) : False"
  shows "?p : ~ P"
apply (unfold not_def)
apply (rule impI)
apply (rule assms)
apply assumption
done

schematic_lemma
  assumes major: "p : ~P"
    and minor: "q : P"
  shows "?p : R"
apply (rule FalseE)
apply (rule mp)
apply (rule major [unfolded not_def])
apply (rule minor)
done

text {* Alternative proof of the result above *}
schematic_lemma
  assumes major: "p : ~P"
    and minor: "q : P"
  shows "?p : R"
apply (rule minor [THEN major [unfolded not_def, THEN mp, THEN FalseE]])
done

end
