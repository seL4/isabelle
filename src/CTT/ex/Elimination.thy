(*  Title:      CTT/ex/Elimination.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Some examples taken from P. Martin-L\"of, Intuitionistic type theory
        (Bibliopolis, 1984).
*)

header "Examples with elimination rules"

theory Elimination
imports CTT
begin

text "This finds the functions fst and snd!"

lemma [folded basic_defs]: "A type ==> ?a : (A*A) --> A"
apply (tactic {* pc_tac [] 1 *})
done

lemma [folded basic_defs]: "A type ==> ?a : (A*A) --> A"
apply (tactic {* pc_tac [] 1 *})
back
done

text "Double negation of the Excluded Middle"
lemma "A type ==> ?a : ((A + (A-->F)) --> F) --> F"
apply (tactic "intr_tac []")
apply (rule ProdE)
apply assumption
apply (tactic "pc_tac [] 1")
done

lemma "[| A type;  B type |] ==> ?a : (A*B) --> (B*A)"
apply (tactic "pc_tac [] 1")
done
(*The sequent version (ITT) could produce an interesting alternative
  by backtracking.  No longer.*)

text "Binary sums and products"
lemma "[| A type; B type; C type |] ==> ?a : (A+B --> C) --> (A-->C) * (B-->C)"
apply (tactic "pc_tac [] 1")
done

(*A distributive law*)
lemma "[| A type;  B type;  C type |] ==> ?a : A * (B+C)  -->  (A*B + A*C)"
apply (tactic "pc_tac [] 1")
done

(*more general version, same proof*)
lemma
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!x. x:A ==> C(x) type"
  shows "?a : (SUM x:A. B(x) + C(x)) --> (SUM x:A. B(x)) + (SUM x:A. C(x))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

text "Construction of the currying functional"
lemma "[| A type;  B type;  C type |] ==> ?a : (A*B --> C) --> (A--> (B-->C))"
apply (tactic "pc_tac [] 1")
done

(*more general goal with same proof*)
lemma
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!z. z: (SUM x:A. B(x)) ==> C(z) type"
  shows "?a : PROD f: (PROD z : (SUM x:A . B(x)) . C(z)).
                      (PROD x:A . PROD y:B(x) . C(<x,y>))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

text "Martin-Lof (1984), page 48: axiom of sum-elimination (uncurry)"
lemma "[| A type;  B type;  C type |] ==> ?a : (A --> (B-->C)) --> (A*B --> C)"
apply (tactic "pc_tac [] 1")
done

(*more general goal with same proof*)
lemma
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!z. z: (SUM x:A . B(x)) ==> C(z) type"
  shows "?a : (PROD x:A . PROD y:B(x) . C(<x,y>))
        --> (PROD z : (SUM x:A . B(x)) . C(z))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

text "Function application"
lemma "[| A type;  B type |] ==> ?a : ((A --> B) * A) --> B"
apply (tactic "pc_tac [] 1")
done

text "Basic test of quantifier reasoning"
lemma
  assumes "A type"
    and "B type"
    and "!!x y.[| x:A;  y:B |] ==> C(x,y) type"
  shows
    "?a :     (SUM y:B . PROD x:A . C(x,y))
          --> (PROD x:A . SUM y:B . C(x,y))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

text "Martin-Lof (1984) pages 36-7: the combinator S"
lemma
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!x y.[| x:A; y:B(x) |] ==> C(x,y) type"
  shows "?a :    (PROD x:A. PROD y:B(x). C(x,y))
             --> (PROD f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

text "Martin-Lof (1984) page 58: the axiom of disjunction elimination"
lemma
  assumes "A type"
    and "B type"
    and "!!z. z: A+B ==> C(z) type"
  shows "?a : (PROD x:A. C(inl(x))) --> (PROD y:B. C(inr(y)))
          --> (PROD z: A+B. C(z))"
apply (tactic {* pc_tac (thms "prems") 1 *})
done

(*towards AXIOM OF CHOICE*)
lemma [folded basic_defs]:
  "[| A type; B type; C type |] ==> ?a : (A --> B*C) --> (A-->B) * (A-->C)"
apply (tactic "pc_tac [] 1")
done


(*Martin-Lof (1984) page 50*)
text "AXIOM OF CHOICE!  Delicate use of elimination rules"
lemma
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!x y.[| x:A;  y:B(x) |] ==> C(x,y) type"
  shows "?a : PROD h: (PROD x:A. SUM y:B(x). C(x,y)).
                         (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (tactic {* intr_tac (thms "prems") *})
apply (tactic "add_mp_tac 2")
apply (tactic "add_mp_tac 1")
apply (erule SumE_fst)
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (rule_tac [4] SumE_snd)
apply (tactic {* typechk_tac (thm "SumE_fst" :: thms "prems") *})
done

text "Axiom of choice.  Proof without fst, snd.  Harder still!"
lemma [folded basic_defs]:
  assumes "A type"
    and "!!x. x:A ==> B(x) type"
    and "!!x y.[| x:A;  y:B(x) |] ==> C(x,y) type"
  shows "?a : PROD h: (PROD x:A. SUM y:B(x). C(x,y)).
                         (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (tactic {* intr_tac (thms "prems") *})
(*Must not use add_mp_tac as subst_prodE hides the construction.*)
apply (rule ProdE [THEN SumE], assumption)
apply (tactic "TRYALL assume_tac")
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (erule_tac [4] ProdE [THEN SumE])
apply (tactic {* typechk_tac (thms "prems") *})
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (tactic {* typechk_tac (thms "prems") *})
apply assumption
done

text "Example of sequent_style deduction"
(*When splitting z:A*B, the assumption C(z) is affected;  ?a becomes
    lam u. split(u,%v w.split(v,%x y.lam z. <x,<y,z>>) ` w)     *)
lemma
  assumes "A type"
    and "B type"
    and "!!z. z:A*B ==> C(z) type"
  shows "?a : (SUM z:A*B. C(z)) --> (SUM u:A. SUM v:B. C(<u,v>))"
apply (rule intr_rls)
apply (tactic {* biresolve_tac safe_brls 2 *})
(*Now must convert assumption C(z) into antecedent C(<kd,ke>) *)
apply (rule_tac [2] a = "y" in ProdE)
apply (tactic {* typechk_tac (thms "prems") *})
apply (rule SumE, assumption)
apply (tactic "intr_tac []")
apply (tactic "TRYALL assume_tac")
apply (tactic {* typechk_tac (thms "prems") *})
done

end
