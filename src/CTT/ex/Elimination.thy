(*  Title:      CTT/ex/Elimination.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Some examples taken from P. Martin-L\"of, Intuitionistic type theory
(Bibliopolis, 1984).
*)

section "Examples with elimination rules"

theory Elimination
imports "../CTT"
begin

text "This finds the functions fst and snd!"

schematic_lemma [folded basic_defs]: "A type \<Longrightarrow> ?a : (A*A) --> A"
apply pc
done

schematic_lemma [folded basic_defs]: "A type \<Longrightarrow> ?a : (A*A) --> A"
apply pc
back
done

text "Double negation of the Excluded Middle"
schematic_lemma "A type \<Longrightarrow> ?a : ((A + (A-->F)) --> F) --> F"
apply intr
apply (rule ProdE)
apply assumption
apply pc
done

schematic_lemma "\<lbrakk>A type; B type\<rbrakk> \<Longrightarrow> ?a : (A*B) \<longrightarrow> (B*A)"
apply pc
done
(*The sequent version (ITT) could produce an interesting alternative
  by backtracking.  No longer.*)

text "Binary sums and products"
schematic_lemma "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A+B --> C) --> (A-->C) * (B-->C)"
apply pc
done

(*A distributive law*)
schematic_lemma "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : A * (B+C)  -->  (A*B + A*C)"
apply pc
done

(*more general version, same proof*)
schematic_lemma
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x. x:A \<Longrightarrow> C(x) type"
  shows "?a : (SUM x:A. B(x) + C(x)) --> (SUM x:A. B(x)) + (SUM x:A. C(x))"
apply (pc assms)
done

text "Construction of the currying functional"
schematic_lemma "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A*B --> C) --> (A--> (B-->C))"
apply pc
done

(*more general goal with same proof*)
schematic_lemma
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (SUM x:A. B(x)) \<Longrightarrow> C(z) type"
  shows "?a : PROD f: (PROD z : (SUM x:A . B(x)) . C(z)).
                      (PROD x:A . PROD y:B(x) . C(<x,y>))"
apply (pc assms)
done

text "Martin-Lof (1984), page 48: axiom of sum-elimination (uncurry)"
schematic_lemma "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A --> (B-->C)) --> (A*B --> C)"
apply pc
done

(*more general goal with same proof*)
schematic_lemma
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (SUM x:A . B(x)) \<Longrightarrow> C(z) type"
  shows "?a : (PROD x:A . PROD y:B(x) . C(<x,y>))
        --> (PROD z : (SUM x:A . B(x)) . C(z))"
apply (pc assms)
done

text "Function application"
schematic_lemma "\<lbrakk>A type; B type\<rbrakk> \<Longrightarrow> ?a : ((A --> B) * A) --> B"
apply pc
done

text "Basic test of quantifier reasoning"
schematic_lemma
  assumes "A type"
    and "B type"
    and "\<And>x y. \<lbrakk>x:A; y:B\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows
    "?a :     (SUM y:B . PROD x:A . C(x,y))
          --> (PROD x:A . SUM y:B . C(x,y))"
apply (pc assms)
done

text "Martin-Lof (1984) pages 36-7: the combinator S"
schematic_lemma
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a :    (PROD x:A. PROD y:B(x). C(x,y))
             --> (PROD f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (pc assms)
done

text "Martin-Lof (1984) page 58: the axiom of disjunction elimination"
schematic_lemma
  assumes "A type"
    and "B type"
    and "\<And>z. z: A+B \<Longrightarrow> C(z) type"
  shows "?a : (PROD x:A. C(inl(x))) --> (PROD y:B. C(inr(y)))
          --> (PROD z: A+B. C(z))"
apply (pc assms)
done

(*towards AXIOM OF CHOICE*)
schematic_lemma [folded basic_defs]:
  "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A --> B*C) --> (A-->B) * (A-->C)"
apply pc
done


(*Martin-Lof (1984) page 50*)
text "AXIOM OF CHOICE!  Delicate use of elimination rules"
schematic_lemma
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a : PROD h: (PROD x:A. SUM y:B(x). C(x,y)).
                         (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (intr assms)
prefer 2 apply add_mp
prefer 2 apply add_mp
apply (erule SumE_fst)
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (rule_tac [4] SumE_snd)
apply (typechk SumE_fst assms)
done

text "Axiom of choice.  Proof without fst, snd.  Harder still!"
schematic_lemma [folded basic_defs]:
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a : PROD h: (PROD x:A. SUM y:B(x). C(x,y)).
                         (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))"
apply (intr assms)
(*Must not use add_mp as subst_prodE hides the construction.*)
apply (rule ProdE [THEN SumE])
apply assumption
apply assumption
apply assumption
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (erule_tac [4] ProdE [THEN SumE])
apply (typechk assms)
apply (rule replace_type)
apply (rule subst_eqtyparg)
apply (rule comp_rls)
apply (typechk assms)
apply assumption
done

text "Example of sequent_style deduction"
(*When splitting z:A*B, the assumption C(z) is affected;  ?a becomes
    lam u. split(u,\<lambda>v w.split(v,\<lambda>x y.lam z. <x,<y,z>>) ` w)     *)
schematic_lemma
  assumes "A type"
    and "B type"
    and "\<And>z. z:A*B \<Longrightarrow> C(z) type"
  shows "?a : (SUM z:A*B. C(z)) --> (SUM u:A. SUM v:B. C(<u,v>))"
apply (rule intr_rls)
apply (tactic {* biresolve_tac safe_brls 2 *})
(*Now must convert assumption C(z) into antecedent C(<kd,ke>) *)
apply (rule_tac [2] a = "y" in ProdE)
apply (typechk assms)
apply (rule SumE, assumption)
apply intr
defer 1
apply assumption+
apply (typechk assms)
done

end
