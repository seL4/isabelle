(*  Title:      CTT/ex/Elimination.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Some examples taken from P. Martin-Löf, Intuitionistic type theory
(Bibliopolis, 1984).
*)

section \<open>Examples with elimination rules\<close>

theory Elimination
imports "../CTT"
begin

text \<open>This finds the functions fst and snd!\<close>

schematic_goal [folded basic_defs]: "A type \<Longrightarrow> ?a : (A \<times> A) \<longrightarrow> A"
apply pc
done

schematic_goal [folded basic_defs]: "A type \<Longrightarrow> ?a : (A \<times> A) \<longrightarrow> A"
  apply pc
  back
  done

text \<open>Double negation of the Excluded Middle\<close>
schematic_goal "A type \<Longrightarrow> ?a : ((A + (A\<longrightarrow>F)) \<longrightarrow> F) \<longrightarrow> F"
  apply intr
  apply (rule ProdE)
   apply assumption
  apply pc
  done

text \<open>Experiment: the proof above in Isar\<close>
lemma
  assumes "A type" shows "(\<^bold>\<lambda>f. f ` inr(\<^bold>\<lambda>y. f ` inl(y))) : ((A + (A\<longrightarrow>F)) \<longrightarrow> F) \<longrightarrow> F"
proof intr
  fix f
  assume f: "f : A + (A \<longrightarrow> F) \<longrightarrow> F" 
  with assms have "inr(\<^bold>\<lambda>y. f ` inl(y)) : A + (A \<longrightarrow> F)"
    by pc
  then show "f ` inr(\<^bold>\<lambda>y. f ` inl(y)) : F" 
    by (rule ProdE [OF f])
qed (rule assms)+

schematic_goal "\<lbrakk>A type; B type\<rbrakk> \<Longrightarrow> ?a : (A \<times> B) \<longrightarrow> (B \<times> A)"
apply pc
done
(*The sequent version (ITT) could produce an interesting alternative
  by backtracking.  No longer.*)

text \<open>Binary sums and products\<close>
schematic_goal "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A + B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C) \<times> (B \<longrightarrow> C)"
  apply pc
  done

(*A distributive law*)
schematic_goal "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : A \<times> (B + C) \<longrightarrow> (A \<times> B + A \<times> C)"
  by pc

(*more general version, same proof*)
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x. x:A \<Longrightarrow> C(x) type"
  shows "?a : (\<Sum>x:A. B(x) + C(x)) \<longrightarrow> (\<Sum>x:A. B(x)) + (\<Sum>x:A. C(x))"
  apply (pc assms)
  done

text \<open>Construction of the currying functional\<close>
schematic_goal "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A \<times> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply pc
  done

(*more general goal with same proof*)
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (\<Sum>x:A. B(x)) \<Longrightarrow> C(z) type"
  shows "?a : \<Prod>f: (\<Prod>z : (\<Sum>x:A . B(x)) . C(z)).
                      (\<Prod>x:A . \<Prod>y:B(x) . C(<x,y>))"
  apply (pc assms)
  done

text \<open>Martin-Löf (1984), page 48: axiom of sum-elimination (uncurry)\<close>
schematic_goal "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<times> B \<longrightarrow> C)"
  apply pc
  done

(*more general goal with same proof*)
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>z. z: (\<Sum>x:A . B(x)) \<Longrightarrow> C(z) type"
  shows "?a : (\<Prod>x:A . \<Prod>y:B(x) . C(<x,y>))
        \<longrightarrow> (\<Prod>z : (\<Sum>x:A . B(x)) . C(z))"
  apply (pc assms)
  done

text \<open>Function application\<close>
schematic_goal "\<lbrakk>A type; B type\<rbrakk> \<Longrightarrow> ?a : ((A \<longrightarrow> B) \<times> A) \<longrightarrow> B"
  apply pc
  done

text \<open>Basic test of quantifier reasoning\<close>
schematic_goal
  assumes "A type"
    and "B type"
    and "\<And>x y. \<lbrakk>x:A; y:B\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows
    "?a :     (\<Sum>y:B . \<Prod>x:A . C(x,y))
          \<longrightarrow> (\<Prod>x:A . \<Sum>y:B . C(x,y))"
  apply (pc assms)
  done

text \<open>Martin-Löf (1984) pages 36-7: the combinator S\<close>
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a :    (\<Prod>x:A. \<Prod>y:B(x). C(x,y))
             \<longrightarrow> (\<Prod>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
  apply (pc assms)
  done

text \<open>Martin-Löf (1984) page 58: the axiom of disjunction elimination\<close>
schematic_goal
  assumes "A type"
    and "B type"
    and "\<And>z. z: A+B \<Longrightarrow> C(z) type"
  shows "?a : (\<Prod>x:A. C(inl(x))) \<longrightarrow> (\<Prod>y:B. C(inr(y)))
          \<longrightarrow> (\<Prod>z: A+B. C(z))"
  apply (pc assms)
  done

(*towards AXIOM OF CHOICE*)
schematic_goal [folded basic_defs]:
  "\<lbrakk>A type; B type; C type\<rbrakk> \<Longrightarrow> ?a : (A \<longrightarrow> B \<times> C) \<longrightarrow> (A \<longrightarrow> B) \<times> (A \<longrightarrow> C)"
  apply pc
  done


(*Martin-Löf (1984) page 50*)
text \<open>AXIOM OF CHOICE!  Delicate use of elimination rules\<close>
schematic_goal
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a : (\<Prod>x:A. \<Sum>y:B(x). C(x,y)) \<longrightarrow> (\<Sum>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
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

text \<open>A structured proof of AC\<close>
lemma Axiom_of_Choice:
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "(\<^bold>\<lambda>f. <\<^bold>\<lambda>x. fst(f`x), \<^bold>\<lambda>x. snd(f`x)>) 
        : (\<Prod>x:A. \<Sum>y:B(x). C(x,y)) \<longrightarrow> (\<Sum>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
proof (intr assms)
  fix f a
  assume f: "f : \<Prod>x:A. Sum(B(x), C(x))" and "a : A" 
  then have fa: "f`a : Sum(B(a), C(a))"
    by (rule ProdE)
  then show "fst(f ` a) : B(a)" 
    by (rule SumE_fst)
  have "snd(f ` a) : C(a, fst(f ` a))"
    by (rule SumE_snd [OF fa]) (typechk SumE_fst assms \<open>a : A\<close>)
  moreover have "(\<^bold>\<lambda>x. fst(f ` x)) ` a = fst(f ` a) : B(a)"
    by (rule ProdC [OF \<open>a : A\<close>]) (typechk SumE_fst f)
  ultimately show "snd(f`a) : C(a, (\<^bold>\<lambda>x. fst(f ` x)) ` a)"
    by (intro replace_type [OF subst_eqtyparg]) (typechk SumE_fst assms \<open>a : A\<close>)
qed

text \<open>Axiom of choice.  Proof without fst, snd.  Harder still!\<close>
schematic_goal [folded basic_defs]:
  assumes "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
    and "\<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> C(x,y) type"
  shows "?a : (\<Prod>x:A. \<Sum>y:B(x). C(x,y)) \<longrightarrow> (\<Sum>f: (\<Prod>x:A. B(x)). \<Prod>x:A. C(x, f`x))"
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

text \<open>Example of sequent-style deduction\<close>
  (*When splitting z:A \<times> B, the assumption C(z) is affected;  ?a becomes
    \<^bold>\<lambda>u. split(u,\<lambda>v w.split(v,\<lambda>x y.\<^bold> \<lambda>z. <x,<y,z>>) ` w)     *)
schematic_goal
  assumes "A type"
    and "B type"
    and "\<And>z. z:A \<times> B \<Longrightarrow> C(z) type"
  shows "?a : (\<Sum>z:A \<times> B. C(z)) \<longrightarrow> (\<Sum>u:A. \<Sum>v:B. C(<u,v>))"
  apply (rule intr_rls)
   apply (tactic \<open>biresolve_tac \<^context> safe_brls 2\<close>)
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
