(*  Title:      HOL/Eisbach/Examples_FOL.thy
    Author:     Daniel Matichuk, NICTA/UNSW
*)

section \<open>Basic Eisbach examples (in FOL)\<close>

theory Examples_FOL
imports FOL Eisbach_Old_Appl_Syntax
begin


subsection \<open>Basic methods\<close>

method my_intros = (rule conjI | rule impI)

lemma "P \<and> Q \<longrightarrow> Z \<and> X"
  apply my_intros+
  oops

method my_intros' uses intros = (rule conjI | rule impI | rule intros)

lemma "P \<and> Q \<longrightarrow> Z \<or> X"
  apply (my_intros' intros: disjI1)+
  oops

method my_spec for x :: 'a = (drule spec[where x="x"])

lemma "\<forall>x. P(x) \<Longrightarrow> P(x)"
  apply (my_spec x)
  apply assumption
  done


subsection \<open>Demo\<close>

named_theorems intros and elims and subst

method prop_solver declares intros elims subst =
  (assumption |
    rule intros | erule elims |
    subst subst | subst (asm) subst |
    (erule notE; solves prop_solver))+

lemmas [intros] =
  conjI
  impI
  disjCI
  iffI
  notI
lemmas [elims] =
  impCE
  conjE
  disjE

lemma "((A \<or> B) \<and> (A \<longrightarrow> C) \<and> (B \<longrightarrow> C)) \<longrightarrow> C"
  apply prop_solver
  done

method guess_all =
  (match premises in U[thin]:"\<forall>x. P (x :: 'a)" for P \<Rightarrow>
    \<open>match premises in "?H (y :: 'a)" for y \<Rightarrow>
       \<open>rule allE[where P = P and x = y, OF U]\<close>
   | match conclusion in "?H (y :: 'a)" for y \<Rightarrow>
       \<open>rule allE[where P = P and x = y, OF U]\<close>\<close>)

lemma "(\<forall>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow> P(y) \<Longrightarrow> Q(y)"
  apply guess_all
  apply prop_solver
  done

lemma "(\<forall>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow>  P(z) \<Longrightarrow> P(y) \<Longrightarrow> Q(y)"
  apply (solves \<open>guess_all, prop_solver\<close>)  \<comment> \<open>Try it without solve\<close>
  done

method guess_ex =
  (match conclusion in
    "\<exists>x. P (x :: 'a)" for P \<Rightarrow>
      \<open>match premises in "?H (x :: 'a)" for x \<Rightarrow>
              \<open>rule exI[where x=x]\<close>\<close>)

lemma "P(x) \<Longrightarrow> \<exists>x. P(x)"
  apply guess_ex
  apply prop_solver
  done

method fol_solver =
  ((guess_ex | guess_all | prop_solver); solves fol_solver)

declare
  allI [intros]
  exE [elims]
  ex_simps [subst]
  all_simps [subst]

lemma "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x)) \<Longrightarrow> (\<forall>x. P(x) \<and> Q(x))"
  and  "\<exists>x. P(x) \<longrightarrow> (\<forall>x. P(x))"
  and "(\<exists>x. \<forall>y. R(x, y)) \<longrightarrow> (\<forall>y. \<exists>x. R(x, y))"
  by fol_solver+

end
