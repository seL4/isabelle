(*  Title:      HOL/Algebra/More_Ring.thy
    Author:     Jeremy Avigad
*)

section \<open>More on rings etc.\<close>

theory More_Ring
  imports Ring
begin

lemma (in cring) field_intro2: "\<zero>\<^bsub>R\<^esub> \<noteq> \<one>\<^bsub>R\<^esub> \<Longrightarrow> \<forall>x \<in> carrier R - {\<zero>\<^bsub>R\<^esub>}. x \<in> Units R \<Longrightarrow> field R"
  apply (unfold_locales)
    apply (use cring_axioms in auto)
   apply (rule trans)
    apply (subgoal_tac "a = (a \<otimes> b) \<otimes> inv b")
     apply assumption
    apply (subst m_assoc)
       apply auto
  apply (unfold Units_def)
  apply auto
  done

lemma (in monoid) inv_char:
  "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y = \<one> \<Longrightarrow> y \<otimes> x = \<one> \<Longrightarrow> inv x = y"
  apply (subgoal_tac "x \<in> Units G")
   apply (subgoal_tac "y = inv x \<otimes> \<one>")
    apply simp
   apply (erule subst)
   apply (subst m_assoc [symmetric])
      apply auto
  apply (unfold Units_def)
  apply auto
  done

lemma (in comm_monoid) comm_inv_char: "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y = \<one> \<Longrightarrow> inv x = y"
  apply (rule inv_char)
     apply auto
  apply (subst m_comm, auto)
  done

lemma (in ring) inv_neg_one [simp]: "inv (\<ominus> \<one>) = \<ominus> \<one>"
  apply (rule inv_char)
     apply (auto simp add: l_minus r_minus)
  done

lemma (in monoid) inv_eq_imp_eq: "x \<in> Units G \<Longrightarrow> y \<in> Units G \<Longrightarrow> inv x = inv y \<Longrightarrow> x = y"
  apply (subgoal_tac "inv (inv x) = inv (inv y)")
   apply (subst (asm) Units_inv_inv)+
    apply auto
  done

lemma (in ring) Units_minus_one_closed [intro]: "\<ominus> \<one> \<in> Units R"
  apply (unfold Units_def)
  apply auto
  apply (rule_tac x = "\<ominus> \<one>" in bexI)
   apply auto
  apply (simp add: l_minus r_minus)
  done

lemma (in monoid) inv_one [simp]: "inv \<one> = \<one>"
  apply (rule inv_char)
     apply auto
  done

lemma (in ring) inv_eq_neg_one_eq: "x \<in> Units R \<Longrightarrow> inv x = \<ominus> \<one> \<longleftrightarrow> x = \<ominus> \<one>"
  apply auto
  apply (subst Units_inv_inv [symmetric])
   apply auto
  done

lemma (in monoid) inv_eq_one_eq: "x \<in> Units G \<Longrightarrow> inv x = \<one> \<longleftrightarrow> x = \<one>"
  by (metis Units_inv_inv inv_one)

end
