(*  Title:      HOL/Algebra/More_Group.thy
    Author:     Jeremy Avigad
*)

section \<open>More on groups\<close>

theory More_Group
  imports Ring
begin

text \<open>
  Show that the units in any monoid give rise to a group.

  The file Residues.thy provides some infrastructure to use
  facts about the unit group within the ring locale.
\<close>

definition units_of :: "('a, 'b) monoid_scheme \<Rightarrow> 'a monoid"
  where "units_of G =
    \<lparr>carrier = Units G, Group.monoid.mult = Group.monoid.mult G, one  = one G\<rparr>"

lemma (in monoid) units_group: "group (units_of G)"
  apply (unfold units_of_def)
  apply (rule groupI)
      apply auto
   apply (subst m_assoc)
      apply auto
  apply (rule_tac x = "inv x" in bexI)
   apply auto
  done

lemma (in comm_monoid) units_comm_group: "comm_group (units_of G)"
  apply (rule group.group_comm_groupI)
   apply (rule units_group)
  apply (insert comm_monoid_axioms)
  apply (unfold units_of_def Units_def comm_monoid_def comm_monoid_axioms_def)
  apply auto
  done

lemma units_of_carrier: "carrier (units_of G) = Units G"
  by (auto simp: units_of_def)

lemma units_of_mult: "mult (units_of G) = mult G"
  by (auto simp: units_of_def)

lemma units_of_one: "one (units_of G) = one G"
  by (auto simp: units_of_def)

lemma (in monoid) units_of_inv: "x \<in> Units G \<Longrightarrow> m_inv (units_of G) x = m_inv G x"
  apply (rule sym)
  apply (subst m_inv_def)
  apply (rule the1_equality)
   apply (rule ex_ex1I)
    apply (subst (asm) Units_def)
    apply auto
     apply (erule inv_unique)
        apply auto
    apply (rule Units_closed)
    apply (simp_all only: units_of_carrier [symmetric])
    apply (insert units_group)
    apply auto
   apply (subst units_of_mult [symmetric])
   apply (subst units_of_one [symmetric])
   apply (erule group.r_inv, assumption)
  apply (subst units_of_mult [symmetric])
  apply (subst units_of_one [symmetric])
  apply (erule group.l_inv, assumption)
  done

lemma (in group) inj_on_const_mult: "a \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. a \<otimes> x) (carrier G)"
  unfolding inj_on_def by auto

lemma (in group) surj_const_mult: "a \<in> carrier G \<Longrightarrow> (\<lambda>x. a \<otimes> x) ` carrier G = carrier G"
  apply (auto simp add: image_def)
  apply (rule_tac x = "(m_inv G a) \<otimes> x" in bexI)
  apply auto
(* auto should get this. I suppose we need "comm_monoid_simprules"
   for ac_simps rewriting. *)
  apply (subst m_assoc [symmetric])
  apply auto
  done

lemma (in group) l_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x \<otimes> a = x \<longleftrightarrow> a = one G"
  apply auto
  apply (subst l_cancel [symmetric])
     prefer 4
     apply (erule ssubst)
     apply auto
  done

lemma (in group) r_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> a \<otimes> x = x \<longleftrightarrow> a = one G"
  apply auto
  apply (subst r_cancel [symmetric])
     prefer 4
     apply (erule ssubst)
     apply auto
  done

(* Is there a better way to do this? *)
lemma (in group) l_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = x \<otimes> a \<longleftrightarrow> a = one G"
  apply (subst eq_commute)
  apply simp
  done

lemma (in group) r_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = a \<otimes> x \<longleftrightarrow> a = one G"
  apply (subst eq_commute)
  apply simp
  done

(* This should be generalized to arbitrary groups, not just commutative
   ones, using Lagrange's theorem. *)

lemma (in comm_group) power_order_eq_one:
  assumes fin [simp]: "finite (carrier G)"
    and a [simp]: "a \<in> carrier G"
  shows "a [^] card(carrier G) = one G"
proof -
  have "(\<Otimes>x\<in>carrier G. x) = (\<Otimes>x\<in>carrier G. a \<otimes> x)"
    by (subst (2) finprod_reindex [symmetric],
      auto simp add: Pi_def inj_on_const_mult surj_const_mult)
  also have "\<dots> = (\<Otimes>x\<in>carrier G. a) \<otimes> (\<Otimes>x\<in>carrier G. x)"
    by (auto simp add: finprod_multf Pi_def)
  also have "(\<Otimes>x\<in>carrier G. a) = a [^] card(carrier G)"
    by (auto simp add: finprod_const)
  finally show ?thesis
(* uses the preceeding lemma *)
    by auto
qed

end
