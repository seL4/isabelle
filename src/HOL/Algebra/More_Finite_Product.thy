(*  Title:      HOL/Algebra/More_Finite_Product.thy
    Author:     Jeremy Avigad
*)

section \<open>More on finite products\<close>

theory More_Finite_Product
  imports More_Group
begin

lemma (in comm_monoid) finprod_UN_disjoint:
  "finite I \<Longrightarrow> (\<forall>i\<in>I. finite (A i)) \<longrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}) \<longrightarrow>
    (\<forall>i\<in>I. \<forall>x \<in> A i. g x \<in> carrier G) \<longrightarrow>
    finprod G g (UNION I A) = finprod G (\<lambda>i. finprod G g (A i)) I"
  apply (induct set: finite)
   apply force
  apply clarsimp
  apply (subst finprod_Un_disjoint)
       apply blast
      apply (erule finite_UN_I)
      apply blast
     apply (fastforce)
    apply (auto intro!: funcsetI finprod_closed)
  done

lemma (in comm_monoid) finprod_Union_disjoint:
  "finite C \<Longrightarrow>
    \<forall>A\<in>C. finite A \<and> (\<forall>x\<in>A. f x \<in> carrier G) \<Longrightarrow>
    \<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {} \<Longrightarrow>
    finprod G f (\<Union>C) = finprod G (finprod G f) C"
  apply (frule finprod_UN_disjoint [of C id f])
  apply auto
  done

lemma (in comm_monoid) finprod_one: "finite A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = \<one>) \<Longrightarrow> finprod G f A = \<one>"
  by (induct set: finite) auto


(* need better simplification rules for rings *)
(* the next one holds more generally for abelian groups *)

lemma (in cring) sum_zero_eq_neg: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> x \<oplus> y = \<zero> \<Longrightarrow> x = \<ominus> y"
  by (metis minus_equality)

lemma (in domain) square_eq_one:
  fixes x
  assumes [simp]: "x \<in> carrier R"
    and "x \<otimes> x = \<one>"
  shows "x = \<one> \<or> x = \<ominus>\<one>"
proof -
  have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = x \<otimes> x \<oplus> \<ominus> \<one>"
    by (simp add: ring_simprules)
  also from \<open>x \<otimes> x = \<one>\<close> have "\<dots> = \<zero>"
    by (simp add: ring_simprules)
  finally have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = \<zero>" .
  then have "(x \<oplus> \<one>) = \<zero> \<or> (x \<oplus> \<ominus> \<one>) = \<zero>"
    by (intro integral) auto
  then show ?thesis
    apply auto
     apply (erule notE)
     apply (rule sum_zero_eq_neg)
       apply auto
    apply (subgoal_tac "x = \<ominus> (\<ominus> \<one>)")
     apply (simp add: ring_simprules)
    apply (rule sum_zero_eq_neg)
      apply auto
    done
qed

lemma (in domain) inv_eq_self: "x \<in> Units R \<Longrightarrow> x = inv x \<Longrightarrow> x = \<one> \<or> x = \<ominus>\<one>"
  by (metis Units_closed Units_l_inv square_eq_one)


text \<open>
  The following translates theorems about groups to the facts about
  the units of a ring. (The list should be expanded as more things are
  needed.)
\<close>

lemma (in ring) finite_ring_finite_units [intro]: "finite (carrier R) \<Longrightarrow> finite (Units R)"
  by (rule finite_subset) auto

lemma (in monoid) units_of_pow:
  fixes n :: nat
  shows "x \<in> Units G \<Longrightarrow> x [^]\<^bsub>units_of G\<^esub> n = x [^]\<^bsub>G\<^esub> n"
  apply (induct n)
  apply (auto simp add: units_group group.is_monoid
    monoid.nat_pow_0 monoid.nat_pow_Suc units_of_one units_of_mult)
  done

lemma (in cring) units_power_order_eq_one:
  "finite (Units R) \<Longrightarrow> a \<in> Units R \<Longrightarrow> a [^] card(Units R) = \<one>"
  apply (subst units_of_carrier [symmetric])
  apply (subst units_of_one [symmetric])
  apply (subst units_of_pow [symmetric])
   apply assumption
  apply (rule comm_group.power_order_eq_one)
    apply (rule units_comm_group)
   apply (unfold units_of_def, auto)
  done

end
