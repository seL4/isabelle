(*  Title:      MiscAlgebra.thy
    ID:         
    Author:     Jeremy Avigad

    These are things that can be added to the Algebra library,
    as well as a few things that could possibly go in Main. 
*)

theory MiscAlgebra
imports 
  "~~/src/HOL/Algebra/Ring"
  "~~/src/HOL/Algebra/FiniteProduct"
begin;

declare One_nat_def [simp del] 


(* Some things for Main? *)

(* finiteness stuff *)

lemma int_bounded_set1 [intro]: "finite {(x::int). a < x & x < b & P x}" 
  apply (subgoal_tac "{x. a < x & x < b & P x} <= {a<..<b}")
  apply (erule finite_subset)
  apply auto
done

lemma image_set_eq_image: "{ f x | x. P x} = f ` { x. P x}"
  unfolding image_def apply auto
done

lemma finite_image_set [simp]: "finite {x. P x} \<Longrightarrow> 
    finite { f x | x. P x}"
  apply (subst image_set_eq_image)
  apply auto
done

(* Examples:

lemma "finite {x. 0 < x & x < 100 & prime (x::int)}"
  by auto

lemma "finite { 3 * x | x. 0 < x & x < 100 & prime (x::int) }"
  by auto

*)

(* The rest is for the algebra libraries *)

(* This goes in FuncSet.thy. Any reason not to make it a simp rule? *)

lemma funcset_id [simp]: "(%x. x): A \<rightarrow> A"
  by (auto simp add: Pi_def);

(* These go in Group.thy. *)

(*
  Show that the units in any monoid give rise to a group.

  The file Residues.thy provides some infrastructure to use
  facts about the unit group within the ring locale.
*)


constdefs 
  units_of :: "('a, 'b) monoid_scheme => 'a monoid"
  "units_of G == (| carrier = Units G,
     Group.monoid.mult = Group.monoid.mult G,
     one  = one G |)";

(*

lemma (in monoid) Units_mult_closed [intro]:
  "x : Units G ==> y : Units G ==> x \<otimes> y : Units G"
  apply (unfold Units_def)
  apply (clarsimp)
  apply (rule_tac x = "xaa \<otimes> xa" in bexI)
  apply auto
  apply (subst m_assoc)
  apply auto
  apply (subst (2) m_assoc [symmetric])
  apply auto
  apply (subst m_assoc)
  apply auto
  apply (subst (2) m_assoc [symmetric])
  apply auto
done

*)

lemma (in monoid) units_group: "group(units_of G)"
  apply (unfold units_of_def)
  apply (rule groupI)
  apply auto
  apply (subst m_assoc)
  apply auto
  apply (rule_tac x = "inv x" in bexI)
  apply auto
done

lemma (in comm_monoid) units_comm_group: "comm_group(units_of G)"
  apply (rule group.group_comm_groupI)
  apply (rule units_group)
  apply (insert prems)
  apply (unfold units_of_def Units_def comm_monoid_def comm_monoid_axioms_def)
  apply auto;
done;

lemma units_of_carrier: "carrier (units_of G) = Units G"
  by (unfold units_of_def, auto)

lemma units_of_mult: "mult(units_of G) = mult G"
  by (unfold units_of_def, auto)

lemma units_of_one: "one(units_of G) = one G"
  by (unfold units_of_def, auto)

lemma (in monoid) units_of_inv: "x : Units G ==> 
    m_inv (units_of G) x = m_inv G x"
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

lemma (in group) inj_on_const_mult: "a: (carrier G) ==> 
    inj_on (%x. a \<otimes> x) (carrier G)"
  by (unfold inj_on_def, auto)

lemma (in group) surj_const_mult: "a : (carrier G) ==>
    (%x. a \<otimes> x) ` (carrier G) = (carrier G)" 
  apply (auto simp add: image_def)
  apply (rule_tac x = "(m_inv G a) \<otimes> x" in bexI)
  apply auto
(* auto should get this. I suppose we need "comm_monoid_simprules"
   for mult_ac rewriting. *)
  apply (subst m_assoc [symmetric])
  apply auto
done

lemma (in group) l_cancel_one [simp]: "x : carrier G \<Longrightarrow> a : carrier G \<Longrightarrow>
    (x \<otimes> a = x) = (a = one G)"
  apply auto
  apply (subst l_cancel [symmetric])
  prefer 4
  apply (erule ssubst)
  apply auto
done

lemma (in group) r_cancel_one [simp]: "x : carrier G \<Longrightarrow> a : carrier G \<Longrightarrow>
    (a \<otimes> x = x) = (a = one G)"
  apply auto
  apply (subst r_cancel [symmetric])
  prefer 4
  apply (erule ssubst)
  apply auto
done

(* Is there a better way to do this? *)

lemma (in group) l_cancel_one' [simp]: "x : carrier G \<Longrightarrow> a : carrier G \<Longrightarrow>
    (x = x \<otimes> a) = (a = one G)"
  by (subst eq_commute, simp)

lemma (in group) r_cancel_one' [simp]: "x : carrier G \<Longrightarrow> a : carrier G \<Longrightarrow>
    (x = a \<otimes> x) = (a = one G)"
  by (subst eq_commute, simp)

(* This should be generalized to arbitrary groups, not just commutative
   ones, using Lagrange's theorem. *)

lemma (in comm_group) power_order_eq_one:
    assumes fin [simp]: "finite (carrier G)"
        and a [simp]: "a : carrier G" 
      shows "a (^) card(carrier G) = one G" 
proof -
  have "(\<Otimes>x:carrier G. x) = (\<Otimes>x:carrier G. a \<otimes> x)"
    by (subst (2) finprod_reindex [symmetric], 
      auto simp add: Pi_def inj_on_const_mult surj_const_mult)
  also have "\<dots> = (\<Otimes>x:carrier G. a) \<otimes> (\<Otimes>x:carrier G. x)"
    by (auto simp add: finprod_multf Pi_def)
  also have "(\<Otimes>x:carrier G. a) = a (^) card(carrier G)"
    by (auto simp add: finprod_const)
  finally show ?thesis
(* uses the preceeding lemma *)
    by auto
qed


(* Miscellaneous *)

lemma (in cring) field_intro2: "\<zero>\<^bsub>R\<^esub> ~= \<one>\<^bsub>R\<^esub> \<Longrightarrow> ALL x : carrier R - {\<zero>\<^bsub>R\<^esub>}.
    x : Units R \<Longrightarrow> field R"
  apply (unfold_locales)
  apply (insert prems, auto)
  apply (rule trans)
  apply (subgoal_tac "a = (a \<otimes> b) \<otimes> inv b")
  apply assumption
  apply (subst m_assoc) 
  apply (auto simp add: Units_r_inv)
  apply (unfold Units_def)
  apply auto
done

lemma (in monoid) inv_char: "x : carrier G \<Longrightarrow> y : carrier G \<Longrightarrow>
  x \<otimes> y = \<one> \<Longrightarrow> y \<otimes> x = \<one> \<Longrightarrow> inv x = y"
  apply (subgoal_tac "x : Units G")
  apply (subgoal_tac "y = inv x \<otimes> \<one>")
  apply simp
  apply (erule subst)
  apply (subst m_assoc [symmetric])
  apply auto
  apply (unfold Units_def)
  apply auto
done

lemma (in comm_monoid) comm_inv_char: "x : carrier G \<Longrightarrow> y : carrier G \<Longrightarrow>
  x \<otimes> y = \<one> \<Longrightarrow> inv x = y"
  apply (rule inv_char)
  apply auto
  apply (subst m_comm, auto) 
done

lemma (in ring) inv_neg_one [simp]: "inv (\<ominus> \<one>) = \<ominus> \<one>"  
  apply (rule inv_char)
  apply (auto simp add: l_minus r_minus)
done

lemma (in monoid) inv_eq_imp_eq: "x : Units G \<Longrightarrow> y : Units G \<Longrightarrow> 
    inv x = inv y \<Longrightarrow> x = y"
  apply (subgoal_tac "inv(inv x) = inv(inv y)")
  apply (subst (asm) Units_inv_inv)+
  apply auto
done

lemma (in ring) Units_minus_one_closed [intro]: "\<ominus> \<one> : Units R"
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

lemma (in ring) inv_eq_neg_one_eq: "x : Units R \<Longrightarrow> (inv x = \<ominus> \<one>) = (x = \<ominus> \<one>)"
  apply auto
  apply (subst Units_inv_inv [symmetric])
  apply auto
done

lemma (in monoid) inv_eq_one_eq: "x : Units G \<Longrightarrow> (inv x = \<one>) = (x = \<one>)"
  apply auto
  apply (subst Units_inv_inv [symmetric])
  apply auto
done


(* This goes in FiniteProduct *)

lemma (in comm_monoid) finprod_UN_disjoint:
  "finite I \<Longrightarrow> (ALL i:I. finite (A i)) \<longrightarrow> (ALL i:I. ALL j:I. i ~= j \<longrightarrow>
     (A i) Int (A j) = {}) \<longrightarrow>
      (ALL i:I. ALL x: (A i). g x : carrier G) \<longrightarrow>
        finprod G g (UNION I A) = finprod G (%i. finprod G g (A i)) I"
  apply (induct set: finite)
  apply force
  apply clarsimp
  apply (subst finprod_Un_disjoint)
  apply blast
  apply (erule finite_UN_I)
  apply blast
  apply (fastsimp)
  apply (auto intro!: funcsetI finprod_closed) 
done

lemma (in comm_monoid) finprod_Union_disjoint:
  "[| finite C; (ALL A:C. finite A & (ALL x:A. f x : carrier G));
      (ALL A:C. ALL B:C. A ~= B --> A Int B = {}) |] 
   ==> finprod G f (Union C) = finprod G (finprod G f) C" 
  apply (frule finprod_UN_disjoint [of C id f])
  apply (unfold Union_def id_def, auto)
done

lemma (in comm_monoid) finprod_one [rule_format]: 
  "finite A \<Longrightarrow> (ALL x:A. f x = \<one>) \<longrightarrow>
     finprod G f A = \<one>"
by (induct set: finite) auto


(* need better simplification rules for rings *)
(* the next one holds more generally for abelian groups *)

lemma (in cring) sum_zero_eq_neg:
  "x : carrier R \<Longrightarrow> y : carrier R \<Longrightarrow> x \<oplus> y = \<zero> \<Longrightarrow> x = \<ominus> y"
  apply (subgoal_tac "\<ominus> y = \<zero> \<oplus> \<ominus> y") 
  apply (erule ssubst)back
  apply (erule subst)
  apply (simp add: ring_simprules)+
done

(* there's a name conflict -- maybe "domain" should be
   "integral_domain" *)

lemma (in Ring.domain) square_eq_one: 
  fixes x
  assumes [simp]: "x : carrier R" and
    "x \<otimes> x = \<one>"
  shows "x = \<one> | x = \<ominus>\<one>"
proof -
  have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = x \<otimes> x \<oplus> \<ominus> \<one>"
    by (simp add: ring_simprules)
  also with `x \<otimes> x = \<one>` have "\<dots> = \<zero>"
    by (simp add: ring_simprules)
  finally have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = \<zero>" .
  hence "(x \<oplus> \<one>) = \<zero> | (x \<oplus> \<ominus> \<one>) = \<zero>"
    by (intro integral, auto)
  thus ?thesis
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

lemma (in Ring.domain) inv_eq_self: "x : Units R \<Longrightarrow>
    x = inv x \<Longrightarrow> x = \<one> | x = \<ominus> \<one>"
  apply (rule square_eq_one)
  apply auto
  apply (erule ssubst)back
  apply (erule Units_r_inv)
done


(*
  The following translates theorems about groups to the facts about
  the units of a ring. (The list should be expanded as more things are
  needed.)
*)

lemma (in ring) finite_ring_finite_units [intro]: "finite (carrier R) \<Longrightarrow> 
    finite (Units R)"
  by (rule finite_subset, auto)

(* this belongs with MiscAlgebra.thy *)
lemma (in monoid) units_of_pow: 
    "x : Units G \<Longrightarrow> x (^)\<^bsub>units_of G\<^esub> (n::nat) = x (^)\<^bsub>G\<^esub> n"
  apply (induct n)
  apply (auto simp add: units_group group.is_monoid  
    monoid.nat_pow_0 monoid.nat_pow_Suc units_of_one units_of_mult
    One_nat_def)
done

lemma (in cring) units_power_order_eq_one: "finite (Units R) \<Longrightarrow> a : Units R
    \<Longrightarrow> a (^) card(Units R) = \<one>"
  apply (subst units_of_carrier [symmetric])
  apply (subst units_of_one [symmetric])
  apply (subst units_of_pow [symmetric])
  apply assumption
  apply (rule comm_group.power_order_eq_one)
  apply (rule units_comm_group)
  apply (unfold units_of_def, auto)
done

end
