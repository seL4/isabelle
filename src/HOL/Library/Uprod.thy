(* Title: HOL/Library/Uprod.thy
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Unordered pairs\<close>

theory Uprod imports Main begin

typedef ('a, 'b) commute = "{f :: 'a \<Rightarrow> 'a \<Rightarrow> 'b. \<forall>x y. f x y = f y x}"
  morphisms apply_commute Abs_commute
  by auto

setup_lifting type_definition_commute

lemma apply_commute_commute: "apply_commute f x y = apply_commute f y x"
by(transfer) simp

context includes lifting_syntax begin

lift_definition rel_commute :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'c) commute \<Rightarrow> ('b, 'd) commute \<Rightarrow> bool"
is "\<lambda>A B. A ===> A ===> B" .

end

definition eq_upair :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool"
where "eq_upair = (\<lambda>(a, b) (c, d). a = c \<and> b = d \<or> a = d \<and> b = c)"

lemma eq_upair_simps [simp]:
  "eq_upair (a, b) (c, d) \<longleftrightarrow> a = c \<and> b = d \<or> a = d \<and> b = c"
by(simp add: eq_upair_def)

lemma equivp_eq_upair: "equivp eq_upair"
by(auto simp add: equivp_def fun_eq_iff)

quotient_type 'a uprod = "'a \<times> 'a" / eq_upair by(rule equivp_eq_upair)

lift_definition Upair :: "'a \<Rightarrow> 'a \<Rightarrow> 'a uprod" is Pair parametric Pair_transfer[of "A" "A" for A] .

lemma uprod_exhaust [case_names Upair, cases type: uprod]:
  obtains a b where "x = Upair a b"
by transfer fastforce

lemma Upair_inject [simp]: "Upair a b = Upair c d \<longleftrightarrow> a = c \<and> b = d \<or> a = d \<and> b = c"
by transfer auto

code_datatype Upair

lift_definition case_uprod :: "('a, 'b) commute \<Rightarrow> 'a uprod \<Rightarrow> 'b" is case_prod
  parametric case_prod_transfer[of A A for A] by auto

lemma case_uprod_simps [simp, code]: "case_uprod f (Upair x y) = apply_commute f x y"
by transfer auto

lemma uprod_split: "P (case_uprod f x) \<longleftrightarrow> (\<forall>a b. x = Upair a b \<longrightarrow> P (apply_commute f a b))"
by transfer auto

lemma uprod_split_asm: "P (case_uprod f x) \<longleftrightarrow> \<not> (\<exists>a b. x = Upair a b \<and> \<not> P (apply_commute f a b))"
by transfer auto

lift_definition not_equal :: "('a, bool) commute" is "(\<noteq>)" by auto

lemma apply_not_equal [simp]: "apply_commute not_equal x y \<longleftrightarrow> x \<noteq> y"
by transfer simp

definition proper_uprod :: "'a uprod \<Rightarrow> bool"
where "proper_uprod = case_uprod not_equal"

lemma proper_uprod_simps [simp, code]: "proper_uprod (Upair x y) \<longleftrightarrow> x \<noteq> y"
by(simp add: proper_uprod_def)

context includes lifting_syntax begin

private lemma set_uprod_parametric':
  "(rel_prod A A ===> rel_set A) (\<lambda>(a, b). {a, b}) (\<lambda>(a, b). {a, b})"
by transfer_prover

lift_definition set_uprod :: "'a uprod \<Rightarrow> 'a set" is "\<lambda>(a, b). {a, b}" 
  parametric set_uprod_parametric' by auto

lemma set_uprod_simps [simp, code]: "set_uprod (Upair x y) = {x, y}"
by transfer simp

lemma finite_set_uprod [simp]: "finite (set_uprod x)"
by(cases x) simp

private lemma map_uprod_parametric':
  "((A ===> B) ===> rel_prod A A ===> rel_prod B B) (\<lambda>f. map_prod f f) (\<lambda>f. map_prod f f)"
by transfer_prover

lift_definition map_uprod :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a uprod \<Rightarrow> 'b uprod" is "\<lambda>f. map_prod f f"
  parametric map_uprod_parametric' by auto

lemma map_uprod_simps [simp, code]: "map_uprod f (Upair x y) = Upair (f x) (f y)"
by transfer simp

private lemma rel_uprod_transfer':
  "((A ===> B ===> (=)) ===> rel_prod A A ===> rel_prod B B ===> (=))
   (\<lambda>R (a, b) (c, d). R a c \<and> R b d \<or> R a d \<and> R b c) (\<lambda>R (a, b) (c, d). R a c \<and> R b d \<or> R a d \<and> R b c)"
by transfer_prover

lift_definition rel_uprod :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a uprod \<Rightarrow> 'b uprod \<Rightarrow> bool"
  is "\<lambda>R (a, b) (c, d). R a c \<and> R b d \<or> R a d \<and> R b c" parametric rel_uprod_transfer'
by auto

lemma rel_uprod_simps [simp, code]:
  "rel_uprod R (Upair a b) (Upair c d) \<longleftrightarrow> R a c \<and> R b d \<or> R a d \<and> R b c"
by transfer auto

lemma Upair_parametric [transfer_rule]: "(A ===> A ===> rel_uprod A) Upair Upair"
unfolding rel_fun_def by transfer auto

lemma case_uprod_parametric [transfer_rule]:
  "(rel_commute A B ===> rel_uprod A ===> B) case_uprod case_uprod"
unfolding rel_fun_def by transfer(force dest: rel_funD)

end

bnf uprod: "'a uprod" 
  map: map_uprod
  sets: set_uprod
  bd: natLeq
  rel: rel_uprod
proof -
  show "map_uprod id = id" unfolding fun_eq_iff by transfer auto
  show "map_uprod (g \<circ> f) = map_uprod g \<circ> map_uprod f" for f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
    unfolding fun_eq_iff by transfer auto
  show "map_uprod f x = map_uprod g x" if "\<And>z. z \<in> set_uprod x \<Longrightarrow> f z = g z" 
    for f :: "'a \<Rightarrow> 'b" and g x using that by transfer auto
  show "set_uprod \<circ> map_uprod f = (`) f \<circ> set_uprod" for f :: "'a \<Rightarrow> 'b" by transfer auto
  show "card_order natLeq" by(rule natLeq_card_order)
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq" by(rule natLeq_cinfinite)
  show "ordLeq3 (card_of (set_uprod x)) natLeq" for x :: "'a uprod"
    by (auto simp: finite_iff_ordLess_natLeq[symmetric] intro: ordLess_imp_ordLeq)
  show "rel_uprod R OO rel_uprod S \<le> rel_uprod (R OO S)"
    for R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool" by(rule predicate2I)(transfer; auto)
  show "rel_uprod R = (\<lambda>x y. \<exists>z. set_uprod z \<subseteq> {(x, y). R x y} \<and> map_uprod fst z = x \<and> map_uprod snd z = y)"
    for R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" by transfer(auto simp add: fun_eq_iff)
qed

lemma pred_uprod_code [simp, code]: "pred_uprod P (Upair x y) \<longleftrightarrow> P x \<and> P y"
by(simp add: pred_uprod_def)

instantiation uprod :: (equal) equal begin

definition equal_uprod :: "'a uprod \<Rightarrow> 'a uprod \<Rightarrow> bool"
where "equal_uprod = (=)"

lemma equal_uprod_code [code]:
  "HOL.equal (Upair x y) (Upair z u) \<longleftrightarrow> x = z \<and> y = u \<or> x = u \<and> y = z"
unfolding equal_uprod_def by simp

instance by standard(simp add: equal_uprod_def)
end

quickcheck_generator uprod constructors: Upair

lemma UNIV_uprod: "UNIV = (\<lambda>x. Upair x x) ` UNIV \<union> (\<lambda>(x, y). Upair x y) ` Sigma UNIV (\<lambda>x. UNIV - {x})"
apply(rule set_eqI)
subgoal for x by(cases x) auto
done

context begin
private lift_definition upair_inv :: "'a uprod \<Rightarrow> 'a"
is "\<lambda>(x, y). if x = y then x else undefined" by auto

lemma finite_UNIV_prod [simp]:
  "finite (UNIV :: 'a uprod set) \<longleftrightarrow> finite (UNIV :: 'a set)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  hence "finite (range (\<lambda>x :: 'a. Upair x x))" by(rule finite_subset[rotated]) simp
  hence "finite (upair_inv ` range (\<lambda>x :: 'a. Upair x x))" by(rule finite_imageI)
  also have "upair_inv (Upair x x) = x" for x :: 'a by transfer simp
  then have "upair_inv ` range (\<lambda>x :: 'a. Upair x x) = UNIV" by(auto simp add: image_image)
  finally show ?rhs .
qed(simp add: UNIV_uprod)

end

lemma card_UNIV_uprod:
  "card (UNIV :: 'a uprod set) = card (UNIV :: 'a set) * (card (UNIV :: 'a set) + 1) div 2"
  (is "?UPROD = ?A * _ div _")
proof(cases "finite (UNIV :: 'a set)")
  case True
  from True obtain f :: "nat \<Rightarrow> 'a" where bij: "bij_betw f {0..<?A} UNIV"
    by (blast dest: ex_bij_betw_nat_finite)
  hence [simp]: "f ` {0..<?A} = UNIV" by(rule bij_betw_imp_surj_on)
  have "UNIV = (\<lambda>(x, y). Upair (f x) (f y)) ` (SIGMA x:{0..<?A}. {..x})"
    apply(rule set_eqI)
    subgoal for x
      apply(cases x)
      apply(clarsimp)
      subgoal for a b
        apply(cases "inv_into {0..<?A} f a \<le> inv_into {0..<?A} f b")
        subgoal by(rule rev_image_eqI[where x="(inv_into {0..<?A} f _, inv_into {0..<?A} f _)"])
                  (auto simp add: inv_into_into[where A="{0..<?A}" and f=f, simplified] intro: f_inv_into_f[where f=f, symmetric])
        subgoal
          apply(simp only: not_le)
          apply(drule less_imp_le)
          apply(rule rev_image_eqI[where x="(inv_into {0..<?A} f _, inv_into {0..<?A} f _)"])
          apply(auto simp add: inv_into_into[where A="{0..<?A}" and f=f, simplified] intro: f_inv_into_f[where f=f, symmetric])
          done
        done
      done
    done
  hence "?UPROD = card \<dots>" by simp
  also have "\<dots> = card (SIGMA x:{0..<?A}. {..x})"
    apply(rule card_image)
    using bij[THEN bij_betw_imp_inj_on]
    by(simp add: inj_on_def Ball_def)(metis leD le_eq_less_or_eq le_less_trans)
  also have "\<dots> = sum Suc {0..<?A}"
    by (subst card_SigmaI) simp_all
  also have "\<dots> = sum of_nat {Suc 0..?A}"
    using sum.atLeast_lessThan_reindex [symmetric, of Suc 0 ?A id]
    by (simp del: sum_op_ivl_Suc add: atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = ?A * (?A + 1) div 2"
    using gauss_sum_from_Suc_0 [of ?A, where ?'a = nat] by simp
  finally show ?thesis .
qed simp

end
