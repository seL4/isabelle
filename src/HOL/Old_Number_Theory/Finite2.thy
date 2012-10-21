(*  Title:      HOL/Old_Number_Theory/Finite2.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {*Finite Sets and Finite Sums*}

theory Finite2
imports IntFact "~~/src/HOL/Library/Infinite_Set"
begin

text{*
  These are useful for combinatorial and number-theoretic counting
  arguments.
*}


subsection {* Useful properties of sums and products *}

lemma setsum_same_function_zcong:
  assumes a: "\<forall>x \<in> S. [f x = g x](mod m)"
  shows "[setsum f S = setsum g S] (mod m)"
proof cases
  assume "finite S"
  thus ?thesis using a by induct (simp_all add: zcong_zadd)
next
  assume "infinite S" thus ?thesis by(simp add:setsum_def)
qed

lemma setprod_same_function_zcong:
  assumes a: "\<forall>x \<in> S. [f x = g x](mod m)"
  shows "[setprod f S = setprod g S] (mod m)"
proof cases
  assume "finite S"
  thus ?thesis using a by induct (simp_all add: zcong_zmult)
next
  assume "infinite S" thus ?thesis by(simp add:setprod_def)
qed

lemma setsum_const: "finite X ==> setsum (%x. (c :: int)) X = c * int(card X)"
  apply (induct set: finite)
  apply (auto simp add: distrib_right distrib_left)
  done

lemma setsum_const2: "finite X ==> int (setsum (%x. (c :: nat)) X) =
    int(c) * int(card X)"
  apply (induct set: finite)
  apply (auto simp add: distrib_left)
  done

lemma setsum_const_mult: "finite A ==> setsum (%x. c * ((f x)::int)) A =
    c * setsum f A"
  by (induct set: finite) (auto simp add: distrib_left)


subsection {* Cardinality of explicit finite sets *}

lemma finite_surjI: "[| B \<subseteq> f ` A; finite A |] ==> finite B"
by (simp add: finite_subset)

lemma bdd_nat_set_l_finite: "finite {y::nat . y < x}"
  by (rule bounded_nat_set_is_finite) blast

lemma bdd_nat_set_le_finite: "finite {y::nat . y \<le> x}"
proof -
  have "{y::nat . y \<le> x} = {y::nat . y < Suc x}" by auto
  then show ?thesis by (auto simp add: bdd_nat_set_l_finite)
qed

lemma  bdd_int_set_l_finite: "finite {x::int. 0 \<le> x & x < n}"
  apply (subgoal_tac " {(x :: int). 0 \<le> x & x < n} \<subseteq>
      int ` {(x :: nat). x < nat n}")
   apply (erule finite_surjI)
   apply (auto simp add: bdd_nat_set_l_finite image_def)
  apply (rule_tac x = "nat x" in exI, simp)
  done

lemma bdd_int_set_le_finite: "finite {x::int. 0 \<le> x & x \<le> n}"
  apply (subgoal_tac "{x. 0 \<le> x & x \<le> n} = {x. 0 \<le> x & x < n + 1}")
   apply (erule ssubst)
   apply (rule bdd_int_set_l_finite)
  apply auto
  done

lemma bdd_int_set_l_l_finite: "finite {x::int. 0 < x & x < n}"
proof -
  have "{x::int. 0 < x & x < n} \<subseteq> {x::int. 0 \<le> x & x < n}"
    by auto
  then show ?thesis by (auto simp add: bdd_int_set_l_finite finite_subset)
qed

lemma bdd_int_set_l_le_finite: "finite {x::int. 0 < x & x \<le> n}"
proof -
  have "{x::int. 0 < x & x \<le> n} \<subseteq> {x::int. 0 \<le> x & x \<le> n}"
    by auto
  then show ?thesis by (auto simp add: bdd_int_set_le_finite finite_subset)
qed

lemma card_bdd_nat_set_l: "card {y::nat . y < x} = x"
proof (induct x)
  case 0
  show "card {y::nat . y < 0} = 0" by simp
next
  case (Suc n)
  have "{y. y < Suc n} = insert n {y. y < n}"
    by auto
  then have "card {y. y < Suc n} = card (insert n {y. y < n})"
    by auto
  also have "... = Suc (card {y. y < n})"
    by (rule card_insert_disjoint) (auto simp add: bdd_nat_set_l_finite)
  finally show "card {y. y < Suc n} = Suc n"
    using `card {y. y < n} = n` by simp
qed

lemma card_bdd_nat_set_le: "card { y::nat. y \<le> x} = Suc x"
proof -
  have "{y::nat. y \<le> x} = { y::nat. y < Suc x}"
    by auto
  then show ?thesis by (auto simp add: card_bdd_nat_set_l)
qed

lemma card_bdd_int_set_l: "0 \<le> (n::int) ==> card {y. 0 \<le> y & y < n} = nat n"
proof -
  assume "0 \<le> n"
  have "inj_on (%y. int y) {y. y < nat n}"
    by (auto simp add: inj_on_def)
  hence "card (int ` {y. y < nat n}) = card {y. y < nat n}"
    by (rule card_image)
  also from `0 \<le> n` have "int ` {y. y < nat n} = {y. 0 \<le> y & y < n}"
    apply (auto simp add: zless_nat_eq_int_zless image_def)
    apply (rule_tac x = "nat x" in exI)
    apply (auto simp add: nat_0_le)
    done
  also have "card {y. y < nat n} = nat n"
    by (rule card_bdd_nat_set_l)
  finally show "card {y. 0 \<le> y & y < n} = nat n" .
qed

lemma card_bdd_int_set_le: "0 \<le> (n::int) ==> card {y. 0 \<le> y & y \<le> n} =
  nat n + 1"
proof -
  assume "0 \<le> n"
  moreover have "{y. 0 \<le> y & y \<le> n} = {y. 0 \<le> y & y < n+1}" by auto
  ultimately show ?thesis
    using card_bdd_int_set_l [of "n + 1"]
    by (auto simp add: nat_add_distrib)
qed

lemma card_bdd_int_set_l_le: "0 \<le> (n::int) ==>
    card {x. 0 < x & x \<le> n} = nat n"
proof -
  assume "0 \<le> n"
  have "inj_on (%x. x+1) {x. 0 \<le> x & x < n}"
    by (auto simp add: inj_on_def)
  hence "card ((%x. x+1) ` {x. 0 \<le> x & x < n}) =
     card {x. 0 \<le> x & x < n}"
    by (rule card_image)
  also from `0 \<le> n` have "... = nat n"
    by (rule card_bdd_int_set_l)
  also have "(%x. x + 1) ` {x. 0 \<le> x & x < n} = {x. 0 < x & x<= n}"
    apply (auto simp add: image_def)
    apply (rule_tac x = "x - 1" in exI)
    apply arith
    done
  finally show "card {x. 0 < x & x \<le> n} = nat n" .
qed

lemma card_bdd_int_set_l_l: "0 < (n::int) ==>
  card {x. 0 < x & x < n} = nat n - 1"
proof -
  assume "0 < n"
  moreover have "{x. 0 < x & x < n} = {x. 0 < x & x \<le> n - 1}"
    by simp
  ultimately show ?thesis
    using insert card_bdd_int_set_l_le [of "n - 1"]
    by (auto simp add: nat_diff_distrib)
qed

lemma int_card_bdd_int_set_l_l: "0 < n ==>
    int(card {x. 0 < x & x < n}) = n - 1"
  apply (auto simp add: card_bdd_int_set_l_l)
  done

lemma int_card_bdd_int_set_l_le: "0 \<le> n ==>
    int(card {x. 0 < x & x \<le> n}) = n"
  by (auto simp add: card_bdd_int_set_l_le)


subsection {* Cardinality of finite cartesian products *}

(* FIXME could be useful in general but not needed here
lemma insert_Sigma [simp]: "(insert x A) <*> B = ({ x } <*> B) \<union> (A <*> B)"
  by blast
 *)

text {* Lemmas for counting arguments. *}

lemma setsum_bij_eq: "[| finite A; finite B; f ` A \<subseteq> B; inj_on f A;
    g ` B \<subseteq> A; inj_on g B |] ==> setsum g B = setsum (g \<circ> f) A"
  apply (frule_tac h = g and f = f in setsum_reindex)
  apply (subgoal_tac "setsum g B = setsum g (f ` A)")
   apply (simp add: inj_on_def)
  apply (subgoal_tac "card A = card B")
   apply (drule_tac A = "f ` A" and B = B in card_seteq)
     apply (auto simp add: card_image)
  apply (frule_tac A = A and B = B and f = f in card_inj_on_le, auto)
  apply (frule_tac A = B and B = A and f = g in card_inj_on_le)
    apply auto
  done

lemma setprod_bij_eq: "[| finite A; finite B; f ` A \<subseteq> B; inj_on f A;
    g ` B \<subseteq> A; inj_on g B |] ==> setprod g B = setprod (g \<circ> f) A"
  apply (frule_tac h = g and f = f in setprod_reindex)
  apply (subgoal_tac "setprod g B = setprod g (f ` A)")
   apply (simp add: inj_on_def)
  apply (subgoal_tac "card A = card B")
   apply (drule_tac A = "f ` A" and B = B in card_seteq)
     apply (auto simp add: card_image)
  apply (frule_tac A = A and B = B and f = f in card_inj_on_le, auto)
  apply (frule_tac A = B and B = A and f = g in card_inj_on_le, auto)
  done

end
