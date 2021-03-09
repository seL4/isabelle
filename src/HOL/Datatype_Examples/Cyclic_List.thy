theory Cyclic_List imports
  "HOL-Library.Confluent_Quotient"
begin

inductive cyclic1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" for xs where
  "cyclic1 xs (rotate1 xs)"

abbreviation cyclic :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cyclic \<equiv> equivclp cyclic1"

lemma cyclic_mapI: "cyclic xs ys \<Longrightarrow> cyclic (map f xs) (map f ys)"
  by(induction rule: equivclp_induct)
    (auto 4 4 elim!: cyclic1.cases simp add: rotate1_map[symmetric] intro: equivclp_into_equivclp cyclic1.intros)

quotient_type 'a cyclic_list = "'a list" / cyclic by simp

lemma map_respect_cyclic: includes lifting_syntax shows
  "((=) ===> cyclic ===> cyclic) map map"
  by(auto simp add: rel_fun_def cyclic_mapI)

lemma confluentp_cyclic1: "confluentp cyclic1"
  by(intro strong_confluentp_imp_confluentp strong_confluentpI)(auto simp add: cyclic1.simps)

lemma cyclic_set_eq: "cyclic xs ys \<Longrightarrow> set xs = set ys"
  by(induction rule: converse_equivclp_induct)(simp_all add: cyclic1.simps, safe, simp_all)

lemma retract_cyclic1:
  assumes "cyclic1 (map f xs) ys"
  shows "\<exists>zs. cyclic xs zs \<and> ys = map f zs \<and> set zs \<subseteq> set xs"
  using assms by(force simp add: cyclic1.simps rotate1_map intro: cyclic1.intros symclpI1)

lemma confluent_quotient_cyclic1:
  "confluent_quotient cyclic1 cyclic cyclic cyclic cyclic cyclic (map fst) (map snd) (map fst) (map snd) list_all2 list_all2 list_all2 set set"
  by(unfold_locales)
    (auto dest: retract_cyclic1 cyclic_set_eq simp add: list.in_rel list.rel_compp map_respect_cyclic[THEN rel_funD, OF refl] confluentp_cyclic1 intro: rtranclp_mono[THEN predicate2D, OF symclp_greater])

lift_bnf 'a cyclic_list
  subgoal by(rule confluent_quotient.subdistributivity[OF confluent_quotient_cyclic1])
  subgoal by(force dest: cyclic_set_eq)
  done

end
