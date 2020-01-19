theory Dlist imports
  "HOL-Library.Confluent_Quotient"
begin

context begin

qualified definition dlist_eq where "dlist_eq = BNF_Def.vimage2p remdups remdups (=)"

lemma equivp_dlist_eq: "equivp dlist_eq"
  unfolding dlist_eq_def by(rule equivp_vimage2p)(rule identity_equivp)

quotient_type 'a dlist = "'a list" / dlist_eq
  by (rule equivp_dlist_eq)

qualified inductive double :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "double (xs @ ys) (xs @ x # ys)" if "x \<in> set ys"

qualified lemma strong_confluentp_double: "strong_confluentp double"
proof
  fix xs ys zs :: "'a list"
  assume ys: "double xs ys" and zs: "double xs zs"
  consider (left) as y bs z cs where "xs = as @ bs @ cs" "ys = as @ y # bs @ cs" "zs = as @ bs @ z # cs" "y \<in> set (bs @ cs)" "z \<in> set cs"
    | (right) as y bs z cs where "xs = as @ bs @ cs" "ys = as @ bs @ y # cs" "zs = as @ z # bs @ cs" "y \<in> set cs" "z \<in> set (bs @ cs)"
  proof -
    show thesis using ys zs
      by(clarsimp simp add: double.simps append_eq_append_conv2)(auto intro: that)
  qed
  then show "\<exists>us. double\<^sup>*\<^sup>* ys us \<and> double\<^sup>=\<^sup>= zs us"
  proof cases
    case left
    let ?us = "as @ y # bs @ z # cs"
    have "double ys ?us" "double zs ?us" using left
      by(auto 4 4 simp add: double.simps)(metis append_Cons append_assoc)+
    then show ?thesis by blast
  next
    case right
    let ?us = "as @ z # bs @ y # cs"
    have "double ys ?us" "double zs ?us" using right
      by(auto 4 4 simp add: double.simps)(metis append_Cons append_assoc)+
    then show ?thesis by blast
  qed
qed

qualified lemma double_Cons1 [simp]: "double xs (x # xs)" if "x \<in> set xs"
  using double.intros[of x xs "[]"] that by simp

qualified lemma double_Cons_same [simp]: "double xs ys \<Longrightarrow> double (x # xs) (x # ys)"
  by(auto simp add: double.simps Cons_eq_append_conv)

qualified lemma doubles_Cons_same: "double\<^sup>*\<^sup>* xs ys \<Longrightarrow> double\<^sup>*\<^sup>* (x # xs) (x # ys)"
  by(induction rule: rtranclp_induct)(auto intro: rtranclp.rtrancl_into_rtrancl)

qualified lemma remdups_into_doubles: "double\<^sup>*\<^sup>* (remdups xs) xs"
  by(induction xs)(auto intro: doubles_Cons_same rtranclp.rtrancl_into_rtrancl)

qualified lemma dlist_eq_into_doubles: "dlist_eq \<le> equivclp double"
  by(auto 4 4 simp add: dlist_eq_def vimage2p_def
     intro: equivclp_trans converse_rtranclp_into_equivclp rtranclp_into_equivclp remdups_into_doubles)

qualified lemma factor_double_map: "double (map f xs) ys \<Longrightarrow> \<exists>zs. dlist_eq xs zs \<and> ys = map f zs"
  by(auto simp add: double.simps dlist_eq_def vimage2p_def map_eq_append_conv)
    (metis list.simps(9) map_append remdups.simps(2) remdups_append2)

qualified lemma dlist_eq_set_eq: "dlist_eq xs ys \<Longrightarrow> set xs = set ys"
  by(simp add: dlist_eq_def vimage2p_def)(metis set_remdups)

qualified lemma dlist_eq_map_respect: "dlist_eq xs ys \<Longrightarrow> dlist_eq (map f xs) (map f ys)"
  by(clarsimp simp add: dlist_eq_def vimage2p_def)(metis remdups_map_remdups)

qualified lemma confluent_quotient_dlist:
  "confluent_quotient double dlist_eq dlist_eq dlist_eq dlist_eq dlist_eq (map fst) (map snd) (map fst) (map snd) list_all2 list_all2 list_all2 set set"
  by(unfold_locales)(auto intro: strong_confluentp_imp_confluentp strong_confluentp_double dest: factor_double_map dlist_eq_into_doubles[THEN predicate2D] dlist_eq_set_eq simp add: list.in_rel list.rel_compp dlist_eq_map_respect equivp_dlist_eq equivp_imp_transp)

lift_bnf 'a dlist [wits: "[]"]
  subgoal for A B by(rule confluent_quotient.subdistributivity[OF confluent_quotient_dlist])
  subgoal by(force dest: dlist_eq_set_eq intro: equivp_reflp[OF equivp_dlist_eq])
  subgoal by(auto simp add: dlist_eq_def vimage2p_def)
  done

end

end
