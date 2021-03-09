(* Author: Florian Haftmann, TU Muenchen
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Lists with elements distinct as canonical example for datatype invariants\<close>

theory Dlist
imports Confluent_Quotient
begin

subsection \<open>The type of distinct lists\<close>

typedef 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

context begin

qualified definition dlist_eq where "dlist_eq = BNF_Def.vimage2p remdups remdups (=)"

qualified lemma equivp_dlist_eq: "equivp dlist_eq"
  unfolding dlist_eq_def by(rule equivp_vimage2p)(rule identity_equivp)

qualified definition abs_dlist :: "'a list \<Rightarrow> 'a dlist" where "abs_dlist = Abs_dlist o remdups"

definition qcr_dlist :: "'a list \<Rightarrow> 'a dlist \<Rightarrow> bool" where "qcr_dlist x y \<longleftrightarrow> y = abs_dlist x"

qualified lemma Quotient_dlist_remdups: "Quotient dlist_eq abs_dlist list_of_dlist qcr_dlist"
  unfolding Quotient_def dlist_eq_def qcr_dlist_def vimage2p_def abs_dlist_def
  by (auto simp add: fun_eq_iff Abs_dlist_inject
    list_of_dlist[simplified] list_of_dlist_inverse distinct_remdups_id)

end

locale Quotient_dlist begin
setup_lifting Dlist.Quotient_dlist_remdups Dlist.equivp_dlist_eq[THEN equivp_reflp2]
end

setup_lifting type_definition_dlist

lemma dlist_eq_iff:
  "dxs = dys \<longleftrightarrow> list_of_dlist dxs = list_of_dlist dys"
  by (simp add: list_of_dlist_inject)

lemma dlist_eqI:
  "list_of_dlist dxs = list_of_dlist dys \<Longrightarrow> dxs = dys"
  by (simp add: dlist_eq_iff)

text \<open>Formal, totalized constructor for \<^typ>\<open>'a dlist\<close>:\<close>

definition Dlist :: "'a list \<Rightarrow> 'a dlist" where
  "Dlist xs = Abs_dlist (remdups xs)"

lemma distinct_list_of_dlist [simp, intro]:
  "distinct (list_of_dlist dxs)"
  using list_of_dlist [of dxs] by simp

lemma list_of_dlist_Dlist [simp]:
  "list_of_dlist (Dlist xs) = remdups xs"
  by (simp add: Dlist_def Abs_dlist_inverse)

lemma remdups_list_of_dlist [simp]:
  "remdups (list_of_dlist dxs) = list_of_dlist dxs"
  by simp

lemma Dlist_list_of_dlist [simp, code abstype]:
  "Dlist (list_of_dlist dxs) = dxs"
  by (simp add: Dlist_def list_of_dlist_inverse distinct_remdups_id)


text \<open>Fundamental operations:\<close>

context
begin

qualified definition empty :: "'a dlist" where
  "empty = Dlist []"

qualified definition insert :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "insert x dxs = Dlist (List.insert x (list_of_dlist dxs))"

qualified definition remove :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "remove x dxs = Dlist (remove1 x (list_of_dlist dxs))"

qualified definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist" where
  "map f dxs = Dlist (remdups (List.map f (list_of_dlist dxs)))"

qualified definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "filter P dxs = Dlist (List.filter P (list_of_dlist dxs))"

qualified definition rotate :: "nat \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "rotate n dxs = Dlist (List.rotate n (list_of_dlist dxs))"

end


text \<open>Derived operations:\<close>

context
begin

qualified definition null :: "'a dlist \<Rightarrow> bool" where
  "null dxs = List.null (list_of_dlist dxs)"

qualified definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" where
  "member dxs = List.member (list_of_dlist dxs)"

qualified definition length :: "'a dlist \<Rightarrow> nat" where
  "length dxs = List.length (list_of_dlist dxs)"

qualified definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f dxs = List.fold f (list_of_dlist dxs)"

qualified definition foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "foldr f dxs = List.foldr f (list_of_dlist dxs)"

end


subsection \<open>Executable version obeying invariant\<close>

lemma list_of_dlist_empty [simp, code abstract]:
  "list_of_dlist Dlist.empty = []"
  by (simp add: Dlist.empty_def)

lemma list_of_dlist_insert [simp, code abstract]:
  "list_of_dlist (Dlist.insert x dxs) = List.insert x (list_of_dlist dxs)"
  by (simp add: Dlist.insert_def)

lemma list_of_dlist_remove [simp, code abstract]:
  "list_of_dlist (Dlist.remove x dxs) = remove1 x (list_of_dlist dxs)"
  by (simp add: Dlist.remove_def)

lemma list_of_dlist_map [simp, code abstract]:
  "list_of_dlist (Dlist.map f dxs) = remdups (List.map f (list_of_dlist dxs))"
  by (simp add: Dlist.map_def)

lemma list_of_dlist_filter [simp, code abstract]:
  "list_of_dlist (Dlist.filter P dxs) = List.filter P (list_of_dlist dxs)"
  by (simp add: Dlist.filter_def)

lemma list_of_dlist_rotate [simp, code abstract]:
  "list_of_dlist (Dlist.rotate n dxs) = List.rotate n (list_of_dlist dxs)"
  by (simp add: Dlist.rotate_def)


text \<open>Explicit executable conversion\<close>

definition dlist_of_list [simp]:
  "dlist_of_list = Dlist"

lemma [code abstract]:
  "list_of_dlist (dlist_of_list xs) = remdups xs"
  by simp


text \<open>Equality\<close>

instantiation dlist :: (equal) equal
begin

definition "HOL.equal dxs dys \<longleftrightarrow> HOL.equal (list_of_dlist dxs) (list_of_dlist dys)"

instance
  by standard (simp add: equal_dlist_def equal list_of_dlist_inject)

end

declare equal_dlist_def [code]

lemma [code nbe]: "HOL.equal (dxs :: 'a::equal dlist) dxs \<longleftrightarrow> True"
  by (fact equal_refl)


subsection \<open>Induction principle and case distinction\<close>

lemma dlist_induct [case_names empty insert, induct type: dlist]:
  assumes empty: "P Dlist.empty"
  assumes insrt: "\<And>x dxs. \<not> Dlist.member dxs x \<Longrightarrow> P dxs \<Longrightarrow> P (Dlist.insert x dxs)"
  shows "P dxs"
proof (cases dxs)
  case (Abs_dlist xs)
  then have "distinct xs" and dxs: "dxs = Dlist xs"
    by (simp_all add: Dlist_def distinct_remdups_id)
  from \<open>distinct xs\<close> have "P (Dlist xs)"
  proof (induct xs)
    case Nil from empty show ?case by (simp add: Dlist.empty_def)
  next
    case (Cons x xs)
    then have "\<not> Dlist.member (Dlist xs) x" and "P (Dlist xs)"
      by (simp_all add: Dlist.member_def List.member_def)
    with insrt have "P (Dlist.insert x (Dlist xs))" .
    with Cons show ?case by (simp add: Dlist.insert_def distinct_remdups_id)
  qed
  with dxs show "P dxs" by simp
qed

lemma dlist_case [cases type: dlist]:
  obtains (empty) "dxs = Dlist.empty"
    | (insert) x dys where "\<not> Dlist.member dys x" and "dxs = Dlist.insert x dys"
proof (cases dxs)
  case (Abs_dlist xs)
  then have dxs: "dxs = Dlist xs" and distinct: "distinct xs"
    by (simp_all add: Dlist_def distinct_remdups_id)
  show thesis
  proof (cases xs)
    case Nil with dxs
    have "dxs = Dlist.empty" by (simp add: Dlist.empty_def)
    with empty show ?thesis .
  next
    case (Cons x xs)
    with dxs distinct have "\<not> Dlist.member (Dlist xs) x"
      and "dxs = Dlist.insert x (Dlist xs)"
      by (simp_all add: Dlist.member_def List.member_def Dlist.insert_def distinct_remdups_id)
    with insert show ?thesis .
  qed
qed


subsection \<open>Functorial structure\<close>

functor map: map
  by (simp_all add: remdups_map_remdups fun_eq_iff dlist_eq_iff)


subsection \<open>Quickcheck generators\<close>

quickcheck_generator dlist predicate: distinct constructors: Dlist.empty, Dlist.insert

subsection \<open>BNF instance\<close>

context begin

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

qualified lemma dlist_eq_into_doubles: "Dlist.dlist_eq \<le> equivclp double"
  by(auto 4 4 simp add: Dlist.dlist_eq_def vimage2p_def
     intro: equivclp_trans converse_rtranclp_into_equivclp rtranclp_into_equivclp remdups_into_doubles)

qualified lemma factor_double_map: "double (map f xs) ys \<Longrightarrow> \<exists>zs. Dlist.dlist_eq xs zs \<and> ys = map f zs \<and> set zs \<subseteq> set xs"
  by(auto simp add: double.simps Dlist.dlist_eq_def vimage2p_def map_eq_append_conv)
    (metis (no_types, hide_lams) list.simps(9) map_append remdups.simps(2) remdups_append2 set_append set_eq_subset set_remdups)

qualified lemma dlist_eq_set_eq: "Dlist.dlist_eq xs ys \<Longrightarrow> set xs = set ys"
  by(simp add: Dlist.dlist_eq_def vimage2p_def)(metis set_remdups)

qualified lemma dlist_eq_map_respect: "Dlist.dlist_eq xs ys \<Longrightarrow> Dlist.dlist_eq (map f xs) (map f ys)"
  by(clarsimp simp add: Dlist.dlist_eq_def vimage2p_def)(metis remdups_map_remdups)

qualified lemma confluent_quotient_dlist:
  "confluent_quotient double Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq
     (map fst) (map snd) (map fst) (map snd) list_all2 list_all2 list_all2 set set"
  by(unfold_locales)(auto intro: strong_confluentp_imp_confluentp strong_confluentp_double
    dest: factor_double_map dlist_eq_into_doubles[THEN predicate2D] dlist_eq_set_eq
    simp add: list.in_rel list.rel_compp dlist_eq_map_respect Dlist.equivp_dlist_eq equivp_imp_transp)

lifting_update dlist.lifting
lifting_forget dlist.lifting

end

context begin
interpretation Quotient_dlist: Quotient_dlist .

lift_bnf (plugins del: code) 'a dlist
  subgoal for A B by(rule confluent_quotient.subdistributivity[OF Dlist.confluent_quotient_dlist])
  subgoal by(force dest: Dlist.dlist_eq_set_eq intro: equivp_reflp[OF Dlist.equivp_dlist_eq])
  done

qualified lemma list_of_dlist_transfer[transfer_rule]:
  "bi_unique R \<Longrightarrow> (rel_fun (Quotient_dlist.pcr_dlist R) (list_all2 R)) remdups list_of_dlist"
  unfolding rel_fun_def Quotient_dlist.pcr_dlist_def qcr_dlist_def Dlist.abs_dlist_def
  by (auto simp: Abs_dlist_inverse intro!: remdups_transfer[THEN rel_funD])

lemma list_of_dlist_map_dlist[simp]:
  "list_of_dlist (map_dlist f xs) = remdups (map f (list_of_dlist xs))"
  by transfer (auto simp: remdups_map_remdups)

end


end
