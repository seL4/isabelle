(*  Title:      HOL/Quotient_Examples/DList.thy
    Author:     Cezary Kaliszyk, University of Tsukuba

Based on typedef version "Library/Dlist" by Florian Haftmann
and theory morphism version by Maksym Bortin
*)

header {* Lists with distinct elements *}

theory DList
imports "~~/src/HOL/Library/Quotient_List"
begin

text {* Some facts about lists *}

lemma remdups_removeAll_commute[simp]:
  "remdups (removeAll x l) = removeAll x (remdups l)"
  by (induct l) auto

lemma removeAll_distinct[simp]:
  assumes "distinct l"
  shows "distinct (removeAll x l)"
  using assms by (induct l) simp_all

lemma removeAll_commute:
  "removeAll x (removeAll y l) = removeAll y (removeAll x l)"
  by (induct l) auto

lemma remdups_hd_notin_tl:
  "remdups dl = h # t \<Longrightarrow> h \<notin> set t"
  by (induct dl arbitrary: h t)
     (case_tac [!] "a \<in> set dl", auto)

lemma remdups_repeat:
  "remdups dl = h # t \<Longrightarrow> t = remdups t"
  by (induct dl arbitrary: h t, case_tac [!] "a \<in> set dl")
     (simp_all, metis remdups_remdups)

lemma remdups_nil_noteq_cons:
  "remdups (h # t) \<noteq> remdups []"
  "remdups [] \<noteq> remdups (h # t)"
  by auto

lemma remdups_eq_map_eq:
  assumes "remdups xa = remdups ya"
    shows "remdups (map f xa) = remdups (map f ya)"
  using assms
  by (induct xa ya rule: list_induct2')
     (metis (full_types) remdups_nil_noteq_cons(2) remdups_map_remdups)+

lemma remdups_eq_member_eq:
  assumes "remdups xa = remdups ya"
    shows "List.member xa = List.member ya"
  using assms
  unfolding fun_eq_iff List.member_def
  by (induct xa ya rule: list_induct2')
     (metis remdups_nil_noteq_cons set_remdups)+

text {* Setting up the quotient type *}

definition
  dlist_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  [simp]: "dlist_eq xs ys \<longleftrightarrow> remdups xs = remdups ys"

lemma dlist_eq_reflp:
  "reflp dlist_eq"
  by (auto intro: reflpI)

lemma dlist_eq_symp:
  "symp dlist_eq"
  by (auto intro: sympI)

lemma dlist_eq_transp:
  "transp dlist_eq"
  by (auto intro: transpI)

lemma dlist_eq_equivp:
  "equivp dlist_eq"
  by (auto intro: equivpI dlist_eq_reflp dlist_eq_symp dlist_eq_transp)

quotient_type
  'a dlist = "'a list" / "dlist_eq"
  by (rule dlist_eq_equivp)

text {* respectfulness and constant definitions *}

definition [simp]: "card_remdups = length \<circ> remdups"
definition [simp]: "foldr_remdups f xs e = foldr f (remdups xs) e"

lemma [quot_respect]:
  "(dlist_eq) Nil Nil"
  "(dlist_eq ===> op =) List.member List.member"
  "(op = ===> dlist_eq ===> dlist_eq) Cons Cons"
  "(op = ===> dlist_eq ===> dlist_eq) removeAll removeAll"
  "(dlist_eq ===> op =) card_remdups card_remdups"
  "(dlist_eq ===> op =) remdups remdups"
  "(op = ===> dlist_eq ===> op =) foldr_remdups foldr_remdups"
  "(op = ===> dlist_eq ===> dlist_eq) map map"
  "(op = ===> dlist_eq ===> dlist_eq) filter filter"
  by (auto intro!: fun_relI simp add: remdups_filter)
     (metis (full_types) set_remdups remdups_eq_map_eq remdups_eq_member_eq)+

quotient_definition empty where "empty :: 'a dlist"
  is "Nil"

quotient_definition insert where "insert :: 'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
  is "Cons"

quotient_definition "member :: 'a dlist \<Rightarrow> 'a \<Rightarrow> bool"
  is "List.member"

quotient_definition foldr where "foldr :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b"
  is "foldr_remdups"

quotient_definition "remove :: 'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
  is "removeAll"

quotient_definition card where "card :: 'a dlist \<Rightarrow> nat"
  is "card_remdups"

quotient_definition map where "map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist"
  is "List.map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"

quotient_definition filter where "filter :: ('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
  is "List.filter"

quotient_definition "list_of_dlist :: 'a dlist \<Rightarrow> 'a list"
  is "remdups"

text {* lifted theorems *}

lemma dlist_member_insert:
  "member dl x \<Longrightarrow> insert x dl = dl"
  by descending (simp add: List.member_def)

lemma dlist_member_insert_eq:
  "member (insert y dl) x = (x = y \<or> member dl x)"
  by descending (simp add: List.member_def)

lemma dlist_insert_idem:
  "insert x (insert x dl) = insert x dl"
  by descending simp

lemma dlist_insert_not_empty:
  "insert x dl \<noteq> empty"
  by descending auto

lemma not_dlist_member_empty:
  "\<not> member empty x"
  by descending (simp add: List.member_def)

lemma not_dlist_member_remove:
  "\<not> member (remove x dl) x"
  by descending (simp add: List.member_def)

lemma dlist_in_remove:
  "a \<noteq> b \<Longrightarrow> member (remove b dl) a = member dl a"
  by descending (simp add: List.member_def)

lemma dlist_not_memb_remove:
  "\<not> member dl x \<Longrightarrow> remove x dl = dl"
  by descending (simp add: List.member_def)

lemma dlist_no_memb_remove_insert:
"\<not> member dl x \<Longrightarrow> remove x (insert x dl) = dl"
  by descending (simp add: List.member_def)

lemma dlist_remove_empty:
  "remove x empty = empty"
  by descending simp

lemma dlist_remove_insert_commute:
  "a \<noteq> b \<Longrightarrow> remove a (insert b dl) = insert b (remove a dl)"
  by descending simp

lemma dlist_remove_commute:
"remove a (remove b dl) = remove b (remove a dl)"
  by (lifting removeAll_commute)

lemma dlist_foldr_empty:
  "foldr f empty e = e"
  by descending simp

lemma dlist_no_memb_foldr:
  assumes "\<not> member dl x"
  shows "foldr f (insert x dl) e = f x (foldr f dl e)"
  using assms by descending (simp add: List.member_def)

lemma dlist_foldr_insert_not_memb:
  assumes "\<not>member t h"
  shows "foldr f (insert h t) e = f h (foldr f t e)"
  using assms by descending (simp add: List.member_def)

lemma list_of_dlist_empty[simp]:
  "list_of_dlist empty = []"
  by descending simp

lemma list_of_dlist_insert[simp]:
  "list_of_dlist (insert x xs) =
    (if member xs x then (remdups (list_of_dlist xs))
    else x # (remdups (list_of_dlist xs)))"
  by descending (simp add: List.member_def remdups_remdups)

lemma list_of_dlist_remove[simp]:
  "list_of_dlist (remove x dxs) = remove1 x (list_of_dlist dxs)"
  by descending (simp add: distinct_remove1_removeAll)

lemma list_of_dlist_map[simp]:
  "list_of_dlist (map f dxs) = remdups (List.map f (list_of_dlist dxs))"
  by descending (simp add: remdups_map_remdups)

lemma list_of_dlist_filter [simp]:
  "list_of_dlist (filter P dxs) = List.filter P (list_of_dlist dxs)"
  by descending (simp add: remdups_filter)

lemma dlist_map_empty:
  "map f empty = empty"
  by descending simp

lemma dlist_map_insert:
  "map f (insert x xs) = insert (f x) (map f xs)"
  by descending simp

lemma dlist_eq_iff:
  "dxs = dys \<longleftrightarrow> list_of_dlist dxs = list_of_dlist dys"
  by descending simp

lemma dlist_eqI:
  "list_of_dlist dxs = list_of_dlist dys \<Longrightarrow> dxs = dys"
  by (simp add: dlist_eq_iff)

abbreviation
  "dlist xs \<equiv> abs_dlist xs"

lemma distinct_list_of_dlist [simp, intro]:
  "distinct (list_of_dlist dxs)"
  by descending simp

lemma list_of_dlist_dlist [simp]:
  "list_of_dlist (dlist xs) = remdups xs"
  unfolding list_of_dlist_def map_fun_apply id_def
  by (metis Quotient_rep_abs[OF Quotient_dlist] dlist_eq_def)

lemma remdups_list_of_dlist [simp]:
  "remdups (list_of_dlist dxs) = list_of_dlist dxs"
  by simp

lemma dlist_list_of_dlist [simp, code abstype]:
  "dlist (list_of_dlist dxs) = dxs"
  by (simp add: list_of_dlist_def)
  (metis Quotient_def Quotient_dlist dlist_eqI list_of_dlist_dlist remdups_list_of_dlist)

lemma dlist_filter_simps:
  "filter P empty = empty"
  "filter P (insert x xs) = (if P x then insert x (filter P xs) else filter P xs)"
  by (lifting filter.simps)

lemma dlist_induct:
  assumes "P empty"
      and "\<And>a dl. P dl \<Longrightarrow> P (insert a dl)"
    shows "P dl"
  using assms by descending (drule list.induct, simp)

lemma dlist_induct_stronger:
  assumes a1: "P empty"
  and     a2: "\<And>x dl. \<lbrakk>\<not>member dl x; P dl\<rbrakk> \<Longrightarrow> P (insert x dl)"
  shows "P dl"
proof(induct dl rule: dlist_induct)
  show "P empty" using a1 by simp
next
  fix x dl
  assume "P dl"
  then show "P (insert x dl)" using a2
    by (cases "member dl x") (simp_all add: dlist_member_insert)
qed

lemma dlist_card_induct:
  assumes "\<And>xs. (\<And>ys. card ys < card xs \<Longrightarrow> P ys) \<Longrightarrow> P xs"
    shows "P xs"
  using assms
  by descending (rule measure_induct [of card_remdups], blast)

lemma dlist_cases:
  "dl = empty \<or> (\<exists>h t. dl = insert h t \<and> \<not> member t h)"
  apply (descending, simp add: List.member_def)
  by (metis list.exhaust remdups_eq_nil_iff remdups_hd_notin_tl remdups_repeat)

lemma dlist_exhaust:
  assumes "y = empty \<Longrightarrow> P"
      and "\<And>a dl. y = insert a dl \<Longrightarrow> P"
    shows "P"
  using assms by (lifting list.exhaust)

lemma dlist_exhaust_stronger:
  assumes "y = empty \<Longrightarrow> P"
      and "\<And>a dl. y = insert a dl \<Longrightarrow> \<not> member dl a \<Longrightarrow> P"
    shows "P"
  using assms by (metis dlist_cases)

end
