(* Author: Florian Haftmann, TU Muenchen 
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Lists with elements distinct as canonical example for datatype invariants\<close>

theory Dlist
imports Main
begin

subsection \<open>The type of distinct lists\<close>

typedef 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

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

qualified fun wpull :: "('a \<times> 'b) list \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> ('a \<times> 'c) list"
where
  "wpull [] ys = []"
| "wpull xs [] = []"
| "wpull ((a, b) # xs) ((b', c) # ys) =
  (if b \<in> snd ` set xs then
     (a, the (map_of (rev ((b', c) # ys)) b)) # wpull xs ((b', c) # ys)
   else if b' \<in> fst ` set ys then
     (the (map_of (map prod.swap (rev ((a, b) # xs))) b'), c) # wpull ((a, b) # xs) ys
   else (a, c) # wpull xs ys)"

qualified lemma wpull_eq_Nil_iff [simp]: "wpull xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
by(cases "(xs, ys)" rule: wpull.cases) simp_all

qualified lemma wpull_induct
  [consumes 1, 
   case_names Nil left[xs eq in_set IH] right[xs ys eq in_set IH] step[xs ys eq IH] ]:
  assumes eq: "remdups (map snd xs) = remdups (map fst ys)"
  and Nil: "P [] []"
  and left: "\<And>a b xs b' c ys.
    \<lbrakk> b \<in> snd ` set xs; remdups (map snd xs) = remdups (map fst ((b', c) # ys)); 
      (b, the (map_of (rev ((b', c) # ys)) b)) \<in> set ((b', c) # ys); P xs ((b', c) # ys) \<rbrakk>
    \<Longrightarrow> P ((a, b) # xs) ((b', c) # ys)"
  and right: "\<And>a b xs b' c ys.
    \<lbrakk> b \<notin> snd ` set xs; b' \<in> fst ` set ys;
      remdups (map snd ((a, b) # xs)) = remdups (map fst ys);
      (the (map_of (map prod.swap (rev ((a, b) #xs))) b'), b') \<in> set ((a, b) # xs);
      P ((a, b) # xs) ys \<rbrakk>
    \<Longrightarrow> P ((a, b) # xs) ((b', c) # ys)"
  and step: "\<And>a b xs c ys.
    \<lbrakk> b \<notin> snd ` set xs; b \<notin> fst ` set ys; remdups (map snd xs) = remdups (map fst ys); 
      P xs ys \<rbrakk>
    \<Longrightarrow> P ((a, b) # xs) ((b, c) # ys)"
  shows "P xs ys"
using eq
proof(induction xs ys rule: wpull.induct)
  case 1 thus ?case by(simp add: Nil)
next
  case 2 thus ?case by(simp split: if_split_asm)
next
  case Cons: (3 a b xs b' c ys)
  let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
  consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
    | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
  thus ?case
  proof cases
    case xs
    with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ?ys)" by auto
    from xs eq have "b \<in> fst ` set ?ys" by (metis list.set_map set_remdups)
    hence "map_of (rev ?ys) b \<noteq> None" unfolding map_of_eq_None_iff by auto
    then obtain c' where "map_of (rev ?ys) b = Some c'" by blast
    then have "(b, the (map_of (rev ?ys) b)) \<in> set ?ys" by(auto dest: map_of_SomeD split: if_split_asm)
    from xs eq this Cons.IH(1)[OF xs eq] show ?thesis by(rule left)
  next
    case ys
    from ys Cons.prems have eq: "remdups (map snd ?xs) = remdups (map fst ys)" by auto
    from ys eq have "b' \<in> snd ` set ?xs" by (metis list.set_map set_remdups)
    hence "map_of (map prod.swap (rev ?xs)) b' \<noteq> None"
      unfolding map_of_eq_None_iff by(auto simp add: image_image)
    then obtain a' where "map_of (map prod.swap (rev ?xs)) b' = Some a'" by blast
    then have "(the (map_of (map prod.swap (rev ?xs)) b'), b') \<in> set ?xs"
      by(auto dest: map_of_SomeD split: if_split_asm)
    from ys eq this Cons.IH(2)[OF ys eq] show ?thesis by(rule right)
  next
    case *: step
    hence "remdups (map snd xs) = remdups (map fst ys)" "b = b'" using Cons.prems by auto
    from * this(1) Cons.IH(3)[OF * this(1)] show ?thesis unfolding \<open>b = b'\<close> by(rule step)
  qed
qed

qualified lemma set_wpull_subset:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "set (wpull xs ys) \<subseteq> set xs O set ys"
using assms by(induction xs ys rule: wpull_induct) auto

qualified lemma set_fst_wpull:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "fst ` set (wpull xs ys) = fst ` set xs"
using assms by(induction xs ys rule: wpull_induct)(auto intro: rev_image_eqI)

qualified lemma set_snd_wpull:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "snd ` set (wpull xs ys) = snd ` set ys"
using assms by(induction xs ys rule: wpull_induct)(auto intro: rev_image_eqI)
  
qualified lemma wpull:
  assumes "distinct xs"
  and "distinct ys"
  and "set xs \<subseteq> {(x, y). R x y}"
  and "set ys \<subseteq> {(x, y). S x y}"
  and eq: "remdups (map snd xs) = remdups (map fst ys)"
  shows "\<exists>zs. distinct zs \<and> set zs \<subseteq> {(x, y). (R OO S) x y} \<and>
         remdups (map fst zs) = remdups (map fst xs) \<and> remdups (map snd zs) = remdups (map snd ys)"
proof(intro exI conjI)
  let ?zs = "remdups (wpull xs ys)"
  show "distinct ?zs" by simp
  show "set ?zs \<subseteq> {(x, y). (R OO S) x y}" using assms(3-4) set_wpull_subset[OF eq] by fastforce
  show "remdups (map fst ?zs) = remdups (map fst xs)" unfolding remdups_map_remdups using eq
    by(induction xs ys rule: wpull_induct)(auto simp add: set_fst_wpull intro: rev_image_eqI)
  show "remdups (map snd ?zs) = remdups (map snd ys)" unfolding remdups_map_remdups using eq
    by(induction xs ys rule: wpull_induct)(auto simp add: set_snd_wpull intro: rev_image_eqI)
qed

qualified lift_definition set :: "'a dlist \<Rightarrow> 'a set" is List.set .

qualified lemma map_transfer [transfer_rule]:
  "(rel_fun (=) (rel_fun (pcr_dlist (=)) (pcr_dlist (=)))) (\<lambda>f x. remdups (List.map f x)) Dlist.map"
by(simp add: rel_fun_def dlist.pcr_cr_eq cr_dlist_def Dlist.map_def remdups_remdups)

bnf "'a dlist"
  map: Dlist.map
  sets: set
  bd: natLeq
  wits: Dlist.empty
unfolding OO_Grp_alt mem_Collect_eq
subgoal by(rule ext)(simp add: dlist_eq_iff)
subgoal by(rule ext)(simp add: dlist_eq_iff remdups_map_remdups)
subgoal by(simp add: dlist_eq_iff set_def cong: list.map_cong)
subgoal by(simp add: set_def fun_eq_iff)
subgoal by(simp add: natLeq_card_order)
subgoal by(simp add: natLeq_cinfinite)
subgoal by(rule ordLess_imp_ordLeq)(simp add: finite_iff_ordLess_natLeq[symmetric] set_def)
subgoal by(rule predicate2I)(transfer; auto simp add: wpull)
subgoal by(simp add: set_def)
done

lifting_update dlist.lifting
lifting_forget dlist.lifting

end

end
