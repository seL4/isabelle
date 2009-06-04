(* Author: Florian Haftmann, TU Muenchen *)

header {* Trees implementing mappings. *}

theory Tree
imports Mapping
begin

subsection {* Type definition and operations *}

datatype ('a, 'b) tree = Empty
  | Branch 'b 'a "('a, 'b) tree" "('a, 'b) tree"

primrec lookup :: "('a\<Colon>linorder, 'b) tree \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "lookup Empty = (\<lambda>_. None)"
  | "lookup (Branch v k l r) = (\<lambda>k'. if k' = k then Some v
       else if k' \<le> k then lookup l k' else lookup r k')"

primrec update :: "'a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "update k v Empty = Branch v k Empty Empty"
  | "update k' v' (Branch v k l r) = (if k' = k then
      Branch v' k l r else if k' \<le> k
      then Branch v k (update k' v' l) r
      else Branch v k l (update k' v' r))"

primrec keys :: "('a\<Colon>linorder, 'b) tree \<Rightarrow> 'a list" where
  "keys Empty = []"
  | "keys (Branch _ k l r) = k # keys l @ keys r"

definition size :: "('a\<Colon>linorder, 'b) tree \<Rightarrow> nat" where
  "size t = length (filter (\<lambda>x. x \<noteq> None) (map (lookup t) (remdups (keys t))))"

fun bulkload :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) tree" where
  [simp del]: "bulkload ks f = (case ks of [] \<Rightarrow> Empty | _ \<Rightarrow> let
     mid = length ks div 2;
     ys = take mid ks;
     x = ks ! mid;
     zs = drop (Suc mid) ks
   in Branch (f x) x (bulkload ys f) (bulkload zs f))"


subsection {* Properties *}

lemma dom_lookup:
  "dom (Tree.lookup t) = set (filter (\<lambda>k. lookup t k \<noteq> None) (remdups (keys t)))"
proof -
  have "dom (Tree.lookup t) = set (filter (\<lambda>k. lookup t k \<noteq> None) (keys t))"
  by (induct t) (auto simp add: dom_if)
  also have "\<dots> = set (filter (\<lambda>k. lookup t k \<noteq> None) (remdups (keys t)))"
    by simp
  finally show ?thesis .
qed

lemma lookup_finite:
  "finite (dom (lookup t))"
  unfolding dom_lookup by simp

lemma lookup_update:
  "lookup (update k v t) = (lookup t)(k \<mapsto> v)"
  by (induct t) (simp_all add: expand_fun_eq)

lemma lookup_bulkload:
  "sorted ks \<Longrightarrow> lookup (bulkload ks f) = (Some o f) |` set ks"
proof (induct ks f rule: bulkload.induct)
  case (1 ks f) show ?case proof (cases ks)
    case Nil then show ?thesis by (simp add: bulkload.simps)
  next
    case (Cons w ws)
    then have case_simp: "\<And>w v::('a, 'b) tree. (case ks of [] \<Rightarrow> v | _ \<Rightarrow> w) = w"
      by (cases ks) auto
    from Cons have "ks \<noteq> []" by simp
    then have "0 < length ks" by simp
    let ?mid = "length ks div 2"
    let ?ys = "take ?mid ks"
    let ?x = "ks ! ?mid"
    let ?zs = "drop (Suc ?mid) ks"
    from `ks \<noteq> []` have ks_split: "ks = ?ys @ [?x] @ ?zs"
      by (simp add: id_take_nth_drop)
    then have in_ks: "\<And>x. x \<in> set ks \<longleftrightarrow> x \<in> set (?ys @ [?x] @ ?zs)"
      by simp
    with ks_split have ys_x: "\<And>y. y \<in> set ?ys \<Longrightarrow> y \<le> ?x"
      and x_zs: "\<And>z. z \<in> set ?zs \<Longrightarrow> ?x \<le> z"
    using `sorted ks` sorted_append [of "?ys" "[?x] @ ?zs"] sorted_append [of "[?x]" "?zs"]
      by simp_all
    have ys: "lookup (bulkload ?ys f) = (Some o f) |` set ?ys"
      by (rule "1.hyps"(1)) (auto intro: Cons sorted_take `sorted ks`)
    have zs: "lookup (bulkload ?zs f) = (Some o f) |` set ?zs"
      by (rule "1.hyps"(2)) (auto intro: Cons sorted_drop `sorted ks`)
    show ?thesis using `0 < length ks`
      by (simp add: bulkload.simps)
        (auto simp add: restrict_map_def in_ks case_simp Let_def ys zs expand_fun_eq
           dest: in_set_takeD in_set_dropD ys_x x_zs)
  qed
qed


subsection {* Trees as mappings *}

definition Tree :: "('a\<Colon>linorder, 'b) tree \<Rightarrow> ('a, 'b) map" where
  "Tree t = Map (Tree.lookup t)"

lemma [code, code del]:
  "(eq_class.eq :: (_, _) map \<Rightarrow> _) = eq_class.eq" ..

lemma [code, code del]:
  "Mapping.delete k m = Mapping.delete k m" ..

code_datatype Tree

lemma empty_Tree [code]:
  "Mapping.empty = Tree Empty"
  by (simp add: Tree_def Mapping.empty_def)

lemma lookup_Tree [code]:
  "Mapping.lookup (Tree t) = lookup t"
  by (simp add: Tree_def)

lemma update_Tree [code]:
  "Mapping.update k v (Tree t) = Tree (update k v t)"
  by (simp add: Tree_def lookup_update)

lemma keys_Tree [code]:
  "Mapping.keys (Tree t) = set (filter (\<lambda>k. lookup t k \<noteq> None) (remdups (keys t)))"
  by (simp add: Tree_def dom_lookup)

lemma size_Tree [code]:
  "Mapping.size (Tree t) = size t"
proof -
  have "card (dom (Tree.lookup t)) = length (filter (\<lambda>x. x \<noteq> None) (map (lookup t) (remdups (keys t))))"
    unfolding dom_lookup by (subst distinct_card) (auto simp add: comp_def)
  then show ?thesis by (auto simp add: Tree_def Mapping.size_def size_def)
qed

lemma tabulate_Tree [code]:
  "Mapping.tabulate ks f = Tree (bulkload (sort ks) f)"
proof -
  have "Mapping.lookup (Mapping.tabulate ks f) = Mapping.lookup (Tree (bulkload (sort ks) f))"
    by (simp add: lookup_Tree lookup_bulkload lookup_tabulate)
  then show ?thesis by (simp add: lookup_inject)
qed

end
