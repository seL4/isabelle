(*  Title:      HOL/Library/RBT_Impl.thy
    Author:     Markus Reiter, TU Muenchen
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Implementation of Red-Black Trees *}

theory RBT_Impl
imports Main
begin

text {*
  For applications, you should use theory @{text RBT} which defines
  an abstract type of red-black tree obeying the invariant.
*}

subsection {* Datatype of RB trees *}

datatype color = R | B
datatype ('a, 'b) rbt = Empty | Branch color "('a, 'b) rbt" 'a 'b "('a, 'b) rbt"

lemma rbt_cases:
  obtains (Empty) "t = Empty" 
  | (Red) l k v r where "t = Branch R l k v r" 
  | (Black) l k v r where "t = Branch B l k v r"
proof (cases t)
  case Empty with that show thesis by blast
next
  case (Branch c) with that show thesis by (cases c) blast+
qed

subsection {* Tree properties *}

subsubsection {* Content of a tree *}

primrec entries :: "('a, 'b) rbt \<Rightarrow> ('a \<times> 'b) list"
where 
  "entries Empty = []"
| "entries (Branch _ l k v r) = entries l @ (k,v) # entries r"

abbreviation (input) entry_in_tree :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"
where
  "entry_in_tree k v t \<equiv> (k, v) \<in> set (entries t)"

definition keys :: "('a, 'b) rbt \<Rightarrow> 'a list" where
  "keys t = map fst (entries t)"

lemma keys_simps [simp, code]:
  "keys Empty = []"
  "keys (Branch c l k v r) = keys l @ k # keys r"
  by (simp_all add: keys_def)

lemma entry_in_tree_keys:
  assumes "(k, v) \<in> set (entries t)"
  shows "k \<in> set (keys t)"
proof -
  from assms have "fst (k, v) \<in> fst ` set (entries t)" by (rule imageI)
  then show ?thesis by (simp add: keys_def)
qed

lemma keys_entries:
  "k \<in> set (keys t) \<longleftrightarrow> (\<exists>v. (k, v) \<in> set (entries t))"
  by (auto intro: entry_in_tree_keys) (auto simp add: keys_def)


subsubsection {* Search tree properties *}

definition tree_less :: "'a\<Colon>order \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"
where
  tree_less_prop: "tree_less k t \<longleftrightarrow> (\<forall>x\<in>set (keys t). x < k)"

abbreviation tree_less_symbol (infix "|\<guillemotleft>" 50)
where "t |\<guillemotleft> x \<equiv> tree_less x t"

definition tree_greater :: "'a\<Colon>order \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool" (infix "\<guillemotleft>|" 50) 
where
  tree_greater_prop: "tree_greater k t = (\<forall>x\<in>set (keys t). k < x)"

lemma tree_less_simps [simp]:
  "tree_less k Empty = True"
  "tree_less k (Branch c lt kt v rt) \<longleftrightarrow> kt < k \<and> tree_less k lt \<and> tree_less k rt"
  by (auto simp add: tree_less_prop)

lemma tree_greater_simps [simp]:
  "tree_greater k Empty = True"
  "tree_greater k (Branch c lt kt v rt) \<longleftrightarrow> k < kt \<and> tree_greater k lt \<and> tree_greater k rt"
  by (auto simp add: tree_greater_prop)

lemmas tree_ord_props = tree_less_prop tree_greater_prop

lemmas tree_greater_nit = tree_greater_prop entry_in_tree_keys
lemmas tree_less_nit = tree_less_prop entry_in_tree_keys

lemma tree_less_eq_trans: "l |\<guillemotleft> u \<Longrightarrow> u \<le> v \<Longrightarrow> l |\<guillemotleft> v"
  and tree_less_trans: "t |\<guillemotleft> x \<Longrightarrow> x < y \<Longrightarrow> t |\<guillemotleft> y"
  and tree_greater_eq_trans: "u \<le> v \<Longrightarrow> v \<guillemotleft>| r \<Longrightarrow> u \<guillemotleft>| r"
  and tree_greater_trans: "x < y \<Longrightarrow> y \<guillemotleft>| t \<Longrightarrow> x \<guillemotleft>| t"
  by (auto simp: tree_ord_props)

primrec sorted :: "('a::linorder, 'b) rbt \<Rightarrow> bool"
where
  "sorted Empty = True"
| "sorted (Branch c l k v r) = (l |\<guillemotleft> k \<and> k \<guillemotleft>| r \<and> sorted l \<and> sorted r)"

lemma sorted_entries:
  "sorted t \<Longrightarrow> List.sorted (List.map fst (entries t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons tree_ord_props 
      dest!: entry_in_tree_keys)+

lemma distinct_entries:
  "sorted t \<Longrightarrow> distinct (List.map fst (entries t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons tree_ord_props 
      dest!: entry_in_tree_keys)+


subsubsection {* Tree lookup *}

primrec lookup :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "lookup Empty k = None"
| "lookup (Branch _ l x y r) k = (if k < x then lookup l k else if x < k then lookup r k else Some y)"

lemma lookup_keys: "sorted t \<Longrightarrow> dom (lookup t) = set (keys t)"
  by (induct t) (auto simp: dom_def tree_greater_prop tree_less_prop)

lemma dom_lookup_Branch: 
  "sorted (Branch c t1 k v t2) \<Longrightarrow> 
    dom (lookup (Branch c t1 k v t2)) 
    = Set.insert k (dom (lookup t1) \<union> dom (lookup t2))"
proof -
  assume "sorted (Branch c t1 k v t2)"
  moreover from this have "sorted t1" "sorted t2" by simp_all
  ultimately show ?thesis by (simp add: lookup_keys)
qed

lemma finite_dom_lookup [simp, intro!]: "finite (dom (lookup t))"
proof (induct t)
  case Empty then show ?case by simp
next
  case (Branch color t1 a b t2)
  let ?A = "Set.insert a (dom (lookup t1) \<union> dom (lookup t2))"
  have "dom (lookup (Branch color t1 a b t2)) \<subseteq> ?A" by (auto split: split_if_asm)
  moreover from Branch have "finite (insert a (dom (lookup t1) \<union> dom (lookup t2)))" by simp
  ultimately show ?case by (rule finite_subset)
qed 

lemma lookup_tree_less[simp]: "t |\<guillemotleft> k \<Longrightarrow> lookup t k = None" 
by (induct t) auto

lemma lookup_tree_greater[simp]: "k \<guillemotleft>| t \<Longrightarrow> lookup t k = None"
by (induct t) auto

lemma lookup_Empty: "lookup Empty = empty"
by (rule ext) simp

lemma map_of_entries:
  "sorted t \<Longrightarrow> map_of (entries t) = lookup t"
proof (induct t)
  case Empty thus ?case by (simp add: lookup_Empty)
next
  case (Branch c t1 k v t2)
  have "lookup (Branch c t1 k v t2) = lookup t2 ++ [k\<mapsto>v] ++ lookup t1"
  proof (rule ext)
    fix x
    from Branch have SORTED: "sorted (Branch c t1 k v t2)" by simp
    let ?thesis = "lookup (Branch c t1 k v t2) x = (lookup t2 ++ [k \<mapsto> v] ++ lookup t1) x"

    have DOM_T1: "!!k'. k'\<in>dom (lookup t1) \<Longrightarrow> k>k'"
    proof -
      fix k'
      from SORTED have "t1 |\<guillemotleft> k" by simp
      with tree_less_prop have "\<forall>k'\<in>set (keys t1). k>k'" by auto
      moreover assume "k'\<in>dom (lookup t1)"
      ultimately show "k>k'" using lookup_keys SORTED by auto
    qed
    
    have DOM_T2: "!!k'. k'\<in>dom (lookup t2) \<Longrightarrow> k<k'"
    proof -
      fix k'
      from SORTED have "k \<guillemotleft>| t2" by simp
      with tree_greater_prop have "\<forall>k'\<in>set (keys t2). k<k'" by auto
      moreover assume "k'\<in>dom (lookup t2)"
      ultimately show "k<k'" using lookup_keys SORTED by auto
    qed
    
    {
      assume C: "x<k"
      hence "lookup (Branch c t1 k v t2) x = lookup t1 x" by simp
      moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
      moreover have "x\<notin>dom (lookup t2)" proof
        assume "x\<in>dom (lookup t2)"
        with DOM_T2 have "k<x" by blast
        with C show False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } moreover {
      assume [simp]: "x=k"
      hence "lookup (Branch c t1 k v t2) x = [k \<mapsto> v] x" by simp
      moreover have "x\<notin>dom (lookup t1)" proof
        assume "x\<in>dom (lookup t1)"
        with DOM_T1 have "k>x" by blast
        thus False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } moreover {
      assume C: "x>k"
      hence "lookup (Branch c t1 k v t2) x = lookup t2 x" by (simp add: less_not_sym[of k x])
      moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
      moreover have "x\<notin>dom (lookup t1)" proof
        assume "x\<in>dom (lookup t1)"
        with DOM_T1 have "k>x" by simp
        with C show False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } ultimately show ?thesis using less_linear by blast
  qed
  also from Branch have "lookup t2 ++ [k \<mapsto> v] ++ lookup t1 = map_of (entries (Branch c t1 k v t2))" by simp
  finally show ?case by simp
qed

lemma lookup_in_tree: "sorted t \<Longrightarrow> lookup t k = Some v \<longleftrightarrow> (k, v) \<in> set (entries t)"
  by (simp add: map_of_entries [symmetric] distinct_entries)

lemma set_entries_inject:
  assumes sorted: "sorted t1" "sorted t2" 
  shows "set (entries t1) = set (entries t2) \<longleftrightarrow> entries t1 = entries t2"
proof -
  from sorted have "distinct (map fst (entries t1))"
    "distinct (map fst (entries t2))"
    by (auto intro: distinct_entries)
  with sorted show ?thesis
    by (auto intro: map_sorted_distinct_set_unique sorted_entries simp add: distinct_map)
qed

lemma entries_eqI:
  assumes sorted: "sorted t1" "sorted t2" 
  assumes lookup: "lookup t1 = lookup t2"
  shows "entries t1 = entries t2"
proof -
  from sorted lookup have "map_of (entries t1) = map_of (entries t2)"
    by (simp add: map_of_entries)
  with sorted have "set (entries t1) = set (entries t2)"
    by (simp add: map_of_inject_set distinct_entries)
  with sorted show ?thesis by (simp add: set_entries_inject)
qed

lemma entries_lookup:
  assumes "sorted t1" "sorted t2" 
  shows "entries t1 = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
  using assms by (auto intro: entries_eqI simp add: map_of_entries [symmetric])

lemma lookup_from_in_tree: 
  assumes "sorted t1" "sorted t2" 
  and "\<And>v. (k\<Colon>'a\<Colon>linorder, v) \<in> set (entries t1) \<longleftrightarrow> (k, v) \<in> set (entries t2)" 
  shows "lookup t1 k = lookup t2 k"
proof -
  from assms have "k \<in> dom (lookup t1) \<longleftrightarrow> k \<in> dom (lookup t2)"
    by (simp add: keys_entries lookup_keys)
  with assms show ?thesis by (auto simp add: lookup_in_tree [symmetric])
qed


subsubsection {* Red-black properties *}

primrec color_of :: "('a, 'b) rbt \<Rightarrow> color"
where
  "color_of Empty = B"
| "color_of (Branch c _ _ _ _) = c"

primrec bheight :: "('a,'b) rbt \<Rightarrow> nat"
where
  "bheight Empty = 0"
| "bheight (Branch c lt k v rt) = (if c = B then Suc (bheight lt) else bheight lt)"

primrec inv1 :: "('a, 'b) rbt \<Rightarrow> bool"
where
  "inv1 Empty = True"
| "inv1 (Branch c lt k v rt) \<longleftrightarrow> inv1 lt \<and> inv1 rt \<and> (c = B \<or> color_of lt = B \<and> color_of rt = B)"

primrec inv1l :: "('a, 'b) rbt \<Rightarrow> bool" -- {* Weaker version *}
where
  "inv1l Empty = True"
| "inv1l (Branch c l k v r) = (inv1 l \<and> inv1 r)"
lemma [simp]: "inv1 t \<Longrightarrow> inv1l t" by (cases t) simp+

primrec inv2 :: "('a, 'b) rbt \<Rightarrow> bool"
where
  "inv2 Empty = True"
| "inv2 (Branch c lt k v rt) = (inv2 lt \<and> inv2 rt \<and> bheight lt = bheight rt)"

definition is_rbt :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> bool" where
  "is_rbt t \<longleftrightarrow> inv1 t \<and> inv2 t \<and> color_of t = B \<and> sorted t"

lemma is_rbt_sorted [simp]:
  "is_rbt t \<Longrightarrow> sorted t" by (simp add: is_rbt_def)

theorem Empty_is_rbt [simp]:
  "is_rbt Empty" by (simp add: is_rbt_def)


subsection {* Insertion *}

fun (* slow, due to massive case splitting *)
  balance :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balance (Branch R a w x b) s t (Branch R c y z d) = Branch R (Branch B a w x b) s t (Branch B c y z d)" |
  "balance (Branch R (Branch R a w x b) s t c) y z d = Branch R (Branch B a w x b) s t (Branch B c y z d)" |
  "balance (Branch R a w x (Branch R b s t c)) y z d = Branch R (Branch B a w x b) s t (Branch B c y z d)" |
  "balance a w x (Branch R b s t (Branch R c y z d)) = Branch R (Branch B a w x b) s t (Branch B c y z d)" |
  "balance a w x (Branch R (Branch R b s t c) y z d) = Branch R (Branch B a w x b) s t (Branch B c y z d)" |
  "balance a s t b = Branch B a s t b"

lemma balance_inv1: "\<lbrakk>inv1l l; inv1l r\<rbrakk> \<Longrightarrow> inv1 (balance l k v r)" 
  by (induct l k v r rule: balance.induct) auto

lemma balance_bheight: "bheight l = bheight r \<Longrightarrow> bheight (balance l k v r) = Suc (bheight l)"
  by (induct l k v r rule: balance.induct) auto

lemma balance_inv2: 
  assumes "inv2 l" "inv2 r" "bheight l = bheight r"
  shows "inv2 (balance l k v r)"
  using assms
  by (induct l k v r rule: balance.induct) auto

lemma balance_tree_greater[simp]: "(v \<guillemotleft>| balance a k x b) = (v \<guillemotleft>| a \<and> v \<guillemotleft>| b \<and> v < k)" 
  by (induct a k x b rule: balance.induct) auto

lemma balance_tree_less[simp]: "(balance a k x b |\<guillemotleft> v) = (a |\<guillemotleft> v \<and> b |\<guillemotleft> v \<and> k < v)"
  by (induct a k x b rule: balance.induct) auto

lemma balance_sorted: 
  fixes k :: "'a::linorder"
  assumes "sorted l" "sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "sorted (balance l k v r)"
using assms proof (induct l k v r rule: balance.induct)
  case ("2_2" a x w b y t c z s va vb vd vc)
  hence "y < z \<and> z \<guillemotleft>| Branch B va vb vd vc" 
    by (auto simp add: tree_ord_props)
  hence "tree_greater y (Branch B va vb vd vc)" by (blast dest: tree_greater_trans)
  with "2_2" show ?case by simp
next
  case ("3_2" va vb vd vc x w b y s c z)
  from "3_2" have "x < y \<and> tree_less x (Branch B va vb vd vc)" 
    by simp
  hence "tree_less y (Branch B va vb vd vc)" by (blast dest: tree_less_trans)
  with "3_2" show ?case by simp
next
  case ("3_3" x w b y s c z t va vb vd vc)
  from "3_3" have "y < z \<and> tree_greater z (Branch B va vb vd vc)" by simp
  hence "tree_greater y (Branch B va vb vd vc)" by (blast dest: tree_greater_trans)
  with "3_3" show ?case by simp
next
  case ("3_4" vd ve vg vf x w b y s c z t va vb vii vc)
  hence "x < y \<and> tree_less x (Branch B vd ve vg vf)" by simp
  hence 1: "tree_less y (Branch B vd ve vg vf)" by (blast dest: tree_less_trans)
  from "3_4" have "y < z \<and> tree_greater z (Branch B va vb vii vc)" by simp
  hence "tree_greater y (Branch B va vb vii vc)" by (blast dest: tree_greater_trans)
  with 1 "3_4" show ?case by simp
next
  case ("4_2" va vb vd vc x w b y s c z t dd)
  hence "x < y \<and> tree_less x (Branch B va vb vd vc)" by simp
  hence "tree_less y (Branch B va vb vd vc)" by (blast dest: tree_less_trans)
  with "4_2" show ?case by simp
next
  case ("5_2" x w b y s c z t va vb vd vc)
  hence "y < z \<and> tree_greater z (Branch B va vb vd vc)" by simp
  hence "tree_greater y (Branch B va vb vd vc)" by (blast dest: tree_greater_trans)
  with "5_2" show ?case by simp
next
  case ("5_3" va vb vd vc x w b y s c z t)
  hence "x < y \<and> tree_less x (Branch B va vb vd vc)" by simp
  hence "tree_less y (Branch B va vb vd vc)" by (blast dest: tree_less_trans)
  with "5_3" show ?case by simp
next
  case ("5_4" va vb vg vc x w b y s c z t vd ve vii vf)
  hence "x < y \<and> tree_less x (Branch B va vb vg vc)" by simp
  hence 1: "tree_less y (Branch B va vb vg vc)" by (blast dest: tree_less_trans)
  from "5_4" have "y < z \<and> tree_greater z (Branch B vd ve vii vf)" by simp
  hence "tree_greater y (Branch B vd ve vii vf)" by (blast dest: tree_greater_trans)
  with 1 "5_4" show ?case by simp
qed simp+

lemma entries_balance [simp]:
  "entries (balance l k v r) = entries l @ (k, v) # entries r"
  by (induct l k v r rule: balance.induct) auto

lemma keys_balance [simp]: 
  "keys (balance l k v r) = keys l @ k # keys r"
  by (simp add: keys_def)

lemma balance_in_tree:  
  "entry_in_tree k x (balance l v y r) \<longleftrightarrow> entry_in_tree k x l \<or> k = v \<and> x = y \<or> entry_in_tree k x r"
  by (auto simp add: keys_def)

lemma lookup_balance[simp]: 
fixes k :: "'a::linorder"
assumes "sorted l" "sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
shows "lookup (balance l k v r) x = lookup (Branch B l k v r) x"
by (rule lookup_from_in_tree) (auto simp:assms balance_in_tree balance_sorted)

primrec paint :: "color \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "paint c Empty = Empty"
| "paint c (Branch _ l k v r) = Branch c l k v r"

lemma paint_inv1l[simp]: "inv1l t \<Longrightarrow> inv1l (paint c t)" by (cases t) auto
lemma paint_inv1[simp]: "inv1l t \<Longrightarrow> inv1 (paint B t)" by (cases t) auto
lemma paint_inv2[simp]: "inv2 t \<Longrightarrow> inv2 (paint c t)" by (cases t) auto
lemma paint_color_of[simp]: "color_of (paint B t) = B" by (cases t) auto
lemma paint_sorted[simp]: "sorted t \<Longrightarrow> sorted (paint c t)" by (cases t) auto
lemma paint_in_tree[simp]: "entry_in_tree k x (paint c t) = entry_in_tree k x t" by (cases t) auto
lemma paint_lookup[simp]: "lookup (paint c t) = lookup t" by (rule ext) (cases t, auto)
lemma paint_tree_greater[simp]: "(v \<guillemotleft>| paint c t) = (v \<guillemotleft>| t)" by (cases t) auto
lemma paint_tree_less[simp]: "(paint c t |\<guillemotleft> v) = (t |\<guillemotleft> v)" by (cases t) auto

fun
  ins :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "ins f k v Empty = Branch R Empty k v Empty" |
  "ins f k v (Branch B l x y r) = (if k < x then balance (ins f k v l) x y r
                               else if k > x then balance l x y (ins f k v r)
                               else Branch B l x (f k y v) r)" |
  "ins f k v (Branch R l x y r) = (if k < x then Branch R (ins f k v l) x y r
                               else if k > x then Branch R l x y (ins f k v r)
                               else Branch R l x (f k y v) r)"

lemma ins_inv1_inv2: 
  assumes "inv1 t" "inv2 t"
  shows "inv2 (ins f k x t)" "bheight (ins f k x t) = bheight t" 
  "color_of t = B \<Longrightarrow> inv1 (ins f k x t)" "inv1l (ins f k x t)"
  using assms
  by (induct f k x t rule: ins.induct) (auto simp: balance_inv1 balance_inv2 balance_bheight)

lemma ins_tree_greater[simp]: "(v \<guillemotleft>| ins f k x t) = (v \<guillemotleft>| t \<and> k > v)"
  by (induct f k x t rule: ins.induct) auto
lemma ins_tree_less[simp]: "(ins f k x t |\<guillemotleft> v) = (t |\<guillemotleft> v \<and> k < v)"
  by (induct f k x t rule: ins.induct) auto
lemma ins_sorted[simp]: "sorted t \<Longrightarrow> sorted (ins f k x t)"
  by (induct f k x t rule: ins.induct) (auto simp: balance_sorted)

lemma keys_ins: "set (keys (ins f k v t)) = { k } \<union> set (keys t)"
  by (induct f k v t rule: ins.induct) auto

lemma lookup_ins: 
  fixes k :: "'a::linorder"
  assumes "sorted t"
  shows "lookup (ins f k v t) x = ((lookup t)(k |-> case lookup t k of None \<Rightarrow> v 
                                                       | Some w \<Rightarrow> f k w v)) x"
using assms by (induct f k v t rule: ins.induct) auto

definition
  insert_with_key :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "insert_with_key f k v t = paint B (ins f k v t)"

lemma insertwk_sorted: "sorted t \<Longrightarrow> sorted (insert_with_key f k x t)"
  by (auto simp: insert_with_key_def)

theorem insertwk_is_rbt: 
  assumes inv: "is_rbt t" 
  shows "is_rbt (insert_with_key f k x t)"
using assms
unfolding insert_with_key_def is_rbt_def
by (auto simp: ins_inv1_inv2)

lemma lookup_insertwk: 
  assumes "sorted t"
  shows "lookup (insert_with_key f k v t) x = ((lookup t)(k |-> case lookup t k of None \<Rightarrow> v 
                                                       | Some w \<Rightarrow> f k w v)) x"
unfolding insert_with_key_def using assms
by (simp add:lookup_ins)

definition
  insertw_def: "insert_with f = insert_with_key (\<lambda>_. f)"

lemma insertw_sorted: "sorted t \<Longrightarrow> sorted (insert_with f k v t)" by (simp add: insertwk_sorted insertw_def)
theorem insertw_is_rbt: "is_rbt t \<Longrightarrow> is_rbt (insert_with f k v t)" by (simp add: insertwk_is_rbt insertw_def)

lemma lookup_insertw:
  assumes "is_rbt t"
  shows "lookup (insert_with f k v t) = (lookup t)(k \<mapsto> (if k:dom (lookup t) then f (the (lookup t k)) v else v))"
using assms
unfolding insertw_def
by (rule_tac ext) (cases "lookup t k", auto simp:lookup_insertwk dom_def)

definition insert :: "'a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "insert = insert_with_key (\<lambda>_ _ nv. nv)"

lemma insert_sorted: "sorted t \<Longrightarrow> sorted (insert k v t)" by (simp add: insertwk_sorted insert_def)
theorem insert_is_rbt [simp]: "is_rbt t \<Longrightarrow> is_rbt (insert k v t)" by (simp add: insertwk_is_rbt insert_def)

lemma lookup_insert: 
  assumes "is_rbt t"
  shows "lookup (insert k v t) = (lookup t)(k\<mapsto>v)"
unfolding insert_def
using assms
by (rule_tac ext) (simp add: lookup_insertwk split:option.split)


subsection {* Deletion *}

lemma bheight_paintR'[simp]: "color_of t = B \<Longrightarrow> bheight (paint R t) = bheight t - 1"
by (cases t rule: rbt_cases) auto

fun
  balance_left :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balance_left (Branch R a k x b) s y c = Branch R (Branch B a k x b) s y c" |
  "balance_left bl k x (Branch B a s y b) = balance bl k x (Branch R a s y b)" |
  "balance_left bl k x (Branch R (Branch B a s y b) t z c) = Branch R (Branch B bl k x a) s y (balance b t z (paint R c))" |
  "balance_left t k x s = Empty"

lemma balance_left_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bheight lt + 1 = bheight rt" "inv1 rt"
  shows "bheight (balance_left lt k v rt) = bheight lt + 1"
  and   "inv2 (balance_left lt k v rt)"
using assms 
by (induct lt k v rt rule: balance_left.induct) (auto simp: balance_inv2 balance_bheight)

lemma balance_left_inv2_app: 
  assumes "inv2 lt" "inv2 rt" "bheight lt + 1 = bheight rt" "color_of rt = B"
  shows "inv2 (balance_left lt k v rt)" 
        "bheight (balance_left lt k v rt) = bheight rt"
using assms 
by (induct lt k v rt rule: balance_left.induct) (auto simp add: balance_inv2 balance_bheight)+ 

lemma balance_left_inv1: "\<lbrakk>inv1l a; inv1 b; color_of b = B\<rbrakk> \<Longrightarrow> inv1 (balance_left a k x b)"
  by (induct a k x b rule: balance_left.induct) (simp add: balance_inv1)+

lemma balance_left_inv1l: "\<lbrakk> inv1l lt; inv1 rt \<rbrakk> \<Longrightarrow> inv1l (balance_left lt k x rt)"
by (induct lt k x rt rule: balance_left.induct) (auto simp: balance_inv1)

lemma balance_left_sorted: "\<lbrakk> sorted l; sorted r; tree_less k l; tree_greater k r \<rbrakk> \<Longrightarrow> sorted (balance_left l k v r)"
apply (induct l k v r rule: balance_left.induct)
apply (auto simp: balance_sorted)
apply (unfold tree_greater_prop tree_less_prop)
by force+

lemma balance_left_tree_greater: 
  fixes k :: "'a::order"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balance_left a x t b"
using assms 
by (induct a x t b rule: balance_left.induct) auto

lemma balance_left_tree_less: 
  fixes k :: "'a::order"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balance_left a x t b |\<guillemotleft> k"
using assms
by (induct a x t b rule: balance_left.induct) auto

lemma balance_left_in_tree: 
  assumes "inv1l l" "inv1 r" "bheight l + 1 = bheight r"
  shows "entry_in_tree k v (balance_left l a b r) = (entry_in_tree k v l \<or> k = a \<and> v = b \<or> entry_in_tree k v r)"
using assms 
by (induct l k v r rule: balance_left.induct) (auto simp: balance_in_tree)

fun
  balance_right :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balance_right a k x (Branch R b s y c) = Branch R a k x (Branch B b s y c)" |
  "balance_right (Branch B a k x b) s y bl = balance (Branch R a k x b) s y bl" |
  "balance_right (Branch R a k x (Branch B b s y c)) t z bl = Branch R (balance (paint R a) k x b) s y (Branch B c t z bl)" |
  "balance_right t k x s = Empty"

lemma balance_right_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bheight lt = bheight rt + 1" "inv1 lt"
  shows "inv2 (balance_right lt k v rt) \<and> bheight (balance_right lt k v rt) = bheight lt"
using assms
by (induct lt k v rt rule: balance_right.induct) (auto simp: balance_inv2 balance_bheight)

lemma balance_right_inv1: "\<lbrakk>inv1 a; inv1l b; color_of a = B\<rbrakk> \<Longrightarrow> inv1 (balance_right a k x b)"
by (induct a k x b rule: balance_right.induct) (simp add: balance_inv1)+

lemma balance_right_inv1l: "\<lbrakk> inv1 lt; inv1l rt \<rbrakk> \<Longrightarrow>inv1l (balance_right lt k x rt)"
by (induct lt k x rt rule: balance_right.induct) (auto simp: balance_inv1)

lemma balance_right_sorted: "\<lbrakk> sorted l; sorted r; tree_less k l; tree_greater k r \<rbrakk> \<Longrightarrow> sorted (balance_right l k v r)"
apply (induct l k v r rule: balance_right.induct)
apply (auto simp:balance_sorted)
apply (unfold tree_less_prop tree_greater_prop)
by force+

lemma balance_right_tree_greater: 
  fixes k :: "'a::order"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balance_right a x t b"
using assms by (induct a x t b rule: balance_right.induct) auto

lemma balance_right_tree_less: 
  fixes k :: "'a::order"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balance_right a x t b |\<guillemotleft> k"
using assms by (induct a x t b rule: balance_right.induct) auto

lemma balance_right_in_tree:
  assumes "inv1 l" "inv1l r" "bheight l = bheight r + 1" "inv2 l" "inv2 r"
  shows "entry_in_tree x y (balance_right l k v r) = (entry_in_tree x y l \<or> x = k \<and> y = v \<or> entry_in_tree x y r)"
using assms by (induct l k v r rule: balance_right.induct) (auto simp: balance_in_tree)

fun
  combine :: "('a,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "combine Empty x = x" 
| "combine x Empty = x" 
| "combine (Branch R a k x b) (Branch R c s y d) = (case (combine b c) of
                                      Branch R b2 t z c2 \<Rightarrow> (Branch R (Branch R a k x b2) t z (Branch R c2 s y d)) |
                                      bc \<Rightarrow> Branch R a k x (Branch R bc s y d))" 
| "combine (Branch B a k x b) (Branch B c s y d) = (case (combine b c) of
                                      Branch R b2 t z c2 \<Rightarrow> Branch R (Branch B a k x b2) t z (Branch B c2 s y d) |
                                      bc \<Rightarrow> balance_left a k x (Branch B bc s y d))" 
| "combine a (Branch R b k x c) = Branch R (combine a b) k x c" 
| "combine (Branch R a k x b) c = Branch R a k x (combine b c)" 

lemma combine_inv2:
  assumes "inv2 lt" "inv2 rt" "bheight lt = bheight rt"
  shows "bheight (combine lt rt) = bheight lt" "inv2 (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct) 
   (auto simp: balance_left_inv2_app split: rbt.splits color.splits)

lemma combine_inv1: 
  assumes "inv1 lt" "inv1 rt"
  shows "color_of lt = B \<Longrightarrow> color_of rt = B \<Longrightarrow> inv1 (combine lt rt)"
         "inv1l (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct)
   (auto simp: balance_left_inv1 split: rbt.splits color.splits)

lemma combine_tree_greater[simp]: 
  fixes k :: "'a::linorder"
  assumes "k \<guillemotleft>| l" "k \<guillemotleft>| r" 
  shows "k \<guillemotleft>| combine l r"
using assms 
by (induct l r rule: combine.induct)
   (auto simp: balance_left_tree_greater split:rbt.splits color.splits)

lemma combine_tree_less[simp]: 
  fixes k :: "'a::linorder"
  assumes "l |\<guillemotleft> k" "r |\<guillemotleft> k" 
  shows "combine l r |\<guillemotleft> k"
using assms 
by (induct l r rule: combine.induct)
   (auto simp: balance_left_tree_less split:rbt.splits color.splits)

lemma combine_sorted: 
  fixes k :: "'a::linorder"
  assumes "sorted l" "sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "sorted (combine l r)"
using assms proof (induct l r rule: combine.induct)
  case (3 a x v b c y w d)
  hence ineqs: "a |\<guillemotleft> x" "x \<guillemotleft>| b" "b |\<guillemotleft> k" "k \<guillemotleft>| c" "c |\<guillemotleft> y" "y \<guillemotleft>| d"
    by auto
  with 3
  show ?case
    by (cases "combine b c" rule: rbt_cases)
      (auto, (metis combine_tree_greater combine_tree_less ineqs ineqs tree_less_simps(2) tree_greater_simps(2) tree_greater_trans tree_less_trans)+)
next
  case (4 a x v b c y w d)
  hence "x < k \<and> tree_greater k c" by simp
  hence "tree_greater x c" by (blast dest: tree_greater_trans)
  with 4 have 2: "tree_greater x (combine b c)" by (simp add: combine_tree_greater)
  from 4 have "k < y \<and> tree_less k b" by simp
  hence "tree_less y b" by (blast dest: tree_less_trans)
  with 4 have 3: "tree_less y (combine b c)" by (simp add: combine_tree_less)
  show ?case
  proof (cases "combine b c" rule: rbt_cases)
    case Empty
    from 4 have "x < y \<and> tree_greater y d" by auto
    hence "tree_greater x d" by (blast dest: tree_greater_trans)
    with 4 Empty have "sorted a" and "sorted (Branch B Empty y w d)" and "tree_less x a" and "tree_greater x (Branch B Empty y w d)" by auto
    with Empty show ?thesis by (simp add: balance_left_sorted)
  next
    case (Red lta va ka rta)
    with 2 4 have "x < va \<and> tree_less x a" by simp
    hence 5: "tree_less va a" by (blast dest: tree_less_trans)
    from Red 3 4 have "va < y \<and> tree_greater y d" by simp
    hence "tree_greater va d" by (blast dest: tree_greater_trans)
    with Red 2 3 4 5 show ?thesis by simp
  next
    case (Black lta va ka rta)
    from 4 have "x < y \<and> tree_greater y d" by auto
    hence "tree_greater x d" by (blast dest: tree_greater_trans)
    with Black 2 3 4 have "sorted a" and "sorted (Branch B (combine b c) y w d)" and "tree_less x a" and "tree_greater x (Branch B (combine b c) y w d)" by auto
    with Black show ?thesis by (simp add: balance_left_sorted)
  qed
next
  case (5 va vb vd vc b x w c)
  hence "k < x \<and> tree_less k (Branch B va vb vd vc)" by simp
  hence "tree_less x (Branch B va vb vd vc)" by (blast dest: tree_less_trans)
  with 5 show ?case by (simp add: combine_tree_less)
next
  case (6 a x v b va vb vd vc)
  hence "x < k \<and> tree_greater k (Branch B va vb vd vc)" by simp
  hence "tree_greater x (Branch B va vb vd vc)" by (blast dest: tree_greater_trans)
  with 6 show ?case by (simp add: combine_tree_greater)
qed simp+

lemma combine_in_tree: 
  assumes "inv2 l" "inv2 r" "bheight l = bheight r" "inv1 l" "inv1 r"
  shows "entry_in_tree k v (combine l r) = (entry_in_tree k v l \<or> entry_in_tree k v r)"
using assms 
proof (induct l r rule: combine.induct)
  case (4 _ _ _ b c)
  hence a: "bheight (combine b c) = bheight b" by (simp add: combine_inv2)
  from 4 have b: "inv1l (combine b c)" by (simp add: combine_inv1)

  show ?case
  proof (cases "combine b c" rule: rbt_cases)
    case Empty
    with 4 a show ?thesis by (auto simp: balance_left_in_tree)
  next
    case (Red lta ka va rta)
    with 4 show ?thesis by auto
  next
    case (Black lta ka va rta)
    with a b 4  show ?thesis by (auto simp: balance_left_in_tree)
  qed 
qed (auto split: rbt.splits color.splits)

fun
  del_from_left :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  del_from_right :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  del :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "del x Empty = Empty" |
  "del x (Branch c a y s b) = (if x < y then del_from_left x a y s b else (if x > y then del_from_right x a y s b else combine a b))" |
  "del_from_left x (Branch B lt z v rt) y s b = balance_left (del x (Branch B lt z v rt)) y s b" |
  "del_from_left x a y s b = Branch R (del x a) y s b" |
  "del_from_right x a y s (Branch B lt z v rt) = balance_right a y s (del x (Branch B lt z v rt))" | 
  "del_from_right x a y s b = Branch R a y s (del x b)"

lemma 
  assumes "inv2 lt" "inv1 lt"
  shows
  "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (del_from_left x lt k v rt) \<and> bheight (del_from_left x lt k v rt) = bheight lt \<and> (color_of lt = B \<and> color_of rt = B \<and> inv1 (del_from_left x lt k v rt) \<or> (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (del_from_left x lt k v rt))"
  and "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (del_from_right x lt k v rt) \<and> bheight (del_from_right x lt k v rt) = bheight lt \<and> (color_of lt = B \<and> color_of rt = B \<and> inv1 (del_from_right x lt k v rt) \<or> (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (del_from_right x lt k v rt))"
  and del_inv1_inv2: "inv2 (del x lt) \<and> (color_of lt = R \<and> bheight (del x lt) = bheight lt \<and> inv1 (del x lt) 
  \<or> color_of lt = B \<and> bheight (del x lt) = bheight lt - 1 \<and> inv1l (del x lt))"
using assms
proof (induct x lt k v rt and x lt k v rt and x lt rule: del_from_left_del_from_right_del.induct)
case (2 y c _ y')
  have "y = y' \<or> y < y' \<or> y > y'" by auto
  thus ?case proof (elim disjE)
    assume "y = y'"
    with 2 show ?thesis by (cases c) (simp add: combine_inv2 combine_inv1)+
  next
    assume "y < y'"
    with 2 show ?thesis by (cases c) auto
  next
    assume "y' < y"
    with 2 show ?thesis by (cases c) auto
  qed
next
  case (3 y lt z v rta y' ss bb) 
  thus ?case by (cases "color_of (Branch B lt z v rta) = B \<and> color_of bb = B") (simp add: balance_left_inv2_with_inv1 balance_left_inv1 balance_left_inv1l)+
next
  case (5 y a y' ss lt z v rta)
  thus ?case by (cases "color_of a = B \<and> color_of (Branch B lt z v rta) = B") (simp add: balance_right_inv2_with_inv1 balance_right_inv1 balance_right_inv1l)+
next
  case ("6_1" y a y' ss) thus ?case by (cases "color_of a = B \<and> color_of Empty = B") simp+
qed auto

lemma 
  del_from_left_tree_less: "\<lbrakk>tree_less v lt; tree_less v rt; k < v\<rbrakk> \<Longrightarrow> tree_less v (del_from_left x lt k y rt)"
  and del_from_right_tree_less: "\<lbrakk>tree_less v lt; tree_less v rt; k < v\<rbrakk> \<Longrightarrow> tree_less v (del_from_right x lt k y rt)"
  and del_tree_less: "tree_less v lt \<Longrightarrow> tree_less v (del x lt)"
by (induct x lt k y rt and x lt k y rt and x lt rule: del_from_left_del_from_right_del.induct) 
   (auto simp: balance_left_tree_less balance_right_tree_less)

lemma del_from_left_tree_greater: "\<lbrakk>tree_greater v lt; tree_greater v rt; k > v\<rbrakk> \<Longrightarrow> tree_greater v (del_from_left x lt k y rt)"
  and del_from_right_tree_greater: "\<lbrakk>tree_greater v lt; tree_greater v rt; k > v\<rbrakk> \<Longrightarrow> tree_greater v (del_from_right x lt k y rt)"
  and del_tree_greater: "tree_greater v lt \<Longrightarrow> tree_greater v (del x lt)"
by (induct x lt k y rt and x lt k y rt and x lt rule: del_from_left_del_from_right_del.induct)
   (auto simp: balance_left_tree_greater balance_right_tree_greater)

lemma "\<lbrakk>sorted lt; sorted rt; tree_less k lt; tree_greater k rt\<rbrakk> \<Longrightarrow> sorted (del_from_left x lt k y rt)"
  and "\<lbrakk>sorted lt; sorted rt; tree_less k lt; tree_greater k rt\<rbrakk> \<Longrightarrow> sorted (del_from_right x lt k y rt)"
  and del_sorted: "sorted lt \<Longrightarrow> sorted (del x lt)"
proof (induct x lt k y rt and x lt k y rt and x lt rule: del_from_left_del_from_right_del.induct)
  case (3 x lta zz v rta yy ss bb)
  from 3 have "tree_less yy (Branch B lta zz v rta)" by simp
  hence "tree_less yy (del x (Branch B lta zz v rta))" by (rule del_tree_less)
  with 3 show ?case by (simp add: balance_left_sorted)
next
  case ("4_2" x vaa vbb vdd vc yy ss bb)
  hence "tree_less yy (Branch R vaa vbb vdd vc)" by simp
  hence "tree_less yy (del x (Branch R vaa vbb vdd vc))" by (rule del_tree_less)
  with "4_2" show ?case by simp
next
  case (5 x aa yy ss lta zz v rta) 
  hence "tree_greater yy (Branch B lta zz v rta)" by simp
  hence "tree_greater yy (del x (Branch B lta zz v rta))" by (rule del_tree_greater)
  with 5 show ?case by (simp add: balance_right_sorted)
next
  case ("6_2" x aa yy ss vaa vbb vdd vc)
  hence "tree_greater yy (Branch R vaa vbb vdd vc)" by simp
  hence "tree_greater yy (del x (Branch R vaa vbb vdd vc))" by (rule del_tree_greater)
  with "6_2" show ?case by simp
qed (auto simp: combine_sorted)

lemma "\<lbrakk>sorted lt; sorted rt; tree_less kt lt; tree_greater kt rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bheight lt = bheight rt; x < kt\<rbrakk> \<Longrightarrow> entry_in_tree k v (del_from_left x lt kt y rt) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v (Branch c lt kt y rt)))"
  and "\<lbrakk>sorted lt; sorted rt; tree_less kt lt; tree_greater kt rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bheight lt = bheight rt; x > kt\<rbrakk> \<Longrightarrow> entry_in_tree k v (del_from_right x lt kt y rt) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v (Branch c lt kt y rt)))"
  and del_in_tree: "\<lbrakk>sorted t; inv1 t; inv2 t\<rbrakk> \<Longrightarrow> entry_in_tree k v (del x t) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v t))"
proof (induct x lt kt y rt and x lt kt y rt and x t rule: del_from_left_del_from_right_del.induct)
  case (2 xx c aa yy ss bb)
  have "xx = yy \<or> xx < yy \<or> xx > yy" by auto
  from this 2 show ?case proof (elim disjE)
    assume "xx = yy"
    with 2 show ?thesis proof (cases "xx = k")
      case True
      from 2 `xx = yy` `xx = k` have "sorted (Branch c aa yy ss bb) \<and> k = yy" by simp
      hence "\<not> entry_in_tree k v aa" "\<not> entry_in_tree k v bb" by (auto simp: tree_less_nit tree_greater_prop)
      with `xx = yy` 2 `xx = k` show ?thesis by (simp add: combine_in_tree)
    qed (simp add: combine_in_tree)
  qed simp+
next    
  case (3 xx lta zz vv rta yy ss bb)
  def mt[simp]: mt == "Branch B lta zz vv rta"
  from 3 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (del xx mt) \<and> (color_of mt = R \<and> bheight (del xx mt) = bheight mt \<and> inv1 (del xx mt) \<or> color_of mt = B \<and> bheight (del xx mt) = bheight mt - 1 \<and> inv1l (del xx mt))" by (blast dest: del_inv1_inv2)
  with 3 have 4: "entry_in_tree k v (del_from_left xx mt yy ss bb) = (False \<or> xx \<noteq> k \<and> entry_in_tree k v mt \<or> (k = yy \<and> v = ss) \<or> entry_in_tree k v bb)" by (simp add: balance_left_in_tree)
  thus ?case proof (cases "xx = k")
    case True
    from 3 True have "tree_greater yy bb \<and> yy > k" by simp
    hence "tree_greater k bb" by (blast dest: tree_greater_trans)
    with 3 4 True show ?thesis by (auto simp: tree_greater_nit)
  qed auto
next
  case ("4_1" xx yy ss bb)
  show ?case proof (cases "xx = k")
    case True
    with "4_1" have "tree_greater yy bb \<and> k < yy" by simp
    hence "tree_greater k bb" by (blast dest: tree_greater_trans)
    with "4_1" `xx = k` 
   have "entry_in_tree k v (Branch R Empty yy ss bb) = entry_in_tree k v Empty" by (auto simp: tree_greater_nit)
    thus ?thesis by auto
  qed simp+
next
  case ("4_2" xx vaa vbb vdd vc yy ss bb)
  thus ?case proof (cases "xx = k")
    case True
    with "4_2" have "k < yy \<and> tree_greater yy bb" by simp
    hence "tree_greater k bb" by (blast dest: tree_greater_trans)
    with True "4_2" show ?thesis by (auto simp: tree_greater_nit)
  qed auto
next
  case (5 xx aa yy ss lta zz vv rta)
  def mt[simp]: mt == "Branch B lta zz vv rta"
  from 5 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (del xx mt) \<and> (color_of mt = R \<and> bheight (del xx mt) = bheight mt \<and> inv1 (del xx mt) \<or> color_of mt = B \<and> bheight (del xx mt) = bheight mt - 1 \<and> inv1l (del xx mt))" by (blast dest: del_inv1_inv2)
  with 5 have 3: "entry_in_tree k v (del_from_right xx aa yy ss mt) = (entry_in_tree k v aa \<or> (k = yy \<and> v = ss) \<or> False \<or> xx \<noteq> k \<and> entry_in_tree k v mt)" by (simp add: balance_right_in_tree)
  thus ?case proof (cases "xx = k")
    case True
    from 5 True have "tree_less yy aa \<and> yy < k" by simp
    hence "tree_less k aa" by (blast dest: tree_less_trans)
    with 3 5 True show ?thesis by (auto simp: tree_less_nit)
  qed auto
next
  case ("6_1" xx aa yy ss)
  show ?case proof (cases "xx = k")
    case True
    with "6_1" have "tree_less yy aa \<and> k > yy" by simp
    hence "tree_less k aa" by (blast dest: tree_less_trans)
    with "6_1" `xx = k` show ?thesis by (auto simp: tree_less_nit)
  qed simp
next
  case ("6_2" xx aa yy ss vaa vbb vdd vc)
  thus ?case proof (cases "xx = k")
    case True
    with "6_2" have "k > yy \<and> tree_less yy aa" by simp
    hence "tree_less k aa" by (blast dest: tree_less_trans)
    with True "6_2" show ?thesis by (auto simp: tree_less_nit)
  qed auto
qed simp


definition delete where
  delete_def: "delete k t = paint B (del k t)"

theorem delete_is_rbt [simp]: assumes "is_rbt t" shows "is_rbt (delete k t)"
proof -
  from assms have "inv2 t" and "inv1 t" unfolding is_rbt_def by auto 
  hence "inv2 (del k t) \<and> (color_of t = R \<and> bheight (del k t) = bheight t \<and> inv1 (del k t) \<or> color_of t = B \<and> bheight (del k t) = bheight t - 1 \<and> inv1l (del k t))" by (rule del_inv1_inv2)
  hence "inv2 (del k t) \<and> inv1l (del k t)" by (cases "color_of t") auto
  with assms show ?thesis
    unfolding is_rbt_def delete_def
    by (auto intro: paint_sorted del_sorted)
qed

lemma delete_in_tree: 
  assumes "is_rbt t" 
  shows "entry_in_tree k v (delete x t) = (x \<noteq> k \<and> entry_in_tree k v t)"
  using assms unfolding is_rbt_def delete_def
  by (auto simp: del_in_tree)

lemma lookup_delete:
  assumes is_rbt: "is_rbt t"
  shows "lookup (delete k t) = (lookup t)|`(-{k})"
proof
  fix x
  show "lookup (delete k t) x = (lookup t |` (-{k})) x" 
  proof (cases "x = k")
    assume "x = k" 
    with is_rbt show ?thesis
      by (cases "lookup (delete k t) k") (auto simp: lookup_in_tree delete_in_tree)
  next
    assume "x \<noteq> k"
    thus ?thesis
      by auto (metis is_rbt delete_is_rbt delete_in_tree is_rbt_sorted lookup_from_in_tree)
  qed
qed


subsection {* Union *}

primrec
  union_with_key :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "union_with_key f t Empty = t"
| "union_with_key f t (Branch c lt k v rt) = union_with_key f (union_with_key f (insert_with_key f k v t) lt) rt"

lemma unionwk_sorted: "sorted lt \<Longrightarrow> sorted (union_with_key f lt rt)" 
  by (induct rt arbitrary: lt) (auto simp: insertwk_sorted)
theorem unionwk_is_rbt[simp]: "is_rbt lt \<Longrightarrow> is_rbt (union_with_key f lt rt)" 
  by (induct rt arbitrary: lt) (simp add: insertwk_is_rbt)+

definition
  union_with where
  "union_with f = union_with_key (\<lambda>_. f)"

theorem unionw_is_rbt: "is_rbt lt \<Longrightarrow> is_rbt (union_with f lt rt)" unfolding union_with_def by simp

definition union where
  "union = union_with_key (%_ _ rv. rv)"

theorem union_is_rbt: "is_rbt lt \<Longrightarrow> is_rbt (union lt rt)" unfolding union_def by simp

lemma union_Branch[simp]:
  "union t (Branch c lt k v rt) = union (union (insert k v t) lt) rt"
  unfolding union_def insert_def
  by simp

lemma lookup_union:
  assumes "is_rbt s" "sorted t"
  shows "lookup (union s t) = lookup s ++ lookup t"
using assms
proof (induct t arbitrary: s)
  case Empty thus ?case by (auto simp: union_def)
next
  case (Branch c l k v r s)
  then have "sorted r" "sorted l" "l |\<guillemotleft> k" "k \<guillemotleft>| r" by auto

  have meq: "lookup s(k \<mapsto> v) ++ lookup l ++ lookup r =
    lookup s ++
    (\<lambda>a. if a < k then lookup l a
    else if k < a then lookup r a else Some v)" (is "?m1 = ?m2")
  proof (rule ext)
    fix a

   have "k < a \<or> k = a \<or> k > a" by auto
    thus "?m1 a = ?m2 a"
    proof (elim disjE)
      assume "k < a"
      with `l |\<guillemotleft> k` have "l |\<guillemotleft> a" by (rule tree_less_trans)
      with `k < a` show ?thesis
        by (auto simp: map_add_def split: option.splits)
    next
      assume "k = a"
      with `l |\<guillemotleft> k` `k \<guillemotleft>| r` 
      show ?thesis by (auto simp: map_add_def)
    next
      assume "a < k"
      from this `k \<guillemotleft>| r` have "a \<guillemotleft>| r" by (rule tree_greater_trans)
      with `a < k` show ?thesis
        by (auto simp: map_add_def split: option.splits)
    qed
  qed

  from Branch have is_rbt: "is_rbt (RBT_Impl.union (RBT_Impl.insert k v s) l)"
    by (auto intro: union_is_rbt insert_is_rbt)
  with Branch have IHs:
    "lookup (union (union (insert k v s) l) r) = lookup (union (insert k v s) l) ++ lookup r"
    "lookup (union (insert k v s) l) = lookup (insert k v s) ++ lookup l"
    by auto
  
  with meq show ?case
    by (auto simp: lookup_insert[OF Branch(3)])

qed


subsection {* Modifying existing entries *}

primrec
  map_entry :: "'a\<Colon>linorder \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "map_entry k f Empty = Empty"
| "map_entry k f (Branch c lt x v rt) =
    (if k < x then Branch c (map_entry k f lt) x v rt
    else if k > x then (Branch c lt x v (map_entry k f rt))
    else Branch c lt x (f v) rt)"

lemma map_entry_color_of: "color_of (map_entry k f t) = color_of t" by (induct t) simp+
lemma map_entry_inv1: "inv1 (map_entry k f t) = inv1 t" by (induct t) (simp add: map_entry_color_of)+
lemma map_entry_inv2: "inv2 (map_entry k f t) = inv2 t" "bheight (map_entry k f t) = bheight t" by (induct t) simp+
lemma map_entry_tree_greater: "tree_greater a (map_entry k f t) = tree_greater a t" by (induct t) simp+
lemma map_entry_tree_less: "tree_less a (map_entry k f t) = tree_less a t" by (induct t) simp+
lemma map_entry_sorted: "sorted (map_entry k f t) = sorted t"
  by (induct t) (simp_all add: map_entry_tree_less map_entry_tree_greater)

theorem map_entry_is_rbt [simp]: "is_rbt (map_entry k f t) = is_rbt t" 
unfolding is_rbt_def by (simp add: map_entry_inv2 map_entry_color_of map_entry_sorted map_entry_inv1 )

theorem lookup_map_entry:
  "lookup (map_entry k f t) = (lookup t)(k := Option.map f (lookup t k))"
  by (induct t) (auto split: option.splits simp add: fun_eq_iff)


subsection {* Mapping all entries *}

primrec
  map :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'c) rbt"
where
  "map f Empty = Empty"
| "map f (Branch c lt k v rt) = Branch c (map f lt) k (f k v) (map f rt)"

lemma map_entries [simp]: "entries (map f t) = List.map (\<lambda>(k, v). (k, f k v)) (entries t)"
  by (induct t) auto
lemma map_keys [simp]: "keys (map f t) = keys t" by (simp add: keys_def split_def)
lemma map_tree_greater: "tree_greater k (map f t) = tree_greater k t" by (induct t) simp+
lemma map_tree_less: "tree_less k (map f t) = tree_less k t" by (induct t) simp+
lemma map_sorted: "sorted (map f t) = sorted t"  by (induct t) (simp add: map_tree_less map_tree_greater)+
lemma map_color_of: "color_of (map f t) = color_of t" by (induct t) simp+
lemma map_inv1: "inv1 (map f t) = inv1 t" by (induct t) (simp add: map_color_of)+
lemma map_inv2: "inv2 (map f t) = inv2 t" "bheight (map f t) = bheight t" by (induct t) simp+
theorem map_is_rbt [simp]: "is_rbt (map f t) = is_rbt t" 
unfolding is_rbt_def by (simp add: map_inv1 map_inv2 map_sorted map_color_of)

theorem lookup_map: "lookup (map f t) x = Option.map (f x) (lookup t x)"
  by (induct t) auto


subsection {* Folding over entries *}

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" where
  "fold f t = List.fold (prod_case f) (entries t)"

lemma fold_simps [simp, code]:
  "fold f Empty = id"
  "fold f (Branch c lt k v rt) = fold f rt \<circ> f k v \<circ> fold f lt"
  by (simp_all add: fold_def fun_eq_iff)


subsection {* Bulkloading a tree *}

definition bulkload :: "('a \<times> 'b) list \<Rightarrow> ('a\<Colon>linorder, 'b) rbt" where
  "bulkload xs = foldr (\<lambda>(k, v). insert k v) xs Empty"

lemma bulkload_is_rbt [simp, intro]:
  "is_rbt (bulkload xs)"
  unfolding bulkload_def by (induct xs) auto

lemma lookup_bulkload:
  "lookup (bulkload xs) = map_of xs"
proof -
  obtain ys where "ys = rev xs" by simp
  have "\<And>t. is_rbt t \<Longrightarrow>
    lookup (List.fold (prod_case insert) ys t) = lookup t ++ map_of (rev ys)"
      by (induct ys) (simp_all add: bulkload_def lookup_insert prod_case_beta)
  from this Empty_is_rbt have
    "lookup (List.fold (prod_case insert) (rev xs) Empty) = lookup Empty ++ map_of xs"
     by (simp add: `ys = rev xs`)
  then show ?thesis by (simp add: bulkload_def lookup_Empty foldr_conv_fold)
qed

hide_const (open) R B Empty insert delete entries keys bulkload lookup map_entry map fold union sorted

end
