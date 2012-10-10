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

lemma non_empty_rbt_keys: 
  "t \<noteq> rbt.Empty \<Longrightarrow> keys t \<noteq> []"
  by (cases t) simp_all

subsubsection {* Search tree properties *}

context ord begin

definition rbt_less :: "'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"
where
  rbt_less_prop: "rbt_less k t \<longleftrightarrow> (\<forall>x\<in>set (keys t). x < k)"

abbreviation rbt_less_symbol (infix "|\<guillemotleft>" 50)
where "t |\<guillemotleft> x \<equiv> rbt_less x t"

definition rbt_greater :: "'a \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool" (infix "\<guillemotleft>|" 50) 
where
  rbt_greater_prop: "rbt_greater k t = (\<forall>x\<in>set (keys t). k < x)"

lemma rbt_less_simps [simp]:
  "Empty |\<guillemotleft> k = True"
  "Branch c lt kt v rt |\<guillemotleft> k \<longleftrightarrow> kt < k \<and> lt |\<guillemotleft> k \<and> rt |\<guillemotleft> k"
  by (auto simp add: rbt_less_prop)

lemma rbt_greater_simps [simp]:
  "k \<guillemotleft>| Empty = True"
  "k \<guillemotleft>| (Branch c lt kt v rt) \<longleftrightarrow> k < kt \<and> k \<guillemotleft>| lt \<and> k \<guillemotleft>| rt"
  by (auto simp add: rbt_greater_prop)

lemmas rbt_ord_props = rbt_less_prop rbt_greater_prop

lemmas rbt_greater_nit = rbt_greater_prop entry_in_tree_keys
lemmas rbt_less_nit = rbt_less_prop entry_in_tree_keys

lemma (in order)
  shows rbt_less_eq_trans: "l |\<guillemotleft> u \<Longrightarrow> u \<le> v \<Longrightarrow> l |\<guillemotleft> v"
  and rbt_less_trans: "t |\<guillemotleft> x \<Longrightarrow> x < y \<Longrightarrow> t |\<guillemotleft> y"
  and rbt_greater_eq_trans: "u \<le> v \<Longrightarrow> v \<guillemotleft>| r \<Longrightarrow> u \<guillemotleft>| r"
  and rbt_greater_trans: "x < y \<Longrightarrow> y \<guillemotleft>| t \<Longrightarrow> x \<guillemotleft>| t"
  by (auto simp: rbt_ord_props)

primrec rbt_sorted :: "('a, 'b) rbt \<Rightarrow> bool"
where
  "rbt_sorted Empty = True"
| "rbt_sorted (Branch c l k v r) = (l |\<guillemotleft> k \<and> k \<guillemotleft>| r \<and> rbt_sorted l \<and> rbt_sorted r)"

end

context linorder begin

lemma rbt_sorted_entries:
  "rbt_sorted t \<Longrightarrow> List.sorted (map fst (entries t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons rbt_ord_props 
      dest!: entry_in_tree_keys)+

lemma distinct_entries:
  "rbt_sorted t \<Longrightarrow> distinct (map fst (entries t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons rbt_ord_props 
      dest!: entry_in_tree_keys)+

lemma distinct_keys:
  "rbt_sorted t \<Longrightarrow> distinct (keys t)"
  by (simp add: distinct_entries keys_def)


subsubsection {* Tree lookup *}

primrec (in ord) rbt_lookup :: "('a, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "rbt_lookup Empty k = None"
| "rbt_lookup (Branch _ l x y r) k = 
   (if k < x then rbt_lookup l k else if x < k then rbt_lookup r k else Some y)"

lemma rbt_lookup_keys: "rbt_sorted t \<Longrightarrow> dom (rbt_lookup t) = set (keys t)"
  by (induct t) (auto simp: dom_def rbt_greater_prop rbt_less_prop)

lemma dom_rbt_lookup_Branch: 
  "rbt_sorted (Branch c t1 k v t2) \<Longrightarrow> 
    dom (rbt_lookup (Branch c t1 k v t2)) 
    = Set.insert k (dom (rbt_lookup t1) \<union> dom (rbt_lookup t2))"
proof -
  assume "rbt_sorted (Branch c t1 k v t2)"
  moreover from this have "rbt_sorted t1" "rbt_sorted t2" by simp_all
  ultimately show ?thesis by (simp add: rbt_lookup_keys)
qed

lemma finite_dom_rbt_lookup [simp, intro!]: "finite (dom (rbt_lookup t))"
proof (induct t)
  case Empty then show ?case by simp
next
  case (Branch color t1 a b t2)
  let ?A = "Set.insert a (dom (rbt_lookup t1) \<union> dom (rbt_lookup t2))"
  have "dom (rbt_lookup (Branch color t1 a b t2)) \<subseteq> ?A" by (auto split: split_if_asm)
  moreover from Branch have "finite (insert a (dom (rbt_lookup t1) \<union> dom (rbt_lookup t2)))" by simp
  ultimately show ?case by (rule finite_subset)
qed 

end

context ord begin

lemma rbt_lookup_rbt_less[simp]: "t |\<guillemotleft> k \<Longrightarrow> rbt_lookup t k = None" 
by (induct t) auto

lemma rbt_lookup_rbt_greater[simp]: "k \<guillemotleft>| t \<Longrightarrow> rbt_lookup t k = None"
by (induct t) auto

lemma rbt_lookup_Empty: "rbt_lookup Empty = empty"
by (rule ext) simp

end

context linorder begin

lemma map_of_entries:
  "rbt_sorted t \<Longrightarrow> map_of (entries t) = rbt_lookup t"
proof (induct t)
  case Empty thus ?case by (simp add: rbt_lookup_Empty)
next
  case (Branch c t1 k v t2)
  have "rbt_lookup (Branch c t1 k v t2) = rbt_lookup t2 ++ [k\<mapsto>v] ++ rbt_lookup t1"
  proof (rule ext)
    fix x
    from Branch have RBT_SORTED: "rbt_sorted (Branch c t1 k v t2)" by simp
    let ?thesis = "rbt_lookup (Branch c t1 k v t2) x = (rbt_lookup t2 ++ [k \<mapsto> v] ++ rbt_lookup t1) x"

    have DOM_T1: "!!k'. k'\<in>dom (rbt_lookup t1) \<Longrightarrow> k>k'"
    proof -
      fix k'
      from RBT_SORTED have "t1 |\<guillemotleft> k" by simp
      with rbt_less_prop have "\<forall>k'\<in>set (keys t1). k>k'" by auto
      moreover assume "k'\<in>dom (rbt_lookup t1)"
      ultimately show "k>k'" using rbt_lookup_keys RBT_SORTED by auto
    qed
    
    have DOM_T2: "!!k'. k'\<in>dom (rbt_lookup t2) \<Longrightarrow> k<k'"
    proof -
      fix k'
      from RBT_SORTED have "k \<guillemotleft>| t2" by simp
      with rbt_greater_prop have "\<forall>k'\<in>set (keys t2). k<k'" by auto
      moreover assume "k'\<in>dom (rbt_lookup t2)"
      ultimately show "k<k'" using rbt_lookup_keys RBT_SORTED by auto
    qed
    
    {
      assume C: "x<k"
      hence "rbt_lookup (Branch c t1 k v t2) x = rbt_lookup t1 x" by simp
      moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
      moreover have "x \<notin> dom (rbt_lookup t2)"
      proof
        assume "x \<in> dom (rbt_lookup t2)"
        with DOM_T2 have "k<x" by blast
        with C show False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } moreover {
      assume [simp]: "x=k"
      hence "rbt_lookup (Branch c t1 k v t2) x = [k \<mapsto> v] x" by simp
      moreover have "x \<notin> dom (rbt_lookup t1)" 
      proof
        assume "x \<in> dom (rbt_lookup t1)"
        with DOM_T1 have "k>x" by blast
        thus False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } moreover {
      assume C: "x>k"
      hence "rbt_lookup (Branch c t1 k v t2) x = rbt_lookup t2 x" by (simp add: less_not_sym[of k x])
      moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
      moreover have "x\<notin>dom (rbt_lookup t1)" proof
        assume "x\<in>dom (rbt_lookup t1)"
        with DOM_T1 have "k>x" by simp
        with C show False by simp
      qed
      ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
    } ultimately show ?thesis using less_linear by blast
  qed
  also from Branch 
  have "rbt_lookup t2 ++ [k \<mapsto> v] ++ rbt_lookup t1 = map_of (entries (Branch c t1 k v t2))" by simp
  finally show ?case by simp
qed

lemma rbt_lookup_in_tree: "rbt_sorted t \<Longrightarrow> rbt_lookup t k = Some v \<longleftrightarrow> (k, v) \<in> set (entries t)"
  by (simp add: map_of_entries [symmetric] distinct_entries)

lemma set_entries_inject:
  assumes rbt_sorted: "rbt_sorted t1" "rbt_sorted t2" 
  shows "set (entries t1) = set (entries t2) \<longleftrightarrow> entries t1 = entries t2"
proof -
  from rbt_sorted have "distinct (map fst (entries t1))"
    "distinct (map fst (entries t2))"
    by (auto intro: distinct_entries)
  with rbt_sorted show ?thesis
    by (auto intro: map_sorted_distinct_set_unique rbt_sorted_entries simp add: distinct_map)
qed

lemma entries_eqI:
  assumes rbt_sorted: "rbt_sorted t1" "rbt_sorted t2" 
  assumes rbt_lookup: "rbt_lookup t1 = rbt_lookup t2"
  shows "entries t1 = entries t2"
proof -
  from rbt_sorted rbt_lookup have "map_of (entries t1) = map_of (entries t2)"
    by (simp add: map_of_entries)
  with rbt_sorted have "set (entries t1) = set (entries t2)"
    by (simp add: map_of_inject_set distinct_entries)
  with rbt_sorted show ?thesis by (simp add: set_entries_inject)
qed

lemma entries_rbt_lookup:
  assumes "rbt_sorted t1" "rbt_sorted t2" 
  shows "entries t1 = entries t2 \<longleftrightarrow> rbt_lookup t1 = rbt_lookup t2"
  using assms by (auto intro: entries_eqI simp add: map_of_entries [symmetric])

lemma rbt_lookup_from_in_tree: 
  assumes "rbt_sorted t1" "rbt_sorted t2" 
  and "\<And>v. (k, v) \<in> set (entries t1) \<longleftrightarrow> (k, v) \<in> set (entries t2)" 
  shows "rbt_lookup t1 k = rbt_lookup t2 k"
proof -
  from assms have "k \<in> dom (rbt_lookup t1) \<longleftrightarrow> k \<in> dom (rbt_lookup t2)"
    by (simp add: keys_entries rbt_lookup_keys)
  with assms show ?thesis by (auto simp add: rbt_lookup_in_tree [symmetric])
qed

end

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

context ord begin

definition is_rbt :: "('a, 'b) rbt \<Rightarrow> bool" where
  "is_rbt t \<longleftrightarrow> inv1 t \<and> inv2 t \<and> color_of t = B \<and> rbt_sorted t"

lemma is_rbt_rbt_sorted [simp]:
  "is_rbt t \<Longrightarrow> rbt_sorted t" by (simp add: is_rbt_def)

theorem Empty_is_rbt [simp]:
  "is_rbt Empty" by (simp add: is_rbt_def)

end

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

context ord begin

lemma balance_rbt_greater[simp]: "(v \<guillemotleft>| balance a k x b) = (v \<guillemotleft>| a \<and> v \<guillemotleft>| b \<and> v < k)" 
  by (induct a k x b rule: balance.induct) auto

lemma balance_rbt_less[simp]: "(balance a k x b |\<guillemotleft> v) = (a |\<guillemotleft> v \<and> b |\<guillemotleft> v \<and> k < v)"
  by (induct a k x b rule: balance.induct) auto

end

lemma (in linorder) balance_rbt_sorted: 
  fixes k :: "'a"
  assumes "rbt_sorted l" "rbt_sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "rbt_sorted (balance l k v r)"
using assms proof (induct l k v r rule: balance.induct)
  case ("2_2" a x w b y t c z s va vb vd vc)
  hence "y < z \<and> z \<guillemotleft>| Branch B va vb vd vc" 
    by (auto simp add: rbt_ord_props)
  hence "y \<guillemotleft>| (Branch B va vb vd vc)" by (blast dest: rbt_greater_trans)
  with "2_2" show ?case by simp
next
  case ("3_2" va vb vd vc x w b y s c z)
  from "3_2" have "x < y \<and> Branch B va vb vd vc |\<guillemotleft> x" 
    by simp
  hence "Branch B va vb vd vc |\<guillemotleft> y" by (blast dest: rbt_less_trans)
  with "3_2" show ?case by simp
next
  case ("3_3" x w b y s c z t va vb vd vc)
  from "3_3" have "y < z \<and> z \<guillemotleft>| Branch B va vb vd vc" by simp
  hence "y \<guillemotleft>| Branch B va vb vd vc" by (blast dest: rbt_greater_trans)
  with "3_3" show ?case by simp
next
  case ("3_4" vd ve vg vf x w b y s c z t va vb vii vc)
  hence "x < y \<and> Branch B vd ve vg vf |\<guillemotleft> x" by simp
  hence 1: "Branch B vd ve vg vf |\<guillemotleft> y" by (blast dest: rbt_less_trans)
  from "3_4" have "y < z \<and> z \<guillemotleft>| Branch B va vb vii vc" by simp
  hence "y \<guillemotleft>| Branch B va vb vii vc" by (blast dest: rbt_greater_trans)
  with 1 "3_4" show ?case by simp
next
  case ("4_2" va vb vd vc x w b y s c z t dd)
  hence "x < y \<and> Branch B va vb vd vc |\<guillemotleft> x" by simp
  hence "Branch B va vb vd vc |\<guillemotleft> y" by (blast dest: rbt_less_trans)
  with "4_2" show ?case by simp
next
  case ("5_2" x w b y s c z t va vb vd vc)
  hence "y < z \<and> z \<guillemotleft>| Branch B va vb vd vc" by simp
  hence "y \<guillemotleft>| Branch B va vb vd vc" by (blast dest: rbt_greater_trans)
  with "5_2" show ?case by simp
next
  case ("5_3" va vb vd vc x w b y s c z t)
  hence "x < y \<and> Branch B va vb vd vc |\<guillemotleft> x" by simp
  hence "Branch B va vb vd vc |\<guillemotleft> y" by (blast dest: rbt_less_trans)
  with "5_3" show ?case by simp
next
  case ("5_4" va vb vg vc x w b y s c z t vd ve vii vf)
  hence "x < y \<and> Branch B va vb vg vc |\<guillemotleft> x" by simp
  hence 1: "Branch B va vb vg vc |\<guillemotleft> y" by (blast dest: rbt_less_trans)
  from "5_4" have "y < z \<and> z \<guillemotleft>| Branch B vd ve vii vf" by simp
  hence "y \<guillemotleft>| Branch B vd ve vii vf" by (blast dest: rbt_greater_trans)
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

lemma (in linorder) rbt_lookup_balance[simp]: 
fixes k :: "'a"
assumes "rbt_sorted l" "rbt_sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
shows "rbt_lookup (balance l k v r) x = rbt_lookup (Branch B l k v r) x"
by (rule rbt_lookup_from_in_tree) (auto simp:assms balance_in_tree balance_rbt_sorted)

primrec paint :: "color \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "paint c Empty = Empty"
| "paint c (Branch _ l k v r) = Branch c l k v r"

lemma paint_inv1l[simp]: "inv1l t \<Longrightarrow> inv1l (paint c t)" by (cases t) auto
lemma paint_inv1[simp]: "inv1l t \<Longrightarrow> inv1 (paint B t)" by (cases t) auto
lemma paint_inv2[simp]: "inv2 t \<Longrightarrow> inv2 (paint c t)" by (cases t) auto
lemma paint_color_of[simp]: "color_of (paint B t) = B" by (cases t) auto
lemma paint_in_tree[simp]: "entry_in_tree k x (paint c t) = entry_in_tree k x t" by (cases t) auto

context ord begin

lemma paint_rbt_sorted[simp]: "rbt_sorted t \<Longrightarrow> rbt_sorted (paint c t)" by (cases t) auto
lemma paint_rbt_lookup[simp]: "rbt_lookup (paint c t) = rbt_lookup t" by (rule ext) (cases t, auto)
lemma paint_rbt_greater[simp]: "(v \<guillemotleft>| paint c t) = (v \<guillemotleft>| t)" by (cases t) auto
lemma paint_rbt_less[simp]: "(paint c t |\<guillemotleft> v) = (t |\<guillemotleft> v)" by (cases t) auto

fun
  rbt_ins :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_ins f k v Empty = Branch R Empty k v Empty" |
  "rbt_ins f k v (Branch B l x y r) = (if k < x then balance (rbt_ins f k v l) x y r
                                       else if k > x then balance l x y (rbt_ins f k v r)
                                       else Branch B l x (f k y v) r)" |
  "rbt_ins f k v (Branch R l x y r) = (if k < x then Branch R (rbt_ins f k v l) x y r
                                       else if k > x then Branch R l x y (rbt_ins f k v r)
                                       else Branch R l x (f k y v) r)"

lemma ins_inv1_inv2: 
  assumes "inv1 t" "inv2 t"
  shows "inv2 (rbt_ins f k x t)" "bheight (rbt_ins f k x t) = bheight t" 
  "color_of t = B \<Longrightarrow> inv1 (rbt_ins f k x t)" "inv1l (rbt_ins f k x t)"
  using assms
  by (induct f k x t rule: rbt_ins.induct) (auto simp: balance_inv1 balance_inv2 balance_bheight)

end

context linorder begin

lemma ins_rbt_greater[simp]: "(v \<guillemotleft>| rbt_ins f (k :: 'a) x t) = (v \<guillemotleft>| t \<and> k > v)"
  by (induct f k x t rule: rbt_ins.induct) auto
lemma ins_rbt_less[simp]: "(rbt_ins f k x t |\<guillemotleft> v) = (t |\<guillemotleft> v \<and> k < v)"
  by (induct f k x t rule: rbt_ins.induct) auto
lemma ins_rbt_sorted[simp]: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_ins f k x t)"
  by (induct f k x t rule: rbt_ins.induct) (auto simp: balance_rbt_sorted)

lemma keys_ins: "set (keys (rbt_ins f k v t)) = { k } \<union> set (keys t)"
  by (induct f k v t rule: rbt_ins.induct) auto

lemma rbt_lookup_ins: 
  fixes k :: "'a"
  assumes "rbt_sorted t"
  shows "rbt_lookup (rbt_ins f k v t) x = ((rbt_lookup t)(k |-> case rbt_lookup t k of None \<Rightarrow> v 
                                                                | Some w \<Rightarrow> f k w v)) x"
using assms by (induct f k v t rule: rbt_ins.induct) auto

end

context ord begin

definition rbt_insert_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where "rbt_insert_with_key f k v t = paint B (rbt_ins f k v t)"

definition rbt_insertw_def: "rbt_insert_with f = rbt_insert_with_key (\<lambda>_. f)"

definition rbt_insert :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_insert = rbt_insert_with_key (\<lambda>_ _ nv. nv)"

end

context linorder begin

lemma rbt_insertwk_rbt_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert_with_key f (k :: 'a) x t)"
  by (auto simp: rbt_insert_with_key_def)

theorem rbt_insertwk_is_rbt: 
  assumes inv: "is_rbt t" 
  shows "is_rbt (rbt_insert_with_key f k x t)"
using assms
unfolding rbt_insert_with_key_def is_rbt_def
by (auto simp: ins_inv1_inv2)

lemma rbt_lookup_rbt_insertwk: 
  assumes "rbt_sorted t"
  shows "rbt_lookup (rbt_insert_with_key f k v t) x = ((rbt_lookup t)(k |-> case rbt_lookup t k of None \<Rightarrow> v 
                                                       | Some w \<Rightarrow> f k w v)) x"
unfolding rbt_insert_with_key_def using assms
by (simp add:rbt_lookup_ins)

lemma rbt_insertw_rbt_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert_with f k v t)" 
  by (simp add: rbt_insertwk_rbt_sorted rbt_insertw_def)
theorem rbt_insertw_is_rbt: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert_with f k v t)"
  by (simp add: rbt_insertwk_is_rbt rbt_insertw_def)

lemma rbt_lookup_rbt_insertw:
  assumes "is_rbt t"
  shows "rbt_lookup (rbt_insert_with f k v t) = (rbt_lookup t)(k \<mapsto> (if k:dom (rbt_lookup t) then f (the (rbt_lookup t k)) v else v))"
using assms
unfolding rbt_insertw_def
by (rule_tac ext) (cases "rbt_lookup t k", auto simp:rbt_lookup_rbt_insertwk dom_def)

lemma rbt_insert_rbt_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert k v t)"
  by (simp add: rbt_insertwk_rbt_sorted rbt_insert_def)
theorem rbt_insert_is_rbt [simp]: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert k v t)"
  by (simp add: rbt_insertwk_is_rbt rbt_insert_def)

lemma rbt_lookup_rbt_insert: 
  assumes "is_rbt t"
  shows "rbt_lookup (rbt_insert k v t) = (rbt_lookup t)(k\<mapsto>v)"
unfolding rbt_insert_def
using assms
by (rule_tac ext) (simp add: rbt_lookup_rbt_insertwk split:option.split)

end

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

lemma (in linorder) balance_left_rbt_sorted: 
  "\<lbrakk> rbt_sorted l; rbt_sorted r; rbt_less k l; k \<guillemotleft>| r \<rbrakk> \<Longrightarrow> rbt_sorted (balance_left l k v r)"
apply (induct l k v r rule: balance_left.induct)
apply (auto simp: balance_rbt_sorted)
apply (unfold rbt_greater_prop rbt_less_prop)
by force+

context order begin

lemma balance_left_rbt_greater: 
  fixes k :: "'a"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balance_left a x t b"
using assms 
by (induct a x t b rule: balance_left.induct) auto

lemma balance_left_rbt_less: 
  fixes k :: "'a"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balance_left a x t b |\<guillemotleft> k"
using assms
by (induct a x t b rule: balance_left.induct) auto

end

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

lemma (in linorder) balance_right_rbt_sorted:
  "\<lbrakk> rbt_sorted l; rbt_sorted r; rbt_less k l; k \<guillemotleft>| r \<rbrakk> \<Longrightarrow> rbt_sorted (balance_right l k v r)"
apply (induct l k v r rule: balance_right.induct)
apply (auto simp:balance_rbt_sorted)
apply (unfold rbt_less_prop rbt_greater_prop)
by force+

context order begin

lemma balance_right_rbt_greater: 
  fixes k :: "'a"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balance_right a x t b"
using assms by (induct a x t b rule: balance_right.induct) auto

lemma balance_right_rbt_less: 
  fixes k :: "'a"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balance_right a x t b |\<guillemotleft> k"
using assms by (induct a x t b rule: balance_right.induct) auto

end

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

context linorder begin

lemma combine_rbt_greater[simp]: 
  fixes k :: "'a"
  assumes "k \<guillemotleft>| l" "k \<guillemotleft>| r" 
  shows "k \<guillemotleft>| combine l r"
using assms 
by (induct l r rule: combine.induct)
   (auto simp: balance_left_rbt_greater split:rbt.splits color.splits)

lemma combine_rbt_less[simp]: 
  fixes k :: "'a"
  assumes "l |\<guillemotleft> k" "r |\<guillemotleft> k" 
  shows "combine l r |\<guillemotleft> k"
using assms 
by (induct l r rule: combine.induct)
   (auto simp: balance_left_rbt_less split:rbt.splits color.splits)

lemma combine_rbt_sorted: 
  fixes k :: "'a"
  assumes "rbt_sorted l" "rbt_sorted r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "rbt_sorted (combine l r)"
using assms proof (induct l r rule: combine.induct)
  case (3 a x v b c y w d)
  hence ineqs: "a |\<guillemotleft> x" "x \<guillemotleft>| b" "b |\<guillemotleft> k" "k \<guillemotleft>| c" "c |\<guillemotleft> y" "y \<guillemotleft>| d"
    by auto
  with 3
  show ?case
    by (cases "combine b c" rule: rbt_cases)
      (auto, (metis combine_rbt_greater combine_rbt_less ineqs ineqs rbt_less_simps(2) rbt_greater_simps(2) rbt_greater_trans rbt_less_trans)+)
next
  case (4 a x v b c y w d)
  hence "x < k \<and> rbt_greater k c" by simp
  hence "rbt_greater x c" by (blast dest: rbt_greater_trans)
  with 4 have 2: "rbt_greater x (combine b c)" by (simp add: combine_rbt_greater)
  from 4 have "k < y \<and> rbt_less k b" by simp
  hence "rbt_less y b" by (blast dest: rbt_less_trans)
  with 4 have 3: "rbt_less y (combine b c)" by (simp add: combine_rbt_less)
  show ?case
  proof (cases "combine b c" rule: rbt_cases)
    case Empty
    from 4 have "x < y \<and> rbt_greater y d" by auto
    hence "rbt_greater x d" by (blast dest: rbt_greater_trans)
    with 4 Empty have "rbt_sorted a" and "rbt_sorted (Branch B Empty y w d)"
      and "rbt_less x a" and "rbt_greater x (Branch B Empty y w d)" by auto
    with Empty show ?thesis by (simp add: balance_left_rbt_sorted)
  next
    case (Red lta va ka rta)
    with 2 4 have "x < va \<and> rbt_less x a" by simp
    hence 5: "rbt_less va a" by (blast dest: rbt_less_trans)
    from Red 3 4 have "va < y \<and> rbt_greater y d" by simp
    hence "rbt_greater va d" by (blast dest: rbt_greater_trans)
    with Red 2 3 4 5 show ?thesis by simp
  next
    case (Black lta va ka rta)
    from 4 have "x < y \<and> rbt_greater y d" by auto
    hence "rbt_greater x d" by (blast dest: rbt_greater_trans)
    with Black 2 3 4 have "rbt_sorted a" and "rbt_sorted (Branch B (combine b c) y w d)" 
      and "rbt_less x a" and "rbt_greater x (Branch B (combine b c) y w d)" by auto
    with Black show ?thesis by (simp add: balance_left_rbt_sorted)
  qed
next
  case (5 va vb vd vc b x w c)
  hence "k < x \<and> rbt_less k (Branch B va vb vd vc)" by simp
  hence "rbt_less x (Branch B va vb vd vc)" by (blast dest: rbt_less_trans)
  with 5 show ?case by (simp add: combine_rbt_less)
next
  case (6 a x v b va vb vd vc)
  hence "x < k \<and> rbt_greater k (Branch B va vb vd vc)" by simp
  hence "rbt_greater x (Branch B va vb vd vc)" by (blast dest: rbt_greater_trans)
  with 6 show ?case by (simp add: combine_rbt_greater)
qed simp+

end

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

context ord begin

fun
  rbt_del_from_left :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_del_from_right :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_del :: "'a\<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_del x Empty = Empty" |
  "rbt_del x (Branch c a y s b) = 
   (if x < y then rbt_del_from_left x a y s b 
    else (if x > y then rbt_del_from_right x a y s b else combine a b))" |
  "rbt_del_from_left x (Branch B lt z v rt) y s b = balance_left (rbt_del x (Branch B lt z v rt)) y s b" |
  "rbt_del_from_left x a y s b = Branch R (rbt_del x a) y s b" |
  "rbt_del_from_right x a y s (Branch B lt z v rt) = balance_right a y s (rbt_del x (Branch B lt z v rt))" | 
  "rbt_del_from_right x a y s b = Branch R a y s (rbt_del x b)"

end

context linorder begin

lemma 
  assumes "inv2 lt" "inv1 lt"
  shows
  "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
   inv2 (rbt_del_from_left x lt k v rt) \<and> 
   bheight (rbt_del_from_left x lt k v rt) = bheight lt \<and> 
   (color_of lt = B \<and> color_of rt = B \<and> inv1 (rbt_del_from_left x lt k v rt) \<or> 
    (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (rbt_del_from_left x lt k v rt))"
  and "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (rbt_del_from_right x lt k v rt) \<and> 
  bheight (rbt_del_from_right x lt k v rt) = bheight lt \<and> 
  (color_of lt = B \<and> color_of rt = B \<and> inv1 (rbt_del_from_right x lt k v rt) \<or> 
   (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (rbt_del_from_right x lt k v rt))"
  and rbt_del_inv1_inv2: "inv2 (rbt_del x lt) \<and> (color_of lt = R \<and> bheight (rbt_del x lt) = bheight lt \<and> inv1 (rbt_del x lt) 
  \<or> color_of lt = B \<and> bheight (rbt_del x lt) = bheight lt - 1 \<and> inv1l (rbt_del x lt))"
using assms
proof (induct x lt k v rt and x lt k v rt and x lt rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
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
  rbt_del_from_left_rbt_less: "\<lbrakk> lt |\<guillemotleft> v; rt |\<guillemotleft> v; k < v\<rbrakk> \<Longrightarrow> rbt_del_from_left x lt k y rt |\<guillemotleft> v"
  and rbt_del_from_right_rbt_less: "\<lbrakk>lt |\<guillemotleft> v; rt |\<guillemotleft> v; k < v\<rbrakk> \<Longrightarrow> rbt_del_from_right x lt k y rt |\<guillemotleft> v"
  and rbt_del_rbt_less: "lt |\<guillemotleft> v \<Longrightarrow> rbt_del x lt |\<guillemotleft> v"
by (induct x lt k y rt and x lt k y rt and x lt rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct) 
   (auto simp: balance_left_rbt_less balance_right_rbt_less)

lemma rbt_del_from_left_rbt_greater: "\<lbrakk>v \<guillemotleft>| lt; v \<guillemotleft>| rt; k > v\<rbrakk> \<Longrightarrow> v \<guillemotleft>| rbt_del_from_left x lt k y rt"
  and rbt_del_from_right_rbt_greater: "\<lbrakk>v \<guillemotleft>| lt; v \<guillemotleft>| rt; k > v\<rbrakk> \<Longrightarrow> v \<guillemotleft>| rbt_del_from_right x lt k y rt"
  and rbt_del_rbt_greater: "v \<guillemotleft>| lt \<Longrightarrow> v \<guillemotleft>| rbt_del x lt"
by (induct x lt k y rt and x lt k y rt and x lt rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
   (auto simp: balance_left_rbt_greater balance_right_rbt_greater)

lemma "\<lbrakk>rbt_sorted lt; rbt_sorted rt; lt |\<guillemotleft> k; k \<guillemotleft>| rt\<rbrakk> \<Longrightarrow> rbt_sorted (rbt_del_from_left x lt k y rt)"
  and "\<lbrakk>rbt_sorted lt; rbt_sorted rt; lt |\<guillemotleft> k; k \<guillemotleft>| rt\<rbrakk> \<Longrightarrow> rbt_sorted (rbt_del_from_right x lt k y rt)"
  and rbt_del_rbt_sorted: "rbt_sorted lt \<Longrightarrow> rbt_sorted (rbt_del x lt)"
proof (induct x lt k y rt and x lt k y rt and x lt rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
  case (3 x lta zz v rta yy ss bb)
  from 3 have "Branch B lta zz v rta |\<guillemotleft> yy" by simp
  hence "rbt_del x (Branch B lta zz v rta) |\<guillemotleft> yy" by (rule rbt_del_rbt_less)
  with 3 show ?case by (simp add: balance_left_rbt_sorted)
next
  case ("4_2" x vaa vbb vdd vc yy ss bb)
  hence "Branch R vaa vbb vdd vc |\<guillemotleft> yy" by simp
  hence "rbt_del x (Branch R vaa vbb vdd vc) |\<guillemotleft> yy" by (rule rbt_del_rbt_less)
  with "4_2" show ?case by simp
next
  case (5 x aa yy ss lta zz v rta) 
  hence "yy \<guillemotleft>| Branch B lta zz v rta" by simp
  hence "yy \<guillemotleft>| rbt_del x (Branch B lta zz v rta)" by (rule rbt_del_rbt_greater)
  with 5 show ?case by (simp add: balance_right_rbt_sorted)
next
  case ("6_2" x aa yy ss vaa vbb vdd vc)
  hence "yy \<guillemotleft>| Branch R vaa vbb vdd vc" by simp
  hence "yy \<guillemotleft>| rbt_del x (Branch R vaa vbb vdd vc)" by (rule rbt_del_rbt_greater)
  with "6_2" show ?case by simp
qed (auto simp: combine_rbt_sorted)

lemma "\<lbrakk>rbt_sorted lt; rbt_sorted rt; lt |\<guillemotleft> kt; kt \<guillemotleft>| rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bheight lt = bheight rt; x < kt\<rbrakk> \<Longrightarrow> entry_in_tree k v (rbt_del_from_left x lt kt y rt) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v (Branch c lt kt y rt)))"
  and "\<lbrakk>rbt_sorted lt; rbt_sorted rt; lt |\<guillemotleft> kt; kt \<guillemotleft>| rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bheight lt = bheight rt; x > kt\<rbrakk> \<Longrightarrow> entry_in_tree k v (rbt_del_from_right x lt kt y rt) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v (Branch c lt kt y rt)))"
  and rbt_del_in_tree: "\<lbrakk>rbt_sorted t; inv1 t; inv2 t\<rbrakk> \<Longrightarrow> entry_in_tree k v (rbt_del x t) = (False \<or> (x \<noteq> k \<and> entry_in_tree k v t))"
proof (induct x lt kt y rt and x lt kt y rt and x t rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
  case (2 xx c aa yy ss bb)
  have "xx = yy \<or> xx < yy \<or> xx > yy" by auto
  from this 2 show ?case proof (elim disjE)
    assume "xx = yy"
    with 2 show ?thesis proof (cases "xx = k")
      case True
      from 2 `xx = yy` `xx = k` have "rbt_sorted (Branch c aa yy ss bb) \<and> k = yy" by simp
      hence "\<not> entry_in_tree k v aa" "\<not> entry_in_tree k v bb" by (auto simp: rbt_less_nit rbt_greater_prop)
      with `xx = yy` 2 `xx = k` show ?thesis by (simp add: combine_in_tree)
    qed (simp add: combine_in_tree)
  qed simp+
next    
  case (3 xx lta zz vv rta yy ss bb)
  def mt[simp]: mt == "Branch B lta zz vv rta"
  from 3 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (rbt_del xx mt) \<and> (color_of mt = R \<and> bheight (rbt_del xx mt) = bheight mt \<and> inv1 (rbt_del xx mt) \<or> color_of mt = B \<and> bheight (rbt_del xx mt) = bheight mt - 1 \<and> inv1l (rbt_del xx mt))" by (blast dest: rbt_del_inv1_inv2)
  with 3 have 4: "entry_in_tree k v (rbt_del_from_left xx mt yy ss bb) = (False \<or> xx \<noteq> k \<and> entry_in_tree k v mt \<or> (k = yy \<and> v = ss) \<or> entry_in_tree k v bb)" by (simp add: balance_left_in_tree)
  thus ?case proof (cases "xx = k")
    case True
    from 3 True have "yy \<guillemotleft>| bb \<and> yy > k" by simp
    hence "k \<guillemotleft>| bb" by (blast dest: rbt_greater_trans)
    with 3 4 True show ?thesis by (auto simp: rbt_greater_nit)
  qed auto
next
  case ("4_1" xx yy ss bb)
  show ?case proof (cases "xx = k")
    case True
    with "4_1" have "yy \<guillemotleft>| bb \<and> k < yy" by simp
    hence "k \<guillemotleft>| bb" by (blast dest: rbt_greater_trans)
    with "4_1" `xx = k` 
   have "entry_in_tree k v (Branch R Empty yy ss bb) = entry_in_tree k v Empty" by (auto simp: rbt_greater_nit)
    thus ?thesis by auto
  qed simp+
next
  case ("4_2" xx vaa vbb vdd vc yy ss bb)
  thus ?case proof (cases "xx = k")
    case True
    with "4_2" have "k < yy \<and> yy \<guillemotleft>| bb" by simp
    hence "k \<guillemotleft>| bb" by (blast dest: rbt_greater_trans)
    with True "4_2" show ?thesis by (auto simp: rbt_greater_nit)
  qed auto
next
  case (5 xx aa yy ss lta zz vv rta)
  def mt[simp]: mt == "Branch B lta zz vv rta"
  from 5 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (rbt_del xx mt) \<and> (color_of mt = R \<and> bheight (rbt_del xx mt) = bheight mt \<and> inv1 (rbt_del xx mt) \<or> color_of mt = B \<and> bheight (rbt_del xx mt) = bheight mt - 1 \<and> inv1l (rbt_del xx mt))" by (blast dest: rbt_del_inv1_inv2)
  with 5 have 3: "entry_in_tree k v (rbt_del_from_right xx aa yy ss mt) = (entry_in_tree k v aa \<or> (k = yy \<and> v = ss) \<or> False \<or> xx \<noteq> k \<and> entry_in_tree k v mt)" by (simp add: balance_right_in_tree)
  thus ?case proof (cases "xx = k")
    case True
    from 5 True have "aa |\<guillemotleft> yy \<and> yy < k" by simp
    hence "aa |\<guillemotleft> k" by (blast dest: rbt_less_trans)
    with 3 5 True show ?thesis by (auto simp: rbt_less_nit)
  qed auto
next
  case ("6_1" xx aa yy ss)
  show ?case proof (cases "xx = k")
    case True
    with "6_1" have "aa |\<guillemotleft> yy \<and> k > yy" by simp
    hence "aa |\<guillemotleft> k" by (blast dest: rbt_less_trans)
    with "6_1" `xx = k` show ?thesis by (auto simp: rbt_less_nit)
  qed simp
next
  case ("6_2" xx aa yy ss vaa vbb vdd vc)
  thus ?case proof (cases "xx = k")
    case True
    with "6_2" have "k > yy \<and> aa |\<guillemotleft> yy" by simp
    hence "aa |\<guillemotleft> k" by (blast dest: rbt_less_trans)
    with True "6_2" show ?thesis by (auto simp: rbt_less_nit)
  qed auto
qed simp

definition (in ord) rbt_delete where
  "rbt_delete k t = paint B (rbt_del k t)"

theorem rbt_delete_is_rbt [simp]: assumes "is_rbt t" shows "is_rbt (rbt_delete k t)"
proof -
  from assms have "inv2 t" and "inv1 t" unfolding is_rbt_def by auto 
  hence "inv2 (rbt_del k t) \<and> (color_of t = R \<and> bheight (rbt_del k t) = bheight t \<and> inv1 (rbt_del k t) \<or> color_of t = B \<and> bheight (rbt_del k t) = bheight t - 1 \<and> inv1l (rbt_del k t))" by (rule rbt_del_inv1_inv2)
  hence "inv2 (rbt_del k t) \<and> inv1l (rbt_del k t)" by (cases "color_of t") auto
  with assms show ?thesis
    unfolding is_rbt_def rbt_delete_def
    by (auto intro: paint_rbt_sorted rbt_del_rbt_sorted)
qed

lemma rbt_delete_in_tree: 
  assumes "is_rbt t" 
  shows "entry_in_tree k v (rbt_delete x t) = (x \<noteq> k \<and> entry_in_tree k v t)"
  using assms unfolding is_rbt_def rbt_delete_def
  by (auto simp: rbt_del_in_tree)

lemma rbt_lookup_rbt_delete:
  assumes is_rbt: "is_rbt t"
  shows "rbt_lookup (rbt_delete k t) = (rbt_lookup t)|`(-{k})"
proof
  fix x
  show "rbt_lookup (rbt_delete k t) x = (rbt_lookup t |` (-{k})) x" 
  proof (cases "x = k")
    assume "x = k" 
    with is_rbt show ?thesis
      by (cases "rbt_lookup (rbt_delete k t) k") (auto simp: rbt_lookup_in_tree rbt_delete_in_tree)
  next
    assume "x \<noteq> k"
    thus ?thesis
      by auto (metis is_rbt rbt_delete_is_rbt rbt_delete_in_tree is_rbt_rbt_sorted rbt_lookup_from_in_tree)
  qed
qed

end

subsection {* Modifying existing entries *}

context ord begin

primrec
  rbt_map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_map_entry k f Empty = Empty"
| "rbt_map_entry k f (Branch c lt x v rt) =
    (if k < x then Branch c (rbt_map_entry k f lt) x v rt
    else if k > x then (Branch c lt x v (rbt_map_entry k f rt))
    else Branch c lt x (f v) rt)"


lemma rbt_map_entry_color_of: "color_of (rbt_map_entry k f t) = color_of t" by (induct t) simp+
lemma rbt_map_entry_inv1: "inv1 (rbt_map_entry k f t) = inv1 t" by (induct t) (simp add: rbt_map_entry_color_of)+
lemma rbt_map_entry_inv2: "inv2 (rbt_map_entry k f t) = inv2 t" "bheight (rbt_map_entry k f t) = bheight t" by (induct t) simp+
lemma rbt_map_entry_rbt_greater: "rbt_greater a (rbt_map_entry k f t) = rbt_greater a t" by (induct t) simp+
lemma rbt_map_entry_rbt_less: "rbt_less a (rbt_map_entry k f t) = rbt_less a t" by (induct t) simp+
lemma rbt_map_entry_rbt_sorted: "rbt_sorted (rbt_map_entry k f t) = rbt_sorted t"
  by (induct t) (simp_all add: rbt_map_entry_rbt_less rbt_map_entry_rbt_greater)

theorem rbt_map_entry_is_rbt [simp]: "is_rbt (rbt_map_entry k f t) = is_rbt t" 
unfolding is_rbt_def by (simp add: rbt_map_entry_inv2 rbt_map_entry_color_of rbt_map_entry_rbt_sorted rbt_map_entry_inv1 )

end

theorem (in linorder) rbt_lookup_rbt_map_entry:
  "rbt_lookup (rbt_map_entry k f t) = (rbt_lookup t)(k := Option.map f (rbt_lookup t k))"
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
lemma map_color_of: "color_of (map f t) = color_of t" by (induct t) simp+
lemma map_inv1: "inv1 (map f t) = inv1 t" by (induct t) (simp add: map_color_of)+
lemma map_inv2: "inv2 (map f t) = inv2 t" "bheight (map f t) = bheight t" by (induct t) simp+

context ord begin

lemma map_rbt_greater: "rbt_greater k (map f t) = rbt_greater k t" by (induct t) simp+
lemma map_rbt_less: "rbt_less k (map f t) = rbt_less k t" by (induct t) simp+
lemma map_rbt_sorted: "rbt_sorted (map f t) = rbt_sorted t"  by (induct t) (simp add: map_rbt_less map_rbt_greater)+
theorem map_is_rbt [simp]: "is_rbt (map f t) = is_rbt t" 
unfolding is_rbt_def by (simp add: map_inv1 map_inv2 map_rbt_sorted map_color_of)

end

theorem (in linorder) rbt_lookup_map: "rbt_lookup (map f t) x = Option.map (f x) (rbt_lookup t x)"
  apply(induct t)
  apply auto
  apply(subgoal_tac "x = a")
  apply auto
  done
 (* FIXME: simproc "antisym less" does not work for linorder context, only for linorder type class
    by (induct t) auto *)

hide_const (open) map

subsection {* Folding over entries *}

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" where
  "fold f t = List.fold (prod_case f) (entries t)"

lemma fold_simps [simp]:
  "fold f Empty = id"
  "fold f (Branch c lt k v rt) = fold f rt \<circ> f k v \<circ> fold f lt"
  by (simp_all add: fold_def fun_eq_iff)

lemma fold_code [code]:
  "fold f Empty c = c"
  "fold f (Branch c lt k v rt) c = fold f rt (f k v (fold f lt c))"
by(simp_all)

(* fold with continuation predicate *)

fun foldi :: "('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a :: linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" 
  where
  "foldi c f Empty s = s" |
  "foldi c f (Branch col l k v r) s = (
    if (c s) then
      let s' = foldi c f l s in
        if (c s') then
          foldi c f r (f k v s')
        else s'
    else 
      s
  )"

subsection {* Bulkloading a tree *}

definition (in ord) rbt_bulkload :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" where
  "rbt_bulkload xs = foldr (\<lambda>(k, v). rbt_insert k v) xs Empty"

context linorder begin

lemma rbt_bulkload_is_rbt [simp, intro]:
  "is_rbt (rbt_bulkload xs)"
  unfolding rbt_bulkload_def by (induct xs) auto

lemma rbt_lookup_rbt_bulkload:
  "rbt_lookup (rbt_bulkload xs) = map_of xs"
proof -
  obtain ys where "ys = rev xs" by simp
  have "\<And>t. is_rbt t \<Longrightarrow>
    rbt_lookup (List.fold (prod_case rbt_insert) ys t) = rbt_lookup t ++ map_of (rev ys)"
      by (induct ys) (simp_all add: rbt_bulkload_def rbt_lookup_rbt_insert prod_case_beta)
  from this Empty_is_rbt have
    "rbt_lookup (List.fold (prod_case rbt_insert) (rev xs) Empty) = rbt_lookup Empty ++ map_of xs"
     by (simp add: `ys = rev xs`)
  then show ?thesis by (simp add: rbt_bulkload_def rbt_lookup_Empty foldr_conv_fold)
qed

end



subsection {* Building a RBT from a sorted list *}

text {* 
  These functions have been adapted from 
  Andrew W. Appel, Efficient Verified Red-Black Trees (September 2011) 
*}

fun rbtreeify_f :: "nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list"
  and rbtreeify_g :: "nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt \<times> ('a \<times> 'b) list"
where
  "rbtreeify_f n kvs =
   (if n = 0 then (Empty, kvs)
    else if n = 1 then
      case kvs of (k, v) # kvs' \<Rightarrow> (Branch R Empty k v Empty, kvs')
    else if (n mod 2 = 0) then
      case rbtreeify_f (n div 2) kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (Branch B t1 k v) (rbtreeify_g (n div 2) kvs')
    else case rbtreeify_f (n div 2) kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (Branch B t1 k v) (rbtreeify_f (n div 2) kvs'))"

| "rbtreeify_g n kvs =
   (if n = 0 \<or> n = 1 then (Empty, kvs)
    else if n mod 2 = 0 then
      case rbtreeify_g (n div 2) kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (Branch B t1 k v) (rbtreeify_g (n div 2) kvs')
    else case rbtreeify_f (n div 2) kvs of (t1, (k, v) # kvs') \<Rightarrow>
        apfst (Branch B t1 k v) (rbtreeify_g (n div 2) kvs'))"

definition rbtreeify :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) rbt"
where "rbtreeify kvs = fst (rbtreeify_g (Suc (length kvs)) kvs)"

declare rbtreeify_f.simps [simp del] rbtreeify_g.simps [simp del]

lemma rbtreeify_f_code [code]:
  "rbtreeify_f n kvs =
   (if n = 0 then (Empty, kvs)
    else if n = 1 then
      case kvs of (k, v) # kvs' \<Rightarrow> 
        (Branch R Empty k v Empty, kvs')
    else let (n', r) = divmod_nat n 2 in
      if r = 0 then
        case rbtreeify_f n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
          apfst (Branch B t1 k v) (rbtreeify_g n' kvs')
      else case rbtreeify_f n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
          apfst (Branch B t1 k v) (rbtreeify_f n' kvs'))"
by(subst rbtreeify_f.simps)(simp only: Let_def divmod_nat_div_mod prod.simps)

lemma rbtreeify_g_code [code]:
  "rbtreeify_g n kvs =
   (if n = 0 \<or> n = 1 then (Empty, kvs)
    else let (n', r) = divmod_nat n 2 in
      if r = 0 then
        case rbtreeify_g n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
          apfst (Branch B t1 k v) (rbtreeify_g n' kvs')
      else case rbtreeify_f n' kvs of (t1, (k, v) # kvs') \<Rightarrow>
          apfst (Branch B t1 k v) (rbtreeify_g n' kvs'))"
by(subst rbtreeify_g.simps)(simp only: Let_def divmod_nat_div_mod prod.simps)

lemma Suc_double_half: "Suc (2 * n) div 2 = n"
by simp

lemma div2_plus_div2: "n div 2 + n div 2 = (n :: nat) - n mod 2"
by arith

lemma rbtreeify_f_rec_aux_lemma:
  "\<lbrakk>k - n div 2 = Suc k'; n \<le> k; n mod 2 = Suc 0\<rbrakk>
  \<Longrightarrow> k' - n div 2 = k - n"
apply(rule add_right_imp_eq[where a = "n - n div 2"])
apply(subst add_diff_assoc2, arith)
apply(simp add: div2_plus_div2)
done

lemma rbtreeify_f_simps:
  "rbtreeify_f 0 kvs = (RBT_Impl.Empty, kvs)"
  "rbtreeify_f (Suc 0) ((k, v) # kvs) = 
  (Branch R Empty k v Empty, kvs)"
  "0 < n \<Longrightarrow> rbtreeify_f (2 * n) kvs =
   (case rbtreeify_f n kvs of (t1, (k, v) # kvs') \<Rightarrow>
     apfst (Branch B t1 k v) (rbtreeify_g n kvs'))"
  "0 < n \<Longrightarrow> rbtreeify_f (Suc (2 * n)) kvs =
   (case rbtreeify_f n kvs of (t1, (k, v) # kvs') \<Rightarrow> 
     apfst (Branch B t1 k v) (rbtreeify_f n kvs'))"
by(subst (1) rbtreeify_f.simps, simp add: Suc_double_half)+

lemma rbtreeify_g_simps:
  "rbtreeify_g 0 kvs = (Empty, kvs)"
  "rbtreeify_g (Suc 0) kvs = (Empty, kvs)"
  "0 < n \<Longrightarrow> rbtreeify_g (2 * n) kvs =
   (case rbtreeify_g n kvs of (t1, (k, v) # kvs') \<Rightarrow> 
     apfst (Branch B t1 k v) (rbtreeify_g n kvs'))"
  "0 < n \<Longrightarrow> rbtreeify_g (Suc (2 * n)) kvs =
   (case rbtreeify_f n kvs of (t1, (k, v) # kvs') \<Rightarrow> 
     apfst (Branch B t1 k v) (rbtreeify_g n kvs'))"
by(subst (1) rbtreeify_g.simps, simp add: Suc_double_half)+

declare rbtreeify_f_simps[simp] rbtreeify_g_simps[simp]

lemma length_rbtreeify_f: "n \<le> length kvs
  \<Longrightarrow> length (snd (rbtreeify_f n kvs)) = length kvs - n"
  and length_rbtreeify_g:"\<lbrakk> 0 < n; n \<le> Suc (length kvs) \<rbrakk>
  \<Longrightarrow> length (snd (rbtreeify_g n kvs)) = Suc (length kvs) - n"
proof(induction n kvs and n kvs rule: rbtreeify_f_rbtreeify_g.induct)
  case (1 n kvs)
  show ?case
  proof(cases "n \<le> 1")
    case True thus ?thesis using "1.prems"
      by(cases n kvs rule: nat.exhaust[case_product list.exhaust]) auto
  next
    case False
    hence "n \<noteq> 0" "n \<noteq> 1" by simp_all
    note IH = "1.IH"[OF this]
    show ?thesis
    proof(cases "n mod 2 = 0")
      case True
      hence "length (snd (rbtreeify_f n kvs)) = 
        length (snd (rbtreeify_f (2 * (n div 2)) kvs))"
        by(metis minus_nat.diff_0 mult_div_cancel)
      also from "1.prems" False obtain k v kvs' 
        where kvs: "kvs = (k, v) # kvs'" by(cases kvs) auto
      also have "0 < n div 2" using False by(simp) 
      note rbtreeify_f_simps(3)[OF this]
      also note kvs[symmetric] 
      also let ?rest1 = "snd (rbtreeify_f (n div 2) kvs)"
      from "1.prems" have "n div 2 \<le> length kvs" by simp
      with True have len: "length ?rest1 = length kvs - n div 2" by(rule IH)
      with "1.prems" False obtain t1 k' v' kvs''
        where kvs'': "rbtreeify_f (n div 2) kvs = (t1, (k', v') # kvs'')"
         by(cases ?rest1)(auto simp add: snd_def split: prod.split_asm)
      note this also note prod.simps(2) also note list.simps(5) 
      also note prod.simps(2) also note snd_apfst
      also have "0 < n div 2" "n div 2 \<le> Suc (length kvs'')" 
        using len "1.prems" False unfolding kvs'' by simp_all
      with True kvs''[symmetric] refl refl
      have "length (snd (rbtreeify_g (n div 2) kvs'')) = 
        Suc (length kvs'') - n div 2" by(rule IH)
      finally show ?thesis using len[unfolded kvs''] "1.prems" True
        by(simp add: Suc_diff_le[symmetric] mult_2[symmetric] mult_div_cancel)
    next
      case False
      hence "length (snd (rbtreeify_f n kvs)) = 
        length (snd (rbtreeify_f (Suc (2 * (n div 2))) kvs))"
        by(metis Suc_eq_plus1_left comm_semiring_1_class.normalizing_semiring_rules(7)
             mod_2_not_eq_zero_eq_one_nat semiring_div_class.mod_div_equality')
      also from "1.prems" `\<not> n \<le> 1` obtain k v kvs' 
        where kvs: "kvs = (k, v) # kvs'" by(cases kvs) auto
      also have "0 < n div 2" using `\<not> n \<le> 1` by(simp) 
      note rbtreeify_f_simps(4)[OF this]
      also note kvs[symmetric] 
      also let ?rest1 = "snd (rbtreeify_f (n div 2) kvs)"
      from "1.prems" have "n div 2 \<le> length kvs" by simp
      with False have len: "length ?rest1 = length kvs - n div 2" by(rule IH)
      with "1.prems" `\<not> n \<le> 1` obtain t1 k' v' kvs''
        where kvs'': "rbtreeify_f (n div 2) kvs = (t1, (k', v') # kvs'')"
        by(cases ?rest1)(auto simp add: snd_def split: prod.split_asm)
      note this also note prod.simps(2) also note list.simps(5) 
      also note prod.simps(2) also note snd_apfst
      also have "n div 2 \<le> length kvs''" 
        using len "1.prems" False unfolding kvs'' by simp arith
      with False kvs''[symmetric] refl refl
      have "length (snd (rbtreeify_f (n div 2) kvs'')) = length kvs'' - n div 2"
        by(rule IH)
      finally show ?thesis using len[unfolded kvs''] "1.prems" False
        by simp(rule rbtreeify_f_rec_aux_lemma[OF sym])
    qed
  qed
next
  case (2 n kvs)
  show ?case
  proof(cases "n > 1")
    case False with `0 < n` show ?thesis
      by(cases n kvs rule: nat.exhaust[case_product list.exhaust]) simp_all
  next
    case True
    hence "\<not> (n = 0 \<or> n = 1)" by simp
    note IH = "2.IH"[OF this]
    show ?thesis
    proof(cases "n mod 2 = 0")
      case True
      hence "length (snd (rbtreeify_g n kvs)) =
        length (snd (rbtreeify_g (2 * (n div 2)) kvs))"
        by(metis minus_nat.diff_0 mult_div_cancel)
      also from "2.prems" True obtain k v kvs' 
        where kvs: "kvs = (k, v) # kvs'" by(cases kvs) auto
      also have "0 < n div 2" using `1 < n` by(simp) 
      note rbtreeify_g_simps(3)[OF this]
      also note kvs[symmetric] 
      also let ?rest1 = "snd (rbtreeify_g (n div 2) kvs)"
      from "2.prems" `1 < n`
      have "0 < n div 2" "n div 2 \<le> Suc (length kvs)" by simp_all
      with True have len: "length ?rest1 = Suc (length kvs) - n div 2" by(rule IH)
      with "2.prems" obtain t1 k' v' kvs''
        where kvs'': "rbtreeify_g (n div 2) kvs = (t1, (k', v') # kvs'')"
        by(cases ?rest1)(auto simp add: snd_def split: prod.split_asm)
      note this also note prod.simps(2) also note list.simps(5) 
      also note prod.simps(2) also note snd_apfst
      also have "n div 2 \<le> Suc (length kvs'')" 
        using len "2.prems" unfolding kvs'' by simp
      with True kvs''[symmetric] refl refl `0 < n div 2`
      have "length (snd (rbtreeify_g (n div 2) kvs'')) = Suc (length kvs'') - n div 2"
        by(rule IH)
      finally show ?thesis using len[unfolded kvs''] "2.prems" True
        by(simp add: Suc_diff_le[symmetric] mult_2[symmetric] mult_div_cancel)
    next
      case False
      hence "length (snd (rbtreeify_g n kvs)) = 
        length (snd (rbtreeify_g (Suc (2 * (n div 2))) kvs))"
        by(metis Suc_eq_plus1_left comm_semiring_1_class.normalizing_semiring_rules(7) 
            mod_2_not_eq_zero_eq_one_nat semiring_div_class.mod_div_equality')
      also from "2.prems" `1 < n` obtain k v kvs'
        where kvs: "kvs = (k, v) # kvs'" by(cases kvs) auto
      also have "0 < n div 2" using `1 < n` by(simp)
      note rbtreeify_g_simps(4)[OF this]
      also note kvs[symmetric] 
      also let ?rest1 = "snd (rbtreeify_f (n div 2) kvs)"
      from "2.prems" have "n div 2 \<le> length kvs" by simp
      with False have len: "length ?rest1 = length kvs - n div 2" by(rule IH)
      with "2.prems" `1 < n` False obtain t1 k' v' kvs'' 
        where kvs'': "rbtreeify_f (n div 2) kvs = (t1, (k', v') # kvs'')"
        by(cases ?rest1)(auto simp add: snd_def split: prod.split_asm, arith)
      note this also note prod.simps(2) also note list.simps(5) 
      also note prod.simps(2) also note snd_apfst
      also have "n div 2 \<le> Suc (length kvs'')" 
        using len "2.prems" False unfolding kvs'' by simp arith
      with False kvs''[symmetric] refl refl `0 < n div 2`
      have "length (snd (rbtreeify_g (n div 2) kvs'')) = Suc (length kvs'') - n div 2"
        by(rule IH)
      finally show ?thesis using len[unfolded kvs''] "2.prems" False
        by(simp add: div2_plus_div2)
    qed
  qed
qed

lemma rbtreeify_induct [consumes 1, case_names f_0 f_1 f_even f_odd g_0 g_1 g_even g_odd]:
  fixes P Q
  defines "f0 == (\<And>kvs. P 0 kvs)"
  and "f1 == (\<And>k v kvs. P (Suc 0) ((k, v) # kvs))"
  and "feven ==
    (\<And>n kvs t k v kvs'. \<lbrakk> n > 0; n \<le> length kvs; P n kvs; 
       rbtreeify_f n kvs = (t, (k, v) # kvs'); n \<le> Suc (length kvs'); Q n kvs' \<rbrakk> 
     \<Longrightarrow> P (2 * n) kvs)"
  and "fodd == 
    (\<And>n kvs t k v kvs'. \<lbrakk> n > 0; n \<le> length kvs; P n kvs;
       rbtreeify_f n kvs = (t, (k, v) # kvs'); n \<le> length kvs'; P n kvs' \<rbrakk> 
    \<Longrightarrow> P (Suc (2 * n)) kvs)"
  and "g0 == (\<And>kvs. Q 0 kvs)"
  and "g1 == (\<And>kvs. Q (Suc 0) kvs)"
  and "geven == 
    (\<And>n kvs t k v kvs'. \<lbrakk> n > 0; n \<le> Suc (length kvs); Q n kvs; 
       rbtreeify_g n kvs = (t, (k, v) # kvs'); n \<le> Suc (length kvs'); Q n kvs' \<rbrakk>
    \<Longrightarrow> Q (2 * n) kvs)"
  and "godd == 
    (\<And>n kvs t k v kvs'. \<lbrakk> n > 0; n \<le> length kvs; P n kvs;
       rbtreeify_f n kvs = (t, (k, v) # kvs'); n \<le> Suc (length kvs'); Q n kvs' \<rbrakk>
    \<Longrightarrow> Q (Suc (2 * n)) kvs)"
  shows "\<lbrakk> n \<le> length kvs; 
           PROP f0; PROP f1; PROP feven; PROP fodd; 
           PROP g0; PROP g1; PROP geven; PROP godd \<rbrakk>
         \<Longrightarrow> P n kvs"
  and "\<lbrakk> n \<le> Suc (length kvs);
          PROP f0; PROP f1; PROP feven; PROP fodd; 
          PROP g0; PROP g1; PROP geven; PROP godd \<rbrakk>
       \<Longrightarrow> Q n kvs"
proof -
  assume f0: "PROP f0" and f1: "PROP f1" and feven: "PROP feven" and fodd: "PROP fodd"
    and g0: "PROP g0" and g1: "PROP g1" and geven: "PROP geven" and godd: "PROP godd"
  show "n \<le> length kvs \<Longrightarrow> P n kvs" and "n \<le> Suc (length kvs) \<Longrightarrow> Q n kvs"
  proof(induction rule: rbtreeify_f_rbtreeify_g.induct)
    case (1 n kvs)
    show ?case
    proof(cases "n \<le> 1")
      case True thus ?thesis using "1.prems"
        by(cases n kvs rule: nat.exhaust[case_product list.exhaust])
          (auto simp add: f0[unfolded f0_def] f1[unfolded f1_def])
    next
      case False 
      hence ns: "n \<noteq> 0" "n \<noteq> 1" by simp_all
      hence ge0: "n div 2 > 0" by simp
      note IH = "1.IH"[OF ns]
      show ?thesis
      proof(cases "n mod 2 = 0")
        case True note ge0 
        moreover from "1.prems" have n2: "n div 2 \<le> length kvs" by simp
        moreover with True have "P (n div 2) kvs" by(rule IH)
        moreover from length_rbtreeify_f[OF n2] ge0 "1.prems" obtain t k v kvs' 
          where kvs': "rbtreeify_f (n div 2) kvs = (t, (k, v) # kvs')"
          by(cases "snd (rbtreeify_f (n div 2) kvs)")
            (auto simp add: snd_def split: prod.split_asm)
        moreover from "1.prems" length_rbtreeify_f[OF n2] ge0
        have "n div 2 \<le> Suc (length kvs')" by(simp add: kvs')
        moreover with True kvs'[symmetric] refl refl
        have "Q (n div 2) kvs'" by(rule IH)
        moreover note feven[unfolded feven_def]
          (* FIXME: why does by(rule feven[unfolded feven_def]) not work? *)
        ultimately have "P (2 * (n div 2)) kvs" by -
        thus ?thesis using True by (metis div_mod_equality' minus_nat.diff_0 nat_mult_commute)
      next
        case False note ge0
        moreover from "1.prems" have n2: "n div 2 \<le> length kvs" by simp
        moreover with False have "P (n div 2) kvs" by(rule IH)
        moreover from length_rbtreeify_f[OF n2] ge0 "1.prems" obtain t k v kvs' 
          where kvs': "rbtreeify_f (n div 2) kvs = (t, (k, v) # kvs')"
          by(cases "snd (rbtreeify_f (n div 2) kvs)")
            (auto simp add: snd_def split: prod.split_asm)
        moreover from "1.prems" length_rbtreeify_f[OF n2] ge0 False
        have "n div 2 \<le> length kvs'" by(simp add: kvs') arith
        moreover with False kvs'[symmetric] refl refl have "P (n div 2) kvs'" by(rule IH)
        moreover note fodd[unfolded fodd_def]
        ultimately have "P (Suc (2 * (n div 2))) kvs" by -
        thus ?thesis using False 
          by simp (metis One_nat_def Suc_eq_plus1_left le_add_diff_inverse mod_less_eq_dividend mult_div_cancel)
      qed
    qed
  next
    case (2 n kvs)
    show ?case
    proof(cases "n \<le> 1")
      case True thus ?thesis using "2.prems"
        by(cases n kvs rule: nat.exhaust[case_product list.exhaust])
          (auto simp add: g0[unfolded g0_def] g1[unfolded g1_def])
    next
      case False 
      hence ns: "\<not> (n = 0 \<or> n = 1)" by simp
      hence ge0: "n div 2 > 0" by simp
      note IH = "2.IH"[OF ns]
      show ?thesis
      proof(cases "n mod 2 = 0")
        case True note ge0
        moreover from "2.prems" have n2: "n div 2 \<le> Suc (length kvs)" by simp
        moreover with True have "Q (n div 2) kvs" by(rule IH)
        moreover from length_rbtreeify_g[OF ge0 n2] ge0 "2.prems" obtain t k v kvs' 
          where kvs': "rbtreeify_g (n div 2) kvs = (t, (k, v) # kvs')"
          by(cases "snd (rbtreeify_g (n div 2) kvs)")
            (auto simp add: snd_def split: prod.split_asm)
        moreover from "2.prems" length_rbtreeify_g[OF ge0 n2] ge0
        have "n div 2 \<le> Suc (length kvs')" by(simp add: kvs')
        moreover with True kvs'[symmetric] refl refl 
        have "Q (n div 2) kvs'" by(rule IH)
        moreover note geven[unfolded geven_def]
        ultimately have "Q (2 * (n div 2)) kvs" by -
        thus ?thesis using True 
          by(metis div_mod_equality' minus_nat.diff_0 nat_mult_commute)
      next
        case False note ge0
        moreover from "2.prems" have n2: "n div 2 \<le> length kvs" by simp
        moreover with False have "P (n div 2) kvs" by(rule IH)
        moreover from length_rbtreeify_f[OF n2] ge0 "2.prems" False obtain t k v kvs' 
          where kvs': "rbtreeify_f (n div 2) kvs = (t, (k, v) # kvs')"
          by(cases "snd (rbtreeify_f (n div 2) kvs)")
            (auto simp add: snd_def split: prod.split_asm, arith)
        moreover from "2.prems" length_rbtreeify_f[OF n2] ge0 False
        have "n div 2 \<le> Suc (length kvs')" by(simp add: kvs') arith
        moreover with False kvs'[symmetric] refl refl
        have "Q (n div 2) kvs'" by(rule IH)
        moreover note godd[unfolded godd_def]
        ultimately have "Q (Suc (2 * (n div 2))) kvs" by -
        thus ?thesis using False 
          by simp (metis One_nat_def Suc_eq_plus1_left le_add_diff_inverse mod_less_eq_dividend mult_div_cancel)
      qed
    qed
  qed
qed

lemma inv1_rbtreeify_f: "n \<le> length kvs 
  \<Longrightarrow> inv1 (fst (rbtreeify_f n kvs))"
  and inv1_rbtreeify_g: "n \<le> Suc (length kvs)
  \<Longrightarrow> inv1 (fst (rbtreeify_g n kvs))"
by(induct n kvs and n kvs rule: rbtreeify_induct) simp_all

fun plog2 :: "nat \<Rightarrow> nat" 
where "plog2 n = (if n \<le> 1 then 0 else plog2 (n div 2) + 1)"

declare plog2.simps [simp del]

lemma plog2_simps [simp]:
  "plog2 0 = 0" "plog2 (Suc 0) = 0"
  "0 < n \<Longrightarrow> plog2 (2 * n) = 1 + plog2 n"
  "0 < n \<Longrightarrow> plog2 (Suc (2 * n)) = 1 + plog2 n"
by(subst plog2.simps, simp add: Suc_double_half)+

lemma bheight_rbtreeify_f: "n \<le> length kvs
  \<Longrightarrow> bheight (fst (rbtreeify_f n kvs)) = plog2 n"
  and bheight_rbtreeify_g: "n \<le> Suc (length kvs)
  \<Longrightarrow> bheight (fst (rbtreeify_g n kvs)) = plog2 n"
by(induct n kvs and n kvs rule: rbtreeify_induct) simp_all

lemma bheight_rbtreeify_f_eq_plog2I:
  "\<lbrakk> rbtreeify_f n kvs = (t, kvs'); n \<le> length kvs \<rbrakk> 
  \<Longrightarrow> bheight t = plog2 n"
using bheight_rbtreeify_f[of n kvs] by simp

lemma bheight_rbtreeify_g_eq_plog2I: 
  "\<lbrakk> rbtreeify_g n kvs = (t, kvs'); n \<le> Suc (length kvs) \<rbrakk>
  \<Longrightarrow> bheight t = plog2 n"
using bheight_rbtreeify_g[of n kvs] by simp

hide_const (open) plog2

lemma inv2_rbtreeify_f: "n \<le> length kvs
  \<Longrightarrow> inv2 (fst (rbtreeify_f n kvs))"
  and inv2_rbtreeify_g: "n \<le> Suc (length kvs)
  \<Longrightarrow> inv2 (fst (rbtreeify_g n kvs))"
by(induct n kvs and n kvs rule: rbtreeify_induct)
  (auto simp add: bheight_rbtreeify_f bheight_rbtreeify_g 
        intro: bheight_rbtreeify_f_eq_plog2I bheight_rbtreeify_g_eq_plog2I)

lemma "n \<le> length kvs \<Longrightarrow> True"
  and color_of_rbtreeify_g:
  "\<lbrakk> n \<le> Suc (length kvs); 0 < n \<rbrakk> 
  \<Longrightarrow> color_of (fst (rbtreeify_g n kvs)) = B"
by(induct n kvs and n kvs rule: rbtreeify_induct) simp_all

lemma entries_rbtreeify_f_append:
  "n \<le> length kvs 
  \<Longrightarrow> entries (fst (rbtreeify_f n kvs)) @ snd (rbtreeify_f n kvs) = kvs"
  and entries_rbtreeify_g_append: 
  "n \<le> Suc (length kvs) 
  \<Longrightarrow> entries (fst (rbtreeify_g n kvs)) @ snd (rbtreeify_g n kvs) = kvs"
by(induction rule: rbtreeify_induct) simp_all

lemma length_entries_rbtreeify_f:
  "n \<le> length kvs \<Longrightarrow> length (entries (fst (rbtreeify_f n kvs))) = n"
  and length_entries_rbtreeify_g: 
  "n \<le> Suc (length kvs) \<Longrightarrow> length (entries (fst (rbtreeify_g n kvs))) = n - 1"
by(induct rule: rbtreeify_induct) simp_all

lemma rbtreeify_f_conv_drop: 
  "n \<le> length kvs \<Longrightarrow> snd (rbtreeify_f n kvs) = drop n kvs"
using entries_rbtreeify_f_append[of n kvs]
by(simp add: append_eq_conv_conj length_entries_rbtreeify_f)

lemma rbtreeify_g_conv_drop: 
  "n \<le> Suc (length kvs) \<Longrightarrow> snd (rbtreeify_g n kvs) = drop (n - 1) kvs"
using entries_rbtreeify_g_append[of n kvs]
by(simp add: append_eq_conv_conj length_entries_rbtreeify_g)

lemma entries_rbtreeify_f [simp]:
  "n \<le> length kvs \<Longrightarrow> entries (fst (rbtreeify_f n kvs)) = take n kvs"
using entries_rbtreeify_f_append[of n kvs]
by(simp add: append_eq_conv_conj length_entries_rbtreeify_f)

lemma entries_rbtreeify_g [simp]:
  "n \<le> Suc (length kvs) \<Longrightarrow> 
  entries (fst (rbtreeify_g n kvs)) = take (n - 1) kvs"
using entries_rbtreeify_g_append[of n kvs]
by(simp add: append_eq_conv_conj length_entries_rbtreeify_g)

lemma keys_rbtreeify_f [simp]: "n \<le> length kvs
  \<Longrightarrow> keys (fst (rbtreeify_f n kvs)) = take n (map fst kvs)"
by(simp add: keys_def take_map)

lemma keys_rbtreeify_g [simp]: "n \<le> Suc (length kvs)
  \<Longrightarrow> keys (fst (rbtreeify_g n kvs)) = take (n - 1) (map fst kvs)"
by(simp add: keys_def take_map)

lemma rbtreeify_fD: 
  "\<lbrakk> rbtreeify_f n kvs = (t, kvs'); n \<le> length kvs \<rbrakk> 
  \<Longrightarrow> entries t = take n kvs \<and> kvs' = drop n kvs"
using rbtreeify_f_conv_drop[of n kvs] entries_rbtreeify_f[of n kvs] by simp

lemma rbtreeify_gD: 
  "\<lbrakk> rbtreeify_g n kvs = (t, kvs'); n \<le> Suc (length kvs) \<rbrakk>
  \<Longrightarrow> entries t = take (n - 1) kvs \<and> kvs' = drop (n - 1) kvs"
using rbtreeify_g_conv_drop[of n kvs] entries_rbtreeify_g[of n kvs] by simp

lemma entries_rbtreeify [simp]: "entries (rbtreeify kvs) = kvs"
by(simp add: rbtreeify_def entries_rbtreeify_g)

context linorder begin

lemma rbt_sorted_rbtreeify_f: 
  "\<lbrakk> n \<le> length kvs; sorted (map fst kvs); distinct (map fst kvs) \<rbrakk> 
  \<Longrightarrow> rbt_sorted (fst (rbtreeify_f n kvs))"
  and rbt_sorted_rbtreeify_g: 
  "\<lbrakk> n \<le> Suc (length kvs); sorted (map fst kvs); distinct (map fst kvs) \<rbrakk>
  \<Longrightarrow> rbt_sorted (fst (rbtreeify_g n kvs))"
proof(induction n kvs and n kvs rule: rbtreeify_induct)
  case (f_even n kvs t k v kvs')
  from rbtreeify_fD[OF `rbtreeify_f n kvs = (t, (k, v) # kvs')` `n \<le> length kvs`]
  have "entries t = take n kvs"
    and kvs': "drop n kvs = (k, v) # kvs'" by simp_all
  hence unfold: "kvs = take n kvs @ (k, v) # kvs'" by(metis append_take_drop_id)
  from `sorted (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<le> k) \<and> (\<forall>(x, y) \<in> set kvs'. k \<le> x)"
    by(subst (asm) unfold)(auto simp add: sorted_append sorted_Cons)
  moreover from `distinct (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<noteq> k) \<and> (\<forall>(x, y) \<in> set kvs'. x \<noteq> k)"
    by(subst (asm) unfold)(auto intro: rev_image_eqI)
  ultimately have "(\<forall>(x, y) \<in> set (take n kvs). x < k) \<and> (\<forall>(x, y) \<in> set kvs'. k < x)"
    by fastforce
  hence "fst (rbtreeify_f n kvs) |\<guillemotleft> k" "k \<guillemotleft>| fst (rbtreeify_g n kvs')"
    using `n \<le> Suc (length kvs')` `n \<le> length kvs` set_take_subset[of "n - 1" kvs']
    by(auto simp add: ord.rbt_greater_prop ord.rbt_less_prop take_map split_def)
  moreover from `sorted (map fst kvs)` `distinct (map fst kvs)`
  have "rbt_sorted (fst (rbtreeify_f n kvs))" by(rule f_even.IH)
  moreover have "sorted (map fst kvs')" "distinct (map fst kvs')"
    using `sorted (map fst kvs)` `distinct (map fst kvs)`
    by(subst (asm) (1 2) unfold, simp add: sorted_append sorted_Cons)+
  hence "rbt_sorted (fst (rbtreeify_g n kvs'))" by(rule f_even.IH)
  ultimately show ?case
    using `0 < n` `rbtreeify_f n kvs = (t, (k, v) # kvs')` by simp
next
  case (f_odd n kvs t k v kvs')
  from rbtreeify_fD[OF `rbtreeify_f n kvs = (t, (k, v) # kvs')` `n \<le> length kvs`]
  have "entries t = take n kvs" 
    and kvs': "drop n kvs = (k, v) # kvs'" by simp_all
  hence unfold: "kvs = take n kvs @ (k, v) # kvs'" by(metis append_take_drop_id)
  from `sorted (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<le> k) \<and> (\<forall>(x, y) \<in> set kvs'. k \<le> x)"
    by(subst (asm) unfold)(auto simp add: sorted_append sorted_Cons)
  moreover from `distinct (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<noteq> k) \<and> (\<forall>(x, y) \<in> set kvs'. x \<noteq> k)"
    by(subst (asm) unfold)(auto intro: rev_image_eqI)
  ultimately have "(\<forall>(x, y) \<in> set (take n kvs). x < k) \<and> (\<forall>(x, y) \<in> set kvs'. k < x)"
    by fastforce
  hence "fst (rbtreeify_f n kvs) |\<guillemotleft> k" "k \<guillemotleft>| fst (rbtreeify_f n kvs')"
    using `n \<le> length kvs'` `n \<le> length kvs` set_take_subset[of n kvs']
    by(auto simp add: rbt_greater_prop rbt_less_prop take_map split_def)
  moreover from `sorted (map fst kvs)` `distinct (map fst kvs)`
  have "rbt_sorted (fst (rbtreeify_f n kvs))" by(rule f_odd.IH)
  moreover have "sorted (map fst kvs')" "distinct (map fst kvs')"
    using `sorted (map fst kvs)` `distinct (map fst kvs)`
    by(subst (asm) (1 2) unfold, simp add: sorted_append sorted_Cons)+
  hence "rbt_sorted (fst (rbtreeify_f n kvs'))" by(rule f_odd.IH)
  ultimately show ?case 
    using `0 < n` `rbtreeify_f n kvs = (t, (k, v) # kvs')` by simp
next
  case (g_even n kvs t k v kvs')
  from rbtreeify_gD[OF `rbtreeify_g n kvs = (t, (k, v) # kvs')` `n \<le> Suc (length kvs)`]
  have t: "entries t = take (n - 1) kvs" 
    and kvs': "drop (n - 1) kvs = (k, v) # kvs'" by simp_all
  hence unfold: "kvs = take (n - 1) kvs @ (k, v) # kvs'" by(metis append_take_drop_id)
  from `sorted (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take (n - 1) kvs). x \<le> k) \<and> (\<forall>(x, y) \<in> set kvs'. k \<le> x)"
    by(subst (asm) unfold)(auto simp add: sorted_append sorted_Cons)
  moreover from `distinct (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take (n - 1) kvs). x \<noteq> k) \<and> (\<forall>(x, y) \<in> set kvs'. x \<noteq> k)"
    by(subst (asm) unfold)(auto intro: rev_image_eqI)
  ultimately have "(\<forall>(x, y) \<in> set (take (n - 1) kvs). x < k) \<and> (\<forall>(x, y) \<in> set kvs'. k < x)"
    by fastforce
  hence "fst (rbtreeify_g n kvs) |\<guillemotleft> k" "k \<guillemotleft>| fst (rbtreeify_g n kvs')"
    using `n \<le> Suc (length kvs')` `n \<le> Suc (length kvs)` set_take_subset[of "n - 1" kvs']
    by(auto simp add: rbt_greater_prop rbt_less_prop take_map split_def)
  moreover from `sorted (map fst kvs)` `distinct (map fst kvs)`
  have "rbt_sorted (fst (rbtreeify_g n kvs))" by(rule g_even.IH)
  moreover have "sorted (map fst kvs')" "distinct (map fst kvs')"
    using `sorted (map fst kvs)` `distinct (map fst kvs)`
    by(subst (asm) (1 2) unfold, simp add: sorted_append sorted_Cons)+
  hence "rbt_sorted (fst (rbtreeify_g n kvs'))" by(rule g_even.IH)
  ultimately show ?case using `0 < n` `rbtreeify_g n kvs = (t, (k, v) # kvs')` by simp
next
  case (g_odd n kvs t k v kvs')
  from rbtreeify_fD[OF `rbtreeify_f n kvs = (t, (k, v) # kvs')` `n \<le> length kvs`]
  have "entries t = take n kvs"
    and kvs': "drop n kvs = (k, v) # kvs'" by simp_all
  hence unfold: "kvs = take n kvs @ (k, v) # kvs'" by(metis append_take_drop_id)
  from `sorted (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<le> k) \<and> (\<forall>(x, y) \<in> set kvs'. k \<le> x)"
    by(subst (asm) unfold)(auto simp add: sorted_append sorted_Cons)
  moreover from `distinct (map fst kvs)` kvs'
  have "(\<forall>(x, y) \<in> set (take n kvs). x \<noteq> k) \<and> (\<forall>(x, y) \<in> set kvs'. x \<noteq> k)"
    by(subst (asm) unfold)(auto intro: rev_image_eqI)
  ultimately have "(\<forall>(x, y) \<in> set (take n kvs). x < k) \<and> (\<forall>(x, y) \<in> set kvs'. k < x)"
    by fastforce
  hence "fst (rbtreeify_f n kvs) |\<guillemotleft> k" "k \<guillemotleft>| fst (rbtreeify_g n kvs')"
    using `n \<le> Suc (length kvs')` `n \<le> length kvs` set_take_subset[of "n - 1" kvs']
    by(auto simp add: rbt_greater_prop rbt_less_prop take_map split_def)
  moreover from `sorted (map fst kvs)` `distinct (map fst kvs)`
  have "rbt_sorted (fst (rbtreeify_f n kvs))" by(rule g_odd.IH)
  moreover have "sorted (map fst kvs')" "distinct (map fst kvs')"
    using `sorted (map fst kvs)` `distinct (map fst kvs)`
    by(subst (asm) (1 2) unfold, simp add: sorted_append sorted_Cons)+
  hence "rbt_sorted (fst (rbtreeify_g n kvs'))" by(rule g_odd.IH)
  ultimately show ?case
    using `0 < n` `rbtreeify_f n kvs = (t, (k, v) # kvs')` by simp
qed simp_all

lemma rbt_sorted_rbtreeify: 
  "\<lbrakk> sorted (map fst kvs); distinct (map fst kvs) \<rbrakk> \<Longrightarrow> rbt_sorted (rbtreeify kvs)"
by(simp add: rbtreeify_def rbt_sorted_rbtreeify_g)

lemma is_rbt_rbtreeify: 
  "\<lbrakk> sorted (map fst kvs); distinct (map fst kvs) \<rbrakk>
  \<Longrightarrow> is_rbt (rbtreeify kvs)"
by(simp add: is_rbt_def rbtreeify_def inv1_rbtreeify_g inv2_rbtreeify_g rbt_sorted_rbtreeify_g color_of_rbtreeify_g)

lemma rbt_lookup_rbtreeify:
  "\<lbrakk> sorted (map fst kvs); distinct (map fst kvs) \<rbrakk> \<Longrightarrow> 
  rbt_lookup (rbtreeify kvs) = map_of kvs"
by(simp add: map_of_entries[symmetric] rbt_sorted_rbtreeify)

end

text {* 
  Functions to compare the height of two rbt trees, taken from 
  Andrew W. Appel, Efficient Verified Red-Black Trees (September 2011)
*}

fun skip_red :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "skip_red (Branch color.R l k v r) = l"
| "skip_red t = t"

fun skip_black :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "skip_black (Branch color.B l k v r) = l"
| "skip_black t = t"

datatype compare = LT | GT | EQ

partial_function (tailrec) compare_height :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> compare"
where
  "compare_height sx s t tx =
  (case (skip_red sx, skip_red s, skip_red t, skip_red tx) of
     (Branch _ sx' _ _ _, Branch _ s' _ _ _, Branch _ t' _ _ _, Branch _ tx' _ _ _) \<Rightarrow> 
       compare_height (skip_black sx') s' t' (skip_black tx')
   | (_, rbt.Empty, _, Branch _ _ _ _ _) \<Rightarrow> LT
   | (Branch _ _ _ _ _, _, rbt.Empty, _) \<Rightarrow> GT
   | (Branch _ sx' _ _ _, Branch _ s' _ _ _, Branch _ t' _ _ _, rbt.Empty) \<Rightarrow>
       compare_height (skip_black sx') s' t' rbt.Empty
   | (rbt.Empty, Branch _ s' _ _ _, Branch _ t' _ _ _, Branch _ tx' _ _ _) \<Rightarrow>
       compare_height rbt.Empty s' t' (skip_black tx')
   | _ \<Rightarrow> EQ)"

declare compare_height.simps [code]

hide_type (open) compare
hide_const (open)
  compare_height skip_black skip_red LT GT EQ compare_case compare_rec 
  Abs_compare Rep_compare compare_rep_set
hide_fact (open)
  Abs_compare_cases Abs_compare_induct Abs_compare_inject Abs_compare_inverse
  Rep_compare Rep_compare_cases Rep_compare_induct Rep_compare_inject Rep_compare_inverse
  compare.simps compare.exhaust compare.induct compare.recs compare.simps
  compare.size compare.case_cong compare.weak_case_cong compare.cases 
  compare.nchotomy compare.split compare.split_asm compare_rec_def
  compare.eq.refl compare.eq.simps
  compare.EQ_def compare.GT_def compare.LT_def
  equal_compare_def
  skip_red_def skip_red.simps skip_red.induct 
  skip_black_def skip_black.simps skip_black.induct
  compare_height.simps

subsection {* union and intersection of sorted associative lists *}

context ord begin

function sunion_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" 
where
  "sunion_with f ((k, v) # as) ((k', v') # bs) =
   (if k > k' then (k', v') # sunion_with f ((k, v) # as) bs
    else if k < k' then (k, v) # sunion_with f as ((k', v') # bs)
    else (k, f k v v') # sunion_with f as bs)"
| "sunion_with f [] bs = bs"
| "sunion_with f as [] = as"
by pat_completeness auto
termination by lexicographic_order

function sinter_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
where
  "sinter_with f ((k, v) # as) ((k', v') # bs) =
  (if k > k' then sinter_with f ((k, v) # as) bs
   else if k < k' then sinter_with f as ((k', v') # bs)
   else (k, f k v v') # sinter_with f as bs)"
| "sinter_with f [] _ = []"
| "sinter_with f _ [] = []"
by pat_completeness auto
termination by lexicographic_order

end

declare ord.sunion_with.simps [code] ord.sinter_with.simps[code]

context linorder begin

lemma set_fst_sunion_with: 
  "set (map fst (sunion_with f xs ys)) = set (map fst xs) \<union> set (map fst ys)"
by(induct f xs ys rule: sunion_with.induct) auto

lemma sorted_sunion_with [simp]:
  "\<lbrakk> sorted (map fst xs); sorted (map fst ys) \<rbrakk> 
  \<Longrightarrow> sorted (map fst (sunion_with f xs ys))"
by(induct f xs ys rule: sunion_with.induct)
  (auto simp add: sorted_Cons set_fst_sunion_with simp del: set_map)

lemma distinct_sunion_with [simp]:
  "\<lbrakk> distinct (map fst xs); distinct (map fst ys); sorted (map fst xs); sorted (map fst ys) \<rbrakk>
  \<Longrightarrow> distinct (map fst (sunion_with f xs ys))"
proof(induct f xs ys rule: sunion_with.induct)
  case (1 f k v xs k' v' ys)
  have "\<lbrakk> \<not> k < k'; \<not> k' < k \<rbrakk> \<Longrightarrow> k = k'" by simp
  thus ?case using "1"
    by(auto simp add: set_fst_sunion_with sorted_Cons simp del: set_map)
qed simp_all

lemma map_of_sunion_with: 
  "\<lbrakk> sorted (map fst xs); sorted (map fst ys) \<rbrakk>
  \<Longrightarrow> map_of (sunion_with f xs ys) k = 
  (case map_of xs k of None \<Rightarrow> map_of ys k 
  | Some v \<Rightarrow> case map_of ys k of None \<Rightarrow> Some v 
              | Some w \<Rightarrow> Some (f k v w))"
by(induct f xs ys rule: sunion_with.induct)(auto simp add: sorted_Cons split: option.split dest: map_of_SomeD bspec)

lemma set_fst_sinter_with [simp]:
  "\<lbrakk> sorted (map fst xs); sorted (map fst ys) \<rbrakk>
  \<Longrightarrow> set (map fst (sinter_with f xs ys)) = set (map fst xs) \<inter> set (map fst ys)"
by(induct f xs ys rule: sinter_with.induct)(auto simp add: sorted_Cons simp del: set_map)

lemma set_fst_sinter_with_subset1:
  "set (map fst (sinter_with f xs ys)) \<subseteq> set (map fst xs)"
by(induct f xs ys rule: sinter_with.induct) auto

lemma set_fst_sinter_with_subset2:
  "set (map fst (sinter_with f xs ys)) \<subseteq> set (map fst ys)"
by(induct f xs ys rule: sinter_with.induct)(auto simp del: set_map)

lemma sorted_sinter_with [simp]:
  "\<lbrakk> sorted (map fst xs); sorted (map fst ys) \<rbrakk>
  \<Longrightarrow> sorted (map fst (sinter_with f xs ys))"
by(induct f xs ys rule: sinter_with.induct)(auto simp add: sorted_Cons simp del: set_map)

lemma distinct_sinter_with [simp]:
  "\<lbrakk> distinct (map fst xs); distinct (map fst ys) \<rbrakk>
  \<Longrightarrow> distinct (map fst (sinter_with f xs ys))"
proof(induct f xs ys rule: sinter_with.induct)
  case (1 f k v as k' v' bs)
  have "\<lbrakk> \<not> k < k'; \<not> k' < k \<rbrakk> \<Longrightarrow> k = k'" by simp
  thus ?case using "1" set_fst_sinter_with_subset1[of f as bs]
    set_fst_sinter_with_subset2[of f as bs]
    by(auto simp del: set_map)
qed simp_all

lemma map_of_sinter_with:
  "\<lbrakk> sorted (map fst xs); sorted (map fst ys) \<rbrakk>
  \<Longrightarrow> map_of (sinter_with f xs ys) k = 
  (case map_of xs k of None \<Rightarrow> None | Some v \<Rightarrow> Option.map (f k v) (map_of ys k))"
apply(induct f xs ys rule: sinter_with.induct)
apply(auto simp add: sorted_Cons Option.map_def split: option.splits dest: map_of_SomeD bspec)
done

end

lemma distinct_map_of_rev: "distinct (map fst xs) \<Longrightarrow> map_of (rev xs) = map_of xs"
by(induct xs)(auto 4 3 simp add: map_add_def intro!: ext split: option.split intro: rev_image_eqI)

lemma map_map_filter: 
  "map f (List.map_filter g xs) = List.map_filter (Option.map f \<circ> g) xs"
by(auto simp add: List.map_filter_def)

lemma map_filter_option_map_const: 
  "List.map_filter (\<lambda>x. Option.map (\<lambda>y. f x) (g (f x))) xs = filter (\<lambda>x. g x \<noteq> None) (map f xs)"
by(auto simp add: map_filter_def filter_map o_def)

lemma set_map_filter: "set (List.map_filter P xs) = the ` (P ` set xs - {None})"
by(auto simp add: List.map_filter_def intro: rev_image_eqI)

context ord begin

definition rbt_union_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_union_with_key f t1 t2 =
  (case RBT_Impl.compare_height t1 t1 t2 t2
   of compare.EQ \<Rightarrow> rbtreeify (sunion_with f (entries t1) (entries t2))
    | compare.LT \<Rightarrow> fold (rbt_insert_with_key (\<lambda>k v w. f k w v)) t1 t2
    | compare.GT \<Rightarrow> fold (rbt_insert_with_key f) t2 t1)"

definition rbt_union_with where
  "rbt_union_with f = rbt_union_with_key (\<lambda>_. f)"

definition rbt_union where
  "rbt_union = rbt_union_with_key (%_ _ rv. rv)"

definition rbt_inter_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_inter_with_key f t1 t2 =
  (case RBT_Impl.compare_height t1 t1 t2 t2 
   of compare.EQ \<Rightarrow> rbtreeify (sinter_with f (entries t1) (entries t2))
    | compare.LT \<Rightarrow> rbtreeify (List.map_filter (\<lambda>(k, v). Option.map (\<lambda>w. (k, f k v w)) (rbt_lookup t2 k)) (entries t1))
    | compare.GT \<Rightarrow> rbtreeify (List.map_filter (\<lambda>(k, v). Option.map (\<lambda>w. (k, f k w v)) (rbt_lookup t1 k)) (entries t2)))"

definition rbt_inter_with where
  "rbt_inter_with f = rbt_inter_with_key (\<lambda>_. f)"

definition rbt_inter where
  "rbt_inter = rbt_inter_with_key (\<lambda>_ _ rv. rv)"

end

context linorder begin

lemma rbt_sorted_entries_right_unique:
  "\<lbrakk> (k, v) \<in> set (entries t); (k, v') \<in> set (entries t); 
     rbt_sorted t \<rbrakk> \<Longrightarrow> v = v'"
by(auto dest!: distinct_entries inj_onD[where x="(k, v)" and y="(k, v')"] simp add: distinct_map)

lemma rbt_sorted_fold_rbt_insertwk:
  "rbt_sorted t \<Longrightarrow> rbt_sorted (List.fold (\<lambda>(k, v). rbt_insert_with_key f k v) xs t)"
by(induct xs rule: rev_induct)(auto simp add: rbt_insertwk_rbt_sorted)

lemma is_rbt_fold_rbt_insertwk:
  assumes "is_rbt t1"
  shows "is_rbt (fold (rbt_insert_with_key f) t2 t1)"
proof -
  def xs \<equiv> "entries t2"
  from assms show ?thesis unfolding fold_def xs_def[symmetric]
    by(induct xs rule: rev_induct)(auto simp add: rbt_insertwk_is_rbt)
qed

lemma rbt_lookup_fold_rbt_insertwk:
  assumes t1: "rbt_sorted t1" and t2: "rbt_sorted t2"
  shows "rbt_lookup (fold (rbt_insert_with_key f) t1 t2) k =
  (case rbt_lookup t1 k of None \<Rightarrow> rbt_lookup t2 k
   | Some v \<Rightarrow> case rbt_lookup t2 k of None \<Rightarrow> Some v
               | Some w \<Rightarrow> Some (f k w v))"
proof -
  def xs \<equiv> "entries t1"
  hence dt1: "distinct (map fst xs)" using t1 by(simp add: distinct_entries)
  with t2 show ?thesis
    unfolding fold_def map_of_entries[OF t1, symmetric]
      xs_def[symmetric] distinct_map_of_rev[OF dt1, symmetric]
    apply(induct xs rule: rev_induct)
    apply(auto simp add: rbt_lookup_rbt_insertwk rbt_sorted_fold_rbt_insertwk split: option.splits)
    apply(auto simp add: distinct_map_of_rev intro: rev_image_eqI)
    done
qed

lemma is_rbt_rbt_unionwk [simp]:
  "\<lbrakk> is_rbt t1; is_rbt t2 \<rbrakk> \<Longrightarrow> is_rbt (rbt_union_with_key f t1 t2)"
by(simp add: rbt_union_with_key_def Let_def is_rbt_fold_rbt_insertwk is_rbt_rbtreeify rbt_sorted_entries distinct_entries split: compare.split)

lemma rbt_lookup_rbt_unionwk:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk> 
  \<Longrightarrow> rbt_lookup (rbt_union_with_key f t1 t2) k = 
  (case rbt_lookup t1 k of None \<Rightarrow> rbt_lookup t2 k 
   | Some v \<Rightarrow> case rbt_lookup t2 k of None \<Rightarrow> Some v 
              | Some w \<Rightarrow> Some (f k v w))"
by(auto simp add: rbt_union_with_key_def Let_def rbt_lookup_fold_rbt_insertwk rbt_sorted_entries distinct_entries map_of_sunion_with map_of_entries rbt_lookup_rbtreeify split: option.split compare.split)

lemma rbt_unionw_is_rbt: "\<lbrakk> is_rbt lt; is_rbt rt \<rbrakk> \<Longrightarrow> is_rbt (rbt_union_with f lt rt)"
by(simp add: rbt_union_with_def)

lemma rbt_union_is_rbt: "\<lbrakk> is_rbt lt; is_rbt rt \<rbrakk> \<Longrightarrow> is_rbt (rbt_union lt rt)"
by(simp add: rbt_union_def)

lemma rbt_lookup_rbt_union:
  "\<lbrakk> rbt_sorted s; rbt_sorted t \<rbrakk> \<Longrightarrow>
  rbt_lookup (rbt_union s t) = rbt_lookup s ++ rbt_lookup t"
by(rule ext)(simp add: rbt_lookup_rbt_unionwk rbt_union_def map_add_def split: option.split)

lemma rbt_interwk_is_rbt [simp]:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk> \<Longrightarrow> is_rbt (rbt_inter_with_key f t1 t2)"
by(auto simp add: rbt_inter_with_key_def Let_def map_map_filter split_def o_def option_map_comp map_filter_option_map_const sorted_filter[where f=id, simplified] rbt_sorted_entries distinct_entries intro: is_rbt_rbtreeify split: compare.split)

lemma rbt_interw_is_rbt:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk> \<Longrightarrow> is_rbt (rbt_inter_with f t1 t2)"
by(simp add: rbt_inter_with_def)

lemma rbt_inter_is_rbt:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk> \<Longrightarrow> is_rbt (rbt_inter t1 t2)"
by(simp add: rbt_inter_def)

lemma rbt_lookup_rbt_interwk:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk>
  \<Longrightarrow> rbt_lookup (rbt_inter_with_key f t1 t2) k =
  (case rbt_lookup t1 k of None \<Rightarrow> None 
   | Some v \<Rightarrow> case rbt_lookup t2 k of None \<Rightarrow> None
               | Some w \<Rightarrow> Some (f k v w))"
by(auto 4 3 simp add: rbt_inter_with_key_def Let_def map_of_entries[symmetric] rbt_lookup_rbtreeify map_map_filter split_def o_def option_map_comp map_filter_option_map_const sorted_filter[where f=id, simplified] rbt_sorted_entries distinct_entries map_of_sinter_with map_of_eq_None_iff set_map_filter split: option.split compare.split intro: rev_image_eqI dest: rbt_sorted_entries_right_unique)

lemma rbt_lookup_rbt_inter:
  "\<lbrakk> rbt_sorted t1; rbt_sorted t2 \<rbrakk>
  \<Longrightarrow> rbt_lookup (rbt_inter t1 t2) = rbt_lookup t2 |` dom (rbt_lookup t1)"
by(auto simp add: rbt_inter_def rbt_lookup_rbt_interwk restrict_map_def split: option.split)

end


subsection {* Code generator setup *}

lemmas [code] =
  ord.rbt_less_prop
  ord.rbt_greater_prop
  ord.rbt_sorted.simps
  ord.rbt_lookup.simps
  ord.is_rbt_def
  ord.rbt_ins.simps
  ord.rbt_insert_with_key_def
  ord.rbt_insertw_def
  ord.rbt_insert_def
  ord.rbt_del_from_left.simps
  ord.rbt_del_from_right.simps
  ord.rbt_del.simps
  ord.rbt_delete_def
  ord.sunion_with.simps
  ord.sinter_with.simps
  ord.rbt_union_with_key_def
  ord.rbt_union_with_def
  ord.rbt_union_def
  ord.rbt_inter_with_key_def
  ord.rbt_inter_with_def
  ord.rbt_inter_def
  ord.rbt_map_entry.simps
  ord.rbt_bulkload_def

text {* More efficient implementations for @{term entries} and @{term keys} *}

definition gen_entries :: 
  "(('a \<times> 'b) \<times> ('a, 'b) rbt) list \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a \<times> 'b) list"
where
  "gen_entries kvts t = entries t @ concat (map (\<lambda>(kv, t). kv # entries t) kvts)"

lemma gen_entries_simps [simp, code]:
  "gen_entries [] Empty = []"
  "gen_entries ((kv, t) # kvts) Empty = kv # gen_entries kvts t"
  "gen_entries kvts (Branch c l k v r) = gen_entries (((k, v), r) # kvts) l"
by(simp_all add: gen_entries_def)

lemma entries_code [code]:
  "entries = gen_entries []"
by(simp add: gen_entries_def fun_eq_iff)

definition gen_keys :: "('a \<times> ('a, 'b) rbt) list \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'a list"
where "gen_keys kts t = RBT_Impl.keys t @ concat (List.map (\<lambda>(k, t). k # keys t) kts)"

lemma gen_keys_simps [simp, code]:
  "gen_keys [] Empty = []"
  "gen_keys ((k, t) # kts) Empty = k # gen_keys kts t"
  "gen_keys kts (Branch c l k v r) = gen_keys ((k, r) # kts) l"
by(simp_all add: gen_keys_def)

lemma keys_code [code]:
  "keys = gen_keys []"
by(simp add: gen_keys_def fun_eq_iff)

text {* Restore original type constraints for constants *}
setup {*
  fold Sign.add_const_constraint
    [(@{const_name rbt_less}, SOME @{typ "('a :: order) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"}),
     (@{const_name rbt_greater}, SOME @{typ "('a :: order) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"}),
     (@{const_name rbt_sorted}, SOME @{typ "('a :: linorder, 'b) rbt \<Rightarrow> bool"}),
     (@{const_name rbt_lookup}, SOME @{typ "('a :: linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"}),
     (@{const_name is_rbt}, SOME @{typ "('a :: linorder, 'b) rbt \<Rightarrow> bool"}),
     (@{const_name rbt_ins}, SOME @{typ "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_insert_with_key}, SOME @{typ "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_insert_with}, SOME @{typ "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a :: linorder) \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_insert}, SOME @{typ "('a :: linorder) \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_del_from_left}, SOME @{typ "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_del_from_right}, SOME @{typ "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_del}, SOME @{typ "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_delete}, SOME @{typ "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_union_with_key}, SOME @{typ "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_union_with}, SOME @{typ "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_union}, SOME @{typ "('a\<Colon>linorder,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_map_entry}, SOME @{typ "'a\<Colon>linorder \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"}),
     (@{const_name rbt_bulkload}, SOME @{typ "('a \<times> 'b) list \<Rightarrow> ('a\<Colon>linorder,'b) rbt"})]
*}

hide_const (open) R B Empty entries keys fold gen_keys gen_entries

end
