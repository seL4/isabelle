(*  Title:      RBT.thy
    Author:     Markus Reiter, TU Muenchen
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Red-Black Trees *}

(*<*)
theory RBT
imports Main AssocList
begin

datatype color = R | B
datatype ('a,'b)"rbt" = Empty | Tr color "('a,'b)rbt" 'a 'b "('a,'b)rbt"

text {* Search tree properties *}

primrec
  pin_tree :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> bool"
where
  "pin_tree k v Empty = False"
| "pin_tree k v (Tr c l x y r) = (k = x \<and> v = y \<or> pin_tree k v l \<or> pin_tree k v r)"

primrec
  keys :: "('k,'v) rbt \<Rightarrow> 'k set"
where
  "keys Empty = {}"
| "keys (Tr _ l k _ r) = { k } \<union> keys l \<union> keys r"

lemma pint_keys: "pin_tree k v t \<Longrightarrow> k \<in> keys t" by (induct t) auto

primrec tlt :: "'a\<Colon>order \<Rightarrow> ('a,'b) rbt \<Rightarrow> bool"
where
  "tlt k Empty = True"
| "tlt k (Tr c lt kt v rt) = (kt < k \<and> tlt k lt \<and> tlt k rt)"

abbreviation tllt (infix "|\<guillemotleft>" 50)
where "t |\<guillemotleft> x == tlt x t"

primrec tgt :: "'a\<Colon>order \<Rightarrow> ('a,'b) rbt \<Rightarrow> bool" (infix "\<guillemotleft>|" 50) 
where
  "tgt k Empty = True"
| "tgt k (Tr c lt kt v rt) = (k < kt \<and> tgt k lt \<and> tgt k rt)"

lemma tlt_prop: "(t |\<guillemotleft> k) = (\<forall>x\<in>keys t. x < k)" by (induct t) auto
lemma tgt_prop: "(k \<guillemotleft>| t) = (\<forall>x\<in>keys t. k < x)" by (induct t) auto
lemmas tlgt_props = tlt_prop tgt_prop

lemmas tgt_nit = tgt_prop pint_keys
lemmas tlt_nit = tlt_prop pint_keys

lemma tlt_trans: "\<lbrakk> t |\<guillemotleft> x; x < y \<rbrakk> \<Longrightarrow> t |\<guillemotleft> y"
  and tgt_trans: "\<lbrakk> x < y; y \<guillemotleft>| t\<rbrakk> \<Longrightarrow> x \<guillemotleft>| t"
by (auto simp: tlgt_props)


primrec st :: "('a::linorder, 'b) rbt \<Rightarrow> bool"
where
  "st Empty = True"
| "st (Tr c l k v r) = (l |\<guillemotleft> k \<and> k \<guillemotleft>| r \<and> st l \<and> st r)"

primrec map_of :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "map_of Empty k = None"
| "map_of (Tr _ l x y r) k = (if k < x then map_of l k else if x < k then map_of r k else Some y)"

lemma map_of_tlt[simp]: "t |\<guillemotleft> k \<Longrightarrow> map_of t k = None" 
by (induct t) auto

lemma map_of_tgt[simp]: "k \<guillemotleft>| t \<Longrightarrow> map_of t k = None"
by (induct t) auto

lemma mapof_keys: "st t \<Longrightarrow> dom (map_of t) = keys t"
by (induct t) (auto simp: dom_def tgt_prop tlt_prop)

lemma mapof_pit: "st t \<Longrightarrow> (map_of t k = Some v) = pin_tree k v t"
by (induct t) (auto simp: tlt_prop tgt_prop pint_keys)

lemma map_of_Empty: "map_of Empty = empty"
by (rule ext) simp

(* a kind of extensionality *)
lemma mapof_from_pit: 
  assumes st: "st t1" "st t2" 
  and eq: "\<And>v. pin_tree (k\<Colon>'a\<Colon>linorder) v t1 = pin_tree k v t2" 
  shows "map_of t1 k = map_of t2 k"
proof (cases "map_of t1 k")
  case None
  then have "\<And>v. \<not> pin_tree k v t1"
    by (simp add: mapof_pit[symmetric] st)
  with None show ?thesis
    by (cases "map_of t2 k") (auto simp: mapof_pit st eq)
next
  case (Some a)
  then show ?thesis
    apply (cases "map_of t2 k")
    apply (auto simp: mapof_pit st eq)
    by (auto simp add: mapof_pit[symmetric] st Some)
qed

subsection {* Red-black properties *}

primrec treec :: "('a,'b) rbt \<Rightarrow> color"
where
  "treec Empty = B"
| "treec (Tr c _ _ _ _) = c"

primrec inv1 :: "('a,'b) rbt \<Rightarrow> bool"
where
  "inv1 Empty = True"
| "inv1 (Tr c lt k v rt) = (inv1 lt \<and> inv1 rt \<and> (c = B \<or> treec lt = B \<and> treec rt = B))"

(* Weaker version *)
primrec inv1l :: "('a,'b) rbt \<Rightarrow> bool"
where
  "inv1l Empty = True"
| "inv1l (Tr c l k v r) = (inv1 l \<and> inv1 r)"
lemma [simp]: "inv1 t \<Longrightarrow> inv1l t" by (cases t) simp+

primrec bh :: "('a,'b) rbt \<Rightarrow> nat"
where
  "bh Empty = 0"
| "bh (Tr c lt k v rt) = (if c = B then Suc (bh lt) else bh lt)"

primrec inv2 :: "('a,'b) rbt \<Rightarrow> bool"
where
  "inv2 Empty = True"
| "inv2 (Tr c lt k v rt) = (inv2 lt \<and> inv2 rt \<and> bh lt = bh rt)"

definition
  "isrbt t = (inv1 t \<and> inv2 t \<and> treec t = B \<and> st t)"

lemma isrbt_st[simp]: "isrbt t \<Longrightarrow> st t" by (simp add: isrbt_def)

lemma rbt_cases:
  obtains (Empty) "t = Empty" 
  | (Red) l k v r where "t = Tr R l k v r" 
  | (Black) l k v r where "t = Tr B l k v r" 
by (cases t, simp) (case_tac "color", auto)

theorem Empty_isrbt[simp]: "isrbt Empty"
unfolding isrbt_def by simp


subsection {* Insertion *}

fun (* slow, due to massive case splitting *)
  balance :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balance (Tr R a w x b) s t (Tr R c y z d) = Tr R (Tr B a w x b) s t (Tr B c y z d)" |
  "balance (Tr R (Tr R a w x b) s t c) y z d = Tr R (Tr B a w x b) s t (Tr B c y z d)" |
  "balance (Tr R a w x (Tr R b s t c)) y z d = Tr R (Tr B a w x b) s t (Tr B c y z d)" |
  "balance a w x (Tr R b s t (Tr R c y z d)) = Tr R (Tr B a w x b) s t (Tr B c y z d)" |
  "balance a w x (Tr R (Tr R b s t c) y z d) = Tr R (Tr B a w x b) s t (Tr B c y z d)" |
  "balance a s t b = Tr B a s t b"

lemma balance_inv1: "\<lbrakk>inv1l l; inv1l r\<rbrakk> \<Longrightarrow> inv1 (balance l k v r)" 
  by (induct l k v r rule: balance.induct) auto

lemma balance_bh: "bh l = bh r \<Longrightarrow> bh (balance l k v r) = Suc (bh l)"
  by (induct l k v r rule: balance.induct) auto

lemma balance_inv2: 
  assumes "inv2 l" "inv2 r" "bh l = bh r"
  shows "inv2 (balance l k v r)"
  using assms
  by (induct l k v r rule: balance.induct) auto

lemma balance_tgt[simp]: "(v \<guillemotleft>| balance a k x b) = (v \<guillemotleft>| a \<and> v \<guillemotleft>| b \<and> v < k)" 
  by (induct a k x b rule: balance.induct) auto

lemma balance_tlt[simp]: "(balance a k x b |\<guillemotleft> v) = (a |\<guillemotleft> v \<and> b |\<guillemotleft> v \<and> k < v)"
  by (induct a k x b rule: balance.induct) auto

lemma balance_st: 
  fixes k :: "'a::linorder"
  assumes "st l" "st r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "st (balance l k v r)"
using assms proof (induct l k v r rule: balance.induct)
  case ("2_2" a x w b y t c z s va vb vd vc)
  hence "y < z \<and> z \<guillemotleft>| Tr B va vb vd vc" 
    by (auto simp add: tlgt_props)
  hence "tgt y (Tr B va vb vd vc)" by (blast dest: tgt_trans)
  with "2_2" show ?case by simp
next
  case ("3_2" va vb vd vc x w b y s c z)
  from "3_2" have "x < y \<and> tlt x (Tr B va vb vd vc)" 
    by (simp add: tlt.simps tgt.simps)
  hence "tlt y (Tr B va vb vd vc)" by (blast dest: tlt_trans)
  with "3_2" show ?case by simp
next
  case ("3_3" x w b y s c z t va vb vd vc)
  from "3_3" have "y < z \<and> tgt z (Tr B va vb vd vc)" by simp
  hence "tgt y (Tr B va vb vd vc)" by (blast dest: tgt_trans)
  with "3_3" show ?case by simp
next
  case ("3_4" vd ve vg vf x w b y s c z t va vb vii vc)
  hence "x < y \<and> tlt x (Tr B vd ve vg vf)" by simp
  hence 1: "tlt y (Tr B vd ve vg vf)" by (blast dest: tlt_trans)
  from "3_4" have "y < z \<and> tgt z (Tr B va vb vii vc)" by simp
  hence "tgt y (Tr B va vb vii vc)" by (blast dest: tgt_trans)
  with 1 "3_4" show ?case by simp
next
  case ("4_2" va vb vd vc x w b y s c z t dd)
  hence "x < y \<and> tlt x (Tr B va vb vd vc)" by simp
  hence "tlt y (Tr B va vb vd vc)" by (blast dest: tlt_trans)
  with "4_2" show ?case by simp
next
  case ("5_2" x w b y s c z t va vb vd vc)
  hence "y < z \<and> tgt z (Tr B va vb vd vc)" by simp
  hence "tgt y (Tr B va vb vd vc)" by (blast dest: tgt_trans)
  with "5_2" show ?case by simp
next
  case ("5_3" va vb vd vc x w b y s c z t)
  hence "x < y \<and> tlt x (Tr B va vb vd vc)" by simp
  hence "tlt y (Tr B va vb vd vc)" by (blast dest: tlt_trans)
  with "5_3" show ?case by simp
next
  case ("5_4" va vb vg vc x w b y s c z t vd ve vii vf)
  hence "x < y \<and> tlt x (Tr B va vb vg vc)" by simp
  hence 1: "tlt y (Tr B va vb vg vc)" by (blast dest: tlt_trans)
  from "5_4" have "y < z \<and> tgt z (Tr B vd ve vii vf)" by simp
  hence "tgt y (Tr B vd ve vii vf)" by (blast dest: tgt_trans)
  with 1 "5_4" show ?case by simp
qed simp+

lemma keys_balance[simp]: 
  "keys (balance l k v r) = { k } \<union> keys l \<union> keys r"
by (induct l k v r rule: balance.induct) auto

lemma balance_pit:  
  "pin_tree k x (balance l v y r) = (pin_tree k x l \<or> k = v \<and> x = y \<or> pin_tree k x r)" 
by (induct l v y r rule: balance.induct) auto

lemma map_of_balance[simp]: 
fixes k :: "'a::linorder"
assumes "st l" "st r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
shows "map_of (balance l k v r) x = map_of (Tr B l k v r) x"
by (rule mapof_from_pit) (auto simp:assms balance_pit balance_st)

primrec paint :: "color \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "paint c Empty = Empty"
| "paint c (Tr _ l k v r) = Tr c l k v r"

lemma paint_inv1l[simp]: "inv1l t \<Longrightarrow> inv1l (paint c t)" by (cases t) auto
lemma paint_inv1[simp]: "inv1l t \<Longrightarrow> inv1 (paint B t)" by (cases t) auto
lemma paint_inv2[simp]: "inv2 t \<Longrightarrow> inv2 (paint c t)" by (cases t) auto
lemma paint_treec[simp]: "treec (paint B t) = B" by (cases t) auto
lemma paint_st[simp]: "st t \<Longrightarrow> st (paint c t)" by (cases t) auto
lemma paint_pit[simp]: "pin_tree k x (paint c t) = pin_tree k x t" by (cases t) auto
lemma paint_mapof[simp]: "map_of (paint c t) = map_of t" by (rule ext) (cases t, auto)
lemma paint_tgt[simp]: "(v \<guillemotleft>| paint c t) = (v \<guillemotleft>| t)" by (cases t) auto
lemma paint_tlt[simp]: "(paint c t |\<guillemotleft> v) = (t |\<guillemotleft> v)" by (cases t) auto

fun
  ins :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "ins f k v Empty = Tr R Empty k v Empty" |
  "ins f k v (Tr B l x y r) = (if k < x then balance (ins f k v l) x y r
                               else if k > x then balance l x y (ins f k v r)
                               else Tr B l x (f k y v) r)" |
  "ins f k v (Tr R l x y r) = (if k < x then Tr R (ins f k v l) x y r
                               else if k > x then Tr R l x y (ins f k v r)
                               else Tr R l x (f k y v) r)"

lemma ins_inv1_inv2: 
  assumes "inv1 t" "inv2 t"
  shows "inv2 (ins f k x t)" "bh (ins f k x t) = bh t" 
  "treec t = B \<Longrightarrow> inv1 (ins f k x t)" "inv1l (ins f k x t)"
  using assms
  by (induct f k x t rule: ins.induct) (auto simp: balance_inv1 balance_inv2 balance_bh)

lemma ins_tgt[simp]: "(v \<guillemotleft>| ins f k x t) = (v \<guillemotleft>| t \<and> k > v)"
  by (induct f k x t rule: ins.induct) auto
lemma ins_tlt[simp]: "(ins f k x t |\<guillemotleft> v) = (t |\<guillemotleft> v \<and> k < v)"
  by (induct f k x t rule: ins.induct) auto
lemma ins_st[simp]: "st t \<Longrightarrow> st (ins f k x t)"
  by (induct f k x t rule: ins.induct) (auto simp: balance_st)

lemma keys_ins: "keys (ins f k v t) = { k } \<union> keys t"
by (induct f k v t rule: ins.induct) auto

lemma map_of_ins: 
  fixes k :: "'a::linorder"
  assumes "st t"
  shows "map_of (ins f k v t) x = ((map_of t)(k |-> case map_of t k of None \<Rightarrow> v 
                                                       | Some w \<Rightarrow> f k w v)) x"
using assms by (induct f k v t rule: ins.induct) auto

definition
  insertwithkey :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "insertwithkey f k v t = paint B (ins f k v t)"

lemma insertwk_st: "st t \<Longrightarrow> st (insertwithkey f k x t)"
  by (auto simp: insertwithkey_def)

theorem insertwk_isrbt: 
  assumes inv: "isrbt t" 
  shows "isrbt (insertwithkey f k x t)"
using assms
unfolding insertwithkey_def isrbt_def
by (auto simp: ins_inv1_inv2)

lemma map_of_insertwk: 
  assumes "st t"
  shows "map_of (insertwithkey f k v t) x = ((map_of t)(k |-> case map_of t k of None \<Rightarrow> v 
                                                       | Some w \<Rightarrow> f k w v)) x"
unfolding insertwithkey_def using assms
by (simp add:map_of_ins)

definition
  insertw_def: "insertwith f = insertwithkey (\<lambda>_. f)"

lemma insertw_st: "st t \<Longrightarrow> st (insertwith f k v t)" by (simp add: insertwk_st insertw_def)
theorem insertw_isrbt: "isrbt t \<Longrightarrow> isrbt (insertwith f k v t)" by (simp add: insertwk_isrbt insertw_def)

lemma map_of_insertw:
  assumes "isrbt t"
  shows "map_of (insertwith f k v t) = (map_of t)(k \<mapsto> (if k:dom (map_of t) then f (the (map_of t k)) v else v))"
using assms
unfolding insertw_def
by (rule_tac ext) (cases "map_of t k", auto simp:map_of_insertwk dom_def)


definition
  "insrt k v t = insertwithkey (\<lambda>_ _ nv. nv) k v t"

lemma insrt_st: "st t \<Longrightarrow> st (insrt k v t)" by (simp add: insertwk_st insrt_def)
theorem insrt_isrbt: "isrbt t \<Longrightarrow> isrbt (insrt k v t)" by (simp add: insertwk_isrbt insrt_def)

lemma map_of_insert: 
  assumes "isrbt t"
  shows "map_of (insrt k v t) = (map_of t)(k\<mapsto>v)"
unfolding insrt_def
using assms
by (rule_tac ext) (simp add: map_of_insertwk split:option.split)


subsection {* Deletion *}

lemma bh_paintR'[simp]: "treec t = B \<Longrightarrow> bh (paint R t) = bh t - 1"
by (cases t rule: rbt_cases) auto

fun
  balleft :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balleft (Tr R a k x b) s y c = Tr R (Tr B a k x b) s y c" |
  "balleft bl k x (Tr B a s y b) = balance bl k x (Tr R a s y b)" |
  "balleft bl k x (Tr R (Tr B a s y b) t z c) = Tr R (Tr B bl k x a) s y (balance b t z (paint R c))" |
  "balleft t k x s = Empty"

lemma balleft_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bh lt + 1 = bh rt" "inv1 rt"
  shows "bh (balleft lt k v rt) = bh lt + 1"
  and   "inv2 (balleft lt k v rt)"
using assms 
by (induct lt k v rt rule: balleft.induct) (auto simp: balance_inv2 balance_bh)

lemma balleft_inv2_app: 
  assumes "inv2 lt" "inv2 rt" "bh lt + 1 = bh rt" "treec rt = B"
  shows "inv2 (balleft lt k v rt)" 
        "bh (balleft lt k v rt) = bh rt"
using assms 
by (induct lt k v rt rule: balleft.induct) (auto simp add: balance_inv2 balance_bh)+ 

lemma balleft_inv1: "\<lbrakk>inv1l a; inv1 b; treec b = B\<rbrakk> \<Longrightarrow> inv1 (balleft a k x b)"
  by (induct a k x b rule: balleft.induct) (simp add: balance_inv1)+

lemma balleft_inv1l: "\<lbrakk> inv1l lt; inv1 rt \<rbrakk> \<Longrightarrow> inv1l (balleft lt k x rt)"
by (induct lt k x rt rule: balleft.induct) (auto simp: balance_inv1)

lemma balleft_st: "\<lbrakk> st l; st r; tlt k l; tgt k r \<rbrakk> \<Longrightarrow> st (balleft l k v r)"
apply (induct l k v r rule: balleft.induct)
apply (auto simp: balance_st)
apply (unfold tgt_prop tlt_prop)
by force+

lemma balleft_tgt: 
  fixes k :: "'a::order"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balleft a x t b"
using assms 
by (induct a x t b rule: balleft.induct) auto

lemma balleft_tlt: 
  fixes k :: "'a::order"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balleft a x t b |\<guillemotleft> k"
using assms
by (induct a x t b rule: balleft.induct) auto

lemma balleft_pit: 
  assumes "inv1l l" "inv1 r" "bh l + 1 = bh r"
  shows "pin_tree k v (balleft l a b r) = (pin_tree k v l \<or> k = a \<and> v = b \<or> pin_tree k v r)"
using assms 
by (induct l k v r rule: balleft.induct) (auto simp: balance_pit)

fun
  balright :: "('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "balright a k x (Tr R b s y c) = Tr R a k x (Tr B b s y c)" |
  "balright (Tr B a k x b) s y bl = balance (Tr R a k x b) s y bl" |
  "balright (Tr R a k x (Tr B b s y c)) t z bl = Tr R (balance (paint R a) k x b) s y (Tr B c t z bl)" |
  "balright t k x s = Empty"

lemma balright_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bh lt = bh rt + 1" "inv1 lt"
  shows "inv2 (balright lt k v rt) \<and> bh (balright lt k v rt) = bh lt"
using assms
by (induct lt k v rt rule: balright.induct) (auto simp: balance_inv2 balance_bh)

lemma balright_inv1: "\<lbrakk>inv1 a; inv1l b; treec a = B\<rbrakk> \<Longrightarrow> inv1 (balright a k x b)"
by (induct a k x b rule: balright.induct) (simp add: balance_inv1)+

lemma balright_inv1l: "\<lbrakk> inv1 lt; inv1l rt \<rbrakk> \<Longrightarrow>inv1l (balright lt k x rt)"
by (induct lt k x rt rule: balright.induct) (auto simp: balance_inv1)

lemma balright_st: "\<lbrakk> st l; st r; tlt k l; tgt k r \<rbrakk> \<Longrightarrow> st (balright l k v r)"
apply (induct l k v r rule: balright.induct)
apply (auto simp:balance_st)
apply (unfold tlt_prop tgt_prop)
by force+

lemma balright_tgt: 
  fixes k :: "'a::order"
  assumes "k \<guillemotleft>| a" "k \<guillemotleft>| b" "k < x" 
  shows "k \<guillemotleft>| balright a x t b"
using assms by (induct a x t b rule: balright.induct) auto

lemma balright_tlt: 
  fixes k :: "'a::order"
  assumes "a |\<guillemotleft> k" "b |\<guillemotleft> k" "x < k" 
  shows "balright a x t b |\<guillemotleft> k"
using assms by (induct a x t b rule: balright.induct) auto

lemma balright_pit:
  assumes "inv1 l" "inv1l r" "bh l = bh r + 1" "inv2 l" "inv2 r"
  shows "pin_tree x y (balright l k v r) = (pin_tree x y l \<or> x = k \<and> y = v \<or> pin_tree x y r)"
using assms by (induct l k v r rule: balright.induct) (auto simp: balance_pit)


text {* app *}

fun
  app :: "('a,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "app Empty x = x" 
| "app x Empty = x" 
| "app (Tr R a k x b) (Tr R c s y d) = (case (app b c) of
                                      Tr R b2 t z c2 \<Rightarrow> (Tr R (Tr R a k x b2) t z (Tr R c2 s y d)) |
                                      bc \<Rightarrow> Tr R a k x (Tr R bc s y d))" 
| "app (Tr B a k x b) (Tr B c s y d) = (case (app b c) of
                                      Tr R b2 t z c2 \<Rightarrow> Tr R (Tr B a k x b2) t z (Tr B c2 s y d) |
                                      bc \<Rightarrow> balleft a k x (Tr B bc s y d))" 
| "app a (Tr R b k x c) = Tr R (app a b) k x c" 
| "app (Tr R a k x b) c = Tr R a k x (app b c)" 

lemma app_inv2:
  assumes "inv2 lt" "inv2 rt" "bh lt = bh rt"
  shows "bh (app lt rt) = bh lt" "inv2 (app lt rt)"
using assms 
by (induct lt rt rule: app.induct) 
   (auto simp: balleft_inv2_app split: rbt.splits color.splits)

lemma app_inv1: 
  assumes "inv1 lt" "inv1 rt"
  shows "treec lt = B \<Longrightarrow> treec rt = B \<Longrightarrow> inv1 (app lt rt)"
         "inv1l (app lt rt)"
using assms 
by (induct lt rt rule: app.induct)
   (auto simp: balleft_inv1 split: rbt.splits color.splits)

lemma app_tgt[simp]: 
  fixes k :: "'a::linorder"
  assumes "k \<guillemotleft>| l" "k \<guillemotleft>| r" 
  shows "k \<guillemotleft>| app l r"
using assms 
by (induct l r rule: app.induct)
   (auto simp: balleft_tgt split:rbt.splits color.splits)

lemma app_tlt[simp]: 
  fixes k :: "'a::linorder"
  assumes "l |\<guillemotleft> k" "r |\<guillemotleft> k" 
  shows "app l r |\<guillemotleft> k"
using assms 
by (induct l r rule: app.induct)
   (auto simp: balleft_tlt split:rbt.splits color.splits)

lemma app_st: 
  fixes k :: "'a::linorder"
  assumes "st l" "st r" "l |\<guillemotleft> k" "k \<guillemotleft>| r"
  shows "st (app l r)"
using assms proof (induct l r rule: app.induct)
  case (3 a x v b c y w d)
  hence ineqs: "a |\<guillemotleft> x" "x \<guillemotleft>| b" "b |\<guillemotleft> k" "k \<guillemotleft>| c" "c |\<guillemotleft> y" "y \<guillemotleft>| d"
    by auto
  with 3
  show ?case
    apply (cases "app b c" rule: rbt_cases)
    apply auto
    by (metis app_tgt app_tlt ineqs ineqs tlt.simps(2) tgt.simps(2) tgt_trans tlt_trans)+
next
  case (4 a x v b c y w d)
  hence "x < k \<and> tgt k c" by simp
  hence "tgt x c" by (blast dest: tgt_trans)
  with 4 have 2: "tgt x (app b c)" by (simp add: app_tgt)
  from 4 have "k < y \<and> tlt k b" by simp
  hence "tlt y b" by (blast dest: tlt_trans)
  with 4 have 3: "tlt y (app b c)" by (simp add: app_tlt)
  show ?case
  proof (cases "app b c" rule: rbt_cases)
    case Empty
    from 4 have "x < y \<and> tgt y d" by auto
    hence "tgt x d" by (blast dest: tgt_trans)
    with 4 Empty have "st a" and "st (Tr B Empty y w d)" and "tlt x a" and "tgt x (Tr B Empty y w d)" by auto
    with Empty show ?thesis by (simp add: balleft_st)
  next
    case (Red lta va ka rta)
    with 2 4 have "x < va \<and> tlt x a" by simp
    hence 5: "tlt va a" by (blast dest: tlt_trans)
    from Red 3 4 have "va < y \<and> tgt y d" by simp
    hence "tgt va d" by (blast dest: tgt_trans)
    with Red 2 3 4 5 show ?thesis by simp
  next
    case (Black lta va ka rta)
    from 4 have "x < y \<and> tgt y d" by auto
    hence "tgt x d" by (blast dest: tgt_trans)
    with Black 2 3 4 have "st a" and "st (Tr B (app b c) y w d)" and "tlt x a" and "tgt x (Tr B (app b c) y w d)" by auto
    with Black show ?thesis by (simp add: balleft_st)
  qed
next
  case (5 va vb vd vc b x w c)
  hence "k < x \<and> tlt k (Tr B va vb vd vc)" by simp
  hence "tlt x (Tr B va vb vd vc)" by (blast dest: tlt_trans)
  with 5 show ?case by (simp add: app_tlt)
next
  case (6 a x v b va vb vd vc)
  hence "x < k \<and> tgt k (Tr B va vb vd vc)" by simp
  hence "tgt x (Tr B va vb vd vc)" by (blast dest: tgt_trans)
  with 6 show ?case by (simp add: app_tgt)
qed simp+

lemma app_pit: 
  assumes "inv2 l" "inv2 r" "bh l = bh r" "inv1 l" "inv1 r"
  shows "pin_tree k v (app l r) = (pin_tree k v l \<or> pin_tree k v r)"
using assms 
proof (induct l r rule: app.induct)
  case (4 _ _ _ b c)
  hence a: "bh (app b c) = bh b" by (simp add: app_inv2)
  from 4 have b: "inv1l (app b c)" by (simp add: app_inv1)

  show ?case
  proof (cases "app b c" rule: rbt_cases)
    case Empty
    with 4 a show ?thesis by (auto simp: balleft_pit)
  next
    case (Red lta ka va rta)
    with 4 show ?thesis by auto
  next
    case (Black lta ka va rta)
    with a b 4  show ?thesis by (auto simp: balleft_pit)
  qed 
qed (auto split: rbt.splits color.splits)

fun
  delformLeft :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  delformRight :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  del :: "('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "del x Empty = Empty" |
  "del x (Tr c a y s b) = (if x < y then delformLeft x a y s b else (if x > y then delformRight x a y s b else app a b))" |
  "delformLeft x (Tr B lt z v rt) y s b = balleft (del x (Tr B lt z v rt)) y s b" |
  "delformLeft x a y s b = Tr R (del x a) y s b" |
  "delformRight x a y s (Tr B lt z v rt) = balright a y s (del x (Tr B lt z v rt))" | 
  "delformRight x a y s b = Tr R a y s (del x b)"

lemma 
  assumes "inv2 lt" "inv1 lt"
  shows
  "\<lbrakk>inv2 rt; bh lt = bh rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (delformLeft x lt k v rt) \<and> bh (delformLeft x lt k v rt) = bh lt \<and> (treec lt = B \<and> treec rt = B \<and> inv1 (delformLeft x lt k v rt) \<or> (treec lt \<noteq> B \<or> treec rt \<noteq> B) \<and> inv1l (delformLeft x lt k v rt))"
  and "\<lbrakk>inv2 rt; bh lt = bh rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (delformRight x lt k v rt) \<and> bh (delformRight x lt k v rt) = bh lt \<and> (treec lt = B \<and> treec rt = B \<and> inv1 (delformRight x lt k v rt) \<or> (treec lt \<noteq> B \<or> treec rt \<noteq> B) \<and> inv1l (delformRight x lt k v rt))"
  and del_inv1_inv2: "inv2 (del x lt) \<and> (treec lt = R \<and> bh (del x lt) = bh lt \<and> inv1 (del x lt) 
  \<or> treec lt = B \<and> bh (del x lt) = bh lt - 1 \<and> inv1l (del x lt))"
using assms
proof (induct x lt k v rt and x lt k v rt and x lt rule: delformLeft_delformRight_del.induct)
case (2 y c _ y')
  have "y = y' \<or> y < y' \<or> y > y'" by auto
  thus ?case proof (elim disjE)
    assume "y = y'"
    with 2 show ?thesis by (cases c) (simp add: app_inv2 app_inv1)+
  next
    assume "y < y'"
    with 2 show ?thesis by (cases c) auto
  next
    assume "y' < y"
    with 2 show ?thesis by (cases c) auto
  qed
next
  case (3 y lt z v rta y' ss bb) 
  thus ?case by (cases "treec (Tr B lt z v rta) = B \<and> treec bb = B") (simp add: balleft_inv2_with_inv1 balleft_inv1 balleft_inv1l)+
next
  case (5 y a y' ss lt z v rta)
  thus ?case by (cases "treec a = B \<and> treec (Tr B lt z v rta) = B") (simp add: balright_inv2_with_inv1 balright_inv1 balright_inv1l)+
next
  case ("6_1" y a y' ss) thus ?case by (cases "treec a = B \<and> treec Empty = B") simp+
qed auto

lemma 
  delformLeft_tlt: "\<lbrakk>tlt v lt; tlt v rt; k < v\<rbrakk> \<Longrightarrow> tlt v (delformLeft x lt k y rt)"
  and delformRight_tlt: "\<lbrakk>tlt v lt; tlt v rt; k < v\<rbrakk> \<Longrightarrow> tlt v (delformRight x lt k y rt)"
  and del_tlt: "tlt v lt \<Longrightarrow> tlt v (del x lt)"
by (induct x lt k y rt and x lt k y rt and x lt rule: delformLeft_delformRight_del.induct) 
   (auto simp: balleft_tlt balright_tlt)

lemma delformLeft_tgt: "\<lbrakk>tgt v lt; tgt v rt; k > v\<rbrakk> \<Longrightarrow> tgt v (delformLeft x lt k y rt)"
  and delformRight_tgt: "\<lbrakk>tgt v lt; tgt v rt; k > v\<rbrakk> \<Longrightarrow> tgt v (delformRight x lt k y rt)"
  and del_tgt: "tgt v lt \<Longrightarrow> tgt v (del x lt)"
by (induct x lt k y rt and x lt k y rt and x lt rule: delformLeft_delformRight_del.induct)
   (auto simp: balleft_tgt balright_tgt)

lemma "\<lbrakk>st lt; st rt; tlt k lt; tgt k rt\<rbrakk> \<Longrightarrow> st (delformLeft x lt k y rt)"
  and "\<lbrakk>st lt; st rt; tlt k lt; tgt k rt\<rbrakk> \<Longrightarrow> st (delformRight x lt k y rt)"
  and del_st: "st lt \<Longrightarrow> st (del x lt)"
proof (induct x lt k y rt and x lt k y rt and x lt rule: delformLeft_delformRight_del.induct)
  case (3 x lta zz v rta yy ss bb)
  from 3 have "tlt yy (Tr B lta zz v rta)" by simp
  hence "tlt yy (del x (Tr B lta zz v rta))" by (rule del_tlt)
  with 3 show ?case by (simp add: balleft_st)
next
  case ("4_2" x vaa vbb vdd vc yy ss bb)
  hence "tlt yy (Tr R vaa vbb vdd vc)" by simp
  hence "tlt yy (del x (Tr R vaa vbb vdd vc))" by (rule del_tlt)
  with "4_2" show ?case by simp
next
  case (5 x aa yy ss lta zz v rta) 
  hence "tgt yy (Tr B lta zz v rta)" by simp
  hence "tgt yy (del x (Tr B lta zz v rta))" by (rule del_tgt)
  with 5 show ?case by (simp add: balright_st)
next
  case ("6_2" x aa yy ss vaa vbb vdd vc)
  hence "tgt yy (Tr R vaa vbb vdd vc)" by simp
  hence "tgt yy (del x (Tr R vaa vbb vdd vc))" by (rule del_tgt)
  with "6_2" show ?case by simp
qed (auto simp: app_st)

lemma "\<lbrakk>st lt; st rt; tlt kt lt; tgt kt rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bh lt = bh rt; x < kt\<rbrakk> \<Longrightarrow> pin_tree k v (delformLeft x lt kt y rt) = (False \<or> (x \<noteq> k \<and> pin_tree k v (Tr c lt kt y rt)))"
  and "\<lbrakk>st lt; st rt; tlt kt lt; tgt kt rt; inv1 lt; inv1 rt; inv2 lt; inv2 rt; bh lt = bh rt; x > kt\<rbrakk> \<Longrightarrow> pin_tree k v (delformRight x lt kt y rt) = (False \<or> (x \<noteq> k \<and> pin_tree k v (Tr c lt kt y rt)))"
  and del_pit: "\<lbrakk>st t; inv1 t; inv2 t\<rbrakk> \<Longrightarrow> pin_tree k v (del x t) = (False \<or> (x \<noteq> k \<and> pin_tree k v t))"
proof (induct x lt kt y rt and x lt kt y rt and x t rule: delformLeft_delformRight_del.induct)
  case (2 xx c aa yy ss bb)
  have "xx = yy \<or> xx < yy \<or> xx > yy" by auto
  from this 2 show ?case proof (elim disjE)
    assume "xx = yy"
    with 2 show ?thesis proof (cases "xx = k")
      case True
      from 2 `xx = yy` `xx = k` have "st (Tr c aa yy ss bb) \<and> k = yy" by simp
      hence "\<not> pin_tree k v aa" "\<not> pin_tree k v bb" by (auto simp: tlt_nit tgt_prop)
      with `xx = yy` 2 `xx = k` show ?thesis by (simp add: app_pit)
    qed (simp add: app_pit)
  qed simp+
next    
  case (3 xx lta zz vv rta yy ss bb)
  def mt[simp]: mt == "Tr B lta zz vv rta"
  from 3 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (del xx mt) \<and> (treec mt = R \<and> bh (del xx mt) = bh mt \<and> inv1 (del xx mt) \<or> treec mt = B \<and> bh (del xx mt) = bh mt - 1 \<and> inv1l (del xx mt))" by (blast dest: del_inv1_inv2)
  with 3 have 4: "pin_tree k v (delformLeft xx mt yy ss bb) = (False \<or> xx \<noteq> k \<and> pin_tree k v mt \<or> (k = yy \<and> v = ss) \<or> pin_tree k v bb)" by (simp add: balleft_pit)
  thus ?case proof (cases "xx = k")
    case True
    from 3 True have "tgt yy bb \<and> yy > k" by simp
    hence "tgt k bb" by (blast dest: tgt_trans)
    with 3 4 True show ?thesis by (auto simp: tgt_nit)
  qed auto
next
  case ("4_1" xx yy ss bb)
  show ?case proof (cases "xx = k")
    case True
    with "4_1" have "tgt yy bb \<and> k < yy" by simp
    hence "tgt k bb" by (blast dest: tgt_trans)
    with "4_1" `xx = k` 
   have "pin_tree k v (Tr R Empty yy ss bb) = pin_tree k v Empty" by (auto simp: tgt_nit)
    thus ?thesis by auto
  qed simp+
next
  case ("4_2" xx vaa vbb vdd vc yy ss bb)
  thus ?case proof (cases "xx = k")
    case True
    with "4_2" have "k < yy \<and> tgt yy bb" by simp
    hence "tgt k bb" by (blast dest: tgt_trans)
    with True "4_2" show ?thesis by (auto simp: tgt_nit)
  qed simp
next
  case (5 xx aa yy ss lta zz vv rta)
  def mt[simp]: mt == "Tr B lta zz vv rta"
  from 5 have "inv2 mt \<and> inv1 mt" by simp
  hence "inv2 (del xx mt) \<and> (treec mt = R \<and> bh (del xx mt) = bh mt \<and> inv1 (del xx mt) \<or> treec mt = B \<and> bh (del xx mt) = bh mt - 1 \<and> inv1l (del xx mt))" by (blast dest: del_inv1_inv2)
  with 5 have 3: "pin_tree k v (delformRight xx aa yy ss mt) = (pin_tree k v aa \<or> (k = yy \<and> v = ss) \<or> False \<or> xx \<noteq> k \<and> pin_tree k v mt)" by (simp add: balright_pit)
  thus ?case proof (cases "xx = k")
    case True
    from 5 True have "tlt yy aa \<and> yy < k" by simp
    hence "tlt k aa" by (blast dest: tlt_trans)
    with 3 5 True show ?thesis by (auto simp: tlt_nit)
  qed auto
next
  case ("6_1" xx aa yy ss)
  show ?case proof (cases "xx = k")
    case True
    with "6_1" have "tlt yy aa \<and> k > yy" by simp
    hence "tlt k aa" by (blast dest: tlt_trans)
    with "6_1" `xx = k` show ?thesis by (auto simp: tlt_nit)
  qed simp
next
  case ("6_2" xx aa yy ss vaa vbb vdd vc)
  thus ?case proof (cases "xx = k")
    case True
    with "6_2" have "k > yy \<and> tlt yy aa" by simp
    hence "tlt k aa" by (blast dest: tlt_trans)
    with True "6_2" show ?thesis by (auto simp: tlt_nit)
  qed simp
qed simp


definition delete where
  delete_def: "delete k t = paint B (del k t)"

theorem delete_isrbt[simp]: assumes "isrbt t" shows "isrbt (delete k t)"
proof -
  from assms have "inv2 t" and "inv1 t" unfolding isrbt_def by auto 
  hence "inv2 (del k t) \<and> (treec t = R \<and> bh (del k t) = bh t \<and> inv1 (del k t) \<or> treec t = B \<and> bh (del k t) = bh t - 1 \<and> inv1l (del k t))" by (rule del_inv1_inv2)
  hence "inv2 (del k t) \<and> inv1l (del k t)" by (cases "treec t") auto
  with assms show ?thesis
    unfolding isrbt_def delete_def
    by (auto intro: paint_st del_st)
qed

lemma delete_pit: 
  assumes "isrbt t" 
  shows "pin_tree k v (delete x t) = (x \<noteq> k \<and> pin_tree k v t)"
  using assms unfolding isrbt_def delete_def
  by (auto simp: del_pit)

lemma map_of_delete:
  assumes isrbt: "isrbt t"
  shows "map_of (delete k t) = (map_of t)|`(-{k})"
proof
  fix x
  show "map_of (delete k t) x = (map_of t |` (-{k})) x" 
  proof (cases "x = k")
    assume "x = k" 
    with isrbt show ?thesis
      by (cases "map_of (delete k t) k") (auto simp: mapof_pit delete_pit)
  next
    assume "x \<noteq> k"
    thus ?thesis
      by auto (metis isrbt delete_isrbt delete_pit isrbt_st mapof_from_pit)
  qed
qed

subsection {* Union *}

primrec
  unionwithkey :: "('a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "unionwithkey f t Empty = t"
| "unionwithkey f t (Tr c lt k v rt) = unionwithkey f (unionwithkey f (insertwithkey f k v t) lt) rt"

lemma unionwk_st: "st lt \<Longrightarrow> st (unionwithkey f lt rt)" 
  by (induct rt arbitrary: lt) (auto simp: insertwk_st)
theorem unionwk_isrbt[simp]: "isrbt lt \<Longrightarrow> isrbt (unionwithkey f lt rt)" 
  by (induct rt arbitrary: lt) (simp add: insertwk_isrbt)+

definition
  unionwith where
  "unionwith f = unionwithkey (\<lambda>_. f)"

theorem unionw_isrbt: "isrbt lt \<Longrightarrow> isrbt (unionwith f lt rt)" unfolding unionwith_def by simp

definition union where
  "union = unionwithkey (%_ _ rv. rv)"

theorem union_isrbt: "isrbt lt \<Longrightarrow> isrbt (union lt rt)" unfolding union_def by simp

lemma union_Tr[simp]:
  "union t (Tr c lt k v rt) = union (union (insrt k v t) lt) rt"
  unfolding union_def insrt_def
  by simp

lemma map_of_union:
  assumes "isrbt s" "st t"
  shows "map_of (union s t) = map_of s ++ map_of t"
using assms
proof (induct t arbitrary: s)
  case Empty thus ?case by (auto simp: union_def)
next
  case (Tr c l k v r s)
  hence strl: "st r" "st l" "l |\<guillemotleft> k" "k \<guillemotleft>| r" by auto

  have meq: "map_of s(k \<mapsto> v) ++ map_of l ++ map_of r =
    map_of s ++
    (\<lambda>a. if a < k then map_of l a
    else if k < a then map_of r a else Some v)" (is "?m1 = ?m2")
  proof (rule ext)
    fix a

   have "k < a \<or> k = a \<or> k > a" by auto
    thus "?m1 a = ?m2 a"
    proof (elim disjE)
      assume "k < a"
      with `l |\<guillemotleft> k` have "l |\<guillemotleft> a" by (rule tlt_trans)
      with `k < a` show ?thesis
        by (auto simp: map_add_def split: option.splits)
    next
      assume "k = a"
      with `l |\<guillemotleft> k` `k \<guillemotleft>| r` 
      show ?thesis by (auto simp: map_add_def)
    next
      assume "a < k"
      from this `k \<guillemotleft>| r` have "a \<guillemotleft>| r" by (rule tgt_trans)
      with `a < k` show ?thesis
        by (auto simp: map_add_def split: option.splits)
    qed
  qed

  from Tr
  have IHs:
    "map_of (union (union (insrt k v s) l) r) = map_of (union (insrt k v s) l) ++ map_of r"
    "map_of (union (insrt k v s) l) = map_of (insrt k v s) ++ map_of l"
    by (auto intro: union_isrbt insrt_isrbt)
  
  with meq show ?case
    by (auto simp: map_of_insert[OF Tr(3)])
qed

subsection {* Adjust *}

primrec
  adjustwithkey :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "adjustwithkey f k Empty = Empty"
| "adjustwithkey f k (Tr c lt x v rt) = (if k < x then (Tr c (adjustwithkey f k lt) x v rt) else if k > x then (Tr c lt x v (adjustwithkey f k rt)) else (Tr c lt x (f x v) rt))"

lemma adjustwk_treec: "treec (adjustwithkey f k t) = treec t" by (induct t) simp+
lemma adjustwk_inv1: "inv1 (adjustwithkey f k t) = inv1 t" by (induct t) (simp add: adjustwk_treec)+
lemma adjustwk_inv2: "inv2 (adjustwithkey f k t) = inv2 t" "bh (adjustwithkey f k t) = bh t" by (induct t) simp+
lemma adjustwk_tgt: "tgt k (adjustwithkey f kk t) = tgt k t" by (induct t) simp+
lemma adjustwk_tlt: "tlt k (adjustwithkey f kk t) = tlt k t" by (induct t) simp+
lemma adjustwk_st: "st (adjustwithkey f k t) = st t" by (induct t) (simp add: adjustwk_tlt adjustwk_tgt)+

theorem adjustwk_isrbt[simp]: "isrbt (adjustwithkey f k t) = isrbt t" 
unfolding isrbt_def by (simp add: adjustwk_inv2 adjustwk_treec adjustwk_st adjustwk_inv1 )

theorem adjustwithkey_map[simp]:
  "map_of (adjustwithkey f k t) x = 
  (if x = k then case map_of t x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f k y)
            else map_of t x)"
by (induct t arbitrary: x) (auto split:option.splits)

definition adjust where
  "adjust f = adjustwithkey (\<lambda>_. f)"

theorem adjust_isrbt[simp]: "isrbt (adjust f k t) = isrbt t" unfolding adjust_def by simp

theorem adjust_map[simp]:
  "map_of (adjust f k t) x = 
  (if x = k then case map_of t x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f y)
            else map_of t x)"
unfolding adjust_def by simp

subsection {* Map *}

primrec
  mapwithkey :: "('a::linorder \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'c) rbt"
where
  "mapwithkey f Empty = Empty"
| "mapwithkey f (Tr c lt k v rt) = Tr c (mapwithkey f lt) k (f k v) (mapwithkey f rt)"

theorem mapwk_keys[simp]: "keys (mapwithkey f t) = keys t" by (induct t) auto
lemma mapwk_tgt: "tgt k (mapwithkey f t) = tgt k t" by (induct t) simp+
lemma mapwk_tlt: "tlt k (mapwithkey f t) = tlt k t" by (induct t) simp+
lemma mapwk_st: "st (mapwithkey f t) = st t"  by (induct t) (simp add: mapwk_tlt mapwk_tgt)+
lemma mapwk_treec: "treec (mapwithkey f t) = treec t" by (induct t) simp+
lemma mapwk_inv1: "inv1 (mapwithkey f t) = inv1 t" by (induct t) (simp add: mapwk_treec)+
lemma mapwk_inv2: "inv2 (mapwithkey f t) = inv2 t" "bh (mapwithkey f t) = bh t" by (induct t) simp+
theorem mapwk_isrbt[simp]: "isrbt (mapwithkey f t) = isrbt t" 
unfolding isrbt_def by (simp add: mapwk_inv1 mapwk_inv2 mapwk_st mapwk_treec)

theorem map_of_mapwk[simp]: "map_of (mapwithkey f t) x = Option.map (f x) (map_of t x)"
by (induct t) auto

definition map
where map_def: "map f == mapwithkey (\<lambda>_. f)"

theorem map_keys[simp]: "keys (map f t) = keys t" unfolding map_def by simp
theorem map_isrbt[simp]: "isrbt (map f t) = isrbt t" unfolding map_def by simp
theorem map_of_map[simp]: "map_of (map f t) = Option.map f o map_of t"
  by (rule ext) (simp add:map_def)

subsection {* Fold *}

text {* The following is still incomplete... *}

primrec
  foldwithkey :: "('a::linorder \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c"
where
  "foldwithkey f Empty v = v"
| "foldwithkey f (Tr c lt k x rt) v = foldwithkey f rt (f k x (foldwithkey f lt v))"

primrec alist_of
where 
  "alist_of Empty = []"
| "alist_of (Tr _ l k v r) = alist_of l @ (k,v) # alist_of r"

lemma map_of_alist_of_aux: "st (Tr c t1 k v t2) \<Longrightarrow> RBT.map_of (Tr c t1 k v t2) = RBT.map_of t2 ++ [k\<mapsto>v] ++ RBT.map_of t1"
proof (rule ext)
  fix x
  assume ST: "st (Tr c t1 k v t2)"
  let ?thesis = "RBT.map_of (Tr c t1 k v t2) x = (RBT.map_of t2 ++ [k \<mapsto> v] ++ RBT.map_of t1) x"

  have DOM_T1: "!!k'. k'\<in>dom (RBT.map_of t1) \<Longrightarrow> k>k'"
  proof -
    fix k'
    from ST have "t1 |\<guillemotleft> k" by simp
    with tlt_prop have "\<forall>k'\<in>keys t1. k>k'" by auto
    moreover assume "k'\<in>dom (RBT.map_of t1)"
    ultimately show "k>k'" using RBT.mapof_keys ST by auto
  qed

  have DOM_T2: "!!k'. k'\<in>dom (RBT.map_of t2) \<Longrightarrow> k<k'"
  proof -
    fix k'
    from ST have "k \<guillemotleft>| t2" by simp
    with tgt_prop have "\<forall>k'\<in>keys t2. k<k'" by auto
    moreover assume "k'\<in>dom (RBT.map_of t2)"
    ultimately show "k<k'" using RBT.mapof_keys ST by auto
  qed

  {
    assume C: "x<k"
    hence "RBT.map_of (Tr c t1 k v t2) x = RBT.map_of t1 x" by simp
    moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
    moreover have "x\<notin>dom (RBT.map_of t2)" proof
      assume "x\<in>dom (RBT.map_of t2)"
      with DOM_T2 have "k<x" by blast
      with C show False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
  } moreover {
    assume [simp]: "x=k"
    hence "RBT.map_of (Tr c t1 k v t2) x = [k \<mapsto> v] x" by simp
    moreover have "x\<notin>dom (RBT.map_of t1)" proof
      assume "x\<in>dom (RBT.map_of t1)"
      with DOM_T1 have "k>x" by blast
      thus False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
  } moreover {
    assume C: "x>k"
    hence "RBT.map_of (Tr c t1 k v t2) x = RBT.map_of t2 x" by (simp add: less_not_sym[of k x])
    moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
    moreover have "x\<notin>dom (RBT.map_of t1)" proof
      assume "x\<in>dom (RBT.map_of t1)"
      with DOM_T1 have "k>x" by simp
      with C show False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd_left map_add_dom_app_simps)
  } ultimately show ?thesis using less_linear by blast
qed

lemma map_of_alist_of:
  shows "st t \<Longrightarrow> Map.map_of (alist_of t) = map_of t"
proof (induct t)
  case Empty thus ?case by (simp add: RBT.map_of_Empty)
next
  case (Tr c t1 k v t2)
  hence "Map.map_of (alist_of (Tr c t1 k v t2)) = RBT.map_of t2 ++ [k \<mapsto> v] ++ RBT.map_of t1" by simp
  also note map_of_alist_of_aux[OF Tr.prems,symmetric]
  finally show ?case .
qed

lemma fold_alist_fold:
  "foldwithkey f t x = foldl (\<lambda>x (k,v). f k v x) x (alist_of t)"
by (induct t arbitrary: x) auto

lemma alist_pit[simp]: "(k, v) \<in> set (alist_of t) = pin_tree k v t"
by (induct t) auto

lemma sorted_alist:
  "st t \<Longrightarrow> sorted (List.map fst (alist_of t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons tlgt_props 
      dest!:pint_keys)+

lemma distinct_alist:
  "st t \<Longrightarrow> distinct (List.map fst (alist_of t))"
by (induct t) 
  (force simp: sorted_append sorted_Cons tlgt_props 
      dest!:pint_keys)+
(*>*)

text {* 
  This theory defines purely functional red-black trees which can be
  used as an efficient representation of finite maps.
*}

subsection {* Data type and invariant *}

text {*
  The type @{typ "('k, 'v) rbt"} denotes red-black trees with keys of
  type @{typ "'k"} and values of type @{typ "'v"}. To function
  properly, the key type must belong to the @{text "linorder"} class.

  A value @{term t} of this type is a valid red-black tree if it
  satisfies the invariant @{text "isrbt t"}.
  This theory provides lemmas to prove that the invariant is
  satisfied throughout the computation.

  The interpretation function @{const "map_of"} returns the partial
  map represented by a red-black tree:
  @{term_type[display] "map_of"}

  This function should be used for reasoning about the semantics of the RBT
  operations. Furthermore, it implements the lookup functionality for
  the data structure: It is executable and the lookup is performed in
  $O(\log n)$.  
*}

subsection {* Operations *}

text {*
  Currently, the following operations are supported:

  @{term_type[display] "Empty"}
  Returns the empty tree. $O(1)$

  @{term_type[display] "insrt"}
  Updates the map at a given position. $O(\log n)$

  @{term_type[display] "delete"}
  Deletes a map entry at a given position. $O(\log n)$

  @{term_type[display] "union"}
  Forms the union of two trees, preferring entries from the first one.

  @{term_type[display] "map"}
  Maps a function over the values of a map. $O(n)$
*}


subsection {* Invariant preservation *}

text {*
  \noindent
  @{thm Empty_isrbt}\hfill(@{text "Empty_isrbt"})

  \noindent
  @{thm insrt_isrbt}\hfill(@{text "insrt_isrbt"})

  \noindent
  @{thm delete_isrbt}\hfill(@{text "delete_isrbt"})

  \noindent
  @{thm union_isrbt}\hfill(@{text "union_isrbt"})

  \noindent
  @{thm map_isrbt}\hfill(@{text "map_isrbt"})
*}

subsection {* Map Semantics *}

text {*
  \noindent
  \underline{@{text "map_of_Empty"}}
  @{thm[display] map_of_Empty}
  \vspace{1ex}

  \noindent
  \underline{@{text "map_of_insert"}}
  @{thm[display] map_of_insert}
  \vspace{1ex}

  \noindent
  \underline{@{text "map_of_delete"}}
  @{thm[display] map_of_delete}
  \vspace{1ex}

  \noindent
  \underline{@{text "map_of_union"}}
  @{thm[display] map_of_union}
  \vspace{1ex}

  \noindent
  \underline{@{text "map_of_map"}}
  @{thm[display] map_of_map}
  \vspace{1ex}
*}

end
