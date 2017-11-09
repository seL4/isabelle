(* Author: Tobias Nipkow *)

section \<open>2-3 Tree Implementation of Sets\<close>

theory Tree23_Set
imports
  Tree23
  Cmp
  Set_by_Ordered
begin

fun isin :: "'a::linorder tree23 \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node2 l a r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)" |
"isin (Node3 l a m b r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow>
       (case cmp x b of
          LT \<Rightarrow> isin m x |
          EQ \<Rightarrow> True |
          GT \<Rightarrow> isin r x))"

datatype 'a up\<^sub>i = T\<^sub>i "'a tree23" | Up\<^sub>i "'a tree23" 'a "'a tree23"

fun tree\<^sub>i :: "'a up\<^sub>i \<Rightarrow> 'a tree23" where
"tree\<^sub>i (T\<^sub>i t) = t" |
"tree\<^sub>i (Up\<^sub>i l a r) = Node2 l a r"

fun ins :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i" where
"ins x Leaf = Up\<^sub>i Leaf x Leaf" |
"ins x (Node2 l a r) =
   (case cmp x a of
      LT \<Rightarrow>
        (case ins x l of
           T\<^sub>i l' => T\<^sub>i (Node2 l' a r) |
           Up\<^sub>i l1 b l2 => T\<^sub>i (Node3 l1 b l2 a r)) |
      EQ \<Rightarrow> T\<^sub>i (Node2 l x r) |
      GT \<Rightarrow>
        (case ins x r of
           T\<^sub>i r' => T\<^sub>i (Node2 l a r') |
           Up\<^sub>i r1 b r2 => T\<^sub>i (Node3 l a r1 b r2)))" |
"ins x (Node3 l a m b r) =
   (case cmp x a of
      LT \<Rightarrow>
        (case ins x l of
           T\<^sub>i l' => T\<^sub>i (Node3 l' a m b r) |
           Up\<^sub>i l1 c l2 => Up\<^sub>i (Node2 l1 c l2) a (Node2 m b r)) |
      EQ \<Rightarrow> T\<^sub>i (Node3 l a m b r) |
      GT \<Rightarrow>
        (case cmp x b of
           GT \<Rightarrow>
             (case ins x r of
                T\<^sub>i r' => T\<^sub>i (Node3 l a m b r') |
                Up\<^sub>i r1 c r2 => Up\<^sub>i (Node2 l a m) b (Node2 r1 c r2)) |
           EQ \<Rightarrow> T\<^sub>i (Node3 l a m b r) |
           LT \<Rightarrow>
             (case ins x m of
                T\<^sub>i m' => T\<^sub>i (Node3 l a m' b r) |
                Up\<^sub>i m1 c m2 => Up\<^sub>i (Node2 l a m1) c (Node2 m2 b r))))"

hide_const insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"insert x t = tree\<^sub>i(ins x t)"

datatype 'a up\<^sub>d = T\<^sub>d "'a tree23" | Up\<^sub>d "'a tree23"

fun tree\<^sub>d :: "'a up\<^sub>d \<Rightarrow> 'a tree23" where
"tree\<^sub>d (T\<^sub>d t) = t" |
"tree\<^sub>d (Up\<^sub>d t) = t"

(* Variation: return None to signal no-change *)

fun node21 :: "'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
"node21 (T\<^sub>d t1) a t2 = T\<^sub>d(Node2 t1 a t2)" |
"node21 (Up\<^sub>d t1) a (Node2 t2 b t3) = Up\<^sub>d(Node3 t1 a t2 b t3)" |
"node21 (Up\<^sub>d t1) a (Node3 t2 b t3 c t4) = T\<^sub>d(Node2 (Node2 t1 a t2) b (Node2 t3 c t4))"

fun node22 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a up\<^sub>d" where
"node22 t1 a (T\<^sub>d t2) = T\<^sub>d(Node2 t1 a t2)" |
"node22 (Node2 t1 b t2) a (Up\<^sub>d t3) = Up\<^sub>d(Node3 t1 b t2 a t3)" |
"node22 (Node3 t1 b t2 c t3) a (Up\<^sub>d t4) = T\<^sub>d(Node2 (Node2 t1 b t2) c (Node2 t3 a t4))"

fun node31 :: "'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
"node31 (T\<^sub>d t1) a t2 b t3 = T\<^sub>d(Node3 t1 a t2 b t3)" |
"node31 (Up\<^sub>d t1) a (Node2 t2 b t3) c t4 = T\<^sub>d(Node2 (Node3 t1 a t2 b t3) c t4)" |
"node31 (Up\<^sub>d t1) a (Node3 t2 b t3 c t4) d t5 = T\<^sub>d(Node3 (Node2 t1 a t2) b (Node2 t3 c t4) d t5)"

fun node32 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
"node32 t1 a (T\<^sub>d t2) b t3 = T\<^sub>d(Node3 t1 a t2 b t3)" |
"node32 t1 a (Up\<^sub>d t2) b (Node2 t3 c t4) = T\<^sub>d(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node32 t1 a (Up\<^sub>d t2) b (Node3 t3 c t4 d t5) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))"

fun node33 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a up\<^sub>d" where
"node33 l a m b (T\<^sub>d r) = T\<^sub>d(Node3 l a m b r)" |
"node33 t1 a (Node2 t2 b t3) c (Up\<^sub>d t4) = T\<^sub>d(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node33 t1 a (Node3 t2 b t3 c t4) d (Up\<^sub>d t5) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))"

fun del_min :: "'a tree23 \<Rightarrow> 'a * 'a up\<^sub>d" where
"del_min (Node2 Leaf a Leaf) = (a, Up\<^sub>d Leaf)" |
"del_min (Node3 Leaf a Leaf b Leaf) = (a, T\<^sub>d(Node2 Leaf b Leaf))" |
"del_min (Node2 l a r) = (let (x,l') = del_min l in (x, node21 l' a r))" |
"del_min (Node3 l a m b r) = (let (x,l') = del_min l in (x, node31 l' a m b r))"

text \<open>In the base cases of \<open>del_min\<close> and \<open>del\<close> it is enough to check if one subtree is a \<open>Leaf\<close>,
in which case balancedness implies that so are the others. Exercise.\<close>

fun del :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
"del x Leaf = T\<^sub>d Leaf" |
"del x (Node2 Leaf a Leaf) =
  (if x = a then Up\<^sub>d Leaf else T\<^sub>d(Node2 Leaf a Leaf))" |
"del x (Node3 Leaf a Leaf b Leaf) =
  T\<^sub>d(if x = a then Node2 Leaf b Leaf else
     if x = b then Node2 Leaf a Leaf
     else Node3 Leaf a Leaf b Leaf)" |
"del x (Node2 l a r) =
  (case cmp x a of
     LT \<Rightarrow> node21 (del x l) a r |
     GT \<Rightarrow> node22 l a (del x r) |
     EQ \<Rightarrow> let (a',t) = del_min r in node22 l a' t)" |
"del x (Node3 l a m b r) =
  (case cmp x a of
     LT \<Rightarrow> node31 (del x l) a m b r |
     EQ \<Rightarrow> let (a',m') = del_min m in node32 l a' m' b r |
     GT \<Rightarrow>
       (case cmp x b of
          LT \<Rightarrow> node32 l a (del x m) b r |
          EQ \<Rightarrow> let (b',r') = del_min r in node33 l a m b' r' |
          GT \<Rightarrow> node33 l a m b (del x r)))"

definition delete :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"delete x t = tree\<^sub>d(del x t)"


subsection "Functional Correctness"

subsubsection "Proofs for isin"

lemma "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems (inorder t))"
by (induction t) (auto simp: elems_simps1 ball_Un)

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems (inorder t))"
by (induction t) (auto simp: elems_simps2)


subsubsection "Proofs for insert"

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(tree\<^sub>i(ins x t)) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps split: up\<^sub>i.splits)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert a t) = ins_list a (inorder t)"
by(simp add: insert_def inorder_ins)


subsubsection "Proofs for delete"

lemma inorder_node21: "height r > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node21 l' a r)) = inorder (tree\<^sub>d l') @ a # inorder r"
by(induct l' a r rule: node21.induct) auto

lemma inorder_node22: "height l > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node22 l a r')) = inorder l @ a # inorder (tree\<^sub>d r')"
by(induct l a r' rule: node22.induct) auto

lemma inorder_node31: "height m > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node31 l' a m b r)) = inorder (tree\<^sub>d l') @ a # inorder m @ b # inorder r"
by(induct l' a m b r rule: node31.induct) auto

lemma inorder_node32: "height r > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node32 l a m' b r)) = inorder l @ a # inorder (tree\<^sub>d m') @ b # inorder r"
by(induct l a m' b r rule: node32.induct) auto

lemma inorder_node33: "height m > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node33 l a m b r')) = inorder l @ a # inorder m @ b # inorder (tree\<^sub>d r')"
by(induct l a m b r' rule: node33.induct) auto

lemmas inorder_nodes = inorder_node21 inorder_node22
  inorder_node31 inorder_node32 inorder_node33

lemma del_minD:
  "del_min t = (x,t') \<Longrightarrow> bal t \<Longrightarrow> height t > 0 \<Longrightarrow>
  x # inorder(tree\<^sub>d t') = inorder t"
by(induction t arbitrary: t' rule: del_min.induct)
  (auto simp: inorder_nodes split: prod.splits)

lemma inorder_del: "\<lbrakk> bal t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(tree\<^sub>d (del x t)) = del_list x (inorder t)"
by(induction t rule: del.induct)
  (auto simp: del_list_simps inorder_nodes del_minD split!: if_split prod.splits)

lemma inorder_delete: "\<lbrakk> bal t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Balancedness\<close>


subsubsection "Proofs for insert"

text{* First a standard proof that @{const ins} preserves @{const bal}. *}

instantiation up\<^sub>i :: (type)height
begin

fun height_up\<^sub>i :: "'a up\<^sub>i \<Rightarrow> nat" where
"height (T\<^sub>i t) = height t" |
"height (Up\<^sub>i l a r) = height l"

instance ..

end

lemma bal_ins: "bal t \<Longrightarrow> bal (tree\<^sub>i(ins a t)) \<and> height(ins a t) = height t"
by (induct t) (auto split!: if_split up\<^sub>i.split) (* 15 secs in 2015 *)

text{* Now an alternative proof (by Brian Huffman) that runs faster because
two properties (balance and height) are combined in one predicate. *}

inductive full :: "nat \<Rightarrow> 'a tree23 \<Rightarrow> bool" where
"full 0 Leaf" |
"\<lbrakk>full n l; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Node2 l p r)" |
"\<lbrakk>full n l; full n m; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Node3 l p m q r)"

inductive_cases full_elims:
  "full n Leaf"
  "full n (Node2 l p r)"
  "full n (Node3 l p m q r)"

inductive_cases full_0_elim: "full 0 t"
inductive_cases full_Suc_elim: "full (Suc n) t"

lemma full_0_iff [simp]: "full 0 t \<longleftrightarrow> t = Leaf"
  by (auto elim: full_0_elim intro: full.intros)

lemma full_Leaf_iff [simp]: "full n Leaf \<longleftrightarrow> n = 0"
  by (auto elim: full_elims intro: full.intros)

lemma full_Suc_Node2_iff [simp]:
  "full (Suc n) (Node2 l p r) \<longleftrightarrow> full n l \<and> full n r"
  by (auto elim: full_elims intro: full.intros)

lemma full_Suc_Node3_iff [simp]:
  "full (Suc n) (Node3 l p m q r) \<longleftrightarrow> full n l \<and> full n m \<and> full n r"
  by (auto elim: full_elims intro: full.intros)

lemma full_imp_height: "full n t \<Longrightarrow> height t = n"
  by (induct set: full, simp_all)

lemma full_imp_bal: "full n t \<Longrightarrow> bal t"
  by (induct set: full, auto dest: full_imp_height)

lemma bal_imp_full: "bal t \<Longrightarrow> full (height t) t"
  by (induct t, simp_all)

lemma bal_iff_full: "bal t \<longleftrightarrow> (\<exists>n. full n t)"
  by (auto elim!: bal_imp_full full_imp_bal)

text {* The @{const "insert"} function either preserves the height of the
tree, or increases it by one. The constructor returned by the @{term
"insert"} function determines which: A return value of the form @{term
"T\<^sub>i t"} indicates that the height will be the same. A value of the
form @{term "Up\<^sub>i l p r"} indicates an increase in height. *}

fun full\<^sub>i :: "nat \<Rightarrow> 'a up\<^sub>i \<Rightarrow> bool" where
"full\<^sub>i n (T\<^sub>i t) \<longleftrightarrow> full n t" |
"full\<^sub>i n (Up\<^sub>i l p r) \<longleftrightarrow> full n l \<and> full n r"

lemma full\<^sub>i_ins: "full n t \<Longrightarrow> full\<^sub>i n (ins a t)"
by (induct rule: full.induct) (auto split: up\<^sub>i.split)

text {* The @{const insert} operation preserves balance. *}

lemma bal_insert: "bal t \<Longrightarrow> bal (insert a t)"
unfolding bal_iff_full insert_def
apply (erule exE)
apply (drule full\<^sub>i_ins [of _ _ a])
apply (cases "ins a t")
apply (auto intro: full.intros)
done


subsection "Proofs for delete"

instantiation up\<^sub>d :: (type)height
begin

fun height_up\<^sub>d :: "'a up\<^sub>d \<Rightarrow> nat" where
"height (T\<^sub>d t) = height t" |
"height (Up\<^sub>d t) = height t + 1"

instance ..

end

lemma bal_tree\<^sub>d_node21:
  "\<lbrakk>bal r; bal (tree\<^sub>d l'); height r = height l' \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d (node21 l' a r))"
by(induct l' a r rule: node21.induct) auto

lemma bal_tree\<^sub>d_node22:
  "\<lbrakk>bal(tree\<^sub>d r'); bal l; height r' = height l \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d (node22 l a r'))"
by(induct l a r' rule: node22.induct) auto

lemma bal_tree\<^sub>d_node31:
  "\<lbrakk> bal (tree\<^sub>d l'); bal m; bal r; height l' = height r; height m = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node31 l' a m b r))"
by(induct l' a m b r rule: node31.induct) auto

lemma bal_tree\<^sub>d_node32:
  "\<lbrakk> bal l; bal (tree\<^sub>d m'); bal r; height l = height r; height m' = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node32 l a m' b r))"
by(induct l a m' b r rule: node32.induct) auto

lemma bal_tree\<^sub>d_node33:
  "\<lbrakk> bal l; bal m; bal(tree\<^sub>d r'); height l = height r'; height m = height r' \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node33 l a m b r'))"
by(induct l a m b r' rule: node33.induct) auto

lemmas bals = bal_tree\<^sub>d_node21 bal_tree\<^sub>d_node22
  bal_tree\<^sub>d_node31 bal_tree\<^sub>d_node32 bal_tree\<^sub>d_node33

lemma height'_node21:
   "height r > 0 \<Longrightarrow> height(node21 l' a r) = max (height l') (height r) + 1"
by(induct l' a r rule: node21.induct)(simp_all)

lemma height'_node22:
   "height l > 0 \<Longrightarrow> height(node22 l a r') = max (height l) (height r') + 1"
by(induct l a r' rule: node22.induct)(simp_all)

lemma height'_node31:
  "height m > 0 \<Longrightarrow> height(node31 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node31.induct)(simp_all add: max_def)

lemma height'_node32:
  "height r > 0 \<Longrightarrow> height(node32 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node32.induct)(simp_all add: max_def)

lemma height'_node33:
  "height m > 0 \<Longrightarrow> height(node33 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node33.induct)(simp_all add: max_def)

lemmas heights = height'_node21 height'_node22
  height'_node31 height'_node32 height'_node33

lemma height_del_min:
  "del_min t = (x, t') \<Longrightarrow> height t > 0 \<Longrightarrow> bal t \<Longrightarrow> height t' = height t"
by(induct t arbitrary: x t' rule: del_min.induct)
  (auto simp: heights split: prod.splits)

lemma height_del: "bal t \<Longrightarrow> height(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp: heights max_def height_del_min split: prod.splits)

lemma bal_del_min:
  "\<lbrakk> del_min t = (x, t'); bal t; height t > 0 \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d t')"
by(induct t arbitrary: x t' rule: del_min.induct)
  (auto simp: heights height_del_min bals split: prod.splits)

lemma bal_tree\<^sub>d_del: "bal t \<Longrightarrow> bal(tree\<^sub>d(del x t))"
by(induction x t rule: del.induct)
  (auto simp: bals bal_del_min height_del height_del_min split: prod.splits)

corollary bal_delete: "bal t \<Longrightarrow> bal(delete x t)"
by(simp add: delete_def bal_tree\<^sub>d_del)


subsection \<open>Overall Correctness\<close>

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = bal
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 6 thus ?case by(simp add: bal_insert)
next
  case 7 thus ?case by(simp add: bal_delete)
qed simp+

end
