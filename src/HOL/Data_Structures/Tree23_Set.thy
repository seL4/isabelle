(* Author: Tobias Nipkow *)

section \<open>2-3 Tree Implementation of Sets\<close>

theory Tree23_Set
imports
  Tree23
  Cmp
  Set_Specs
begin

declare sorted_wrt.simps(2)[simp del]

definition empty :: "'a tree23" where
"empty = Leaf"

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

datatype 'a upI = TI "'a tree23" | OF "'a tree23" 'a "'a tree23"

fun treeI :: "'a upI \<Rightarrow> 'a tree23" where
"treeI (TI t) = t" |
"treeI (OF l a r) = Node2 l a r"

fun ins :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a upI" where
"ins x Leaf = OF Leaf x Leaf" |
"ins x (Node2 l a r) =
   (case cmp x a of
      LT \<Rightarrow>
        (case ins x l of
           TI l' => TI (Node2 l' a r) |
           OF l1 b l2 => TI (Node3 l1 b l2 a r)) |
      EQ \<Rightarrow> TI (Node2 l a r) |
      GT \<Rightarrow>
        (case ins x r of
           TI r' => TI (Node2 l a r') |
           OF r1 b r2 => TI (Node3 l a r1 b r2)))" |
"ins x (Node3 l a m b r) =
   (case cmp x a of
      LT \<Rightarrow>
        (case ins x l of
           TI l' => TI (Node3 l' a m b r) |
           OF l1 c l2 => OF (Node2 l1 c l2) a (Node2 m b r)) |
      EQ \<Rightarrow> TI (Node3 l a m b r) |
      GT \<Rightarrow>
        (case cmp x b of
           GT \<Rightarrow>
             (case ins x r of
                TI r' => TI (Node3 l a m b r') |
                OF r1 c r2 => OF (Node2 l a m) b (Node2 r1 c r2)) |
           EQ \<Rightarrow> TI (Node3 l a m b r) |
           LT \<Rightarrow>
             (case ins x m of
                TI m' => TI (Node3 l a m' b r) |
                OF m1 c m2 => OF (Node2 l a m1) c (Node2 m2 b r))))"

hide_const insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"insert x t = treeI(ins x t)"

datatype 'a upD = TD "'a tree23" | UF "'a tree23"

fun treeD :: "'a upD \<Rightarrow> 'a tree23" where
"treeD (TD t) = t" |
"treeD (UF t) = t"

(* Variation: return None to signal no-change *)

fun node21 :: "'a upD \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a upD" where
"node21 (TD t1) a t2 = TD(Node2 t1 a t2)" |
"node21 (UF t1) a (Node2 t2 b t3) = UF(Node3 t1 a t2 b t3)" |
"node21 (UF t1) a (Node3 t2 b t3 c t4) = TD(Node2 (Node2 t1 a t2) b (Node2 t3 c t4))"

fun node22 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a upD \<Rightarrow> 'a upD" where
"node22 t1 a (TD t2) = TD(Node2 t1 a t2)" |
"node22 (Node2 t1 b t2) a (UF t3) = UF(Node3 t1 b t2 a t3)" |
"node22 (Node3 t1 b t2 c t3) a (UF t4) = TD(Node2 (Node2 t1 b t2) c (Node2 t3 a t4))"

fun node31 :: "'a upD \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a upD" where
"node31 (TD t1) a t2 b t3 = TD(Node3 t1 a t2 b t3)" |
"node31 (UF t1) a (Node2 t2 b t3) c t4 = TD(Node2 (Node3 t1 a t2 b t3) c t4)" |
"node31 (UF t1) a (Node3 t2 b t3 c t4) d t5 = TD(Node3 (Node2 t1 a t2) b (Node2 t3 c t4) d t5)"

fun node32 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a upD \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a upD" where
"node32 t1 a (TD t2) b t3 = TD(Node3 t1 a t2 b t3)" |
"node32 t1 a (UF t2) b (Node2 t3 c t4) = TD(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node32 t1 a (UF t2) b (Node3 t3 c t4 d t5) = TD(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))"

fun node33 :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a upD \<Rightarrow> 'a upD" where
"node33 l a m b (TD r) = TD(Node3 l a m b r)" |
"node33 t1 a (Node2 t2 b t3) c (UF t4) = TD(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node33 t1 a (Node3 t2 b t3 c t4) d (UF t5) = TD(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))"

fun split_min :: "'a tree23 \<Rightarrow> 'a * 'a upD" where
"split_min (Node2 Leaf a Leaf) = (a, UF Leaf)" |
"split_min (Node3 Leaf a Leaf b Leaf) = (a, TD(Node2 Leaf b Leaf))" |
"split_min (Node2 l a r) = (let (x,l') = split_min l in (x, node21 l' a r))" |
"split_min (Node3 l a m b r) = (let (x,l') = split_min l in (x, node31 l' a m b r))"

text \<open>In the base cases of \<open>split_min\<close> and \<open>del\<close> it is enough to check if one subtree is a \<open>Leaf\<close>,
in which case completeness implies that so are the others. Exercise.\<close>

fun del :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a upD" where
"del x Leaf = TD Leaf" |
"del x (Node2 Leaf a Leaf) =
  (if x = a then UF Leaf else TD(Node2 Leaf a Leaf))" |
"del x (Node3 Leaf a Leaf b Leaf) =
  TD(if x = a then Node2 Leaf b Leaf else
     if x = b then Node2 Leaf a Leaf
     else Node3 Leaf a Leaf b Leaf)" |
"del x (Node2 l a r) =
  (case cmp x a of
     LT \<Rightarrow> node21 (del x l) a r |
     GT \<Rightarrow> node22 l a (del x r) |
     EQ \<Rightarrow> let (a',r') = split_min r in node22 l a' r')" |
"del x (Node3 l a m b r) =
  (case cmp x a of
     LT \<Rightarrow> node31 (del x l) a m b r |
     EQ \<Rightarrow> let (a',m') = split_min m in node32 l a' m' b r |
     GT \<Rightarrow>
       (case cmp x b of
          LT \<Rightarrow> node32 l a (del x m) b r |
          EQ \<Rightarrow> let (b',r') = split_min r in node33 l a m b' r' |
          GT \<Rightarrow> node33 l a m b (del x r)))"

definition delete :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"delete x t = treeD(del x t)"


subsection "Functional Correctness"

subsubsection "Proofs for isin"

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
by (induction t) (auto simp: isin_simps)


subsubsection "Proofs for insert"

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(treeI(ins x t)) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps split: upI.splits)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert a t) = ins_list a (inorder t)"
by(simp add: insert_def inorder_ins)


subsubsection "Proofs for delete"

lemma inorder_node21: "height r > 0 \<Longrightarrow>
  inorder (treeD (node21 l' a r)) = inorder (treeD l') @ a # inorder r"
by(induct l' a r rule: node21.induct) auto

lemma inorder_node22: "height l > 0 \<Longrightarrow>
  inorder (treeD (node22 l a r')) = inorder l @ a # inorder (treeD r')"
by(induct l a r' rule: node22.induct) auto

lemma inorder_node31: "height m > 0 \<Longrightarrow>
  inorder (treeD (node31 l' a m b r)) = inorder (treeD l') @ a # inorder m @ b # inorder r"
by(induct l' a m b r rule: node31.induct) auto

lemma inorder_node32: "height r > 0 \<Longrightarrow>
  inorder (treeD (node32 l a m' b r)) = inorder l @ a # inorder (treeD m') @ b # inorder r"
by(induct l a m' b r rule: node32.induct) auto

lemma inorder_node33: "height m > 0 \<Longrightarrow>
  inorder (treeD (node33 l a m b r')) = inorder l @ a # inorder m @ b # inorder (treeD r')"
by(induct l a m b r' rule: node33.induct) auto

lemmas inorder_nodes = inorder_node21 inorder_node22
  inorder_node31 inorder_node32 inorder_node33

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> complete t \<Longrightarrow> height t > 0 \<Longrightarrow>
  x # inorder(treeD t') = inorder t"
by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: inorder_nodes split: prod.splits)

lemma inorder_del: "\<lbrakk> complete t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(treeD (del x t)) = del_list x (inorder t)"
by(induction t rule: del.induct)
  (auto simp: del_list_simps inorder_nodes split_minD split!: if_split prod.splits)

lemma inorder_delete: "\<lbrakk> complete t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Completeness\<close>


subsubsection "Proofs for insert"

text\<open>First a standard proof that \<^const>\<open>ins\<close> preserves \<^const>\<open>complete\<close>.\<close>

fun hI :: "'a upI \<Rightarrow> nat" where
"hI (TI t) = height t" |
"hI (OF l a r) = height l"

lemma complete_ins: "complete t \<Longrightarrow> complete (treeI(ins a t)) \<and> hI(ins a t) = height t"
by (induct t) (auto split!: if_split upI.split) (* 15 secs in 2015 *)

text\<open>Now an alternative proof (by Brian Huffman) that runs faster because
two properties (completeness and height) are combined in one predicate.\<close>

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

lemma full_imp_complete: "full n t \<Longrightarrow> complete t"
  by (induct set: full, auto dest: full_imp_height)

lemma complete_imp_full: "complete t \<Longrightarrow> full (height t) t"
  by (induct t, simp_all)

lemma complete_iff_full: "complete t \<longleftrightarrow> (\<exists>n. full n t)"
  by (auto elim!: complete_imp_full full_imp_complete)

text \<open>The \<^const>\<open>insert\<close> function either preserves the height of the
tree, or increases it by one. The constructor returned by the \<^term>\<open>insert\<close> function determines which: A return value of the form \<^term>\<open>TI t\<close> indicates that the height will be the same. A value of the
form \<^term>\<open>OF l p r\<close> indicates an increase in height.\<close>

fun full\<^sub>i :: "nat \<Rightarrow> 'a upI \<Rightarrow> bool" where
"full\<^sub>i n (TI t) \<longleftrightarrow> full n t" |
"full\<^sub>i n (OF l p r) \<longleftrightarrow> full n l \<and> full n r"

lemma full\<^sub>i_ins: "full n t \<Longrightarrow> full\<^sub>i n (ins a t)"
by (induct rule: full.induct) (auto split: upI.split)

text \<open>The \<^const>\<open>insert\<close> operation preserves completeance.\<close>

lemma complete_insert: "complete t \<Longrightarrow> complete (insert a t)"
unfolding complete_iff_full insert_def
apply (erule exE)
apply (drule full\<^sub>i_ins [of _ _ a])
apply (cases "ins a t")
apply (auto intro: full.intros)
done


subsection "Proofs for delete"

fun hD :: "'a upD \<Rightarrow> nat" where
"hD (TD t) = height t" |
"hD (UF t) = height t + 1"

lemma complete_treeD_node21:
  "\<lbrakk>complete r; complete (treeD l'); height r = hD l' \<rbrakk> \<Longrightarrow> complete (treeD (node21 l' a r))"
by(induct l' a r rule: node21.induct) auto

lemma complete_treeD_node22:
  "\<lbrakk>complete(treeD r'); complete l; hD r' = height l \<rbrakk> \<Longrightarrow> complete (treeD (node22 l a r'))"
by(induct l a r' rule: node22.induct) auto

lemma complete_treeD_node31:
  "\<lbrakk> complete (treeD l'); complete m; complete r; hD l' = height r; height m = height r \<rbrakk>
  \<Longrightarrow> complete (treeD (node31 l' a m b r))"
by(induct l' a m b r rule: node31.induct) auto

lemma complete_treeD_node32:
  "\<lbrakk> complete l; complete (treeD m'); complete r; height l = height r; hD m' = height r \<rbrakk>
  \<Longrightarrow> complete (treeD (node32 l a m' b r))"
by(induct l a m' b r rule: node32.induct) auto

lemma complete_treeD_node33:
  "\<lbrakk> complete l; complete m; complete(treeD r'); height l = hD r'; height m = hD r' \<rbrakk>
  \<Longrightarrow> complete (treeD (node33 l a m b r'))"
by(induct l a m b r' rule: node33.induct) auto

lemmas completes = complete_treeD_node21 complete_treeD_node22
  complete_treeD_node31 complete_treeD_node32 complete_treeD_node33

lemma height'_node21:
   "height r > 0 \<Longrightarrow> hD(node21 l' a r) = max (hD l') (height r) + 1"
by(induct l' a r rule: node21.induct)(simp_all)

lemma height'_node22:
   "height l > 0 \<Longrightarrow> hD(node22 l a r') = max (height l) (hD r') + 1"
by(induct l a r' rule: node22.induct)(simp_all)

lemma height'_node31:
  "height m > 0 \<Longrightarrow> hD(node31 l a m b r) =
   max (hD l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node31.induct)(simp_all add: max_def)

lemma height'_node32:
  "height r > 0 \<Longrightarrow> hD(node32 l a m b r) =
   max (height l) (max (hD m) (height r)) + 1"
by(induct l a m b r rule: node32.induct)(simp_all add: max_def)

lemma height'_node33:
  "height m > 0 \<Longrightarrow> hD(node33 l a m b r) =
   max (height l) (max (height m) (hD r)) + 1"
by(induct l a m b r rule: node33.induct)(simp_all add: max_def)

lemmas heights = height'_node21 height'_node22
  height'_node31 height'_node32 height'_node33

lemma height_split_min:
  "split_min t = (x, t') \<Longrightarrow> height t > 0 \<Longrightarrow> complete t \<Longrightarrow> hD t' = height t"
by(induct t arbitrary: x t' rule: split_min.induct)
  (auto simp: heights split: prod.splits)

lemma height_del: "complete t \<Longrightarrow> hD(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp: heights max_def height_split_min split: prod.splits)

lemma complete_split_min:
  "\<lbrakk> split_min t = (x, t'); complete t; height t > 0 \<rbrakk> \<Longrightarrow> complete (treeD t')"
by(induct t arbitrary: x t' rule: split_min.induct)
  (auto simp: heights height_split_min completes split: prod.splits)

lemma complete_treeD_del: "complete t \<Longrightarrow> complete(treeD(del x t))"
by(induction x t rule: del.induct)
  (auto simp: completes complete_split_min height_del height_split_min split: prod.splits)

corollary complete_delete: "complete t \<Longrightarrow> complete(delete x t)"
by(simp add: delete_def complete_treeD_del)


subsection \<open>Overall Correctness\<close>

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = complete
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 6 thus ?case by(simp add: complete_insert)
next
  case 7 thus ?case by(simp add: complete_delete)
qed (simp add: empty_def)+

end
