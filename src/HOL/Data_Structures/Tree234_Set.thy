(* Author: Tobias Nipkow *)

section \<open>2-3-4 Tree Implementation of Sets\<close>

theory Tree234_Set
imports
  Tree234
  Cmp
  Set_Specs
begin

declare sorted_wrt.simps(2)[simp del]

subsection \<open>Set operations on 2-3-4 trees\<close>

definition empty :: "'a tree234" where
"empty = Leaf"

fun isin :: "'a::linorder tree234 \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node2 l a r) x =
  (case cmp x a of LT \<Rightarrow> isin l x | EQ \<Rightarrow> True | GT \<Rightarrow> isin r x)" |
"isin (Node3 l a m b r) x =
  (case cmp x a of LT \<Rightarrow> isin l x | EQ \<Rightarrow> True | GT \<Rightarrow> (case cmp x b of
   LT \<Rightarrow> isin m x | EQ \<Rightarrow> True | GT \<Rightarrow> isin r x))" |
"isin (Node4 t1 a t2 b t3 c t4) x =
  (case cmp x b of
     LT \<Rightarrow>
       (case cmp x a of
          LT \<Rightarrow> isin t1 x |
          EQ \<Rightarrow> True |
          GT \<Rightarrow> isin t2 x) |
     EQ \<Rightarrow> True |
     GT \<Rightarrow>
       (case cmp x c of
          LT \<Rightarrow> isin t3 x |
          EQ \<Rightarrow> True |
          GT \<Rightarrow> isin t4 x))"

datatype 'a up\<^sub>i = T\<^sub>i "'a tree234" | Up\<^sub>i "'a tree234" 'a "'a tree234"

fun tree\<^sub>i :: "'a up\<^sub>i \<Rightarrow> 'a tree234" where
"tree\<^sub>i (T\<^sub>i t) = t" |
"tree\<^sub>i (Up\<^sub>i l a r) = Node2 l a r"

fun ins :: "'a::linorder \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>i" where
"ins x Leaf = Up\<^sub>i Leaf x Leaf" |
"ins x (Node2 l a r) =
   (case cmp x a of
      LT \<Rightarrow> (case ins x l of
              T\<^sub>i l' => T\<^sub>i (Node2 l' a r)
            | Up\<^sub>i l1 b l2 => T\<^sub>i (Node3 l1 b l2 a r)) |
      EQ \<Rightarrow> T\<^sub>i (Node2 l x r) |
      GT \<Rightarrow> (case ins x r of
              T\<^sub>i r' => T\<^sub>i (Node2 l a r')
            | Up\<^sub>i r1 b r2 => T\<^sub>i (Node3 l a r1 b r2)))" |
"ins x (Node3 l a m b r) =
   (case cmp x a of
      LT \<Rightarrow> (case ins x l of
              T\<^sub>i l' => T\<^sub>i (Node3 l' a m b r)
            | Up\<^sub>i l1 c l2 => Up\<^sub>i (Node2 l1 c l2) a (Node2 m b r)) |
      EQ \<Rightarrow> T\<^sub>i (Node3 l a m b r) |
      GT \<Rightarrow> (case cmp x b of
               GT \<Rightarrow> (case ins x r of
                       T\<^sub>i r' => T\<^sub>i (Node3 l a m b r')
                     | Up\<^sub>i r1 c r2 => Up\<^sub>i (Node2 l a m) b (Node2 r1 c r2)) |
               EQ \<Rightarrow> T\<^sub>i (Node3 l a m b r) |
               LT \<Rightarrow> (case ins x m of
                       T\<^sub>i m' => T\<^sub>i (Node3 l a m' b r)
                     | Up\<^sub>i m1 c m2 => Up\<^sub>i (Node2 l a m1) c (Node2 m2 b r))))" |
"ins x (Node4 t1 a t2 b t3 c t4) =
  (case cmp x b of
     LT \<Rightarrow>
       (case cmp x a of
          LT \<Rightarrow>
            (case ins x t1 of
               T\<^sub>i t => T\<^sub>i (Node4 t a t2 b t3 c t4) |
               Up\<^sub>i l y r => Up\<^sub>i (Node2 l y r) a (Node3 t2 b t3 c t4)) |
          EQ \<Rightarrow> T\<^sub>i (Node4 t1 a t2 b t3 c t4) |
          GT \<Rightarrow>
            (case ins x t2 of
               T\<^sub>i t => T\<^sub>i (Node4 t1 a t b t3 c t4) |
               Up\<^sub>i l y r => Up\<^sub>i (Node2 t1 a l) y (Node3 r b t3 c t4))) |
     EQ \<Rightarrow> T\<^sub>i (Node4 t1 a t2 b t3 c t4) |
     GT \<Rightarrow>
       (case cmp x c of
          LT \<Rightarrow>
            (case ins x t3 of
              T\<^sub>i t => T\<^sub>i (Node4 t1 a t2 b t c t4) |
              Up\<^sub>i l y r => Up\<^sub>i (Node2 t1 a t2) b (Node3 l y r c t4)) |
          EQ \<Rightarrow> T\<^sub>i (Node4 t1 a t2 b t3 c t4) |
          GT \<Rightarrow>
            (case ins x t4 of
              T\<^sub>i t => T\<^sub>i (Node4 t1 a t2 b t3 c t) |
              Up\<^sub>i l y r => Up\<^sub>i (Node2 t1 a t2) b (Node3 t3 c l y r))))"

hide_const insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree234 \<Rightarrow> 'a tree234" where
"insert x t = tree\<^sub>i(ins x t)"

datatype 'a up\<^sub>d = T\<^sub>d "'a tree234" | Up\<^sub>d "'a tree234"

fun tree\<^sub>d :: "'a up\<^sub>d \<Rightarrow> 'a tree234" where
"tree\<^sub>d (T\<^sub>d t) = t" |
"tree\<^sub>d (Up\<^sub>d t) = t"

fun node21 :: "'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node21 (T\<^sub>d l) a r = T\<^sub>d(Node2 l a r)" |
"node21 (Up\<^sub>d l) a (Node2 lr b rr) = Up\<^sub>d(Node3 l a lr b rr)" |
"node21 (Up\<^sub>d l) a (Node3 lr b mr c rr) = T\<^sub>d(Node2 (Node2 l a lr) b (Node2 mr c rr))" |
"node21 (Up\<^sub>d t1) a (Node4 t2 b t3 c t4 d t5) = T\<^sub>d(Node2 (Node2 t1 a t2) b (Node3 t3 c t4 d t5))"

fun node22 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a up\<^sub>d" where
"node22 l a (T\<^sub>d r) = T\<^sub>d(Node2 l a r)" |
"node22 (Node2 ll b rl) a (Up\<^sub>d r) = Up\<^sub>d(Node3 ll b rl a r)" |
"node22 (Node3 ll b ml c rl) a (Up\<^sub>d r) = T\<^sub>d(Node2 (Node2 ll b ml) c (Node2 rl a r))" |
"node22 (Node4 t1 a t2 b t3 c t4) d (Up\<^sub>d t5) = T\<^sub>d(Node2 (Node2 t1 a t2) b (Node3 t3 c t4 d t5))"

fun node31 :: "'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node31 (T\<^sub>d t1) a t2 b t3 = T\<^sub>d(Node3 t1 a t2 b t3)" |
"node31 (Up\<^sub>d t1) a (Node2 t2 b t3) c t4 = T\<^sub>d(Node2 (Node3 t1 a t2 b t3) c t4)" |
"node31 (Up\<^sub>d t1) a (Node3 t2 b t3 c t4) d t5 = T\<^sub>d(Node3 (Node2 t1 a t2) b (Node2 t3 c t4) d t5)" |
"node31 (Up\<^sub>d t1) a (Node4 t2 b t3 c t4 d t5) e t6 = T\<^sub>d(Node3 (Node2 t1 a t2) b (Node3 t3 c t4 d t5) e t6)"

fun node32 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node32 t1 a (T\<^sub>d t2) b t3 = T\<^sub>d(Node3 t1 a t2 b t3)" |
"node32 t1 a (Up\<^sub>d t2) b (Node2 t3 c t4) = T\<^sub>d(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node32 t1 a (Up\<^sub>d t2) b (Node3 t3 c t4 d t5) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))" |
"node32 t1 a (Up\<^sub>d t2) b (Node4 t3 c t4 d t5 e t6) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node3 t4 d t5 e t6))"

fun node33 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a up\<^sub>d" where
"node33 l a m b (T\<^sub>d r) = T\<^sub>d(Node3 l a m b r)" |
"node33 t1 a (Node2 t2 b t3) c (Up\<^sub>d t4) = T\<^sub>d(Node2 t1 a (Node3 t2 b t3 c t4))" |
"node33 t1 a (Node3 t2 b t3 c t4) d (Up\<^sub>d t5) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))" |
"node33 t1 a (Node4 t2 b t3 c t4 d t5) e (Up\<^sub>d t6) = T\<^sub>d(Node3 t1 a (Node2 t2 b t3) c (Node3 t4 d t5 e t6))"

fun node41 :: "'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node41 (T\<^sub>d t1) a t2 b t3 c t4 = T\<^sub>d(Node4 t1 a t2 b t3 c t4)" |
"node41 (Up\<^sub>d t1) a (Node2 t2 b t3) c t4 d t5 = T\<^sub>d(Node3 (Node3 t1 a t2 b t3) c t4 d t5)" |
"node41 (Up\<^sub>d t1) a (Node3 t2 b t3 c t4) d t5 e t6 = T\<^sub>d(Node4 (Node2 t1 a t2) b (Node2 t3 c t4) d t5 e t6)" |
"node41 (Up\<^sub>d t1) a (Node4 t2 b t3 c t4 d t5) e t6 f t7 = T\<^sub>d(Node4 (Node2 t1 a t2) b (Node3 t3 c t4 d t5) e t6 f t7)"

fun node42 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node42 t1 a (T\<^sub>d t2) b t3 c t4 = T\<^sub>d(Node4 t1 a t2 b t3 c t4)" |
"node42 (Node2 t1 a t2) b (Up\<^sub>d t3) c t4 d t5 = T\<^sub>d(Node3 (Node3 t1 a t2 b t3) c t4 d t5)" |
"node42 (Node3 t1 a t2 b t3) c (Up\<^sub>d t4) d t5 e t6 = T\<^sub>d(Node4 (Node2 t1 a t2) b (Node2 t3 c t4) d t5 e t6)" |
"node42 (Node4 t1 a t2 b t3 c t4) d (Up\<^sub>d t5) e t6 f t7 = T\<^sub>d(Node4 (Node2 t1 a t2) b (Node3 t3 c t4 d t5) e t6 f t7)"

fun node43 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"node43 t1 a t2 b (T\<^sub>d t3) c t4 = T\<^sub>d(Node4 t1 a t2 b t3 c t4)" |
"node43 t1 a (Node2 t2 b t3) c (Up\<^sub>d t4) d t5 = T\<^sub>d(Node3 t1 a (Node3 t2 b t3 c t4) d t5)" |
"node43 t1 a (Node3 t2 b t3 c t4) d (Up\<^sub>d t5) e t6 = T\<^sub>d(Node4 t1 a (Node2 t2 b t3) c (Node2 t4 d t5) e t6)" |
"node43 t1 a (Node4 t2 b t3 c t4 d t5) e (Up\<^sub>d t6) f t7 = T\<^sub>d(Node4 t1 a (Node2 t2 b t3) c (Node3 t4 d t5 e t6) f t7)"

fun node44 :: "'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a tree234 \<Rightarrow> 'a \<Rightarrow> 'a up\<^sub>d \<Rightarrow> 'a up\<^sub>d" where
"node44 t1 a t2 b t3 c (T\<^sub>d t4) = T\<^sub>d(Node4 t1 a t2 b t3 c t4)" |
"node44 t1 a t2 b (Node2 t3 c t4) d (Up\<^sub>d t5) = T\<^sub>d(Node3 t1 a t2 b (Node3 t3 c t4 d t5))" |
"node44 t1 a t2 b (Node3 t3 c t4 d t5) e (Up\<^sub>d t6) = T\<^sub>d(Node4 t1 a t2 b (Node2 t3 c t4) d (Node2 t5 e t6))" |
"node44 t1 a t2 b (Node4 t3 c t4 d t5 e t6) f (Up\<^sub>d t7) = T\<^sub>d(Node4 t1 a t2 b (Node2 t3 c t4) d (Node3 t5 e t6 f t7))"

fun split_min :: "'a tree234 \<Rightarrow> 'a * 'a up\<^sub>d" where
"split_min (Node2 Leaf a Leaf) = (a, Up\<^sub>d Leaf)" |
"split_min (Node3 Leaf a Leaf b Leaf) = (a, T\<^sub>d(Node2 Leaf b Leaf))" |
"split_min (Node4 Leaf a Leaf b Leaf c Leaf) = (a, T\<^sub>d(Node3 Leaf b Leaf c Leaf))" |
"split_min (Node2 l a r) = (let (x,l') = split_min l in (x, node21 l' a r))" |
"split_min (Node3 l a m b r) = (let (x,l') = split_min l in (x, node31 l' a m b r))" |
"split_min (Node4 l a m b n c r) = (let (x,l') = split_min l in (x, node41 l' a m b n c r))"

fun del :: "'a::linorder \<Rightarrow> 'a tree234 \<Rightarrow> 'a up\<^sub>d" where
"del k Leaf = T\<^sub>d Leaf" |
"del k (Node2 Leaf p Leaf) = (if k=p then Up\<^sub>d Leaf else T\<^sub>d(Node2 Leaf p Leaf))" |
"del k (Node3 Leaf p Leaf q Leaf) = T\<^sub>d(if k=p then Node2 Leaf q Leaf
  else if k=q then Node2 Leaf p Leaf else Node3 Leaf p Leaf q Leaf)" |
"del k (Node4 Leaf a Leaf b Leaf c Leaf) =
  T\<^sub>d(if k=a then Node3 Leaf b Leaf c Leaf else
     if k=b then Node3 Leaf a Leaf c Leaf else
     if k=c then Node3 Leaf a Leaf b Leaf
     else Node4 Leaf a Leaf b Leaf c Leaf)" |
"del k (Node2 l a r) = (case cmp k a of
  LT \<Rightarrow> node21 (del k l) a r |
  GT \<Rightarrow> node22 l a (del k r) |
  EQ \<Rightarrow> let (a',t) = split_min r in node22 l a' t)" |
"del k (Node3 l a m b r) = (case cmp k a of
  LT \<Rightarrow> node31 (del k l) a m b r |
  EQ \<Rightarrow> let (a',m') = split_min m in node32 l a' m' b r |
  GT \<Rightarrow> (case cmp k b of
           LT \<Rightarrow> node32 l a (del k m) b r |
           EQ \<Rightarrow> let (b',r') = split_min r in node33 l a m b' r' |
           GT \<Rightarrow> node33 l a m b (del k r)))" |
"del k (Node4 l a m b n c r) = (case cmp k b of
  LT \<Rightarrow> (case cmp k a of
          LT \<Rightarrow> node41 (del k l) a m b n c r |
          EQ \<Rightarrow> let (a',m') = split_min m in node42 l a' m' b n c r |
          GT \<Rightarrow> node42 l a (del k m) b n c r) |
  EQ \<Rightarrow> let (b',n') = split_min n in node43 l a m b' n' c r |
  GT \<Rightarrow> (case cmp k c of
           LT \<Rightarrow> node43 l a m b (del k n) c r |
           EQ \<Rightarrow> let (c',r') = split_min r in node44 l a m b n c' r' |
           GT \<Rightarrow> node44 l a m b n c (del k r)))"

definition delete :: "'a::linorder \<Rightarrow> 'a tree234 \<Rightarrow> 'a tree234" where
"delete x t = tree\<^sub>d(del x t)"


subsection "Functional correctness"

subsubsection \<open>Functional correctness of isin:\<close>

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
by (induction t) (auto simp: isin_simps ball_Un)


subsubsection \<open>Functional correctness of insert:\<close>

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(tree\<^sub>i(ins x t)) = ins_list x (inorder t)"
by(induction t) (auto, auto simp: ins_list_simps split!: if_splits up\<^sub>i.splits)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert a t) = ins_list a (inorder t)"
by(simp add: insert_def inorder_ins)


subsubsection \<open>Functional correctness of delete\<close>

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

lemma inorder_node41: "height m > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node41 l' a m b n c r)) = inorder (tree\<^sub>d l') @ a # inorder m @ b # inorder n @ c # inorder r"
by(induct l' a m b n c r rule: node41.induct) auto

lemma inorder_node42: "height l > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node42 l a m b n c r)) = inorder l @ a # inorder (tree\<^sub>d m) @ b # inorder n @ c # inorder r"
by(induct l a m b n c r rule: node42.induct) auto

lemma inorder_node43: "height m > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node43 l a m b n c r)) = inorder l @ a # inorder m @ b # inorder(tree\<^sub>d n) @ c # inorder r"
by(induct l a m b n c r rule: node43.induct) auto

lemma inorder_node44: "height n > 0 \<Longrightarrow>
  inorder (tree\<^sub>d (node44 l a m b n c r)) = inorder l @ a # inorder m @ b # inorder n @ c # inorder (tree\<^sub>d r)"
by(induct l a m b n c r rule: node44.induct) auto

lemmas inorder_nodes = inorder_node21 inorder_node22
  inorder_node31 inorder_node32 inorder_node33
  inorder_node41 inorder_node42 inorder_node43 inorder_node44

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> bal t \<Longrightarrow> height t > 0 \<Longrightarrow>
  x # inorder(tree\<^sub>d t') = inorder t"
by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: inorder_nodes split: prod.splits)

lemma inorder_del: "\<lbrakk> bal t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(tree\<^sub>d (del x t)) = del_list x (inorder t)"
by(induction t rule: del.induct)
  (auto simp: inorder_nodes del_list_simps split_minD split!: if_split prod.splits)
  (* 30 secs (2016) *)

lemma inorder_delete: "\<lbrakk> bal t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Balancedness\<close>

subsubsection "Proofs for insert"

text\<open>First a standard proof that @{const ins} preserves @{const bal}.\<close>

instantiation up\<^sub>i :: (type)height
begin

fun height_up\<^sub>i :: "'a up\<^sub>i \<Rightarrow> nat" where
"height (T\<^sub>i t) = height t" |
"height (Up\<^sub>i l a r) = height l"

instance ..

end

lemma bal_ins: "bal t \<Longrightarrow> bal (tree\<^sub>i(ins a t)) \<and> height(ins a t) = height t"
by (induct t) (auto split!: if_split up\<^sub>i.split)


text\<open>Now an alternative proof (by Brian Huffman) that runs faster because
two properties (balance and height) are combined in one predicate.\<close>

inductive full :: "nat \<Rightarrow> 'a tree234 \<Rightarrow> bool" where
"full 0 Leaf" |
"\<lbrakk>full n l; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Node2 l p r)" |
"\<lbrakk>full n l; full n m; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Node3 l p m q r)" |
"\<lbrakk>full n l; full n m; full n m'; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Node4 l p m q m' q' r)"

inductive_cases full_elims:
  "full n Leaf"
  "full n (Node2 l p r)"
  "full n (Node3 l p m q r)"
  "full n (Node4 l p m q m' q' r)"

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

lemma full_Suc_Node4_iff [simp]:
  "full (Suc n) (Node4 l p m q m' q' r) \<longleftrightarrow> full n l \<and> full n m \<and> full n m' \<and> full n r"
  by (auto elim: full_elims intro: full.intros)

lemma full_imp_height: "full n t \<Longrightarrow> height t = n"
  by (induct set: full, simp_all)

lemma full_imp_bal: "full n t \<Longrightarrow> bal t"
  by (induct set: full, auto dest: full_imp_height)

lemma bal_imp_full: "bal t \<Longrightarrow> full (height t) t"
  by (induct t, simp_all)

lemma bal_iff_full: "bal t \<longleftrightarrow> (\<exists>n. full n t)"
  by (auto elim!: bal_imp_full full_imp_bal)

text \<open>The @{const "insert"} function either preserves the height of the
tree, or increases it by one. The constructor returned by the @{term
"insert"} function determines which: A return value of the form @{term
"T\<^sub>i t"} indicates that the height will be the same. A value of the
form @{term "Up\<^sub>i l p r"} indicates an increase in height.\<close>

primrec full\<^sub>i :: "nat \<Rightarrow> 'a up\<^sub>i \<Rightarrow> bool" where
"full\<^sub>i n (T\<^sub>i t) \<longleftrightarrow> full n t" |
"full\<^sub>i n (Up\<^sub>i l p r) \<longleftrightarrow> full n l \<and> full n r"

lemma full\<^sub>i_ins: "full n t \<Longrightarrow> full\<^sub>i n (ins a t)"
by (induct rule: full.induct) (auto, auto split: up\<^sub>i.split)

text \<open>The @{const insert} operation preserves balance.\<close>

lemma bal_insert: "bal t \<Longrightarrow> bal (insert a t)"
unfolding bal_iff_full insert_def
apply (erule exE)
apply (drule full\<^sub>i_ins [of _ _ a])
apply (cases "ins a t")
apply (auto intro: full.intros)
done


subsubsection "Proofs for delete"

instantiation up\<^sub>d :: (type)height
begin

fun height_up\<^sub>d :: "'a up\<^sub>d \<Rightarrow> nat" where
"height (T\<^sub>d t) = height t" |
"height (Up\<^sub>d t) = height t + 1"

instance ..

end

lemma bal_tree\<^sub>d_node21:
  "\<lbrakk>bal r; bal (tree\<^sub>d l); height r = height l \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d (node21 l a r))"
by(induct l a r rule: node21.induct) auto

lemma bal_tree\<^sub>d_node22:
  "\<lbrakk>bal(tree\<^sub>d r); bal l; height r = height l \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d (node22 l a r))"
by(induct l a r rule: node22.induct) auto

lemma bal_tree\<^sub>d_node31:
  "\<lbrakk> bal (tree\<^sub>d l); bal m; bal r; height l = height r; height m = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node31 l a m b r))"
by(induct l a m b r rule: node31.induct) auto

lemma bal_tree\<^sub>d_node32:
  "\<lbrakk> bal l; bal (tree\<^sub>d m); bal r; height l = height r; height m = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node32 l a m b r))"
by(induct l a m b r rule: node32.induct) auto

lemma bal_tree\<^sub>d_node33:
  "\<lbrakk> bal l; bal m; bal(tree\<^sub>d r); height l = height r; height m = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node33 l a m b r))"
by(induct l a m b r rule: node33.induct) auto

lemma bal_tree\<^sub>d_node41:
  "\<lbrakk> bal (tree\<^sub>d l); bal m; bal n; bal r; height l = height r; height m = height r; height n = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node41 l a m b n c r))"
by(induct l a m b n c r rule: node41.induct) auto

lemma bal_tree\<^sub>d_node42:
  "\<lbrakk> bal l; bal (tree\<^sub>d m); bal n; bal r; height l = height r; height m = height r; height n = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node42 l a m b n c r))"
by(induct l a m b n c r rule: node42.induct) auto

lemma bal_tree\<^sub>d_node43:
  "\<lbrakk> bal l; bal m; bal (tree\<^sub>d n); bal r; height l = height r; height m = height r; height n = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node43 l a m b n c r))"
by(induct l a m b n c r rule: node43.induct) auto

lemma bal_tree\<^sub>d_node44:
  "\<lbrakk> bal l; bal m; bal n; bal (tree\<^sub>d r); height l = height r; height m = height r; height n = height r \<rbrakk>
  \<Longrightarrow> bal (tree\<^sub>d (node44 l a m b n c r))"
by(induct l a m b n c r rule: node44.induct) auto

lemmas bals = bal_tree\<^sub>d_node21 bal_tree\<^sub>d_node22
  bal_tree\<^sub>d_node31 bal_tree\<^sub>d_node32 bal_tree\<^sub>d_node33
  bal_tree\<^sub>d_node41 bal_tree\<^sub>d_node42 bal_tree\<^sub>d_node43 bal_tree\<^sub>d_node44

lemma height_node21:
   "height r > 0 \<Longrightarrow> height(node21 l a r) = max (height l) (height r) + 1"
by(induct l a r rule: node21.induct)(simp_all add: max.assoc)

lemma height_node22:
   "height l > 0 \<Longrightarrow> height(node22 l a r) = max (height l) (height r) + 1"
by(induct l a r rule: node22.induct)(simp_all add: max.assoc)

lemma height_node31:
  "height m > 0 \<Longrightarrow> height(node31 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node31.induct)(simp_all add: max_def)

lemma height_node32:
  "height r > 0 \<Longrightarrow> height(node32 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node32.induct)(simp_all add: max_def)

lemma height_node33:
  "height m > 0 \<Longrightarrow> height(node33 l a m b r) =
   max (height l) (max (height m) (height r)) + 1"
by(induct l a m b r rule: node33.induct)(simp_all add: max_def)

lemma height_node41:
  "height m > 0 \<Longrightarrow> height(node41 l a m b n c r) =
   max (height l) (max (height m) (max (height n) (height r))) + 1"
by(induct l a m b n c r rule: node41.induct)(simp_all add: max_def)

lemma height_node42:
  "height l > 0 \<Longrightarrow> height(node42 l a m b n c r) =
   max (height l) (max (height m) (max (height n) (height r))) + 1"
by(induct l a m b n c r rule: node42.induct)(simp_all add: max_def)

lemma height_node43:
  "height m > 0 \<Longrightarrow> height(node43 l a m b n c r) =
   max (height l) (max (height m) (max (height n) (height r))) + 1"
by(induct l a m b n c r rule: node43.induct)(simp_all add: max_def)

lemma height_node44:
  "height n > 0 \<Longrightarrow> height(node44 l a m b n c r) =
   max (height l) (max (height m) (max (height n) (height r))) + 1"
by(induct l a m b n c r rule: node44.induct)(simp_all add: max_def)

lemmas heights = height_node21 height_node22
  height_node31 height_node32 height_node33
  height_node41 height_node42 height_node43 height_node44

lemma height_split_min:
  "split_min t = (x, t') \<Longrightarrow> height t > 0 \<Longrightarrow> bal t \<Longrightarrow> height t' = height t"
by(induct t arbitrary: x t' rule: split_min.induct)
  (auto simp: heights split: prod.splits)

lemma height_del: "bal t \<Longrightarrow> height(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp add: heights height_split_min split!: if_split prod.split)

lemma bal_split_min:
  "\<lbrakk> split_min t = (x, t'); bal t; height t > 0 \<rbrakk> \<Longrightarrow> bal (tree\<^sub>d t')"
by(induct t arbitrary: x t' rule: split_min.induct)
  (auto simp: heights height_split_min bals split: prod.splits)

lemma bal_tree\<^sub>d_del: "bal t \<Longrightarrow> bal(tree\<^sub>d(del x t))"
by(induction x t rule: del.induct)
  (auto simp: bals bal_split_min height_del height_split_min split!: if_split prod.split)

corollary bal_delete: "bal t \<Longrightarrow> bal(delete x t)"
by(simp add: delete_def bal_tree\<^sub>d_del)

subsection \<open>Overall Correctness\<close>

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
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
qed (simp add: empty_def)+

end
