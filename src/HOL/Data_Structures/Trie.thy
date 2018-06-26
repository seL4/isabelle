(* Author: Tobias Nipkow *)

section \<open>Trie and Patricia Trie Implementations of \mbox{\<open>bool list set\<close>}\<close>

theory Trie
imports Set_Specs
begin

hide_const (open) insert

declare Let_def[simp]


subsection "Trie"

datatype trie = Leaf | Node bool "trie * trie"

text \<open>The pairing allows things like \<open>Node b (if \<dots> then (l,r) else (r,l))\<close>.\<close>

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool" where
"isin Leaf ks = False" |
"isin (Node b (l,r)) ks =
   (case ks of
      [] \<Rightarrow> b |
      k#ks \<Rightarrow> isin (if k then r else l) ks)"

fun insert :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"insert [] Leaf = Node True (Leaf,Leaf)" |
"insert [] (Node b lr) = Node True lr" |
"insert (k#ks) Leaf =
  Node False (if k then (Leaf, insert ks Leaf)
                   else (insert ks Leaf, Leaf))" |
"insert (k#ks) (Node b (l,r)) =
  Node b (if k then (l, insert ks r)
               else (insert ks l, r))"

fun shrink_Node :: "bool \<Rightarrow> trie * trie \<Rightarrow> trie" where
"shrink_Node b lr = (if \<not> b \<and> lr = (Leaf,Leaf) then Leaf else Node b lr)"

fun delete :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"delete ks Leaf = Leaf" |
"delete ks (Node b (l,r)) =
   (case ks of
      [] \<Rightarrow> shrink_Node False (l,r) |
      k#ks' \<Rightarrow> shrink_Node b (if k then (l, delete ks' r) else (delete ks' l, r)))"

fun invar :: "trie \<Rightarrow> bool" where
"invar Leaf = True" |
"invar (Node b (l,r)) = ((\<not> b \<longrightarrow> l \<noteq> Leaf \<or> r \<noteq> Leaf) \<and> invar l \<and> invar r)"


subsubsection \<open>Functional Correctness\<close>

lemma isin_insert: "isin (insert as t) bs = (as = bs \<or> isin t bs)"
apply(induction as t arbitrary: bs rule: insert.induct)
apply(auto split: list.splits)
done

lemma isin_delete: "isin (delete as t) bs = (as \<noteq> bs \<and> isin t bs)"
apply(induction as t arbitrary: bs rule: delete.induct)
 apply simp
apply (auto split: list.splits; fastforce)
done

lemma insert_not_Leaf: "insert ks t \<noteq> Leaf"
by(cases "(ks,t)" rule: insert.cases) auto

lemma invar_insert: "invar t \<Longrightarrow> invar (insert ks t)"
by(induction ks t rule: insert.induct)(auto simp: insert_not_Leaf)

lemma invar_delete: "invar t \<Longrightarrow> invar (delete ks t)"
by(induction ks t rule: delete.induct)(auto split: list.split)

interpretation T: Set
where empty = Leaf and insert = insert and delete = delete and isin = isin
and set = "\<lambda>t. {x. isin t x}" and invar = invar
proof (standard, goal_cases)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case 3 thus ?case by (auto simp add: isin_insert)
next
  case 4 thus ?case by (auto simp add: isin_delete)
next
  case 5 thus ?case by simp
next
  case 6 thus ?case by (auto simp add: invar_insert)
next
  case 7 thus ?case by (auto simp add: invar_delete)
qed


subsection "Patricia Trie"

datatype trieP = LeafP | NodeP "bool list" bool "trieP * trieP"

fun isinP :: "trieP \<Rightarrow> bool list \<Rightarrow> bool" where
"isinP LeafP ks = False" |
"isinP (NodeP ps b (l,r)) ks =
  (let n = length ps in
   if ps = take n ks
   then case drop n ks of [] \<Rightarrow> b | k#ks' \<Rightarrow> isinP (if k then r else l) ks'
   else False)"

text \<open>\<open>split xs ys = (zs, xs', ys')\<close> iff
  \<open>zs\<close> is the longest common prefix of \<open>xs\<close> and \<open>ys\<close> and
  \<open>xs = zs @ xs'\<close> and \<open>ys = zs @ ys'\<close>\<close>
fun split where
"split [] ys = ([],[],ys)" |
"split xs [] = ([],xs,[])" |
"split (x#xs) (y#ys) =
  (if x\<noteq>y then ([],x#xs,y#ys)
   else let (ps,xs',ys') = split xs ys in (x#ps,xs',ys'))"

fun insertP :: "bool list \<Rightarrow> trieP \<Rightarrow> trieP" where
"insertP ks LeafP  = NodeP ks True (LeafP,LeafP)" |
"insertP ks (NodeP ps b (l,r)) =
  (case split ks ps of
     (qs,k#ks',p#ps') \<Rightarrow>
       let tp = NodeP ps' b (l,r); tk = NodeP ks' True (LeafP,LeafP)
       in NodeP qs False (if k then (tp,tk) else (tk,tp)) |
     (qs,k#ks',[]) \<Rightarrow>
       NodeP ps b (if k then (l,insertP ks' r) else (insertP ks' l, r)) |
     (qs,[],p#ps') \<Rightarrow>
       let t = NodeP ps' b (l,r)
       in NodeP qs True (if p then (LeafP, t) else (t, LeafP)) |
     (qs,[],[]) \<Rightarrow> NodeP ps True (l,r))"

fun shrink_NodeP where
"shrink_NodeP ps b lr = (if b then NodeP ps b lr else
  case lr of
     (LeafP, LeafP) \<Rightarrow> LeafP |
     (LeafP, NodeP ps' b' lr') \<Rightarrow> NodeP (ps @ True # ps') b' lr' |
     (NodeP ps' b' lr', LeafP) \<Rightarrow> NodeP (ps @ False # ps') b' lr' |
     _ \<Rightarrow> NodeP ps b lr)"

fun deleteP :: "bool list \<Rightarrow> trieP \<Rightarrow> trieP" where
"deleteP ks LeafP  = LeafP" |
"deleteP ks (NodeP ps b (l,r)) =
  (case split ks ps of
     (qs,_,p#ps') \<Rightarrow> NodeP ps b (l,r) |
     (qs,k#ks',[]) \<Rightarrow>
       shrink_NodeP ps b (if k then (l, deleteP ks' r) else (deleteP ks' l, r)) |
     (qs,[],[]) \<Rightarrow> shrink_NodeP ps False (l,r))"

fun invarP :: "trieP \<Rightarrow> bool" where
"invarP LeafP = True" |
"invarP (NodeP ps b (l,r)) = ((\<not>b \<longrightarrow> l \<noteq> LeafP \<or> r \<noteq> LeafP) \<and> invarP l \<and> invarP r)"

text \<open>The abstraction function(s):\<close>

fun prefix_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"prefix_trie [] t = t" |
"prefix_trie (k#ks) t =
  (let t' = prefix_trie ks t in shrink_Node False (if k then (Leaf,t') else (t',Leaf)))"

fun abs_trieP :: "trieP \<Rightarrow> trie" where
"abs_trieP LeafP = Leaf" |
"abs_trieP (NodeP ps b (l,r)) = prefix_trie ps (Node b (abs_trieP l, abs_trieP r))"


subsubsection \<open>Functional Correctness\<close>

text \<open>IsinP:\<close>

lemma isin_prefix_trie: "isin (prefix_trie ps t) ks =
  (length ks \<ge> length ps \<and>
  (let n = length ps in ps = take n ks \<and> isin t (drop n ks)))"
by(induction ps arbitrary: ks)(auto split: list.split)

lemma isinP: "isinP t ks = isin (abs_trieP t) ks"
apply(induction t arbitrary: ks rule: abs_trieP.induct)
 apply(auto simp: isin_prefix_trie split: list.split)
 using nat_le_linear apply force
using nat_le_linear apply force
done

text \<open>Insert:\<close>

lemma prefix_trie_Leaf_iff: "prefix_trie ps t = Leaf \<longleftrightarrow> t = Leaf"
by (induction ps) auto

lemma prefix_trie_Leafs: "prefix_trie ks (Node True (Leaf,Leaf)) = insert ks Leaf"
by(induction ks) (auto simp: prefix_trie_Leaf_iff)

lemma prefix_trie_Leaf: "prefix_trie ps Leaf = Leaf"
by(induction ps) auto

lemma insert_append: "insert (ks @ ks') (prefix_trie ks t) = prefix_trie ks (insert ks' t)"
by(induction ks) (auto simp: prefix_trie_Leaf_iff insert_not_Leaf prefix_trie_Leaf)

lemma prefix_trie_append: "prefix_trie (ps @ qs) t = prefix_trie ps (prefix_trie qs t)"
by(induction ps) auto

lemma split_iff: "split xs ys = (zs, xs', ys') \<longleftrightarrow>
  xs = zs @ xs' \<and> ys = zs @ ys' \<and> (xs' \<noteq> [] \<and> ys' \<noteq> [] \<longrightarrow> hd xs' \<noteq> hd ys')"
proof(induction xs ys arbitrary: zs xs' ys' rule: split.induct)
  case 1 thus ?case by auto
next
  case 2 thus ?case by auto
next
  case 3 thus ?case by(clarsimp simp: Cons_eq_append_conv split: prod.splits if_splits) auto
qed

lemma abs_trieP_insertP:
  "abs_trieP (insertP ks t) = insert ks (abs_trieP t)"
apply(induction t arbitrary: ks)
apply(auto simp: prefix_trie_Leafs insert_append prefix_trie_append
        prefix_trie_Leaf_iff split_iff split: list.split prod.split)
done

corollary isinP_insertP: "isinP (insertP ks t) ks' = (ks=ks' \<or> isinP t ks')"
by (simp add: isin_insert isinP abs_trieP_insertP)

lemma insertP_not_LeafP: "insertP ks t \<noteq> LeafP"
apply(induction ks t rule: insertP.induct)
apply(auto split: prod.split list.split)
done

lemma invarP_insertP: "invarP t \<Longrightarrow> invarP (insertP ks t)"
apply(induction ks t rule: insertP.induct)
apply(auto simp: insertP_not_LeafP split: prod.split list.split)
done

text \<open>Delete:\<close>

lemma invar_shrink_NodeP: "\<lbrakk> invarP l; invarP r \<rbrakk> \<Longrightarrow> invarP (shrink_NodeP ps b (l,r))"
by(auto split: trieP.split)

lemma invarP_deleteP: "invarP t \<Longrightarrow> invarP (deleteP ks t)"
apply(induction t arbitrary: ks)
apply(auto simp: invar_shrink_NodeP split_iff simp del: shrink_NodeP.simps
           split!: list.splits prod.split if_splits)
done

lemma delete_append:
  "delete (ks @ ks') (prefix_trie ks t) = prefix_trie ks (delete ks' t)"
by(induction ks) auto

lemma abs_trieP_shrink_NodeP:
  "abs_trieP (shrink_NodeP ps b (l,r)) = prefix_trie ps (shrink_Node b (abs_trieP l, abs_trieP r))"
apply(induction ps arbitrary: b l r)
apply (auto simp: prefix_trie_Leaf prefix_trie_Leaf_iff prefix_trie_append
            split!: trieP.splits if_splits)
done

lemma abs_trieP_deleteP:
  "abs_trieP (deleteP ks t) = delete ks (abs_trieP t)"
apply(induction t arbitrary: ks)
apply(auto simp: prefix_trie_Leafs delete_append prefix_trie_Leaf
                 abs_trieP_shrink_NodeP prefix_trie_append split_iff
           simp del: shrink_NodeP.simps split!: list.split prod.split if_splits)
done

corollary isinP_deleteP: "isinP (deleteP ks t) ks' = (ks\<noteq>ks' \<and> isinP t ks')"
by (simp add: isin_delete isinP abs_trieP_deleteP)

interpretation PT: Set
where empty = LeafP and insert = insertP and delete = deleteP
and isin = isinP and set = "\<lambda>t. {x. isinP t x}" and invar = invarP
proof (standard, goal_cases)
  case 1 thus ?case by (simp)
next
  case 2 thus ?case by (simp)
next
  case 3 thus ?case by (auto simp add: isinP_insertP)
next
  case 4 thus ?case by (auto simp add: isinP_deleteP)
next
  case 5 thus ?case by (simp)
next
  case 6 thus ?case by (simp add: invarP_insertP)
next
  case 7 thus ?case by (auto simp add: invarP_deleteP)
qed

end
