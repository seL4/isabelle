section \<open>Tries via Functions\<close>

theory Trie_Fun
imports
  Set_Specs
begin

text \<open>A trie where each node maps a key to sub-tries via a function.
Nice abstract model. Not efficient because of the function space.\<close>

datatype 'a trie = Nd bool "'a \<Rightarrow> 'a trie option"

definition empty :: "'a trie" where
[simp]: "empty = Nd False (\<lambda>_. None)"

fun isin :: "'a trie \<Rightarrow> 'a list \<Rightarrow> bool" where
"isin (Nd b m) [] = b" |
"isin (Nd b m) (k # xs) = (case m k of None \<Rightarrow> False | Some t \<Rightarrow> isin t xs)"

fun insert :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
"insert [] (Nd b m) = Nd True m" |
"insert (x#xs) (Nd b m) =
   (let s = (case m x of None \<Rightarrow> empty | Some t \<Rightarrow> t) in Nd b (m(x := Some(insert xs s))))"

fun delete :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
"delete [] (Nd b m) = Nd False m" |
"delete (x#xs) (Nd b m) = Nd b
   (case m x of
      None \<Rightarrow> m |
      Some t \<Rightarrow> m(x := Some(delete xs t)))"

text \<open>Use (a tuned version of) @{const isin} as an abstraction function:\<close>

lemma isin_case: "isin (Nd b m) xs =
  (case xs of
   [] \<Rightarrow> b |
   x # ys \<Rightarrow> (case m x of None \<Rightarrow> False | Some t \<Rightarrow> isin t ys))"
by(cases xs)auto

definition set :: "'a trie \<Rightarrow> 'a list set" where
[simp]: "set t = {xs. isin t xs}"

lemma isin_set: "isin t xs = (xs \<in> set t)"
by simp

lemma set_insert: "set (insert xs t) = set t \<union> {xs}"
by (induction xs t rule: insert.induct)
   (auto simp: isin_case split!: if_splits option.splits list.splits)

lemma set_delete: "set (delete xs t) = set t - {xs}"
by (induction xs t rule: delete.induct)
   (auto simp: isin_case split!: if_splits option.splits list.splits)

interpretation S: Set
where empty = empty and isin = isin and insert = insert and delete = delete
and set = set and invar = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by (simp add: isin_case split: list.split)
next
  case 2 show ?case by(rule isin_set)
next
  case 3 show ?case by(rule set_insert)
next
  case 4 show ?case by(rule set_delete)
qed (rule TrueI)+

end
