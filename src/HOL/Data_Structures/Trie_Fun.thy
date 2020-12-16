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
   Nd b (m(x := Some(insert xs (case m x of None \<Rightarrow> empty | Some t \<Rightarrow> t))))"

fun delete :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
"delete [] (Nd b m) = Nd False m" |
"delete (x#xs) (Nd b m) = Nd b
   (case m x of
      None \<Rightarrow> m |
      Some t \<Rightarrow> m(x := Some(delete xs t)))"

text \<open>The actual definition of \<open>set\<close> is a bit cryptic but canonical, to enable
primrec to prove termination:\<close>

primrec set :: "'a trie \<Rightarrow> 'a list set" where
"set (Nd b m) = (if b then {[]} else {}) \<union>
    (\<Union>a. case (map_option set o m) a of None \<Rightarrow> {} | Some t \<Rightarrow> (#) a ` t)"

text \<open>This is the more human-readable version:\<close>

lemma set_Nd:
  "set (Nd b m) =
     (if b then {[]} else {}) \<union>
     (\<Union>a. case m a of None \<Rightarrow> {} | Some t \<Rightarrow> (#) a ` set t)"
by (auto simp: split: option.splits)

lemma isin_set: "isin t xs = (xs \<in> set t)"
apply(induction t xs rule: isin.induct)
apply (auto split: option.split)
done

lemma set_insert: "set (insert xs t) = set t \<union> {xs}"
proof(induction xs t rule: insert.induct)
  case 1 thus ?case by simp
next
  case 2
  thus ?case
    apply(simp)
    apply(subst set_eq_iff)
    apply(auto split!: if_splits option.splits)
     apply fastforce
    by (metis imageI option.sel)
qed

lemma set_delete: "set (delete xs t) = set t - {xs}"
proof(induction xs t rule: delete.induct)
  case 1 thus ?case by (force split: option.splits)
next
  case 2
  show ?case
    apply (auto simp add: image_iff 2 split!: if_splits option.splits)
     apply (metis DiffI empty_iff insert_iff option.inject)
     apply (metis DiffI empty_iff insert_iff option.inject)
    done
qed

interpretation S: Set
where empty = empty and isin = isin and insert = insert and delete = delete
and set = set and invar = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: set_insert)
next
  case 4 thus ?case by(simp add: set_delete)
qed (rule TrueI)+

end
