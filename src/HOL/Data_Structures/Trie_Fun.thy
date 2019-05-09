section \<open>Tries via Functions\<close>

theory Trie_Fun
imports
  Set_Specs
begin

text \<open>A trie where each node maps a key to sub-tries via a function.
Nice abstract model. Not efficient because of the function space.\<close>

datatype 'a trie = Lf | Nd bool "'a \<Rightarrow> 'a trie option"

fun isin :: "'a trie \<Rightarrow> 'a list \<Rightarrow> bool" where
"isin Lf xs = False" |
"isin (Nd b m) [] = b" |
"isin (Nd b m) (k # xs) = (case m k of None \<Rightarrow> False | Some t \<Rightarrow> isin t xs)"

fun insert :: "('a::linorder) list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
"insert [] Lf = Nd True (\<lambda>x. None)" |
"insert [] (Nd b m) = Nd True m" |
"insert (x#xs) Lf = Nd False ((\<lambda>x. None)(x := Some(insert xs Lf)))" |
"insert (x#xs) (Nd b m) =
   Nd b (m(x := Some(insert xs (case m x of None \<Rightarrow> Lf | Some t \<Rightarrow> t))))"

fun delete :: "('a::linorder) list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
"delete xs Lf = Lf" |
"delete [] (Nd b m) = Nd False m" |
"delete (x#xs) (Nd b m) = Nd b
   (case m x of
      None \<Rightarrow> m |
      Some t \<Rightarrow> m(x := Some(delete xs t)))"

primrec set :: "'a trie \<Rightarrow> 'a list set" where
"set Lf = {}" |
"set (Nd b m) = (if b then {[]} else {}) \<union>
    (\<Union>a. case (map_option set o m) a of None \<Rightarrow> {} | Some t \<Rightarrow> (#) a ` t)"

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
  case 2 thus ?case by simp
next
  case 3 thus ?case by simp (subst set_eq_iff, simp)
next
  case 4
  thus ?case
    apply(simp)
    apply(subst set_eq_iff)
    apply(auto split!: if_splits option.splits)
     apply fastforce
    by (metis imageI option.sel)
qed

lemma set_delete: "set (delete xs t) = set t - {xs}"
proof(induction xs t rule: delete.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by (force split: option.splits)
next
  case 3
  thus ?case
    apply (auto simp add: image_iff split!: if_splits option.splits)
       apply blast
      apply (metis insertE insertI2 insert_Diff_single option.inject)
     apply blast
    by (metis insertE insertI2 insert_Diff_single option.inject)
qed

interpretation S: Set
where empty = Lf and isin = isin and insert = insert and delete = delete
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
