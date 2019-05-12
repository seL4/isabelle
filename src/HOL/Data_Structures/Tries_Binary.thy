(* Author: Tobias Nipkow *)

section "Binary Tries and Patricia Tries"

theory Tries_Binary
imports Set_Specs
begin

hide_const (open) insert

declare Let_def[simp]

fun sel2 :: "bool \<Rightarrow> 'a * 'a \<Rightarrow> 'a" where
"sel2 b (a1,a2) = (if b then a2 else a1)"

fun mod2 :: "('a \<Rightarrow> 'a) \<Rightarrow> bool \<Rightarrow> 'a * 'a \<Rightarrow> 'a * 'a" where
"mod2 f b (a1,a2) = (if b then (a1,f a2) else (f a1,a2))"


subsection "Trie"

datatype trie = Lf | Nd bool "trie * trie"

definition empty :: trie where
[simp]: "empty = Lf"

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool" where
"isin Lf ks = False" |
"isin (Nd b lr) ks =
   (case ks of
      [] \<Rightarrow> b |
      k#ks \<Rightarrow> isin (sel2 k lr) ks)"

fun insert :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"insert [] Lf = Nd True (Lf,Lf)" |
"insert [] (Nd b lr) = Nd True lr" |
"insert (k#ks) Lf = Nd False (mod2 (insert ks) k (Lf,Lf))" |
"insert (k#ks) (Nd b lr) = Nd b (mod2 (insert ks) k lr)"

lemma isin_insert: "isin (insert xs t) ys = (xs = ys \<or> isin t ys)"
apply(induction xs t arbitrary: ys rule: insert.induct)
apply (auto split: list.splits if_splits)
done

text \<open>A simple implementation of delete; does not shrink the trie!\<close>

fun delete0 :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"delete0 ks Lf = Lf" |
"delete0 ks (Nd b lr) =
   (case ks of
      [] \<Rightarrow> Nd False lr |
      k#ks' \<Rightarrow> Nd b (mod2 (delete0 ks') k lr))"

lemma isin_delete0: "isin (delete0 as t) bs = (as \<noteq> bs \<and> isin t bs)"
apply(induction as t arbitrary: bs rule: delete0.induct)
apply (auto split: list.splits if_splits)
done

text \<open>Now deletion with shrinking:\<close>

fun node :: "bool \<Rightarrow> trie * trie \<Rightarrow> trie" where
"node b lr = (if \<not> b \<and> lr = (Lf,Lf) then Lf else Nd b lr)"

fun delete :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"delete ks Lf = Lf" |
"delete ks (Nd b lr) =
   (case ks of
      [] \<Rightarrow> node False lr |
      k#ks' \<Rightarrow> node b (mod2 (delete ks') k lr))"

lemma isin_delete: "isin (delete xs t) ys = (xs \<noteq> ys \<and> isin t ys)"
apply(induction xs t arbitrary: ys rule: delete.induct)
 apply simp
apply (auto split: list.splits if_splits)
  apply (metis isin.simps(1))
 apply (metis isin.simps(1))
  done

definition set_trie :: "trie \<Rightarrow> bool list set" where
"set_trie t = {xs. isin t xs}"

lemma set_trie_empty: "set_trie empty = {}"
by(simp add: set_trie_def)

lemma set_trie_isin: "isin t xs = (xs \<in> set_trie t)"
by(simp add: set_trie_def)

lemma set_trie_insert: "set_trie(insert xs t) = set_trie t \<union> {xs}"
by(auto simp add: isin_insert set_trie_def)

lemma set_trie_delete: "set_trie(delete xs t) = set_trie t - {xs}"
by(auto simp add: isin_delete set_trie_def)

interpretation S: Set
where empty = empty and isin = isin and insert = insert and delete = delete
and set = set_trie and invar = "\<lambda>t. True"
proof (standard, goal_cases)
  case 1 show ?case by (rule set_trie_empty)
next
  case 2 show ?case by(rule set_trie_isin)
next
  case 3 thus ?case by(auto simp: set_trie_insert)
next
  case 4 show ?case by(rule set_trie_delete)
qed (rule TrueI)+


subsection "Patricia Trie"

datatype ptrie = LfP | NdP "bool list" bool "ptrie * ptrie"

fun isinP :: "ptrie \<Rightarrow> bool list \<Rightarrow> bool" where
"isinP LfP ks = False" |
"isinP (NdP ps b lr) ks =
  (let n = length ps in
   if ps = take n ks
   then case drop n ks of [] \<Rightarrow> b | k#ks' \<Rightarrow> isinP (sel2 k lr) ks'
   else False)"

fun split where
"split [] ys = ([],[],ys)" |
"split xs [] = ([],xs,[])" |
"split (x#xs) (y#ys) =
  (if x\<noteq>y then ([],x#xs,y#ys)
   else let (ps,xs',ys') = split xs ys in (x#ps,xs',ys'))"


lemma mod2_cong[fundef_cong]:
  "\<lbrakk> lr = lr'; k = k'; \<And>a b. lr'=(a,b) \<Longrightarrow> f (a) = f' (a) ; \<And>a b. lr'=(a,b) \<Longrightarrow> f (b) = f' (b) \<rbrakk>
  \<Longrightarrow> mod2 f k lr= mod2 f' k' lr'"
by(cases lr, cases lr', auto)

fun insertP :: "bool list \<Rightarrow> ptrie \<Rightarrow> ptrie" where
"insertP ks LfP  = NdP ks True (LfP,LfP)" |
"insertP ks (NdP ps b lr) =
  (case split ks ps of
     (qs,k#ks',p#ps') \<Rightarrow>
       let tp = NdP ps' b lr; tk = NdP ks' True (LfP,LfP) in
       NdP qs False (if k then (tp,tk) else (tk,tp)) |
     (qs,k#ks',[]) \<Rightarrow>
       NdP ps b (mod2 (insertP ks') k lr) |
     (qs,[],p#ps') \<Rightarrow>
       let t = NdP ps' b lr in
       NdP qs True (if p then (LfP,t) else (t,LfP)) |
     (qs,[],[]) \<Rightarrow> NdP ps True lr)"


fun nodeP :: "bool list \<Rightarrow> bool \<Rightarrow> ptrie * ptrie \<Rightarrow> ptrie" where
"nodeP ps b lr = (if \<not> b \<and> lr = (LfP,LfP) then LfP else NdP ps b lr)"

fun deleteP :: "bool list \<Rightarrow> ptrie \<Rightarrow> ptrie" where
"deleteP ks LfP  = LfP" |
"deleteP ks (NdP ps b lr) =
  (case split ks ps of
     (qs,ks',p#ps') \<Rightarrow> NdP ps b lr |
     (qs,k#ks',[]) \<Rightarrow> nodeP ps b (mod2 (deleteP ks') k lr) |
     (qs,[],[]) \<Rightarrow> nodeP ps False lr)"


subsubsection \<open>Functional Correctness\<close>

text \<open>First step: @{typ ptrie} implements @{typ trie} via the abstraction function \<open>abs_ptrie\<close>:\<close>

fun prefix_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"prefix_trie [] t = t" |
"prefix_trie (k#ks) t =
  (let t' = prefix_trie ks t in Nd False (if k then (Lf,t') else (t',Lf)))"

fun abs_ptrie :: "ptrie \<Rightarrow> trie" where
"abs_ptrie LfP = Lf" |
"abs_ptrie (NdP ps b (l,r)) = prefix_trie ps (Nd b (abs_ptrie l, abs_ptrie r))"


text \<open>Correctness of @{const isinP}:\<close>

lemma isin_prefix_trie:
  "isin (prefix_trie ps t) ks
   = (ps = take (length ps) ks \<and> isin t (drop (length ps) ks))"
apply(induction ps arbitrary: ks)
apply(auto split: list.split)
done

lemma isinP:
  "isinP t ks = isin (abs_ptrie t) ks"
apply(induction t arbitrary: ks rule: abs_ptrie.induct)
 apply(auto simp: isin_prefix_trie split: list.split)
done


text \<open>Correctness of @{const insertP}:\<close>

lemma prefix_trie_Lfs: "prefix_trie ks (Nd True (Lf,Lf)) = insert ks Lf"
apply(induction ks)
apply auto
done

lemma insert_prefix_trie_same:
  "insert ps (prefix_trie ps (Nd b lr)) = prefix_trie ps (Nd True lr)"
apply(induction ps)
apply auto
done

lemma insert_append: "insert (ks @ ks') (prefix_trie ks t) = prefix_trie ks (insert ks' t)"
apply(induction ks)
apply auto
done

lemma prefix_trie_append: "prefix_trie (ps @ qs) t = prefix_trie ps (prefix_trie qs t)"
apply(induction ps)
apply auto
done

lemma split_if: "split ks ps = (qs, ks', ps') \<Longrightarrow>
  ks = qs @ ks' \<and> ps = qs @ ps' \<and> (ks' \<noteq> [] \<and> ps' \<noteq> [] \<longrightarrow> hd ks' \<noteq> hd ps')"
apply(induction ks ps arbitrary: qs ks' ps' rule: split.induct)
apply(auto split: prod.splits if_splits)
done

lemma abs_ptrie_insertP:
  "abs_ptrie (insertP ks t) = insert ks (abs_ptrie t)"
apply(induction t arbitrary: ks)
apply(auto simp: prefix_trie_Lfs insert_prefix_trie_same insert_append prefix_trie_append
           dest!: split_if split: list.split prod.split if_splits)
done


text \<open>Correctness of @{const deleteP}:\<close>

lemma prefix_trie_Lf: "prefix_trie xs t = Lf \<longleftrightarrow> xs = [] \<and> t = Lf"
by(cases xs)(auto)

lemma abs_ptrie_Lf: "abs_ptrie t = Lf \<longleftrightarrow> t = LfP"
by(cases t) (auto simp: prefix_trie_Lf)

lemma delete_prefix_trie:
  "delete xs (prefix_trie xs (Nd b (l,r)))
   = (if (l,r) = (Lf,Lf) then Lf else prefix_trie xs (Nd False (l,r)))"
by(induction xs)(auto simp: prefix_trie_Lf)

lemma delete_append_prefix_trie:
  "delete (xs @ ys) (prefix_trie xs t)
   = (if delete ys t = Lf then Lf else prefix_trie xs (delete ys t))"
by(induction xs)(auto simp: prefix_trie_Lf)

lemma delete_abs_ptrie:
  "delete ks (abs_ptrie t) = abs_ptrie (deleteP ks t)"
apply(induction t arbitrary: ks)
apply(auto simp: delete_prefix_trie delete_append_prefix_trie
        prefix_trie_append prefix_trie_Lf abs_ptrie_Lf
        dest!: split_if split: if_splits list.split prod.split)
done


text \<open>The overall correctness proof. Simply composes correctness lemmas.\<close>

definition set_ptrie :: "ptrie \<Rightarrow> bool list set" where
"set_ptrie = set_trie o abs_ptrie"

lemma set_ptrie_insertP: "set_ptrie (insertP xs t) = set_ptrie t \<union> {xs}"
by(simp add: abs_ptrie_insertP set_trie_insert set_ptrie_def)

interpretation SP: Set
where empty = LfP and isin = isinP and insert = insertP and delete = deleteP
and set = set_ptrie and invar = "\<lambda>t. True"
proof (standard, goal_cases)
  case 1 show ?case by (simp add: set_ptrie_def set_trie_def)
next
  case 2 thus ?case by(simp add: isinP set_ptrie_def set_trie_def)
next
  case 3 thus ?case by (auto simp: set_ptrie_insertP)
next
  case 4 thus ?case
    by(auto simp: isin_delete set_ptrie_def set_trie_def simp flip: delete_abs_ptrie)
qed (rule TrueI)+

end
