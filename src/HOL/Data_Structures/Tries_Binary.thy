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
proof (induction xs t arbitrary: ys rule: insert.induct)
qed (auto split: list.splits if_splits)

text \<open>A simple implementation of delete; does not shrink the trie!\<close>

fun delete0 :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
  "delete0 ks Lf = Lf" |
  "delete0 ks (Nd b lr) =
   (case ks of
      [] \<Rightarrow> Nd False lr |
      k#ks' \<Rightarrow> Nd b (mod2 (delete0 ks') k lr))"

lemma isin_delete0: "isin (delete0 as t) bs = (as \<noteq> bs \<and> isin t bs)"
proof (induction as t arbitrary: bs rule: delete0.induct)
qed (auto split: list.splits if_splits)

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
   apply (auto split: list.splits if_splits)
   apply (metis isin.simps(1))+
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

text \<open>Invariant: tries are fully shrunk:\<close>
fun invar where
  "invar Lf = True" |
  "invar (Nd b (l,r)) = (invar l \<and> invar r \<and> (l = Lf \<and> r = Lf \<longrightarrow> b))"

lemma insert_Lf: "insert xs t \<noteq> Lf"
  using insert.elims by blast

lemma invar_insert: "invar t \<Longrightarrow> invar(insert xs t)"
proof(induction xs t rule: insert.induct)
  case 1 thus ?case by simp
next
  case (2 b lr)
  thus ?case by(cases lr; simp)
next
  case (3 k ks)
  thus ?case by(simp; cases ks; auto)
next
  case (4 k ks b lr)
  then show ?case by(cases lr; auto simp: insert_Lf)
qed

lemma invar_delete: "invar t \<Longrightarrow> invar(delete xs t)"
proof(induction t arbitrary: xs)
  case Lf thus ?case by simp
next
  case (Nd b lr)
  thus ?case by(cases lr)(auto split: list.split)
qed

interpretation S: Set
  where empty = empty and isin = isin and insert = insert and delete = delete
    and set = set_trie and invar = invar
  unfolding Set_def
  by (smt (verit, best) Tries_Binary.empty_def invar.simps(1) invar_delete invar_insert set_trie_delete set_trie_empty set_trie_insert set_trie_isin)


subsection "Patricia Trie"

datatype trieP = LfP | NdP "bool list" bool "trieP * trieP"

text \<open>Fully shrunk:\<close>
fun invarP where
  "invarP LfP = True" |
  "invarP (NdP ps b (l,r)) = (invarP l \<and> invarP r \<and> (l = LfP \<or> r = LfP \<longrightarrow> b))"

fun isinP :: "trieP \<Rightarrow> bool list \<Rightarrow> bool" where
  "isinP LfP ks = False" |
  "isinP (NdP ps b lr) ks =
  (let n = length ps in
   if ps = take n ks
   then case drop n ks of [] \<Rightarrow> b | k#ks' \<Rightarrow> isinP (sel2 k lr) ks'
   else False)"

definition emptyP :: trieP where
  [simp]: "emptyP = LfP"

fun lcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "lcp [] ys = ([],[],ys)" |
  "lcp xs [] = ([],xs,[])" |
  "lcp (x#xs) (y#ys) =
  (if x\<noteq>y then ([],x#xs,y#ys)
   else let (ps,xs',ys') = lcp xs ys in (x#ps,xs',ys'))"


lemma mod2_cong[fundef_cong]:
  "\<lbrakk> lr = lr'; k = k'; \<And>a b. lr'=(a,b) \<Longrightarrow> f (a) = f' (a) ; \<And>a b. lr'=(a,b) \<Longrightarrow> f (b) = f' (b) \<rbrakk>
  \<Longrightarrow> mod2 f k lr= mod2 f' k' lr'"
  by(cases lr, cases lr', auto)


fun insertP :: "bool list \<Rightarrow> trieP \<Rightarrow> trieP" where
  "insertP ks LfP  = NdP ks True (LfP,LfP)" |
  "insertP ks (NdP ps b lr) =
  (case lcp ks ps of
     (qs, k#ks', p#ps') \<Rightarrow>
       let tp = NdP ps' b lr; tk = NdP ks' True (LfP,LfP) in
       NdP qs False (if k then (tp,tk) else (tk,tp)) |
     (qs, k#ks', []) \<Rightarrow>
       NdP ps b (mod2 (insertP ks') k lr) |
     (qs, [], p#ps') \<Rightarrow>
       let t = NdP ps' b lr in
       NdP qs True (if p then (LfP,t) else (t,LfP)) |
     (qs,[],[]) \<Rightarrow> NdP ps True lr)"


text \<open>Smart constructor that shrinks:\<close>
definition nodeP :: "bool list \<Rightarrow> bool \<Rightarrow> trieP * trieP \<Rightarrow> trieP" where
  "nodeP ps b lr =
 (if b then  NdP ps b lr
  else case lr of
   (LfP,LfP) \<Rightarrow> LfP |
   (LfP, NdP ks b lr) \<Rightarrow> NdP (ps @ True # ks) b lr |
   (NdP ks b lr, LfP) \<Rightarrow> NdP (ps @ False # ks) b lr |
   _ \<Rightarrow> NdP ps b lr)"

fun deleteP :: "bool list \<Rightarrow> trieP \<Rightarrow> trieP" where
  "deleteP ks LfP  = LfP" |
  "deleteP ks (NdP ps b lr) =
  (case lcp ks ps of
     (_, _, _#_) \<Rightarrow> NdP ps b lr |
     (_, k#ks', []) \<Rightarrow> nodeP ps b (mod2 (deleteP ks') k lr) |
     (_, [], []) \<Rightarrow> nodeP ps False lr)"



subsubsection \<open>Functional Correctness\<close>

text \<open>First step: @{typ trieP} implements @{typ trie} via the abstraction function \<open>abs_trieP\<close>:\<close>

fun prefix_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
  "prefix_trie [] t = t" |
  "prefix_trie (k#ks) t =
  (let t' = prefix_trie ks t in Nd False (if k then (Lf,t') else (t',Lf)))"

fun abs_trieP :: "trieP \<Rightarrow> trie" where
  "abs_trieP LfP = Lf" |
  "abs_trieP (NdP ps b (l,r)) = prefix_trie ps (Nd b (abs_trieP l, abs_trieP r))"


text \<open>Correctness of @{const isinP}:\<close>

lemma isin_prefix_trie:
  "isin (prefix_trie ps t) ks
   = (ps = take (length ps) ks \<and> isin t (drop (length ps) ks))"
  by (induction ps arbitrary: ks) (auto split: list.split)

lemma abs_trieP_isinP:
  "isinP t ks = isin (abs_trieP t) ks"
proof (induction t arbitrary: ks rule: abs_trieP.induct)
qed (auto simp: isin_prefix_trie split: list.split)


text \<open>Correctness of @{const insertP}:\<close>

lemma prefix_trie_Lfs: "prefix_trie ks (Nd True (Lf,Lf)) = insert ks Lf"
  by (induction ks) auto

lemma insert_prefix_trie_same:
  "insert ps (prefix_trie ps (Nd b lr)) = prefix_trie ps (Nd True lr)"
  by (induction ps) auto

lemma insert_append: "insert (ks @ ks') (prefix_trie ks t) = prefix_trie ks (insert ks' t)"
  by (induction ks) auto

lemma prefix_trie_append: "prefix_trie (ps @ qs) t = prefix_trie ps (prefix_trie qs t)"
  by (induction ps) auto

lemma lcp_if: "lcp ks ps = (qs, ks', ps') \<Longrightarrow>
  ks = qs @ ks' \<and> ps = qs @ ps' \<and> (ks' \<noteq> [] \<and> ps' \<noteq> [] \<longrightarrow> hd ks' \<noteq> hd ps')"
proof (induction ks ps arbitrary: qs ks' ps' rule: lcp.induct)
qed (auto split: prod.splits if_splits)

lemma abs_trieP_insertP:
  "abs_trieP (insertP ks t) = insert ks (abs_trieP t)"
proof (induction t arbitrary: ks)
qed (auto simp: prefix_trie_Lfs insert_prefix_trie_same insert_append prefix_trie_append
    dest!: lcp_if split: list.split prod.split if_splits)


text \<open>Correctness of @{const deleteP}:\<close>

lemma prefix_trie_Lf: "prefix_trie xs t = Lf \<longleftrightarrow> xs = [] \<and> t = Lf"
  by(cases xs)(auto)

lemma abs_trieP_Lf: "abs_trieP t = Lf \<longleftrightarrow> t = LfP"
  by(cases t) (auto simp: prefix_trie_Lf)

lemma delete_prefix_trie:
  "delete xs (prefix_trie xs (Nd b (l,r)))
   = (if (l,r) = (Lf,Lf) then Lf else prefix_trie xs (Nd False (l,r)))"
  by(induction xs)(auto simp: prefix_trie_Lf)

lemma delete_append_prefix_trie:
  "delete (xs @ ys) (prefix_trie xs t)
   = (if delete ys t = Lf then Lf else prefix_trie xs (delete ys t))"
  by(induction xs)(auto simp: prefix_trie_Lf)

lemma nodeP_LfP2: "nodeP xs False (LfP, LfP) = LfP"
  by(simp add: nodeP_def)

text \<open>Some non-inductive aux. lemmas:\<close>

lemma abs_trieP_nodeP: "a\<noteq>LfP \<or> b \<noteq> LfP \<Longrightarrow>
  abs_trieP (nodeP xs f (a, b)) = prefix_trie xs (Nd f (abs_trieP a, abs_trieP b))"
  by(auto simp add: nodeP_def prefix_trie_append split: trieP.split)

lemma nodeP_True: "nodeP ps True lr = NdP ps True lr"
  by(simp add: nodeP_def)

lemma delete_abs_trieP:
  "delete ks (abs_trieP t) = abs_trieP (deleteP ks t)"
proof (induction t arbitrary: ks)
qed (auto simp: delete_prefix_trie delete_append_prefix_trie
    prefix_trie_append prefix_trie_Lf abs_trieP_Lf nodeP_LfP2 abs_trieP_nodeP nodeP_True
    dest!: lcp_if split: if_splits list.split prod.split)

text \<open>Invariant preservation:\<close>

lemma insertP_LfP: "insertP xs t \<noteq> LfP"
  by(cases t)(auto split: prod.split list.split)

lemma invarP_insertP: "invarP t \<Longrightarrow> invarP(insertP xs t)"
proof(induction t arbitrary: xs)
  case LfP thus ?case by simp
next
  case (NdP bs b lr)
  then show ?case
    by(cases lr)(auto simp: insertP_LfP split: prod.split list.split)
qed

(* Inlining this proof leads to nontermination *)
lemma invarP_nodeP: "\<lbrakk> invarP t1; invarP t2\<rbrakk> \<Longrightarrow> invarP (nodeP xs b (t1, t2))"
  by (auto simp add: nodeP_def split: trieP.split)

lemma invarP_deleteP: "invarP t \<Longrightarrow> invarP(deleteP xs t)"
proof(induction t arbitrary: xs)
  case LfP thus ?case by simp
next
  case (NdP ks b lr)
  thus ?case by(cases lr)(auto simp: invarP_nodeP split: prod.split list.split)
qed


text \<open>The overall correctness proof. Simply composes correctness lemmas.\<close>

definition set_trieP :: "trieP \<Rightarrow> bool list set" where
  "set_trieP = set_trie o abs_trieP"

lemma isinP_set_trieP: "isinP t xs = (xs \<in> set_trieP t)"
  by(simp add: abs_trieP_isinP set_trie_isin set_trieP_def)

lemma set_trieP_insertP: "set_trieP (insertP xs t) = set_trieP t \<union> {xs}"
  by(simp add: abs_trieP_insertP set_trie_insert set_trieP_def)

lemma set_trieP_deleteP: "set_trieP (deleteP xs t) = set_trieP t - {xs}"
  by(auto simp: set_trie_delete set_trieP_def simp flip: delete_abs_trieP)

interpretation SP: Set
  where empty = emptyP and isin = isinP and insert = insertP and delete = deleteP
    and set = set_trieP and invar = invarP
proof (standard, goal_cases)
  case 1 show ?case by (simp add: set_trieP_def set_trie_def)
next
  case 2 show ?case by(rule isinP_set_trieP)
next
  case 3 thus ?case by (auto simp: set_trieP_insertP)
next
  case 4 thus ?case by(auto simp: set_trieP_deleteP)
next
  case 5 thus ?case by(simp)
next
  case 6 thus ?case by(rule invarP_insertP)
next
  case 7 thus ?case by(rule invarP_deleteP)
qed

end
