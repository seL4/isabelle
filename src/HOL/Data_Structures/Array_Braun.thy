section "Arrays via Braun Trees"

theory Array_Braun
imports
  Array_Specs
  Braun_Tree
begin

subsection "Array"

fun lookup1 :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a" where
"lookup1 (Node l x r) n = (if n=1 then x else lookup1 (if even n then l else r) (n div 2))"

fun update1 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"update1 n x Leaf = Node Leaf x Leaf" |
"update1 n x (Node l a r) =
  (if n=1 then Node l x r else
   if even n then Node (update1 (n div 2) x l) a r
            else Node l a (update1 (n div 2) x r))"

fun adds :: "'a list \<Rightarrow> nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"adds [] n t = t" |
"adds (x#xs) n t = adds xs (n+1) (update1 (n+1) x t)"

fun list :: "'a tree \<Rightarrow> 'a list" where
"list Leaf = []" |
"list (Node l x r) = x # splice (list l) (list r)"


subsubsection "Functional Correctness"

lemma size_list: "size(list t) = size t"
by(induction t)(auto)

lemma minus1_div2: "(n - Suc 0) div 2 = (if odd n then n div 2 else n div 2 - 1)"
by auto arith

lemma nth_splice: "\<lbrakk> n < size xs + size ys;  size ys \<le> size xs;  size xs \<le> size ys + 1 \<rbrakk>
  \<Longrightarrow> splice xs ys ! n = (if even n then xs else ys) ! (n div 2)"
apply(induction xs ys arbitrary: n rule: splice.induct)
apply (auto simp: nth_Cons' minus1_div2)
done

lemma div2_in_bounds:
  "\<lbrakk> braun (Node l x r); n \<in> {1..size(Node l x r)}; n > 1 \<rbrakk> \<Longrightarrow>
   (odd n \<longrightarrow> n div 2 \<in> {1..size r}) \<and> (even n \<longrightarrow> n div 2 \<in> {1..size l})"
by auto arith

declare upt_Suc[simp del]


text \<open>@{const lookup1}\<close>

lemma nth_list_lookup1: "\<lbrakk>braun t; i < size t\<rbrakk> \<Longrightarrow> list t ! i = lookup1 t (i+1)"
proof(induction t arbitrary: i)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case using div2_in_bounds[OF Node.prems(1), of "i+1"]
    by (auto simp: nth_splice minus1_div2 size_list)
qed

lemma list_eq_map_lookup1: "braun t \<Longrightarrow> list t = map (lookup1 t) [1..<size t + 1]"
by(auto simp add: list_eq_iff_nth_eq size_list nth_list_lookup1)


text \<open>@{const update1}\<close>

lemma size_update1: "\<lbrakk> braun t;  n \<in> {1.. size t} \<rbrakk> \<Longrightarrow> size(update1 n x t) = size t"
proof(induction t arbitrary: n)
  case Leaf thus ?case by simp
next
  case Node thus ?case using div2_in_bounds[OF Node.prems] by simp
qed

lemma braun_update1: "\<lbrakk>braun t;  n \<in> {1.. size t} \<rbrakk> \<Longrightarrow> braun(update1 n x t)"
proof(induction t arbitrary: n)
  case Leaf thus ?case by simp
next
  case Node thus ?case
    using div2_in_bounds[OF Node.prems] by (simp add: size_update1)
qed

lemma lookup1_update1: "\<lbrakk> braun t;  n \<in> {1.. size t} \<rbrakk> \<Longrightarrow>
  lookup1 (update1 n x t) m = (if n=m then x else lookup1 t m)"
proof(induction t arbitrary: m n)
  case Leaf
  then show ?case by simp
next
  have aux: "\<lbrakk> odd n; odd m \<rbrakk> \<Longrightarrow> n div 2 = (m::nat) div 2 \<longleftrightarrow> m=n" for m n
    using odd_two_times_div_two_succ by fastforce
  case Node
  thus ?case using div2_in_bounds[OF Node.prems] by (auto simp: aux)
qed

lemma list_update1: "\<lbrakk> braun t;  n \<in> {1.. size t} \<rbrakk> \<Longrightarrow> list(update1 n x t) = (list t)[n-1 := x]"
by(auto simp add: list_eq_map_lookup1 list_eq_iff_nth_eq lookup1_update1 size_update1 braun_update1)

text \<open>A second proof of @{thm list_update1}:\<close>

lemma diff1_eq_iff: "n > 0 \<Longrightarrow> n - Suc 0 = m \<longleftrightarrow> n = m+1"
by arith

lemma list_update_splice:
  "\<lbrakk> n < size xs + size ys;  size ys \<le> size xs;  size xs \<le> size ys + 1 \<rbrakk> \<Longrightarrow>
  (splice xs ys) [n := x] =
  (if even n then splice (xs[n div 2 := x]) ys else splice xs (ys[n div 2 := x]))"
by(induction xs ys arbitrary: n rule: splice.induct) (auto split: nat.split)

lemma list_update2: "\<lbrakk> braun t;  n \<in> {1.. size t} \<rbrakk> \<Longrightarrow> list(update1 n x t) = (list t)[n-1 := x]"
proof(induction t arbitrary: n)
  case Leaf thus ?case by simp
next
  case (Node l a r) thus ?case using div2_in_bounds[OF Node.prems]
    by(auto simp: list_update_splice diff1_eq_iff size_list split: nat.split)
qed


text \<open>@{const adds}\<close>

lemma splice_last: shows
  "size ys \<le> size xs \<Longrightarrow> splice (xs @ [x]) ys = splice xs ys @ [x]"
and "size ys+1 \<ge> size xs \<Longrightarrow> splice xs (ys @ [y]) = splice xs ys @ [y]"
by(induction xs ys arbitrary: x y rule: splice.induct) (auto)

lemma list_add_hi: "braun t \<Longrightarrow> list(update1 (Suc(size t)) x t) = list t @ [x]"
by(induction t)(auto simp: splice_last size_list)

lemma size_add_hi: "braun t \<Longrightarrow> m = size t \<Longrightarrow> size(update1 (Suc m) x t) = size t + 1"
by(induction t arbitrary: m)(auto)

lemma braun_add_hi: "braun t \<Longrightarrow> braun(update1 (Suc(size t)) x t)"
by(induction t)(auto simp: size_add_hi)

lemma size_braun_adds:
  "\<lbrakk> braun t; size t = n \<rbrakk> \<Longrightarrow> size(adds xs n t) = size t + length xs \<and> braun (adds xs n t)"
by(induction xs arbitrary: t n)(auto simp: braun_add_hi size_add_hi)

lemma list_adds: "\<lbrakk> braun t; size t = n \<rbrakk> \<Longrightarrow> list(adds xs n t) = list t @ xs"
by(induction xs arbitrary: t n)(auto simp: size_braun_adds list_add_hi size_add_hi braun_add_hi)


subsubsection "Array Implementation"

interpretation A: Array
where lookup = "\<lambda>(t,l) n. lookup1 t (n+1)"
and update = "\<lambda>n x (t,l). (update1 (n+1) x t, l)"
and len = "\<lambda>(t,l). l"
and array = "\<lambda>xs. (adds xs 0 Leaf, length xs)"
and invar = "\<lambda>(t,l). braun t \<and> l = size t"
and list = "\<lambda>(t,l). list t"
proof (standard, goal_cases)
  case 1 thus ?case by (simp add: nth_list_lookup1 split: prod.splits)
next
  case 2 thus ?case by (simp add: list_update1 split: prod.splits)
next
  case 3 thus ?case by (simp add: size_list split: prod.splits)
next
  case 4 thus ?case by (simp add: list_adds)
next
  case 5 thus ?case by (simp add: braun_update1 size_update1 split: prod.splits)
next
  case 6 thus ?case by (simp add: size_braun_adds split: prod.splits)
qed


subsection "Flexible Array"

fun add_lo where
"add_lo x Leaf = Node Leaf x Leaf" |
"add_lo x (Node l a r) = Node (add_lo a r) x l"

fun merge where
"merge Leaf r = r" |
"merge (Node l a r) rr = Node rr a (merge l r)"

fun del_lo where
"del_lo Leaf = Leaf" |
"del_lo (Node l a r) = merge l r"

fun del_hi :: "nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"del_hi n Leaf = Leaf" |
"del_hi n (Node l x r) =
	(if n = 1 then Leaf
	 else if even n
	     then Node (del_hi (n div 2) l) x r
	     else Node l x (del_hi (n div 2) r))"


subsubsection "Functional Correctness"


text \<open>@{const add_lo}\<close>

lemma list_add_lo: "braun t \<Longrightarrow> list (add_lo a t) = a # list t"
by(induction t arbitrary: a) auto

lemma braun_add_lo: "braun t \<Longrightarrow> braun(add_lo x t)"
by(induction t arbitrary: x) (auto simp add: list_add_lo simp flip: size_list)


text \<open>@{const del_lo}\<close>

lemma list_merge: "braun (Node l x r) \<Longrightarrow> list(merge l r) = splice (list l) (list r)"
by (induction l r rule: merge.induct) auto

lemma braun_merge: "braun (Node l x r) \<Longrightarrow> braun(merge l r)"
by (induction l r rule: merge.induct)(auto simp add: list_merge simp flip: size_list)

lemma list_del_lo: "braun t \<Longrightarrow> list(del_lo t) = tl (list t)"
by (cases t) (simp_all add: list_merge)

lemma braun_del_lo: "braun t \<Longrightarrow> braun(del_lo t)"
by (cases t) (simp_all add: braun_merge)


text \<open>@{const del_hi}\<close>

lemma list_Nil_iff: "list t = [] \<longleftrightarrow> t = Leaf"
by(cases t) simp_all

lemma butlast_splice: "butlast (splice xs ys) =
  (if size xs > size ys then splice (butlast xs) ys else splice xs (butlast ys))"
by(induction xs ys rule: splice.induct) (auto)

lemma list_del_hi: "braun t \<Longrightarrow> size t = st \<Longrightarrow> list(del_hi st t) = butlast(list t)"
apply(induction t arbitrary: st)
by(auto simp: list_Nil_iff size_list butlast_splice)

lemma braun_del_hi: "braun t \<Longrightarrow> size t = st \<Longrightarrow> braun(del_hi st t)"
apply(induction t arbitrary: st)
by(auto simp: list_del_hi simp flip: size_list)


subsubsection "Flexible Array Implementation"

interpretation AF: Array_Flex
where lookup = "\<lambda>(t,l) n. lookup1 t (n+1)"
and update = "\<lambda>n x (t,l). (update1 (n+1) x t, l)"
and len = "\<lambda>(t,l). l"
and array = "\<lambda>xs. (adds xs 0 Leaf, length xs)"
and invar = "\<lambda>(t,l). braun t \<and> l = size t"
and list = "\<lambda>(t,l). list t"
and add_lo = "\<lambda>x (t,l). (add_lo x t, l+1)"
and del_lo = "\<lambda>(t,l). (del_lo t, l-1)"
and add_hi = "\<lambda>x (t,l). (update1 (Suc l) x t, l+1)"
and del_hi = "\<lambda>(t,l). (del_hi l t, l-1)"
proof (standard, goal_cases)
  case 1 thus ?case by (simp add: list_add_lo split: prod.splits)
next
  case 2 thus ?case by (simp add: list_del_lo split: prod.splits)
next
  case 3 thus ?case by (simp add: list_add_hi braun_add_hi split: prod.splits)
next
  case 4 thus ?case by (simp add: list_del_hi split: prod.splits)
next
  case 5 thus ?case by (simp add: braun_add_lo list_add_lo flip: size_list split: prod.splits)
next
  case 6 thus ?case by (simp add: braun_del_lo list_del_lo flip: size_list split: prod.splits)
next
  case 7 thus ?case by (simp add: size_add_hi braun_add_hi split: prod.splits)
next
  case 8 thus ?case by (simp add: braun_del_hi list_del_hi flip: size_list split: prod.splits)
qed


subsection "Faster"

fun braun_of_naive :: "'a \<Rightarrow> nat \<Rightarrow> 'a tree" where
"braun_of_naive x n = (if n=0 then Leaf
  else let m = (n-1) div 2
       in if odd n then Node (braun_of_naive x m) x (braun_of_naive x m)
       else Node (braun_of_naive x (m + 1)) x (braun_of_naive x m))"

fun braun2_of :: "'a \<Rightarrow> nat \<Rightarrow> 'a tree * 'a tree" where
"braun2_of x n = (if n = 0 then (Leaf, Node Leaf x Leaf)
  else let (s,t) = braun2_of x ((n-1) div 2)
       in if odd n then (Node s x s, Node t x s) else (Node t x s, Node t x t))"

definition braun_of :: "'a \<Rightarrow> nat \<Rightarrow> 'a tree" where
"braun_of x n = fst (braun2_of x n)"

declare braun2_of.simps [simp del]

lemma braun2_of_size_braun: "braun2_of x n = (s,t) \<Longrightarrow> size s = n \<and> size t = n+1 \<and> braun s \<and> braun t"
proof(induction x n arbitrary: s t rule: braun2_of.induct)
  case (1 x n)
  then show ?case
    by (auto simp: braun2_of.simps[of x n] split: prod.splits if_splits) presburger+
qed

lemma braun2_of_replicate:
  "braun2_of x n = (s,t) \<Longrightarrow> list s = replicate n x \<and> list t = replicate (n+1) x"
proof(induction x n arbitrary: s t rule: braun2_of.induct)
  case (1 x n)
  have "x # replicate m x = replicate (m+1) x" for m by simp
  with 1 show ?case
    apply (auto simp: braun2_of.simps[of x n] replicate.simps(2)[of 0 x]
        simp del: replicate.simps(2) split: prod.splits if_splits)
    by presburger+
qed

corollary braun_braun_of: "braun(braun_of x n)"
unfolding braun_of_def by (metis eq_fst_iff braun2_of_size_braun)

corollary list_braun_of: "list(braun_of x n) = replicate n x"
unfolding braun_of_def by (metis eq_fst_iff braun2_of_replicate)

end