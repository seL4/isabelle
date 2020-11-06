(* Author: Tobias Nipkow, with contributions by Thomas Sewell *)

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


paragraph \<open>\<^const>\<open>lookup1\<close>\<close>

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


paragraph \<open>\<^const>\<open>update1\<close>\<close>

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


paragraph \<open>\<^const>\<open>adds\<close>\<close>

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


paragraph \<open>\<^const>\<open>add_lo\<close>\<close>

lemma list_add_lo: "braun t \<Longrightarrow> list (add_lo a t) = a # list t"
by(induction t arbitrary: a) auto

lemma braun_add_lo: "braun t \<Longrightarrow> braun(add_lo x t)"
by(induction t arbitrary: x) (auto simp add: list_add_lo simp flip: size_list)


paragraph \<open>\<^const>\<open>del_lo\<close>\<close>

lemma list_merge: "braun (Node l x r) \<Longrightarrow> list(merge l r) = splice (list l) (list r)"
by (induction l r rule: merge.induct) auto

lemma braun_merge: "braun (Node l x r) \<Longrightarrow> braun(merge l r)"
by (induction l r rule: merge.induct)(auto simp add: list_merge simp flip: size_list)

lemma list_del_lo: "braun t \<Longrightarrow> list(del_lo t) = tl (list t)"
by (cases t) (simp_all add: list_merge)

lemma braun_del_lo: "braun t \<Longrightarrow> braun(del_lo t)"
by (cases t) (simp_all add: braun_merge)


paragraph \<open>\<^const>\<open>del_hi\<close>\<close>

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


subsubsection \<open>Size\<close>

fun diff :: "'a tree \<Rightarrow> nat \<Rightarrow> nat" where
"diff Leaf _ = 0" |
"diff (Node l x r) n = (if n=0 then 1 else if even n then diff r (n div 2 - 1) else diff l (n div 2))"

fun size_fast :: "'a tree \<Rightarrow> nat" where
"size_fast Leaf = 0" |
"size_fast (Node l x r) = (let n = size_fast r in 1 + 2*n + diff l n)"

declare Let_def[simp]

lemma diff: "braun t \<Longrightarrow> size t : {n, n + 1} \<Longrightarrow> diff t n = size t - n"
by(induction t arbitrary: n) auto

lemma size_fast: "braun t \<Longrightarrow> size_fast t = size t"
by(induction t) (auto simp add: diff)


subsubsection \<open>Initialization with 1 element\<close>

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


subsubsection "Proof Infrastructure"

text \<open>Originally due to Thomas Sewell.\<close>

paragraph \<open>\<open>take_nths\<close>\<close>

fun take_nths :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"take_nths i k [] = []" |
"take_nths i k (x # xs) = (if i = 0 then x # take_nths (2^k - 1) k xs
  else take_nths (i - 1) k xs)"

text \<open>This is the more concise definition but seems to complicate the proofs:\<close>

lemma take_nths_eq_nths: "take_nths i k xs = nths xs (\<Union>n. {n*2^k + i})"
proof(induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume [simp]: "i = 0"
    have "(\<Union>n. {(n+1) * 2 ^ k - 1}) = {m. \<exists>n. Suc m = n * 2 ^ k}"
      apply (auto simp del: mult_Suc)
      by (metis diff_Suc_Suc diff_zero mult_eq_0_iff not0_implies_Suc)
    thus ?thesis by (simp add: Cons.IH ac_simps nths_Cons)
  next
    assume [arith]: "i \<noteq> 0"
    have "(\<Union>n. {n * 2 ^ k + i - 1}) = {m. \<exists>n. Suc m = n * 2 ^ k + i}"
      apply auto
      by (metis diff_Suc_Suc diff_zero)
    thus ?thesis by (simp add: Cons.IH nths_Cons)
  qed
qed

lemma take_nths_drop:
  "take_nths i k (drop j xs) = take_nths (i + j) k xs"
by (induct xs arbitrary: i j; simp add: drop_Cons split: nat.split)

lemma take_nths_00:
  "take_nths 0 0 xs = xs"
by (induct xs; simp)

lemma splice_take_nths:
  "splice (take_nths 0 (Suc 0) xs) (take_nths (Suc 0) (Suc 0) xs) = xs"
by (induct xs; simp)

lemma take_nths_take_nths:
  "take_nths i m (take_nths j n xs) = take_nths ((i * 2^n) + j) (m + n) xs"
by (induct xs arbitrary: i j; simp add: algebra_simps power_add)

lemma take_nths_empty:
  "(take_nths i k xs = []) = (length xs \<le> i)"
by (induction xs arbitrary: i k) auto

lemma hd_take_nths:
  "i < length xs \<Longrightarrow> hd(take_nths i k xs) = xs ! i"
by (induction xs arbitrary: i k) auto

lemma take_nths_01_splice:
  "\<lbrakk> length xs = length ys \<or> length xs = length ys + 1 \<rbrakk> \<Longrightarrow>
   take_nths 0 (Suc 0) (splice xs ys) = xs \<and>
   take_nths (Suc 0) (Suc 0) (splice xs ys) = ys"
by (induct xs arbitrary: ys; case_tac ys; simp)

lemma length_take_nths_00:
  "length (take_nths 0 (Suc 0) xs) = length (take_nths (Suc 0) (Suc 0) xs) \<or>
   length (take_nths 0 (Suc 0) xs) = length (take_nths (Suc 0) (Suc 0) xs) + 1"
by (induct xs) auto


paragraph \<open>\<open>braun_list\<close>\<close>

fun braun_list :: "'a tree \<Rightarrow> 'a list \<Rightarrow> bool" where
"braun_list Leaf xs = (xs = [])" |
"braun_list (Node l x r) xs = (xs \<noteq> [] \<and> x = hd xs \<and>
    braun_list l (take_nths 1 1 xs) \<and>
    braun_list r (take_nths 2 1 xs))"

lemma braun_list_eq:
  "braun_list t xs = (braun t \<and> xs = list t)"
proof (induct t arbitrary: xs)
  case Leaf
  show ?case by simp
next
  case Node
  show ?case
    using length_take_nths_00[of xs] splice_take_nths[of xs]
    by (auto simp: neq_Nil_conv Node.hyps size_list[symmetric] take_nths_01_splice)
qed


subsubsection \<open>Converting a list of elements into a Braun tree\<close>

fun nodes :: "'a tree list \<Rightarrow> 'a list \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list" where
"nodes (l#ls) (x#xs) (r#rs) = Node l x r # nodes ls xs rs" |
"nodes (l#ls) (x#xs) [] = Node l x Leaf # nodes ls xs []" |
"nodes [] (x#xs) (r#rs) = Node Leaf x r # nodes [] xs rs" |
"nodes [] (x#xs) [] = Node Leaf x Leaf # nodes [] xs []" |
"nodes ls [] rs = []"

fun brauns :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a tree list" where
"brauns k xs = (if xs = [] then [] else
   let ys = take (2^k) xs;
       zs = drop (2^k) xs;
       ts = brauns (k+1) zs
   in nodes ts ys (drop (2^k) ts))"

declare brauns.simps[simp del]

definition brauns1 :: "'a list \<Rightarrow> 'a tree" where
"brauns1 xs = (if xs = [] then Leaf else brauns 0 xs ! 0)"

fun T_brauns :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
"T_brauns k xs = (if xs = [] then 0 else
   let ys = take (2^k) xs;
       zs = drop (2^k) xs;
       ts = brauns (k+1) zs
   in 4 * min (2^k) (length xs) + T_brauns (k+1) zs)"


paragraph "Functional correctness"

text \<open>The proof is originally due to Thomas Sewell.\<close>

lemma length_nodes:
  "length (nodes ls xs rs) = length xs"
by (induct ls xs rs rule: nodes.induct; simp)

lemma nth_nodes:
  "i < length xs \<Longrightarrow> nodes ls xs rs ! i =
  Node (if i < length ls then ls ! i else Leaf) (xs ! i)
    (if i < length rs then rs ! i else Leaf)"
by (induct ls xs rs arbitrary: i rule: nodes.induct;
    simp add: nth_Cons split: nat.split)

theorem length_brauns:
  "length (brauns k xs) = min (length xs) (2 ^ k)"
proof (induct xs arbitrary: k rule: measure_induct_rule[where f=length])
  case (less xs) thus ?case by (simp add: brauns.simps[of k xs] length_nodes)
qed

theorem brauns_correct:
  "i < min (length xs) (2 ^ k) \<Longrightarrow> braun_list (brauns k xs ! i) (take_nths i k xs)"
proof (induct xs arbitrary: i k rule: measure_induct_rule[where f=length])
  case (less xs)
  have "xs \<noteq> []" using less.prems by auto
  let ?zs = "drop (2^k) xs"
  let ?ts = "brauns (Suc k) ?zs"
  from less.hyps[of ?zs _ "Suc k"]
  have IH: "\<lbrakk> j = i + 2 ^ k;  i < min (length ?zs) (2 ^ (k+1)) \<rbrakk> \<Longrightarrow>
    braun_list (?ts ! i) (take_nths j (Suc k) xs)" for i j
    using \<open>xs \<noteq> []\<close> by (simp add: take_nths_drop)
  show ?case
    using less.prems
    by (auto simp: brauns.simps[of k xs] nth_nodes take_nths_take_nths
                   IH take_nths_empty hd_take_nths length_brauns)
qed

corollary brauns1_correct:
  "braun (brauns1 xs) \<and> list (brauns1 xs) = xs"
using brauns_correct[of 0 xs 0]
by (simp add: brauns1_def braun_list_eq take_nths_00)


paragraph "Running Time Analysis"

theorem T_brauns:
  "T_brauns k xs = 4 * length xs"
proof (induction xs arbitrary: k rule: measure_induct_rule[where f = length])
  case (less xs)
  show ?case
  proof cases
    assume "xs = []"
    thus ?thesis by(simp)
  next
    assume "xs \<noteq> []"
    let ?zs = "drop (2^k) xs"
    have "T_brauns k xs = T_brauns (k+1) ?zs + 4 * min (2^k) (length xs)"
     using \<open>xs \<noteq> []\<close> by(simp)
    also have "\<dots> = 4 * length ?zs + 4 * min (2^k) (length xs)"
      using less[of ?zs "k+1"] \<open>xs \<noteq> []\<close>
      by (simp)
    also have "\<dots> = 4 * length xs"
      by(simp)
    finally show ?case .
  qed
qed


subsubsection \<open>Converting a Braun Tree into a List of Elements\<close>

text \<open>The code and the proof are originally due to Thomas Sewell (except running time).\<close>

function list_fast_rec :: "'a tree list \<Rightarrow> 'a list" where
"list_fast_rec ts = (let us = filter (\<lambda>t. t \<noteq> Leaf) ts in
  if us = [] then [] else
  map value us @ list_fast_rec (map left us @ map right us))"
by (pat_completeness, auto)

lemma list_fast_rec_term1: "ts \<noteq> [] \<Longrightarrow> Leaf \<notin> set ts \<Longrightarrow>
  sum_list (map (size o left) ts) + sum_list (map (size o right) ts) < sum_list (map size ts)"
  apply (clarsimp simp: sum_list_addf[symmetric] sum_list_map_filter')
  apply (rule sum_list_strict_mono; clarsimp?)
  apply (case_tac x; simp)
  done

lemma list_fast_rec_term: "us \<noteq> [] \<Longrightarrow> us = filter (\<lambda>t. t \<noteq> \<langle>\<rangle>) ts \<Longrightarrow>
  sum_list (map (size o left) us) + sum_list (map (size o right) us) < sum_list (map size ts)"
  apply (rule order_less_le_trans, rule list_fast_rec_term1, simp_all)
  apply (rule sum_list_filter_le_nat)
  done

termination
  apply (relation "measure (sum_list o map size)")
   apply simp
  apply (simp add: list_fast_rec_term)
  done

declare list_fast_rec.simps[simp del]

definition list_fast :: "'a tree \<Rightarrow> 'a list" where
"list_fast t = list_fast_rec [t]"

function T_list_fast_rec :: "'a tree list \<Rightarrow> nat" where
"T_list_fast_rec ts = (let us = filter (\<lambda>t. t \<noteq> Leaf) ts
  in length ts + (if us = [] then 0 else
  5 * length us + T_list_fast_rec (map left us @ map right us)))"
by (pat_completeness, auto)

termination
  apply (relation "measure (sum_list o map size)")
   apply simp
  apply (simp add: list_fast_rec_term)
  done

declare T_list_fast_rec.simps[simp del]

paragraph "Functional Correctness"

lemma list_fast_rec_all_Leaf:
  "\<forall>t \<in> set ts. t = Leaf \<Longrightarrow> list_fast_rec ts = []"
by (simp add: filter_empty_conv list_fast_rec.simps)

lemma take_nths_eq_single:
  "length xs - i < 2^n \<Longrightarrow> take_nths i n xs = take 1 (drop i xs)"
by (induction xs arbitrary: i n; simp add: drop_Cons')

lemma braun_list_Nil:
  "braun_list t [] = (t = Leaf)"
by (cases t; simp)

lemma braun_list_not_Nil: "xs \<noteq> [] \<Longrightarrow>
  braun_list t xs =
 (\<exists>l x r. t = Node l x r \<and> x = hd xs \<and>
    braun_list l (take_nths 1 1 xs) \<and>
    braun_list r (take_nths 2 1 xs))"
by(cases t; simp)

theorem list_fast_rec_correct:
  "\<lbrakk> length ts = 2 ^ k; \<forall>i < 2 ^ k. braun_list (ts ! i) (take_nths i k xs) \<rbrakk>
    \<Longrightarrow> list_fast_rec ts = xs"
proof (induct xs arbitrary: k ts rule: measure_induct_rule[where f=length])
  case (less xs)
  show ?case
  proof (cases "length xs < 2 ^ k")
    case True
    from less.prems True have filter:
      "\<exists>n. ts = map (\<lambda>x. Node Leaf x Leaf) xs @ replicate n Leaf"
      apply (rule_tac x="length ts - length xs" in exI)
      apply (clarsimp simp: list_eq_iff_nth_eq)
      apply(auto simp: nth_append braun_list_not_Nil take_nths_eq_single braun_list_Nil hd_drop_conv_nth)
      done
    thus ?thesis
      by (clarsimp simp: list_fast_rec.simps[of ts] o_def list_fast_rec_all_Leaf)
  next
    case False
    with less.prems(2) have *:
      "\<forall>i < 2 ^ k. ts ! i \<noteq> Leaf
         \<and> value (ts ! i) = xs ! i
         \<and> braun_list (left (ts ! i)) (take_nths (i + 2 ^ k) (Suc k) xs)
         \<and> (\<forall>ys. ys = take_nths (i + 2 * 2 ^ k) (Suc k) xs
                 \<longrightarrow> braun_list (right (ts ! i)) ys)"
      by (auto simp: take_nths_empty hd_take_nths braun_list_not_Nil take_nths_take_nths
                     algebra_simps)
    have 1: "map value ts = take (2 ^ k) xs"
      using less.prems(1) False by (simp add: list_eq_iff_nth_eq *)
    have 2: "list_fast_rec (map left ts @ map right ts) = drop (2 ^ k) xs"
      using less.prems(1) False
      by (auto intro!: Nat.diff_less less.hyps[where k= "Suc k"]
               simp: nth_append * take_nths_drop algebra_simps)
    from less.prems(1) False show ?thesis
      by (auto simp: list_fast_rec.simps[of ts] 1 2 * all_set_conv_all_nth)
  qed
qed

corollary list_fast_correct:
  "braun t \<Longrightarrow> list_fast t = list t"
by (simp add: list_fast_def take_nths_00 braun_list_eq list_fast_rec_correct[where k=0])

paragraph "Running Time Analysis"

lemma sum_tree_list_children: "\<forall>t \<in> set ts. t \<noteq> Leaf \<Longrightarrow>
  (\<Sum>t\<leftarrow>ts. k * size t) = (\<Sum>t \<leftarrow> map left ts @ map right ts. k * size t) + k * length ts"
by(induction ts)(auto simp add: neq_Leaf_iff algebra_simps)

theorem T_list_fast_rec_ub:
  "T_list_fast_rec ts \<le> sum_list (map (\<lambda>t. 7*size t + 1) ts)"
proof (induction ts rule: measure_induct_rule[where f="sum_list o map size"])
  case (less ts)
  let ?us = "filter (\<lambda>t. t \<noteq> Leaf) ts"
  show ?case
  proof cases
    assume "?us = []"
    thus ?thesis using T_list_fast_rec.simps[of ts]
      by(simp add: sum_list_Suc)
    next
    assume "?us \<noteq> []"
    let ?children = "map left ?us @ map right ?us"
    have "T_list_fast_rec ts = T_list_fast_rec ?children + 5 * length ?us + length ts"
     using \<open>?us \<noteq> []\<close> T_list_fast_rec.simps[of ts] by(simp)
    also have "\<dots> \<le> (\<Sum>t\<leftarrow>?children. 7 * size t + 1) + 5 * length ?us + length ts"
      using less[of "?children"] list_fast_rec_term[of "?us"] \<open>?us \<noteq> []\<close>
      by (simp)
    also have "\<dots> = (\<Sum>t\<leftarrow>?children. 7*size t) + 7 * length ?us + length ts"
      by(simp add: sum_list_Suc o_def)
    also have "\<dots> = (\<Sum>t\<leftarrow>?us. 7*size t) + length ts"
      by(simp add: sum_tree_list_children)
    also have "\<dots> \<le> (\<Sum>t\<leftarrow>ts. 7*size t) + length ts"
      by(simp add: sum_list_filter_le_nat)
    also have "\<dots> = (\<Sum>t\<leftarrow>ts. 7 * size t + 1)"
      by(simp add: sum_list_Suc)
    finally show ?case .
  qed
qed

end
