(* Author: Bohua Zhan, with modifications by Tobias Nipkow *)

section \<open>Interval Trees\<close>

theory Interval_Tree
imports
  "HOL-Data_Structures.Cmp"
  "HOL-Data_Structures.List_Ins_Del"
  "HOL-Data_Structures.Isin2"
  "HOL-Data_Structures.Set_Specs"
begin

subsection \<open>Intervals\<close>

text \<open>The following definition of intervals uses the \<^bold>\<open>typedef\<close> command
to define the type of non-empty intervals as a subset of the type of pairs \<open>p\<close>
where @{prop "fst p \<le> snd p"}:\<close>

typedef (overloaded) 'a::linorder ivl =
  "{p :: 'a \<times> 'a. fst p \<le> snd p}" by auto

text \<open>More precisely, @{typ "'a ivl"} is isomorphic with that subset via the function
@{const Rep_ivl}. Hence the basic interval properties are not immediate but
need simple proofs:\<close>

definition low :: "'a::linorder ivl \<Rightarrow> 'a" where
"low p = fst (Rep_ivl p)"

definition high :: "'a::linorder ivl \<Rightarrow> 'a" where
"high p = snd (Rep_ivl p)"

lemma ivl_is_interval: "low p \<le> high p"
by (metis Rep_ivl high_def low_def mem_Collect_eq)

lemma ivl_inj: "low p = low q \<Longrightarrow> high p = high q \<Longrightarrow> p = q"
by (metis Rep_ivl_inverse high_def low_def prod_eqI)

text \<open>Now we can forget how exactly intervals were defined.\<close>


instantiation ivl :: (linorder) linorder begin

definition ivl_less: "(x < y) = (low x < low y | (low x = low y \<and> high x < high y))"
definition ivl_less_eq: "(x \<le> y) = (low x < low y | (low x = low y \<and> high x \<le> high y))"

instance proof
  fix x y z :: "'a ivl"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using ivl_less ivl_less_eq by force
  show b: "x \<le> x"
    by (simp add: ivl_less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt ivl_less_eq dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using ivl_less_eq a ivl_inj ivl_less by fastforce
  show e: "x \<le> y \<or> y \<le> x"
    by (meson ivl_less_eq leI not_less_iff_gr_or_eq)
qed end


definition overlap :: "('a::linorder) ivl \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"overlap x y \<longleftrightarrow> (high x \<ge> low y \<and> high y \<ge> low x)"

definition has_overlap :: "('a::linorder) ivl set \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"has_overlap S y \<longleftrightarrow> (\<exists>x\<in>S. overlap x y)"


subsection \<open>Interval Trees\<close>

type_synonym 'a ivl_tree = "('a ivl * 'a) tree"

fun max_hi :: "('a::order_bot) ivl_tree \<Rightarrow> 'a" where
"max_hi Leaf = bot" |
"max_hi (Node _ (_,m) _) = m"

definition max3 :: "('a::linorder) ivl \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"max3 a m n = max (high a) (max m n)"

fun inv_max_hi :: "('a::{linorder,order_bot}) ivl_tree \<Rightarrow> bool" where
"inv_max_hi Leaf \<longleftrightarrow> True" |
"inv_max_hi (Node l (a, m) r) \<longleftrightarrow> (m = max3 a (max_hi l) (max_hi r) \<and> inv_max_hi l \<and> inv_max_hi r)"

lemma max_hi_is_max:
  "inv_max_hi t \<Longrightarrow> a \<in> set_tree t \<Longrightarrow> high a \<le> max_hi t"
by (induct t, auto simp add: max3_def max_def)

lemma max_hi_exists:
  "inv_max_hi t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> \<exists>a\<in>set_tree t. high a = max_hi t"
proof (induction t rule: tree2_induct)
  case Leaf
  then show ?case by auto
next
  case N: (Node l v m r)
  then show ?case
  proof (cases l rule: tree2_cases)
    case Leaf
    then show ?thesis
      using N.prems(1) N.IH(2) by (cases r, auto simp add: max3_def max_def le_bot)
  next
    case Nl: Node
    then show ?thesis
    proof (cases r rule: tree2_cases)
      case Leaf
      then show ?thesis
        using N.prems(1) N.IH(1) Nl by (auto simp add: max3_def max_def le_bot)
    next
      case Nr: Node
      obtain p1 where p1: "p1 \<in> set_tree l" "high p1 = max_hi l"
        using N.IH(1) N.prems(1) Nl by auto
      obtain p2 where p2: "p2 \<in> set_tree r" "high p2 = max_hi r"
        using N.IH(2) N.prems(1) Nr by auto
      then show ?thesis
        using p1 p2 N.prems(1) by (auto simp add: max3_def max_def)
    qed
  qed
qed


subsection \<open>Insertion and Deletion\<close>

definition node where
[simp]: "node l a r = Node l (a, max3 a (max_hi l) (max_hi r)) r"

fun insert :: "'a::{linorder,order_bot} ivl \<Rightarrow> 'a ivl_tree \<Rightarrow> 'a ivl_tree" where
"insert x Leaf = Node Leaf (x, high x) Leaf" |
"insert x (Node l (a, m) r) =
  (case cmp x a of
     EQ \<Rightarrow> Node l (a, m) r |
     LT \<Rightarrow> node (insert x l) a r |
     GT \<Rightarrow> node l a (insert x r))"

lemma inorder_insert:
  "sorted (inorder t) \<Longrightarrow> inorder (insert x t) = ins_list x (inorder t)"
by (induct t rule: tree2_induct) (auto simp: ins_list_simps)

lemma inv_max_hi_insert:
  "inv_max_hi t \<Longrightarrow> inv_max_hi (insert x t)"
by (induct t rule: tree2_induct) (auto simp add: max3_def)

fun split_min :: "'a::{linorder,order_bot} ivl_tree \<Rightarrow> 'a ivl \<times> 'a ivl_tree" where
"split_min (Node l (a, m) r) =
  (if l = Leaf then (a, r)
   else let (x,l') = split_min l in (x, node l' a r))"

fun delete :: "'a::{linorder,order_bot} ivl \<Rightarrow> 'a ivl_tree \<Rightarrow> 'a ivl_tree" where
"delete x Leaf = Leaf" |
"delete x (Node l (a, m) r) =
  (case cmp x a of
     LT \<Rightarrow> node (delete x l) a r |
     GT \<Rightarrow> node l a (delete x r) |
     EQ \<Rightarrow> if r = Leaf then l else
           let (a', r') = split_min r in node l a' r')"

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by (induct t arbitrary: t' rule: split_min.induct)
   (auto simp: sorted_lems split: prod.splits if_splits)

lemma inorder_delete:
  "sorted (inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by (induct t)
   (auto simp: del_list_simps split_minD Let_def split: prod.splits)

lemma inv_max_hi_split_min:
  "\<lbrakk> t \<noteq> Leaf;  inv_max_hi t \<rbrakk> \<Longrightarrow> inv_max_hi (snd (split_min t))"
by (induct t) (auto split: prod.splits)

lemma inv_max_hi_delete:
  "inv_max_hi t \<Longrightarrow> inv_max_hi (delete x t)"
apply (induct t)
 apply simp
using inv_max_hi_split_min by (fastforce simp add: Let_def split: prod.splits)


subsection \<open>Search\<close>

text \<open>Does interval \<open>x\<close> overlap with any interval in the tree?\<close>

fun search :: "'a::{linorder,order_bot} ivl_tree \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"search Leaf x = False" |
"search (Node l (a, m) r) x =
  (if overlap x a then True
   else if l \<noteq> Leaf \<and> max_hi l \<ge> low x then search l x
   else search r x)"

lemma search_correct:
  "inv_max_hi t \<Longrightarrow> sorted (inorder t) \<Longrightarrow> search t x = has_overlap (set_tree t) x"
proof (induction t rule: tree2_induct)
  case Leaf
  then show ?case by (auto simp add: has_overlap_def)
next
  case (Node l a m r)
  have search_l: "search l x = has_overlap (set_tree l) x"
    using Node.IH(1) Node.prems by (auto simp: sorted_wrt_append)
  have search_r: "search r x = has_overlap (set_tree r) x"
    using Node.IH(2) Node.prems by (auto simp: sorted_wrt_append)
  show ?case
  proof (cases "overlap a x")
    case True
    thus ?thesis by (auto simp: overlap_def has_overlap_def)
  next
    case a_disjoint: False
    then show ?thesis
    proof cases
      assume [simp]: "l = Leaf"
      have search_eval: "search (Node l (a, m) r) x = search r x"
        using a_disjoint overlap_def by auto
      show ?thesis
        unfolding search_eval search_r
        by (auto simp add: has_overlap_def a_disjoint)
    next
      assume "l \<noteq> Leaf"
      then show ?thesis
      proof (cases "max_hi l \<ge> low x")
        case max_hi_l_ge: True
        have "inv_max_hi l"
          using Node.prems(1) by auto
        then obtain p where p: "p \<in> set_tree l" "high p = max_hi l"
          using \<open>l \<noteq> Leaf\<close> max_hi_exists by auto
        have search_eval: "search (Node l (a, m) r) x = search l x"
          using a_disjoint \<open>l \<noteq> Leaf\<close> max_hi_l_ge by (auto simp: overlap_def)
        show ?thesis
        proof (cases "low p \<le> high x")
          case True
          have "overlap p x"
            unfolding overlap_def using True p(2) max_hi_l_ge by auto
          then show ?thesis
            unfolding search_eval search_l
            using p(1) by(auto simp: has_overlap_def overlap_def)
        next
          case False
          have "\<not>overlap x rp" if asm: "rp \<in> set_tree r" for rp
          proof -
            have "low p \<le> low rp"
              using asm p(1) Node(4) by(fastforce simp: sorted_wrt_append ivl_less)
            then show ?thesis
              using False by (auto simp: overlap_def)
          qed
          then show ?thesis
            unfolding search_eval search_l
            using a_disjoint by (auto simp: has_overlap_def overlap_def)
        qed
      next
        case False
        have search_eval: "search (Node l (a, m) r) x = search r x"
          using a_disjoint False by (auto simp: overlap_def)
        have "\<not>overlap x lp" if asm: "lp \<in> set_tree l" for lp
          using asm False Node.prems(1) max_hi_is_max
          by (fastforce simp: overlap_def)
        then show ?thesis
          unfolding search_eval search_r
          using a_disjoint by (auto simp: has_overlap_def overlap_def)
      qed
    qed
  qed
qed

definition empty :: "'a ivl_tree" where
"empty = Leaf"


subsection \<open>Specification\<close>

locale Interval_Set = Set +
  fixes has_overlap :: "'t \<Rightarrow> 'a::linorder ivl \<Rightarrow> bool"
  assumes set_overlap: "invar s \<Longrightarrow> has_overlap s x = Interval_Tree.has_overlap (set s) x"

interpretation S: Interval_Set
  where empty = Leaf and insert = insert and delete = delete
  and has_overlap = search and isin = isin and set = set_tree
  and invar = "\<lambda>t. inv_max_hi t \<and> sorted (inorder t)"
proof (standard, goal_cases)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case by (simp add: isin_set_inorder)
next
  case 3
  then show ?case by(simp add: inorder_insert set_ins_list flip: set_inorder)
next
  case 4
  then show ?case by(simp add: inorder_delete set_del_list flip: set_inorder)
next
  case 5
  then show ?case by auto
next
  case 6
  then show ?case by (simp add: inorder_insert inv_max_hi_insert sorted_ins_list)
next
  case 7
  then show ?case by (simp add: inorder_delete inv_max_hi_delete sorted_del_list)
next
  case 8
  then show ?case by (simp add: search_correct)
qed

end
