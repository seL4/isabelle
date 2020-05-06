(* Author: Tobias Nipkow *)

section "AVL Tree Implementation of Maps"

theory AVL_Map
imports
  AVL_Set
  Lookup2
begin

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree_ht \<Rightarrow> ('a*'b) tree_ht" where
"update x y Leaf = Node Leaf ((x,y), 1) Leaf" |
"update x y (Node l ((a,b), h) r) = (case cmp x a of
   EQ \<Rightarrow> Node l ((x,y), h) r |
   LT \<Rightarrow> balL (update x y l) (a,b) r |
   GT \<Rightarrow> balR l (a,b) (update x y r))"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b) tree_ht \<Rightarrow> ('a*'b) tree_ht" where
"delete _ Leaf = Leaf" |
"delete x (Node l ((a,b), h) r) = (case cmp x a of
   EQ \<Rightarrow> if l = Leaf then r
         else let (l', ab') = split_max l in balR l' ab' r |
   LT \<Rightarrow> balR (delete x l) (a,b) r |
   GT \<Rightarrow> balL l (a,b) (delete x r))"


subsection \<open>Functional Correctness\<close>

theorem inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by (induct t) (auto simp: upd_list_simps inorder_balL inorder_balR)


theorem inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR
      inorder_split_maxD split: prod.splits)


subsection \<open>AVL invariants\<close>


subsubsection \<open>Insertion maintains AVL balance\<close>

theorem avl_update:
  assumes "avl t"
  shows "avl(update x y t)"
        "(height (update x y t) = height t \<or> height (update x y t) = height t + 1)"
using assms
proof (induction x y t rule: update.induct)
  case eq2: (2 x y l a b h r)
  case 1
  show ?case
  proof(cases "x = a")
    case True with eq2 1 show ?thesis by simp
  next
    case False
    with eq2 1 show ?thesis 
    proof(cases "x<a")
      case True with eq2 1 show ?thesis by (auto intro!: avl_balL)
    next
      case False with eq2 1 \<open>x\<noteq>a\<close> show ?thesis by (auto intro!: avl_balR)
    qed
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True with eq2 1 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height (update x y l) = height r + 2")
        case False with eq2 2 \<open>x < a\<close> show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (update x y l) (a,b) r) = height r + 2) \<or>
          (height (balL (update x y l) (a,b) r) = height r + 3)" (is "?A \<or> ?B")
          using eq2 2 \<open>x<a\<close> height_balL[OF _ _ True] by simp
        thus ?thesis
        proof
          assume ?A with 2 \<open>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with True 1 eq2(2) \<open>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height (update x y r) = height l + 2")
        case False with eq2 2 \<open>\<not>x < a\<close> show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l (a,b) (update x y r)) = height l + 2) \<or>
          (height (balR l (a,b) (update x y r)) = height l + 3)"  (is "?A \<or> ?B")
          using eq2 2 \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> height_balR[OF _ _ True] by simp
        thus ?thesis 
        proof
          assume ?A with 2 \<open>\<not>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with True 1 eq2(4) \<open>\<not>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    qed
  qed
qed simp_all


subsubsection \<open>Deletion maintains AVL balance\<close>

theorem avl_delete:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t rule: tree2_induct)
  case (Node l ab h r)
  obtain a b where [simp]: "ab = (a,b)" by fastforce
  case 1
  show ?case
  proof(cases "x = a")
    case True with Node 1 show ?thesis
      using avl_split_max[of l] by (auto intro!: avl_balR split: prod.split)
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True with Node 1 show ?thesis by (auto intro!: avl_balR)
    next
      case False with Node 1 \<open>x\<noteq>a\<close> show ?thesis by (auto intro!: avl_balL)
    qed
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True then show ?thesis using 1 avl_split_max[of l]
      by(auto simp: balR_def max_absorb2 split!: if_splits prod.split tree.split)
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False with Node 1 \<open>x < a\<close> show ?thesis by(auto simp: balR_def)
      next
        case True 
        thus ?thesis using height_balR[OF _ _ True, of ab] 2 Node(1,2) \<open>x < a\<close> by simp linarith
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False with Node 1 \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> show ?thesis by(auto simp: balL_def)
      next
        case True
        thus ?thesis
          using height_balL[OF _ _ True, of ab] 2 Node(3,4) \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> by auto
      qed
    qed
  qed
qed simp_all


interpretation M: Map_by_Ordered
where empty = empty and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = avl
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 show ?case by (simp add: empty_def)
next
  case 6 thus ?case by(simp add: avl_update(1))
next
  case 7 thus ?case by(simp add: avl_delete(1))
qed

end
