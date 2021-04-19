(* Author: Tobias Nipkow *)

section \<open>Alternative Deletion in Red-Black Trees\<close>

theory RBT_Set2
imports RBT_Set
begin

text \<open>This is a conceptually simpler version of deletion. Instead of the tricky \<open>join\<close>
function this version follows the standard approach of replacing the deleted element
(in function \<open>del\<close>) by the minimal element in its right subtree.\<close>

fun split_min :: "'a rbt \<Rightarrow> 'a \<times> 'a rbt" where
"split_min (Node l (a, _) r) =
  (if l = Leaf then (a,r)
   else let (x,l') = split_min l
        in (x, if color l = Black then baldL l' a r else R l' a r))"

fun del :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"del x Leaf = Leaf" |
"del x (Node l (a, _) r) =
  (case cmp x a of
     LT \<Rightarrow> let l' = del x l in if l \<noteq> Leaf \<and> color l = Black
           then baldL l' a r else R l' a r |
     GT \<Rightarrow> let r' = del x r in if r \<noteq> Leaf \<and> color r = Black
           then baldR l a r' else R l a r' |
     EQ \<Rightarrow> if r = Leaf then l else let (a',r') = split_min r in
           if color r = Black then baldR l a' r' else R l a' r')"

text \<open>The first two \<open>let\<close>s speed up the automatic proof of \<open>inv_del\<close> below.\<close>

definition delete :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

declare Let_def[simp]

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: inorder_baldL sorted_lems split: prod.splits if_splits)

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
by(induction x t rule: del.induct)
  (auto simp: del_list_simps inorder_baldL inorder_baldR split_minD split: prod.splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by (auto simp: delete_def inorder_del inorder_paint)


subsection \<open>Structural invariants\<close>

lemma neq_Red[simp]: "(c \<noteq> Red) = (c = Black)"
by (cases c) auto


subsubsection \<open>Deletion\<close>

lemma inv_split_min: "\<lbrakk> split_min t = (x,t'); t \<noteq> Leaf; invh t; invc t \<rbrakk> \<Longrightarrow>
   invh t' \<and>
   (color t = Red \<longrightarrow> bheight t' = bheight t \<and> invc t') \<and>
   (color t = Black \<longrightarrow> bheight t' = bheight t - 1 \<and> invc2 t')"
apply(induction t arbitrary: x t' rule: split_min.induct)
apply(auto simp: inv_baldR inv_baldL invc2I dest!: neq_LeafD
           split: if_splits prod.splits)
done

text \<open>An automatic proof. It is quite brittle, e.g. inlining the \<open>let\<close>s in @{const del} breaks it.\<close>
lemma inv_del: "\<lbrakk> invh t; invc t \<rbrakk> \<Longrightarrow>
   invh (del x t) \<and>
   (color t = Red \<longrightarrow> bheight (del x t) = bheight t \<and> invc (del x t)) \<and>
   (color t = Black \<longrightarrow> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
apply(induction x t rule: del.induct)
apply(auto simp: inv_baldR inv_baldL invc2I dest!: inv_split_min dest: neq_LeafD
           split!: prod.splits if_splits)
done

text\<open>A structured proof where one can see what is used in each case.\<close>
lemma inv_del2: "\<lbrakk> invh t; invc t \<rbrakk> \<Longrightarrow>
   invh (del x t) \<and>
   (color t = Red \<longrightarrow> bheight (del x t) = bheight t \<and> invc (del x t)) \<and>
   (color t = Black \<longrightarrow> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
proof(induction x t rule: del.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x l a c r)
  note if_split[split del]
  show ?case
  proof cases
    assume "x < a"
    show ?thesis
    proof cases (* For readability; is automated more (below) *)
      assume "l = Leaf" thus ?thesis using \<open>x < a\<close> "2.prems" by(auto)
    next
      assume l: "l \<noteq> Leaf"
      show ?thesis
      proof (cases "color l")
        assume *: "color l = Black"
        hence "bheight l > 0" using l neq_LeafD[of l] by auto
        thus ?thesis using \<open>x < a\<close> "2.IH"(1) "2.prems" inv_baldL[of "del x l"] * l by(auto)
      next
        assume "color l = Red"
        thus ?thesis using \<open>x < a\<close> "2.prems" "2.IH"(1) by(auto)
      qed
    qed
  next (* more automation: *)
    assume "\<not> x < a"
    show ?thesis
    proof cases
      assume "x > a"
      show ?thesis using \<open>a < x\<close> "2.IH"(2) "2.prems" neq_LeafD[of r] inv_baldR[of _ "del x r"]
          by(auto split: if_split)
    
    next
      assume "\<not> x > a"
      show ?thesis using "2.prems" \<open>\<not> x < a\<close> \<open>\<not> x > a\<close>
          by(auto simp: inv_baldR invc2I dest!: inv_split_min dest: neq_LeafD split: prod.split if_split)
    qed
  qed
qed

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete x t)"
by (metis delete_def rbt_def color_paint_Black inv_del invh_paint)

text \<open>Overall correctness:\<close>

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = rbt
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: rbt_def empty_def) 
next
  case 6 thus ?case by (simp add: rbt_insert) 
next
  case 7 thus ?case by (simp add: rbt_delete) 
qed


end
