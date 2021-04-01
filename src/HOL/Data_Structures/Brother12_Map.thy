(* Author: Tobias Nipkow *)

section \<open>1-2 Brother Tree Implementation of Maps\<close>

theory Brother12_Map
imports
  Brother12_Set
  Map_Specs
begin

fun lookup :: "('a \<times> 'b) bro \<Rightarrow> 'a::linorder \<Rightarrow> 'b option" where
"lookup N0 x = None" |
"lookup (N1 t) x = lookup t x" |
"lookup (N2 l (a,b) r) x =
  (case cmp x a of
     LT \<Rightarrow> lookup l x |
     EQ \<Rightarrow> Some b |
     GT \<Rightarrow> lookup r x)"

locale update = insert
begin

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) bro \<Rightarrow> ('a\<times>'b) bro" where
"upd x y N0 = L2 (x,y)" |
"upd x y (N1 t) = n1 (upd x y t)" |
"upd x y (N2 l (a,b) r) =
  (case cmp x a of
     LT \<Rightarrow> n2 (upd x y l) (a,b) r |
     EQ \<Rightarrow> N2 l (a,y) r |
     GT \<Rightarrow> n2 l (a,b) (upd x y r))"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) bro \<Rightarrow> ('a\<times>'b) bro" where
"update x y t = tree(upd x y t)"

end

context delete
begin

fun del :: "'a::linorder \<Rightarrow> ('a\<times>'b) bro \<Rightarrow> ('a\<times>'b) bro" where
"del _ N0         = N0" |
"del x (N1 t)     = N1 (del x t)" |
"del x (N2 l (a,b) r) =
  (case cmp x a of
     LT \<Rightarrow> n2 (del x l) (a,b) r |
     GT \<Rightarrow> n2 l (a,b) (del x r) |
     EQ \<Rightarrow> (case split_min r of
              None \<Rightarrow> N1 l |
              Some (ab, r') \<Rightarrow> n2 l ab r'))"

definition delete :: "'a::linorder \<Rightarrow> ('a\<times>'b) bro \<Rightarrow> ('a\<times>'b) bro" where
"delete a t = tree (del a t)"

end

subsection "Functional Correctness Proofs"

subsubsection "Proofs for lookup"

lemma lookup_map_of: "t \<in> T h \<Longrightarrow>
  sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by(induction h arbitrary: t) (auto simp: map_of_simps split: option.splits)

subsubsection "Proofs for update"

context update
begin

lemma inorder_upd: "t \<in> T h \<Longrightarrow>
  sorted1(inorder t) \<Longrightarrow> inorder(upd x y t) = upd_list x y (inorder t)"
by(induction h arbitrary: t) (auto simp: upd_list_simps inorder_n1 inorder_n2)

lemma inorder_update: "t \<in> T h \<Longrightarrow>
  sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(simp add: update_def inorder_upd inorder_tree)

end

subsubsection \<open>Proofs for deletion\<close>

context delete
begin

lemma inorder_del:
  "t \<in> T h \<Longrightarrow> sorted1(inorder t) \<Longrightarrow> inorder(del x t) = del_list x (inorder t)"
  apply (induction h arbitrary: t)
  apply (auto simp: del_list_simps inorder_n2)
  apply (auto simp: del_list_simps inorder_n2
     inorder_split_min[OF UnI1] inorder_split_min[OF UnI2] split: option.splits)
  done

lemma inorder_delete:
  "t \<in> T h \<Longrightarrow> sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del inorder_tree)

end


subsection \<open>Invariant Proofs\<close>

subsubsection \<open>Proofs for update\<close>

context update
begin

lemma upd_type:
  "(t \<in> B h \<longrightarrow> upd x y t \<in> Bp h) \<and> (t \<in> U h \<longrightarrow> upd x y t \<in> T h)"
apply(induction h arbitrary: t)
 apply (simp)
apply (fastforce simp: Bp_if_B n2_type dest: n1_type)
done

lemma update_type:
  "t \<in> B h \<Longrightarrow> update x y t \<in> B h \<union> B (Suc h)"
unfolding update_def by (metis upd_type tree_type)

end

subsubsection "Proofs for deletion"

context delete
begin

lemma del_type:
  "t \<in> B h \<Longrightarrow> del x t \<in> T h"
  "t \<in> U h \<Longrightarrow> del x t \<in> Um h"
proof (induction h arbitrary: x t)
  case (Suc h)
  { case 1
    then obtain l a b r where [simp]: "t = N2 l (a,b) r" and
      lr: "l \<in> T h" "r \<in> T h" "l \<in> B h \<or> r \<in> B h" by auto
    have ?case if "x < a"
    proof cases
      assume "l \<in> B h"
      from n2_type3[OF Suc.IH(1)[OF this] lr(2)]
      show ?thesis using \<open>x<a\<close> by(simp)
    next
      assume "l \<notin> B h"
      hence "l \<in> U h" "r \<in> B h" using lr by auto
      from n2_type1[OF Suc.IH(2)[OF this(1)] this(2)]
      show ?thesis using \<open>x<a\<close> by(simp)
    qed
    moreover
    have ?case if "x > a"
    proof cases
      assume "r \<in> B h"
      from n2_type3[OF lr(1) Suc.IH(1)[OF this]]
      show ?thesis using \<open>x>a\<close> by(simp)
    next
      assume "r \<notin> B h"
      hence "l \<in> B h" "r \<in> U h" using lr by auto
      from n2_type2[OF this(1) Suc.IH(2)[OF this(2)]]
      show ?thesis using \<open>x>a\<close> by(simp)
    qed
    moreover
    have ?case if [simp]: "x=a"
    proof (cases "split_min r")
      case None
      show ?thesis
      proof cases
        assume "r \<in> B h"
        with split_minNoneN0[OF this None] lr show ?thesis by(simp)
      next
        assume "r \<notin> B h"
        hence "r \<in> U h" using lr by auto
        with split_minNoneN1[OF this None] lr(3) show ?thesis by (simp)
      qed
    next
      case [simp]: (Some br')
      obtain b r' where [simp]: "br' = (b,r')" by fastforce
      show ?thesis
      proof cases
        assume "r \<in> B h"
        from split_min_type(1)[OF this] n2_type3[OF lr(1)]
        show ?thesis by simp
      next
        assume "r \<notin> B h"
        hence "l \<in> B h" and "r \<in> U h" using lr by auto
        from split_min_type(2)[OF this(2)] n2_type2[OF this(1)]
        show ?thesis by simp
      qed
    qed
    ultimately show ?case by auto                         
  }
  { case 2 with Suc.IH(1) show ?case by auto }
qed auto

lemma delete_type:
  "t \<in> B h \<Longrightarrow> delete x t \<in> B h \<union> B(h-1)"
unfolding delete_def
by (cases h) (simp, metis del_type(1) tree_type Suc_eq_plus1 diff_Suc_1)

end

subsection "Overall correctness"

interpretation Map_by_Ordered
where empty = empty and lookup = lookup and update = update.update
and delete = delete.delete and inorder = inorder and inv = "\<lambda>t. \<exists>h. t \<in> B h"
proof (standard, goal_cases)
  case 2 thus ?case by(auto intro!: lookup_map_of)
next
  case 3 thus ?case by(auto intro!: update.inorder_update)
next
  case 4 thus ?case by(auto intro!: delete.inorder_delete)
next
  case 6 thus ?case using update.update_type by (metis Un_iff)
next
  case 7 thus ?case using delete.delete_type by blast
qed (auto simp: empty_def)

end
