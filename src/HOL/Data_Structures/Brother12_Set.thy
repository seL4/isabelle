(* Author: Tobias Nipkow, Daniel Stüwe *)

section \<open>1-2 Brother Tree Implementation of Sets\<close>

theory Brother12_Set
imports
  Cmp
  Set_Specs
  "HOL-Number_Theory.Fib"
begin

subsection \<open>Data Type and Operations\<close>

datatype 'a bro =
  N0 |
  N1 "'a bro" |
  N2 "'a bro" 'a "'a bro" |
  (* auxiliary constructors: *)
  L2 'a |
  N3 "'a bro" 'a "'a bro" 'a "'a bro"

definition empty :: "'a bro" where
"empty = N0"

fun inorder :: "'a bro \<Rightarrow> 'a list" where
"inorder N0 = []" |
"inorder (N1 t) = inorder t" |
"inorder (N2 l a r) = inorder l @ a # inorder r" |
"inorder (L2 a) = [a]" |
"inorder (N3 t1 a1 t2 a2 t3) = inorder t1 @ a1 # inorder t2 @ a2 # inorder t3"

fun isin :: "'a bro \<Rightarrow> 'a::linorder \<Rightarrow> bool" where
"isin N0 x = False" |
"isin (N1 t) x = isin t x" |
"isin (N2 l a r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

fun n1 :: "'a bro \<Rightarrow> 'a bro" where
"n1 (L2 a) = N2 N0 a N0" |
"n1 (N3 t1 a1 t2 a2 t3) = N2 (N2 t1 a1 t2) a2 (N1 t3)" |
"n1 t = N1 t"

hide_const (open) insert

locale insert
begin

fun n2 :: "'a bro \<Rightarrow> 'a \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"n2 (L2 a1) a2 t = N3 N0 a1 N0 a2 t" |
"n2 (N3 t1 a1 t2 a2 t3) a3 (N1 t4) = N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4)" |
"n2 (N3 t1 a1 t2 a2 t3) a3 t4 = N3 (N2 t1 a1 t2) a2 (N1 t3) a3 t4" |
"n2 t1 a1 (L2 a2) = N3 t1 a1 N0 a2 N0" |
"n2 (N1 t1) a1 (N3 t2 a2 t3 a3 t4) = N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4)" |
"n2 t1 a1 (N3 t2 a2 t3 a3 t4) = N3 t1 a1 (N1 t2) a2 (N2 t3 a3 t4)" |
"n2 t1 a t2 = N2 t1 a t2"

fun ins :: "'a::linorder \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"ins x N0 = L2 x" |
"ins x (N1 t) = n1 (ins x t)" |
"ins x (N2 l a r) =
  (case cmp x a of
     LT \<Rightarrow> n2 (ins x l) a r |
     EQ \<Rightarrow> N2 l a r |
     GT \<Rightarrow> n2 l a (ins x r))"

fun tree :: "'a bro \<Rightarrow> 'a bro" where
"tree (L2 a) = N2 N0 a N0" |
"tree (N3 t1 a1 t2 a2 t3) = N2 (N2 t1 a1 t2) a2 (N1 t3)" |
"tree t = t"

definition insert :: "'a::linorder \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"insert x t = tree(ins x t)"

end

locale delete
begin

fun n2 :: "'a bro \<Rightarrow> 'a \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"n2 (N1 t1) a1 (N1 t2) = N1 (N2 t1 a1 t2)" |
"n2 (N1 (N1 t1)) a1 (N2 (N1 t2) a2 (N2 t3 a3 t4)) =
  N1 (N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4))" |
"n2 (N1 (N1 t1)) a1 (N2 (N2 t2 a2 t3) a3 (N1 t4)) =
  N1 (N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4))" |
"n2 (N1 (N1 t1)) a1 (N2 (N2 t2 a2 t3) a3 (N2 t4 a4 t5)) =
  N2 (N2 (N1 t1) a1 (N2 t2 a2 t3)) a3 (N1 (N2 t4 a4 t5))" |
"n2 (N2 (N1 t1) a1 (N2 t2 a2 t3)) a3 (N1 (N1 t4)) =
  N1 (N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4))" |
"n2 (N2 (N2 t1 a1 t2) a2 (N1 t3)) a3 (N1 (N1 t4)) =
  N1 (N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4))" |
"n2 (N2 (N2 t1 a1 t2) a2 (N2 t3 a3 t4)) a5 (N1 (N1 t5)) =
  N2 (N1 (N2 t1 a1 t2)) a2 (N2 (N2 t3 a3 t4) a5 (N1 t5))" |
"n2 t1 a1 t2 = N2 t1 a1 t2"

fun split_min :: "'a bro \<Rightarrow> ('a \<times> 'a bro) option" where
"split_min N0 = None" |
"split_min (N1 t) =
  (case split_min t of
     None \<Rightarrow> None |
     Some (a, t') \<Rightarrow> Some (a, N1 t'))" |
"split_min (N2 t1 a t2) =
  (case split_min t1 of
     None \<Rightarrow> Some (a, N1 t2) |
     Some (b, t1') \<Rightarrow> Some (b, n2 t1' a t2))"

fun del :: "'a::linorder \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"del _ N0         = N0" |
"del x (N1 t)     = N1 (del x t)" |
"del x (N2 l a r) =
  (case cmp x a of
     LT \<Rightarrow> n2 (del x l) a r |
     GT \<Rightarrow> n2 l a (del x r) |
     EQ \<Rightarrow> (case split_min r of
              None \<Rightarrow> N1 l |
              Some (b, r') \<Rightarrow> n2 l b r'))"

fun tree :: "'a bro \<Rightarrow> 'a bro" where
"tree (N1 t) = t" |
"tree t = t"

definition delete :: "'a::linorder \<Rightarrow> 'a bro \<Rightarrow> 'a bro" where
"delete a t = tree (del a t)"

end

subsection \<open>Invariants\<close>

fun B :: "nat \<Rightarrow> 'a bro set"
and U :: "nat \<Rightarrow> 'a bro set" where
"B 0 = {N0}" |
"B (Suc h) = { N2 t1 a t2 | t1 a t2. 
  t1 \<in> B h \<union> U h \<and> t2 \<in> B h \<or> t1 \<in> B h \<and> t2 \<in> B h \<union> U h}" |
"U 0 = {}" |
"U (Suc h) = N1 ` B h"

abbreviation "T h \<equiv> B h \<union> U h"

fun Bp :: "nat \<Rightarrow> 'a bro set" where
"Bp 0 = B 0 \<union> L2 ` UNIV" |
"Bp (Suc 0) = B (Suc 0) \<union> {N3 N0 a N0 b N0|a b. True}" |
"Bp (Suc(Suc h)) = B (Suc(Suc h)) \<union>
  {N3 t1 a t2 b t3 | t1 a t2 b t3. t1 \<in> B (Suc h) \<and> t2 \<in> U (Suc h) \<and> t3 \<in> B (Suc h)}"

fun Um :: "nat \<Rightarrow> 'a bro set" where
"Um 0 = {}" |
"Um (Suc h) = N1 ` T h"


subsection "Functional Correctness Proofs"

subsubsection "Proofs for isin"

lemma isin_set:
  "t \<in> T h \<Longrightarrow> sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set(inorder t))"
by(induction h arbitrary: t) (fastforce simp: isin_simps split: if_splits)+

subsubsection "Proofs for insertion"

lemma inorder_n1: "inorder(n1 t) = inorder t"
by(cases t rule: n1.cases) (auto simp: sorted_lems)

context insert
begin

lemma inorder_n2: "inorder(n2 l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: n2.cases) (auto simp: sorted_lems)

lemma inorder_tree: "inorder(tree t) = inorder t"
by(cases t) auto

lemma inorder_ins: "t \<in> T h \<Longrightarrow>
  sorted(inorder t) \<Longrightarrow> inorder(ins a t) = ins_list a (inorder t)"
by(induction h arbitrary: t) (auto simp: ins_list_simps inorder_n1 inorder_n2)

lemma inorder_insert: "t \<in> T h \<Longrightarrow>
  sorted(inorder t) \<Longrightarrow> inorder(insert a t) = ins_list a (inorder t)"
by(simp add: insert_def inorder_ins inorder_tree)

end

subsubsection \<open>Proofs for deletion\<close>

context delete
begin

lemma inorder_tree: "inorder(tree t) = inorder t"
by(cases t) auto

lemma inorder_n2: "inorder(n2 l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: n2.cases) (auto)

lemma inorder_split_min:
  "t \<in> T h \<Longrightarrow> (split_min t = None \<longleftrightarrow> inorder t = []) \<and>
  (split_min t = Some(a,t') \<longrightarrow> inorder t = a # inorder t')"
by(induction h arbitrary: t a t') (auto simp: inorder_n2 split: option.splits)

lemma inorder_del:
  "t \<in> T h \<Longrightarrow> sorted(inorder t) \<Longrightarrow> inorder(del x t) = del_list x (inorder t)"
  apply (induction h arbitrary: t) 
  apply (auto simp: del_list_simps inorder_n2 split: option.splits)
  apply (auto simp: del_list_simps inorder_n2
     inorder_split_min[OF UnI1] inorder_split_min[OF UnI2] split: option.splits)
  done

lemma inorder_delete:
  "t \<in> T h \<Longrightarrow> sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del inorder_tree)

end


subsection \<open>Invariant Proofs\<close>

subsubsection \<open>Proofs for insertion\<close>

lemma n1_type: "t \<in> Bp h \<Longrightarrow> n1 t \<in> T (Suc h)"
by(cases h rule: Bp.cases) auto

context insert
begin

lemma tree_type: "t \<in> Bp h \<Longrightarrow> tree t \<in> B h \<union> B (Suc h)"
by(cases h rule: Bp.cases) auto

lemma n2_type:
  "(t1 \<in> Bp h \<and> t2 \<in> T h \<longrightarrow> n2 t1 a t2 \<in> Bp (Suc h)) \<and>
   (t1 \<in> T h \<and> t2 \<in> Bp h \<longrightarrow> n2 t1 a t2 \<in> Bp (Suc h))"
apply(cases h rule: Bp.cases)
apply (auto)[2]
apply(rule conjI impI | erule conjE exE imageE | simp | erule disjE)+
done

lemma Bp_if_B: "t \<in> B h \<Longrightarrow> t \<in> Bp h"
by (cases h rule: Bp.cases) simp_all

text\<open>An automatic proof:\<close>

lemma
  "(t \<in> B h \<longrightarrow> ins x t \<in> Bp h) \<and> (t \<in> U h \<longrightarrow> ins x t \<in> T h)"
apply(induction h arbitrary: t)
 apply (simp)
apply (fastforce simp: Bp_if_B n2_type dest: n1_type)
done

text\<open>A detailed proof:\<close>

lemma ins_type:
shows "t \<in> B h \<Longrightarrow> ins x t \<in> Bp h" and "t \<in> U h \<Longrightarrow> ins x t \<in> T h"
proof(induction h arbitrary: t)
  case 0
  { case 1 thus ?case by simp
  next
    case 2 thus ?case by simp }
next
  case (Suc h)
  { case 1
    then obtain t1 a t2 where [simp]: "t = N2 t1 a t2" and
      t1: "t1 \<in> T h" and t2: "t2 \<in> T h" and t12: "t1 \<in> B h \<or> t2 \<in> B h"
      by auto
    have ?case if "x < a"
    proof -
      have "n2 (ins x t1) a t2 \<in> Bp (Suc h)"
      proof cases
        assume "t1 \<in> B h"
        with t2 show ?thesis by (simp add: Suc.IH(1) n2_type)
      next
        assume "t1 \<notin> B h"
        hence 1: "t1 \<in> U h" and 2: "t2 \<in> B h" using t1 t12 by auto
        show ?thesis by (metis Suc.IH(2)[OF 1] Bp_if_B[OF 2] n2_type)
      qed
      with \<open>x < a\<close> show ?case by simp
    qed
    moreover
    have ?case if "a < x"
    proof -
      have "n2 t1 a (ins x t2) \<in> Bp (Suc h)"
      proof cases
        assume "t2 \<in> B h"
        with t1 show ?thesis by (simp add: Suc.IH(1) n2_type)
      next
        assume "t2 \<notin> B h"
        hence 1: "t1 \<in> B h" and 2: "t2 \<in> U h" using t2 t12 by auto
        show ?thesis by (metis Bp_if_B[OF 1] Suc.IH(2)[OF 2] n2_type)
      qed
      with \<open>a < x\<close> show ?case by simp
    qed
    moreover
    have ?case if "x = a"
    proof -
      from 1 have "t \<in> Bp (Suc h)" by(rule Bp_if_B)
      thus "?case" using \<open>x = a\<close> by simp
    qed
    ultimately show ?case by auto
  next
    case 2 thus ?case using Suc(1) n1_type by fastforce }
qed

lemma insert_type:
  "t \<in> B h \<Longrightarrow> insert x t \<in> B h \<union> B (Suc h)"
unfolding insert_def by (metis ins_type(1) tree_type)

end

subsubsection "Proofs for deletion"

lemma B_simps[simp]: 
  "N1 t \<in> B h = False"
  "L2 y \<in> B h = False"
  "(N3 t1 a1 t2 a2 t3) \<in> B h = False"
  "N0 \<in> B h \<longleftrightarrow> h = 0"
by (cases h, auto)+

context delete
begin

lemma n2_type1:
  "\<lbrakk>t1 \<in> Um h; t2 \<in> B h\<rbrakk> \<Longrightarrow> n2 t1 a t2 \<in> T (Suc h)"
apply(cases h rule: Bp.cases)
apply auto[2]
apply(erule exE bexE conjE imageE | simp | erule disjE)+
done

lemma n2_type2:
  "\<lbrakk>t1 \<in> B h ; t2 \<in> Um h \<rbrakk> \<Longrightarrow> n2 t1 a t2 \<in> T (Suc h)"
apply(cases h rule: Bp.cases)
apply auto[2]
apply(erule exE bexE conjE imageE | simp | erule disjE)+
done

lemma n2_type3:
  "\<lbrakk>t1 \<in> T h ; t2 \<in> T h \<rbrakk> \<Longrightarrow> n2 t1 a t2 \<in> T (Suc h)"
apply(cases h rule: Bp.cases)
apply auto[2]
apply(erule exE bexE conjE imageE | simp | erule disjE)+
done

lemma split_minNoneN0: "\<lbrakk>t \<in> B h; split_min t = None\<rbrakk> \<Longrightarrow>  t = N0"
by (cases t) (auto split: option.splits)

lemma split_minNoneN1 : "\<lbrakk>t \<in> U h; split_min t = None\<rbrakk> \<Longrightarrow> t = N1 N0"
by (cases h) (auto simp: split_minNoneN0  split: option.splits)

lemma split_min_type:
  "t \<in> B h \<Longrightarrow> split_min t = Some (a, t') \<Longrightarrow> t' \<in> T h"
  "t \<in> U h \<Longrightarrow> split_min t = Some (a, t') \<Longrightarrow> t' \<in> Um h"
proof (induction h arbitrary: t a t')
  case (Suc h)
  { case 1
    then obtain t1 a t2 where [simp]: "t = N2 t1 a t2" and
      t12: "t1 \<in> T h" "t2 \<in> T h" "t1 \<in> B h \<or> t2 \<in> B h"
      by auto
    show ?case
    proof (cases "split_min t1")
      case None
      show ?thesis
      proof cases
        assume "t1 \<in> B h"
        with split_minNoneN0[OF this None] 1 show ?thesis by(auto)
      next
        assume "t1 \<notin> B h"
        thus ?thesis using 1 None by (auto)
      qed
    next
      case [simp]: (Some bt')
      obtain b t1' where [simp]: "bt' = (b,t1')" by fastforce
      show ?thesis
      proof cases
        assume "t1 \<in> B h"
        from Suc.IH(1)[OF this] 1 have "t1' \<in> T h" by simp
        from n2_type3[OF this t12(2)] 1 show ?thesis by auto
      next
        assume "t1 \<notin> B h"
        hence t1: "t1 \<in> U h" and t2: "t2 \<in> B h" using t12 by auto
        from Suc.IH(2)[OF t1] have "t1' \<in> Um h" by simp
        from n2_type1[OF this t2] 1 show ?thesis by auto
      qed
    qed
  }
  { case 2
    then obtain t1 where [simp]: "t = N1 t1" and t1: "t1 \<in> B h" by auto
    show ?case
    proof (cases "split_min t1")
      case None
      with split_minNoneN0[OF t1 None] 2 show ?thesis by(auto)
    next
      case [simp]: (Some bt')
      obtain b t1' where [simp]: "bt' = (b,t1')" by fastforce
      from Suc.IH(1)[OF t1] have "t1' \<in> T h" by simp
      thus ?thesis using 2 by auto
    qed
  }
qed auto

lemma del_type:
  "t \<in> B h \<Longrightarrow> del x t \<in> T h"
  "t \<in> U h \<Longrightarrow> del x t \<in> Um h"
proof (induction h arbitrary: x t)
  case (Suc h)
  { case 1
    then obtain l a r where [simp]: "t = N2 l a r" and
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

lemma tree_type: "t \<in> T (h+1) \<Longrightarrow> tree t \<in> B (h+1) \<union> B h"
by(auto)

lemma delete_type: "t \<in> B h \<Longrightarrow> delete x t \<in> B h \<union> B(h-1)"
unfolding delete_def
by (cases h) (simp, metis del_type(1) tree_type Suc_eq_plus1 diff_Suc_1)

end


subsection "Overall correctness"

interpretation Set_by_Ordered
where empty = empty and isin = isin and insert = insert.insert
and delete = delete.delete and inorder = inorder and inv = "\<lambda>t. \<exists>h. t \<in> B h"
proof (standard, goal_cases)
  case 2 thus ?case by(auto intro!: isin_set)
next
  case 3 thus ?case by(auto intro!: insert.inorder_insert)
next
  case 4 thus ?case by(auto intro!: delete.inorder_delete)
next
  case 6 thus ?case using insert.insert_type by blast
next
  case 7 thus ?case using delete.delete_type by blast
qed (auto simp: empty_def)


subsection \<open>Height-Size Relation\<close>

text \<open>By Daniel St\"uwe\<close>

fun fib_tree :: "nat \<Rightarrow> unit bro" where
  "fib_tree 0 = N0" 
| "fib_tree (Suc 0) = N2 N0 () N0"
| "fib_tree (Suc(Suc h)) = N2 (fib_tree (h+1)) () (N1 (fib_tree h))"

fun fib' :: "nat \<Rightarrow> nat" where
  "fib' 0 = 0" 
| "fib' (Suc 0) = 1"
| "fib' (Suc(Suc h)) = 1 + fib' (Suc h) + fib' h"

fun size :: "'a bro \<Rightarrow> nat" where
  "size N0 = 0" 
| "size (N1 t) = size t"
| "size (N2 t1 _ t2) = 1 + size t1 + size t2"

lemma fib_tree_B: "fib_tree h \<in> B h"
by (induction h rule: fib_tree.induct) auto

declare [[names_short]]

lemma size_fib': "size (fib_tree h) = fib' h"
by (induction h rule: fib_tree.induct) auto

lemma fibfib: "fib' h + 1 = fib (Suc(Suc h))"
by (induction h rule: fib_tree.induct) auto

lemma B_N2_cases[consumes 1]:
assumes "N2 t1 a t2 \<in> B (Suc n)"
obtains 
  (BB) "t1 \<in> B n" and "t2 \<in> B n" |
  (UB) "t1 \<in> U n" and "t2 \<in> B n" |
  (BU) "t1 \<in> B n" and "t2 \<in> U n"
using assms by auto

lemma size_bounded: "t \<in> B h \<Longrightarrow> size t \<ge> size (fib_tree h)"
unfolding size_fib' proof (induction h arbitrary: t rule: fib'.induct)
case (3 h t')
  note main = 3
  then obtain t1 a t2 where t': "t' = N2 t1 a t2" by auto
  with main have "N2 t1 a t2 \<in> B (Suc (Suc h))" by auto
  thus ?case proof (cases rule: B_N2_cases)
    case BB
    then obtain x y z where t2: "t2 = N2 x y z \<or> t2 = N2 z y x" "x \<in> B h" by auto
    show ?thesis unfolding t' using main(1)[OF BB(1)] main(2)[OF t2(2)] t2(1) by auto
  next
    case UB
    then obtain t11 where t1: "t1 = N1 t11" "t11 \<in> B h" by auto
    show ?thesis unfolding t' t1(1) using main(2)[OF t1(2)] main(1)[OF UB(2)] by simp
  next
    case BU
    then obtain t22 where t2: "t2 = N1 t22" "t22 \<in> B h" by auto
    show ?thesis unfolding t' t2(1) using main(2)[OF t2(2)] main(1)[OF BU(1)] by simp
  qed
qed auto

theorem "t \<in> B h \<Longrightarrow> fib (h + 2) \<le> size t + 1"
using size_bounded
by (simp add: size_fib' fibfib[symmetric] del: fib.simps)

end
