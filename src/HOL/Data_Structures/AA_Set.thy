(*
Author: Tobias Nipkow

Added trivial cases to function `adjust' to obviate invariants.
*)

section \<open>AA Tree Implementation of Sets\<close>

theory AA_Set
imports
  Isin2
  Cmp
begin

type_synonym 'a aa_tree = "('a,nat) tree"

fun lvl :: "'a aa_tree \<Rightarrow> nat" where
"lvl Leaf = 0" |
"lvl (Node lv _ _ _) = lv"
(*
fun invar :: "'a aa_tree \<Rightarrow> bool" where
"invar Leaf = True" |
"invar (Node h l a r) =
 (invar l \<and> invar r \<and>
  h = lvl l + 1 \<and> (h = lvl r + 1 \<or> (\<exists>lr b rr. r = Node h lr b rr \<and> h = lvl rr + 1)))"
*)
fun skew :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"skew (Node lva (Node lvb t1 b t2) a t3) =
  (if lva = lvb then Node lva t1 b (Node lva t2 a t3) else Node lva (Node lvb t1 b t2) a t3)" |
"skew t = t"

fun split :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"split (Node lva t1 a (Node lvb t2 b (Node lvc t3 c t4))) =
   (if lva = lvb \<and> lvb = lvc (* lva = lvc suffices *)
    then Node (lva+1) (Node lva t1 a t2) b (Node lva t3 c t4)
    else Node lva t1 a (Node lvb t2 b (Node lvc t3 c t4)))" |
"split t = t"

hide_const (open) insert

fun insert :: "'a::cmp \<Rightarrow> 'a aa_tree \<Rightarrow> 'a aa_tree" where
"insert x Leaf = Node 1 Leaf x Leaf" |
"insert x (Node lv t1 a t2) =
  (case cmp x a of
     LT \<Rightarrow> split (skew (Node lv (insert x t1) a t2)) |
     GT \<Rightarrow> split (skew (Node lv t1 a (insert x t2))) |
     EQ \<Rightarrow> Node lv t1 x t2)"

(* wrong in paper! *)
fun del_max :: "'a aa_tree \<Rightarrow> 'a aa_tree * 'a" where
"del_max (Node lv l a Leaf) = (l,a)" |
"del_max (Node lv l a r) = (let (r',b) = del_max r in (Node lv l a r', b))"

fun sngl :: "'a aa_tree \<Rightarrow> bool" where
"sngl Leaf = False" |
"sngl (Node _ _ _ Leaf) = True" |
"sngl (Node lva _ _ (Node lvb _ _ _)) = (lva > lvb)"

definition adjust :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"adjust t =
 (case t of
  Node lv l x r \<Rightarrow>
   (if lvl l >= lv-1 \<and> lvl r >= lv-1 then t else
    if lvl r < lv-1 \<and> sngl l then skew (Node (lv-1) l x r) else
    if lvl r < lv-1
    then case l of
           Node lva t1 a (Node lvb t2 b t3)
             \<Rightarrow> Node (lvb+1) (Node lva t1 a t2) b (Node (lv-1) t3 x r) |
           _ \<Rightarrow> t (* unreachable *)
    else
    if lvl r < lv then split (Node (lv-1) l x r)
    else
      case r of
        Leaf \<Rightarrow> Leaf (* unreachable *) |
        Node lvb t1 b t4 \<Rightarrow>
          (case t1 of
             Node lva t2 a t3
               \<Rightarrow> Node (lva+1) (Node (lv-1) l x t2) a
                    (split (Node (if sngl t1 then lva-1 else lva) t3 b t4))
           | _ \<Rightarrow> t (* unreachable *))))"

fun delete :: "'a::cmp \<Rightarrow> 'a aa_tree \<Rightarrow> 'a aa_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node lv l a r) =
  (case cmp x a of
     LT \<Rightarrow> adjust (Node lv (delete x l) a r) |
     GT \<Rightarrow> adjust (Node lv l a (delete x r)) |
     EQ \<Rightarrow> (if l = Leaf then r
            else let (l',b) = del_max l in adjust (Node lv l' b r)))"


subsection "Functional Correctness"

subsubsection "Proofs for insert"

lemma inorder_split: "inorder(split t) = inorder t"
by(cases t rule: split.cases) (auto)

lemma inorder_skew: "inorder(skew t) = inorder t"
by(cases t rule: skew.cases) (auto)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps inorder_split inorder_skew)

subsubsection "Proofs for delete"

lemma del_maxD:
  "\<lbrakk> del_max t = (t',x); t \<noteq> Leaf \<rbrakk> \<Longrightarrow> inorder t' @ [x] = inorder t"
by(induction t arbitrary: t' rule: del_max.induct)
  (auto simp: sorted_lems split: prod.splits)

lemma inorder_adjust: "t \<noteq> Leaf \<Longrightarrow> inorder(adjust t) = inorder t"
by(induction t)
  (auto simp: adjust_def inorder_skew inorder_split split: tree.splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_adjust del_maxD split: prod.splits)


subsection "Overall correctness"

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end