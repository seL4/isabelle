(* Author: Tobias Nipkow *)

section \<open>Association List Update and Deletion\<close>

theory AList_Upd_Del
imports Sorted_Less
begin

abbreviation "sorted1 ps \<equiv> sorted(map fst ps)"

text\<open>Define own @{text map_of} function to avoid pulling in an unknown
amount of lemmas implicitly (via the simpset).\<close>

hide_const (open) map_of

fun map_of :: "('a*'b)list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"map_of [] = (\<lambda>x. None)" |
"map_of ((a,b)#ps) = (\<lambda>x. if x=a then Some b else map_of ps x)"

text \<open>Updating an association list:\<close>

fun upd_list :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) list \<Rightarrow> ('a*'b) list" where
"upd_list x y [] = [(x,y)]" |
"upd_list x y ((a,b)#ps) =
  (if x < a then (x,y)#(a,b)#ps else
  if x = a then (x,y)#ps else (a,b) # upd_list x y ps)"

fun del_list :: "'a::linorder \<Rightarrow> ('a*'b)list \<Rightarrow> ('a*'b)list" where
"del_list x [] = []" |
"del_list x ((a,b)#ps) = (if x = a then ps else (a,b) # del_list x ps)"


subsection \<open>Lemmas for @{const map_of}\<close>

lemma map_of_ins_list: "map_of (upd_list x y ps) = (map_of ps)(x := Some y)"
by(induction ps) auto

lemma map_of_append: "map_of (ps @ qs) x =
  (case map_of ps x of None \<Rightarrow> map_of qs x | Some y \<Rightarrow> Some y)"
by(induction ps)(auto)

lemma map_of_None: "sorted (x # map fst ps) \<Longrightarrow> map_of ps x = None"
by (induction ps) (fastforce simp: sorted_lems sorted_wrt_Cons)+

lemma map_of_None2: "sorted (map fst ps @ [x]) \<Longrightarrow> map_of ps x = None"
by (induction ps) (auto simp: sorted_lems)

lemma map_of_del_list: "sorted1 ps \<Longrightarrow>
  map_of(del_list x ps) = (map_of ps)(x := None)"
by(induction ps) (auto simp: map_of_None sorted_lems fun_eq_iff)

lemma map_of_sorted_Cons: "sorted (a # map fst ps) \<Longrightarrow> x < a \<Longrightarrow>
   map_of ps x = None"
by (simp add: map_of_None sorted_Cons_le)

lemma map_of_sorted_snoc: "sorted (map fst ps @ [a]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  map_of ps x = None"
by (simp add: map_of_None2 sorted_snoc_le)

lemmas map_of_sorteds = map_of_sorted_Cons map_of_sorted_snoc
lemmas map_of_simps = sorted_lems map_of_append map_of_sorteds


subsection \<open>Lemmas for @{const upd_list}\<close>

lemma sorted_upd_list: "sorted1 ps \<Longrightarrow> sorted1 (upd_list x y ps)"
apply(induction ps)
 apply simp
apply(case_tac ps)
 apply auto
done

lemma upd_list_sorted: "sorted1 (ps @ [(a,b)]) \<Longrightarrow>
  upd_list x y (ps @ (a,b) # qs) =
    (if x < a then upd_list x y ps @ (a,b) # qs
    else ps @ upd_list x y ((a,b) # qs))"
by(induction ps) (auto simp: sorted_lems)

text\<open>In principle, @{thm upd_list_sorted} suffices, but the following two
corollaries speed up proofs.\<close>

corollary upd_list_sorted1: "\<lbrakk> sorted (map fst ps @ [a]); x < a \<rbrakk> \<Longrightarrow>
  upd_list x y (ps @ (a,b) # qs) =  upd_list x y ps @ (a,b) # qs"
by (auto simp: upd_list_sorted)

corollary upd_list_sorted2: "\<lbrakk> sorted (map fst ps @ [a]); a \<le> x \<rbrakk> \<Longrightarrow>
  upd_list x y (ps @ (a,b) # qs) = ps @ upd_list x y ((a,b) # qs)"
by (auto simp: upd_list_sorted)

lemmas upd_list_simps = sorted_lems upd_list_sorted1 upd_list_sorted2

text\<open>Splay trees need two additional @{const upd_list} lemmas:\<close>

lemma upd_list_Cons:
  "sorted1 ((x,y) # xs) \<Longrightarrow> upd_list x y xs = (x,y) # xs"
by (induction xs) auto

lemma upd_list_snoc:
  "sorted1 (xs @ [(x,y)]) \<Longrightarrow> upd_list x y xs = xs @ [(x,y)]"
by(induction xs) (auto simp add: sorted_mid_iff2)


subsection \<open>Lemmas for @{const del_list}\<close>

lemma sorted_del_list: "sorted1 ps \<Longrightarrow> sorted1 (del_list x ps)"
apply(induction ps)
 apply simp
apply(case_tac ps)
apply (auto simp: sorted_Cons_le)
done

lemma del_list_idem: "x \<notin> set(map fst xs) \<Longrightarrow> del_list x xs = xs"
by (induct xs) auto

lemma del_list_sorted: "sorted1 (ps @ (a,b) # qs) \<Longrightarrow>
  del_list x (ps @ (a,b) # qs) =
    (if x < a then del_list x ps @ (a,b) # qs
     else ps @ del_list x ((a,b) # qs))"
by(induction ps)
  (fastforce simp: sorted_lems sorted_wrt_Cons intro!: del_list_idem)+

text\<open>In principle, @{thm del_list_sorted} suffices, but the following
corollaries speed up proofs.\<close>

corollary del_list_sorted1: "sorted1 (xs @ (a,b) # ys) \<Longrightarrow> a \<le> x \<Longrightarrow>
  del_list x (xs @ (a,b) # ys) = xs @ del_list x ((a,b) # ys)"
by (auto simp: del_list_sorted)

lemma del_list_sorted2: "sorted1 (xs @ (a,b) # ys) \<Longrightarrow> x < a \<Longrightarrow>
  del_list x (xs @ (a,b) # ys) = del_list x xs @ (a,b) # ys"
by (auto simp: del_list_sorted)

lemma del_list_sorted3:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs) \<Longrightarrow> x < b \<Longrightarrow>
  del_list x (xs @ (a,a') # ys @ (b,b') # zs) = del_list x (xs @ (a,a') # ys) @ (b,b') # zs"
by (auto simp: del_list_sorted sorted_lems)

lemma del_list_sorted4:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) \<Longrightarrow> x < c \<Longrightarrow>
  del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) = del_list x (xs @ (a,a') # ys @ (b,b') # zs) @ (c,c') # us"
by (auto simp: del_list_sorted sorted_lems)

lemma del_list_sorted5:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us @ (d,d') # vs) \<Longrightarrow> x < d \<Longrightarrow>
   del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us @ (d,d') # vs) =
   del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) @ (d,d') # vs" 
by (auto simp: del_list_sorted sorted_lems)

lemmas del_list_simps = sorted_lems
  del_list_sorted1
  del_list_sorted2
  del_list_sorted3
  del_list_sorted4
  del_list_sorted5

text\<open>Splay trees need two additional @{const del_list} lemmas:\<close>

lemma del_list_notin_Cons: "sorted (x # map fst xs) \<Longrightarrow> del_list x xs = xs"
by(induction xs)(fastforce simp: sorted_wrt_Cons)+

lemma del_list_sorted_app:
  "sorted(map fst xs @ [x]) \<Longrightarrow> del_list x (xs @ ys) = xs @ del_list x ys"
by (induction xs) (auto simp: sorted_mid_iff2)

end
