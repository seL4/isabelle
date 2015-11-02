(* Author: Tobias Nipkow *)

section {* Association List Update and Deletion *}

theory AList_Upd_Del
imports Sorted_Less
begin

abbreviation "sorted1 ps \<equiv> sorted(map fst ps)"

text{* Define own @{text map_of} function to avoid pulling in an unknown
amount of lemmas implicitly (via the simpset). *}

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
by (induction ps) (auto simp: sorted_lems sorted_Cons_iff)

lemma map_of_None2: "sorted (map fst ps @ [x]) \<Longrightarrow> map_of ps x = None"
by (induction ps) (auto simp: sorted_lems)

lemma map_of_del_list: "sorted1 ps \<Longrightarrow>
  map_of(del_list x ps) = (map_of ps)(x := None)"
by(induction ps) (auto simp: map_of_None sorted_lems fun_eq_iff)

lemma map_of_sorted_Cons: "sorted (a # map fst ps) \<Longrightarrow> x < a \<Longrightarrow>
   map_of ps x = None"
by (meson less_trans map_of_None sorted_Cons_iff)

lemma map_of_sorted_snoc: "sorted (map fst ps @ [a]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  map_of ps x = None"
by (meson le_less_trans map_of_None2 not_less sorted_snoc_iff)

lemmas map_of_sorteds = map_of_sorted_Cons map_of_sorted_snoc
lemmas map_of_simps = sorted_lems map_of_append map_of_sorteds


subsection \<open>Lemmas for @{const upd_list}\<close>

lemma sorted_upd_list: "sorted1 ps \<Longrightarrow> sorted1 (upd_list x y ps)"
apply(induction ps)
 apply simp
apply(case_tac ps)
 apply auto
done

lemma upd_list_sorted1: "\<lbrakk> sorted (map fst ps @ [a]); x < a \<rbrakk> \<Longrightarrow>
  upd_list x y (ps @ (a,b) # qs) =  upd_list x y ps @ (a,b) # qs"
by(induction ps) (auto simp: sorted_lems)

lemma upd_list_sorted2: "\<lbrakk> sorted (map fst ps @ [a]); a \<le> x \<rbrakk> \<Longrightarrow>
  upd_list x y (ps @ (a,b) # qs) = ps @ upd_list x y ((a,b) # qs)"
by(induction ps) (auto simp: sorted_lems)

lemmas upd_list_simps = sorted_lems upd_list_sorted1 upd_list_sorted2

(*
lemma set_ins_list[simp]: "set (ins_list x xs) = insert x (set xs)"
by(induction xs) auto

lemma distinct_if_sorted: "sorted xs \<Longrightarrow> distinct xs"
apply(induction xs rule: sorted.induct)
apply auto
by (metis in_set_conv_decomp_first less_imp_not_less sorted_mid_iff2)

lemma set_del_list_eq [simp]: "distinct xs ==> set(del_list x xs) = set xs - {x}"
apply(induct xs)
 apply simp
apply simp
apply blast
done
*)


subsection \<open>Lemmas for @{const del_list}\<close>

lemma sorted_del_list: "sorted1 ps \<Longrightarrow> sorted1 (del_list x ps)"
apply(induction ps)
 apply simp
apply(case_tac ps)
apply auto
by (meson order.strict_trans sorted_Cons_iff)

lemma del_list_idem: "x \<notin> set(map fst xs) \<Longrightarrow> del_list x xs = xs"
by (induct xs) auto

lemma del_list_sorted1: "sorted1 (xs @ [(a,b)]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  del_list x (xs @ (a,b) # ys) = xs @ del_list x ((a,b) # ys)"
by (induction xs) (auto simp: sorted_mid_iff2)

lemma del_list_sorted2: "sorted1 (xs @ (a,b) # ys) \<Longrightarrow> x < a \<Longrightarrow>
  del_list x (xs @ (a,b) # ys) = del_list x xs @ (a,b) # ys"
by (induction xs) (fastforce simp: sorted_Cons_iff intro!: del_list_idem)+

lemma del_list_sorted3:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs) \<Longrightarrow> x < b \<Longrightarrow>
  del_list x (xs @ (a,a') # ys @ (b,b') # zs) = del_list x (xs @ (a,a') # ys) @ (b,b') # zs"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted2 ball_Un)

lemma del_list_sorted4:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) \<Longrightarrow> x < c \<Longrightarrow>
  del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) = del_list x (xs @ (a,a') # ys @ (b,b') # zs) @ (c,c') # us"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted3)

lemma del_list_sorted5:
  "sorted1 (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us @ (d,d') # vs) \<Longrightarrow> x < d \<Longrightarrow>
   del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us @ (d,d') # vs) =
   del_list x (xs @ (a,a') # ys @ (b,b') # zs @ (c,c') # us) @ (d,d') # vs" 
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted4)

lemmas del_list_sorted =
  del_list_sorted1 del_list_sorted2 del_list_sorted3 del_list_sorted4 del_list_sorted5

lemmas del_list_simps = sorted_lems del_list_sorted

end
