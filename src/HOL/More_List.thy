(* Author:  Florian Haftmann, TU Muenchen *)

header {* Operations on lists beyond the standard List theory *}

theory More_List
imports List
begin

text {* Fold combinator with canonical argument order *}

primrec fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
    "fold f [] = id"
  | "fold f (x # xs) = fold f xs \<circ> f x"

lemma foldl_fold:
  "foldl f s xs = fold (\<lambda>x s. f s x) xs s"
  by (induct xs arbitrary: s) simp_all

lemma foldr_fold_rev:
  "foldr f xs = fold f (rev xs)"
  by (simp add: foldr_foldl foldl_fold fun_eq_iff)

lemma fold_rev_conv [code_unfold]:
  "fold f (rev xs) = foldr f xs"
  by (simp add: foldr_fold_rev)
  
lemma fold_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> fold f xs a = fold g ys b"
  by (induct ys arbitrary: a b xs) simp_all

lemma fold_id:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = id"
  shows "fold f xs = id"
  using assms by (induct xs) simp_all

lemma fold_commute:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> h \<circ> g x = f x \<circ> h"
  shows "h \<circ> fold g xs = fold f xs \<circ> h"
  using assms by (induct xs) (simp_all add: fun_eq_iff)

lemma fold_commute_apply:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> h \<circ> g x = f x \<circ> h"
  shows "h (fold g xs s) = fold f xs (h s)"
proof -
  from assms have "h \<circ> fold g xs = fold f xs \<circ> h" by (rule fold_commute)
  then show ?thesis by (simp add: fun_eq_iff)
qed

lemma fold_invariant: 
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> Q x" and "P s"
    and "\<And>x s. Q x \<Longrightarrow> P s \<Longrightarrow> P (f x s)"
  shows "P (fold f xs s)"
  using assms by (induct xs arbitrary: s) simp_all

lemma fold_weak_invariant:
  assumes "P s"
    and "\<And>s x. x \<in> set xs \<Longrightarrow> P s \<Longrightarrow> P (f x s)"
  shows "P (fold f xs s)"
  using assms by (induct xs arbitrary: s) simp_all

lemma fold_append [simp]:
  "fold f (xs @ ys) = fold f ys \<circ> fold f xs"
  by (induct xs) simp_all

lemma fold_map [code_unfold]:
  "fold g (map f xs) = fold (g o f) xs"
  by (induct xs) simp_all

lemma fold_remove1_split:
  assumes f: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x \<circ> f y = f y \<circ> f x"
    and x: "x \<in> set xs"
  shows "fold f xs = fold f (remove1 x xs) \<circ> f x"
  using assms by (induct xs) (auto simp add: o_assoc [symmetric])

lemma fold_rev:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f y \<circ> f x = f x \<circ> f y"
  shows "fold f (rev xs) = fold f xs"
using assms by (induct xs) (simp_all add: fold_commute_apply fun_eq_iff)

lemma foldr_fold:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f y \<circ> f x = f x \<circ> f y"
  shows "foldr f xs = fold f xs"
  using assms unfolding foldr_fold_rev by (rule fold_rev)

lemma fold_Cons_rev:
  "fold Cons xs = append (rev xs)"
  by (induct xs) simp_all

lemma rev_conv_fold [code]:
  "rev xs = fold Cons xs []"
  by (simp add: fold_Cons_rev)

lemma fold_append_concat_rev:
  "fold append xss = append (concat (rev xss))"
  by (induct xss) simp_all

lemma concat_conv_foldr [code]:
  "concat xss = foldr append xss []"
  by (simp add: fold_append_concat_rev foldr_fold_rev)

lemma fold_plus_listsum_rev:
  "fold plus xs = plus (listsum (rev xs))"
  by (induct xs) (simp_all add: add.assoc)

lemma (in monoid_add) listsum_conv_fold [code]:
  "listsum xs = fold (\<lambda>x y. y + x) xs 0"
  by (auto simp add: listsum_foldl foldl_fold fun_eq_iff)

lemma (in linorder) sort_key_conv_fold:
  assumes "inj_on f (set xs)"
  shows "sort_key f xs = fold (insort_key f) xs []"
proof -
  have "fold (insort_key f) (rev xs) = fold (insort_key f) xs"
  proof (rule fold_rev, rule ext)
    fix zs
    fix x y
    assume "x \<in> set xs" "y \<in> set xs"
    with assms have *: "f y = f x \<Longrightarrow> y = x" by (auto dest: inj_onD)
    have **: "x = y \<longleftrightarrow> y = x" by auto
    show "(insort_key f y \<circ> insort_key f x) zs = (insort_key f x \<circ> insort_key f y) zs"
      by (induct zs) (auto intro: * simp add: **)
  qed
  then show ?thesis by (simp add: sort_key_def foldr_fold_rev)
qed

lemma (in linorder) sort_conv_fold:
  "sort xs = fold insort xs []"
  by (rule sort_key_conv_fold) simp


text {* @{const Finite_Set.fold} and @{const fold} *}

lemma (in comp_fun_commute) fold_set_fold_remdups:
  "Finite_Set.fold f y (set xs) = fold f (remdups xs) y"
  by (rule sym, induct xs arbitrary: y) (simp_all add: fold_fun_comm insert_absorb)

lemma (in comp_fun_idem) fold_set_fold:
  "Finite_Set.fold f y (set xs) = fold f xs y"
  by (rule sym, induct xs arbitrary: y) (simp_all add: fold_fun_comm)

lemma (in ab_semigroup_idem_mult) fold1_set_fold:
  assumes "xs \<noteq> []"
  shows "Finite_Set.fold1 times (set xs) = fold times (tl xs) (hd xs)"
proof -
  interpret comp_fun_idem times by (fact comp_fun_idem)
  from assms obtain y ys where xs: "xs = y # ys"
    by (cases xs) auto
  show ?thesis
  proof (cases "set ys = {}")
    case True with xs show ?thesis by simp
  next
    case False
    then have "fold1 times (insert y (set ys)) = Finite_Set.fold times y (set ys)"
      by (simp only: finite_set fold1_eq_fold_idem)
    with xs show ?thesis by (simp add: fold_set_fold mult_commute)
  qed
qed

lemma (in lattice) Inf_fin_set_fold:
  "Inf_fin (set (x # xs)) = fold inf xs x"
proof -
  interpret ab_semigroup_idem_mult "inf :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact ab_semigroup_idem_mult_inf)
  show ?thesis
    by (simp add: Inf_fin_def fold1_set_fold del: set.simps)
qed

lemma (in lattice) Inf_fin_set_foldr [code_unfold]:
  "Inf_fin (set (x # xs)) = foldr inf xs x"
  by (simp add: Inf_fin_set_fold ac_simps foldr_fold fun_eq_iff del: set.simps)

lemma (in lattice) Sup_fin_set_fold:
  "Sup_fin (set (x # xs)) = fold sup xs x"
proof -
  interpret ab_semigroup_idem_mult "sup :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact ab_semigroup_idem_mult_sup)
  show ?thesis
    by (simp add: Sup_fin_def fold1_set_fold del: set.simps)
qed

lemma (in lattice) Sup_fin_set_foldr [code_unfold]:
  "Sup_fin (set (x # xs)) = foldr sup xs x"
  by (simp add: Sup_fin_set_fold ac_simps foldr_fold fun_eq_iff del: set.simps)

lemma (in linorder) Min_fin_set_fold:
  "Min (set (x # xs)) = fold min xs x"
proof -
  interpret ab_semigroup_idem_mult "min :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact ab_semigroup_idem_mult_min)
  show ?thesis
    by (simp add: Min_def fold1_set_fold del: set.simps)
qed

lemma (in linorder) Min_fin_set_foldr [code_unfold]:
  "Min (set (x # xs)) = foldr min xs x"
  by (simp add: Min_fin_set_fold ac_simps foldr_fold fun_eq_iff del: set.simps)

lemma (in linorder) Max_fin_set_fold:
  "Max (set (x # xs)) = fold max xs x"
proof -
  interpret ab_semigroup_idem_mult "max :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact ab_semigroup_idem_mult_max)
  show ?thesis
    by (simp add: Max_def fold1_set_fold del: set.simps)
qed

lemma (in linorder) Max_fin_set_foldr [code_unfold]:
  "Max (set (x # xs)) = foldr max xs x"
  by (simp add: Max_fin_set_fold ac_simps foldr_fold fun_eq_iff del: set.simps)

lemma (in complete_lattice) Inf_set_fold:
  "Inf (set xs) = fold inf xs top"
proof -
  interpret comp_fun_idem "inf :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact comp_fun_idem_inf)
  show ?thesis by (simp add: Inf_fold_inf fold_set_fold inf_commute)
qed

lemma (in complete_lattice) Inf_set_foldr [code_unfold]:
  "Inf (set xs) = foldr inf xs top"
  by (simp add: Inf_set_fold ac_simps foldr_fold fun_eq_iff)

lemma (in complete_lattice) Sup_set_fold:
  "Sup (set xs) = fold sup xs bot"
proof -
  interpret comp_fun_idem "sup :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact comp_fun_idem_sup)
  show ?thesis by (simp add: Sup_fold_sup fold_set_fold sup_commute)
qed

lemma (in complete_lattice) Sup_set_foldr [code_unfold]:
  "Sup (set xs) = foldr sup xs bot"
  by (simp add: Sup_set_fold ac_simps foldr_fold fun_eq_iff)

lemma (in complete_lattice) INFI_set_fold:
  "INFI (set xs) f = fold (inf \<circ> f) xs top"
  unfolding INF_def set_map [symmetric] Inf_set_fold fold_map ..

lemma (in complete_lattice) SUPR_set_fold:
  "SUPR (set xs) f = fold (sup \<circ> f) xs bot"
  unfolding SUP_def set_map [symmetric] Sup_set_fold fold_map ..


text {* @{text nth_map} *}

definition nth_map :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "nth_map n f xs = (if n < length xs then
       take n xs @ [f (xs ! n)] @ drop (Suc n) xs
     else xs)"

lemma nth_map_id:
  "n \<ge> length xs \<Longrightarrow> nth_map n f xs = xs"
  by (simp add: nth_map_def)

lemma nth_map_unfold:
  "n < length xs \<Longrightarrow> nth_map n f xs = take n xs @ [f (xs ! n)] @ drop (Suc n) xs"
  by (simp add: nth_map_def)

lemma nth_map_Nil [simp]:
  "nth_map n f [] = []"
  by (simp add: nth_map_def)

lemma nth_map_zero [simp]:
  "nth_map 0 f (x # xs) = f x # xs"
  by (simp add: nth_map_def)

lemma nth_map_Suc [simp]:
  "nth_map (Suc n) f (x # xs) = x # nth_map n f xs"
  by (simp add: nth_map_def)


text {* monad operation *}

definition bind :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list" where
  "bind xs f = concat (map f xs)"

lemma bind_simps [simp]:
  "bind [] f = []"
  "bind (x # xs) f = f x @ bind xs f"
  by (simp_all add: bind_def)

end
