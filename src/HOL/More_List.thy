(* Author:  Florian Haftmann, TU Muenchen *)

header {* Operations on lists beyond the standard List theory *}

theory More_List
imports List
begin

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
