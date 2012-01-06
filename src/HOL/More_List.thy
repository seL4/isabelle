(* Author:  Florian Haftmann, TU Muenchen *)

header {* Operations on lists beyond the standard List theory *}

theory More_List
imports List
begin

text {* monad operation *}

definition bind :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list" where
  "bind xs f = concat (map f xs)"

lemma bind_simps [simp]:
  "bind [] f = []"
  "bind (x # xs) f = f x @ bind xs f"
  by (simp_all add: bind_def)

end
