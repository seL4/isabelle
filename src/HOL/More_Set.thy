
(* Author: Florian Haftmann, TU Muenchen *)

header {* Relating (finite) sets and lists *}

theory More_Set
imports List
begin

subsection {* Functorial operations *}

lemma inter_code [code]:
  "A \<inter> set xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  "A \<inter> List.coset xs = foldr Set.remove xs A"
  by (simp add: inter_project project_def) (simp add: Diff_eq [symmetric] minus_set_foldr)

lemma subtract_code [code]:
  "A - set xs = foldr Set.remove xs A"
  "A - List.coset xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  by (auto simp add: minus_set_foldr)

lemma union_code [code]:
  "set xs \<union> A = foldr insert xs A"
  "List.coset xs \<union> A = List.coset (List.filter (\<lambda>x. x \<notin> A) xs)"
  by (auto simp add: union_set_foldr)

definition Inf :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp, code_abbrev]: "Inf = Complete_Lattices.Inf"

hide_const (open) Inf

definition Sup :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp, code_abbrev]: "Sup = Complete_Lattices.Sup"

hide_const (open) Sup

lemma Inf_code [code]:
  "More_Set.Inf (set xs) = foldr inf xs top"
  "More_Set.Inf (List.coset []) = bot"
  by (simp_all add: Inf_set_foldr)

lemma Sup_sup [code]:
  "More_Set.Sup (set xs) = foldr sup xs bot"
  "More_Set.Sup (List.coset []) = top"
  by (simp_all add: Sup_set_foldr)

(* FIXME: better implement conversion by bisection *)

lemma pred_of_set_fold_sup:
  assumes "finite A"
  shows "pred_of_set A = Finite_Set.fold sup bot (Predicate.single ` A)" (is "?lhs = ?rhs")
proof (rule sym)
  interpret comp_fun_idem "sup :: 'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a Predicate.pred"
    by (fact comp_fun_idem_sup)
  from `finite A` show "?rhs = ?lhs" by (induct A) (auto intro!: pred_eqI)
qed

lemma pred_of_set_set_fold_sup:
  "pred_of_set (set xs) = fold sup (map Predicate.single xs) bot"
proof -
  interpret comp_fun_idem "sup :: 'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a Predicate.pred"
    by (fact comp_fun_idem_sup)
  show ?thesis by (simp add: pred_of_set_fold_sup fold_set_fold [symmetric])
qed

lemma pred_of_set_set_foldr_sup [code]:
  "pred_of_set (set xs) = foldr sup (map Predicate.single xs) bot"
  by (simp add: pred_of_set_set_fold_sup ac_simps foldr_fold fun_eq_iff)

end

