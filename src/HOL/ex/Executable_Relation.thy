theory Executable_Relation
imports Main
begin

subsection {* A dedicated type for relations *}

subsubsection {* Definition of the dedicated type for relations *}

typedef 'a rel = "UNIV :: (('a * 'a) set) set"
morphisms set_of_rel rel_of_set by simp

setup_lifting type_definition_rel

lift_definition Rel :: "'a set => ('a * 'a) set => 'a rel" is "\<lambda> X R. Id_on X Un R" .

subsubsection {* Constant definitions on relations *}

hide_const (open) converse relcomp rtrancl Image

lift_definition member :: "'a * 'a => 'a rel => bool" is "Set.member" .

lift_definition converse :: "'a rel => 'a rel" is "Relation.converse" .

lift_definition union :: "'a rel => 'a rel => 'a rel" is "Set.union" .

lift_definition relcomp :: "'a rel => 'a rel => 'a rel" is "Relation.relcomp" .

lift_definition rtrancl :: "'a rel => 'a rel" is "Transitive_Closure.rtrancl" .

lift_definition Image :: "'a rel => 'a set => 'a set" is "Relation.Image" .

subsubsection {* Code generation *}

code_datatype Rel

lemma [code]:
  "member (x, y) (Rel X R) = ((x = y \<and> x : X) \<or> (x, y) : R)"
by transfer auto

lemma [code]:
  "converse (Rel X R) = Rel X (R^-1)"
by transfer auto

lemma [code]:
  "union (Rel X R) (Rel Y S) = Rel (X Un Y) (R Un S)"
by transfer auto

lemma [code]:
   "relcomp (Rel X R) (Rel Y S) = Rel (X Int Y) (Set.filter (%(x, y). y : Y) R Un (Set.filter (%(x, y). x : X) S Un R O S))"
by transfer (auto simp add: Id_on_eqI relcomp.simps)

lemma [code]:
  "rtrancl (Rel X R) = Rel UNIV (R^+)"
apply transfer
apply auto
apply (metis Id_on_iff Un_commute UNIV_I rtrancl_Un_separatorE rtrancl_eq_or_trancl)
by (metis in_rtrancl_UnI trancl_into_rtrancl)

lemma [code]:
  "Image (Rel X R) S = (X Int S) Un (R `` S)"
by transfer auto

quickcheck_generator rel constructors: Rel

lemma
  "member (x, (y :: nat)) (rtrancl (union R S)) \<Longrightarrow> member (x, y) (union (rtrancl R) (rtrancl S))"
quickcheck[exhaustive, expect = counterexample]
oops

end
