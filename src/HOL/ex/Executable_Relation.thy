theory Executable_Relation
imports Main
begin

subsection {* Preliminaries on the raw type of relations *}

definition rel_raw :: "'a set => ('a * 'a) set => ('a * 'a) set"
where
  "rel_raw X R = Id_on X Un R"

lemma member_raw:
  "(x, y) : (rel_raw X R) = ((x = y \<and> x : X) \<or> (x, y) : R)"
unfolding rel_raw_def by auto


lemma Id_raw:
  "Id = rel_raw UNIV {}"
unfolding rel_raw_def by auto

lemma converse_raw:
  "converse (rel_raw X R) = rel_raw X (converse R)"
unfolding rel_raw_def by auto

lemma union_raw:
  "(rel_raw X R) Un (rel_raw Y S) = rel_raw (X Un Y) (R Un S)"
unfolding rel_raw_def by auto

lemma comp_Id_on:
  "Id_on X O R = Set.project (%(x, y). x : X) R"
by (auto intro!: relcompI)

lemma comp_Id_on':
  "R O Id_on X = Set.project (%(x, y). y : X) R"
by auto

lemma project_Id_on:
  "Set.project (%(x, y). x : X) (Id_on Y) = Id_on (X Int Y)"
by auto

lemma relcomp_raw:
  "(rel_raw X R) O (rel_raw Y S) = rel_raw (X Int Y) (Set.project (%(x, y). y : Y) R Un (Set.project (%(x, y). x : X) S Un R O S))"
unfolding rel_raw_def
apply simp
apply (simp add: comp_Id_on)
apply (simp add: project_Id_on)
apply (simp add: comp_Id_on')
apply auto
done

lemma rtrancl_raw:
  "(rel_raw X R)^* = rel_raw UNIV (R^+)"
unfolding rel_raw_def
apply auto
apply (metis Id_on_iff Un_commute iso_tuple_UNIV_I rtrancl_Un_separatorE rtrancl_eq_or_trancl)
by (metis in_rtrancl_UnI trancl_into_rtrancl)

lemma Image_raw:
  "(rel_raw X R) `` S = (X Int S) Un (R `` S)"
unfolding rel_raw_def by auto

subsection {* A dedicated type for relations *}

subsubsection {* Definition of the dedicated type for relations *}

quotient_type 'a rel = "('a * 'a) set" / "(op =)"
morphisms set_of_rel rel_of_set by (metis identity_equivp)

lemma [simp]:
  "rel_of_set (set_of_rel S) = S"
by (rule Quotient3_abs_rep[OF Quotient3_rel])

lemma [simp]:
  "set_of_rel (rel_of_set R) = R"
by (rule Quotient3_rep_abs[OF Quotient3_rel]) (rule refl)

lemmas rel_raw_of_set_eqI[intro!] = arg_cong[where f="rel_of_set"]

quotient_definition rel where "rel :: 'a set => ('a * 'a) set => 'a rel" is rel_raw done

subsubsection {* Constant definitions on relations *}

hide_const (open) converse relcomp rtrancl Image

quotient_definition member :: "'a * 'a => 'a rel => bool" where
  "member" is "Set.member :: 'a * 'a => ('a * 'a) set => bool" done

quotient_definition converse :: "'a rel => 'a rel"
where
  "converse" is "Relation.converse :: ('a * 'a) set => ('a * 'a) set" done

quotient_definition union :: "'a rel => 'a rel => 'a rel"
where
  "union" is "Set.union :: ('a * 'a) set => ('a * 'a) set => ('a * 'a) set" done

quotient_definition relcomp :: "'a rel => 'a rel => 'a rel"
where
  "relcomp" is "Relation.relcomp :: ('a * 'a) set => ('a * 'a) set => ('a * 'a) set" done

quotient_definition rtrancl :: "'a rel => 'a rel"
where
  "rtrancl" is "Transitive_Closure.rtrancl :: ('a * 'a) set => ('a * 'a) set" done

quotient_definition Image :: "'a rel => 'a set => 'a set"
where
  "Image" is "Relation.Image :: ('a * 'a) set => 'a set => 'a set" done

subsubsection {* Code generation *}

code_datatype rel

lemma [code]:
  "member (x, y) (rel X R) = ((x = y \<and> x : X) \<or> (x, y) : R)"
by (lifting member_raw)

lemma [code]:
  "converse (rel X R) = rel X (R^-1)"
by (lifting converse_raw)

lemma [code]:
  "union (rel X R) (rel Y S) = rel (X Un Y) (R Un S)"
by (lifting union_raw)

lemma [code]:
   "relcomp (rel X R) (rel Y S) = rel (X Int Y) (Set.project (%(x, y). y : Y) R Un (Set.project (%(x, y). x : X) S Un R O S))"
by (lifting relcomp_raw)

lemma [code]:
  "rtrancl (rel X R) = rel UNIV (R^+)"
by (lifting rtrancl_raw)

lemma [code]:
  "Image (rel X R) S = (X Int S) Un (R `` S)"
by (lifting Image_raw)

quickcheck_generator rel constructors: rel

lemma
  "member (x, (y :: nat)) (rtrancl (union R S)) \<Longrightarrow> member (x, y) (union (rtrancl R) (rtrancl S))"
quickcheck[exhaustive, expect = counterexample]
oops

end
