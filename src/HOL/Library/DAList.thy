(*  Title:      HOL/Library/DAList.thy
    Author:     Lukas Bulwahn, TU Muenchen *)

header {* Abstract type of association lists with unique keys *}

theory DAList
imports AList
begin

text {* This was based on some existing fragments in the AFP-Collection framework. *}

subsection {* Preliminaries *}

lemma distinct_map_fst_filter:
   "distinct (map fst xs) ==> distinct (map fst (List.filter P xs))"
by (induct xs) auto

subsection {* Type @{text "('key, 'value) alist" } *}

typedef (open) ('key, 'value) alist = "{xs :: ('key \<times> 'value) list. (distinct o map fst) xs}"
  morphisms impl_of Alist
proof
  show "[] \<in> {xs. (distinct o map fst) xs}" by simp
qed

setup_lifting type_definition_alist

lemma alist_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
by(simp add: impl_of_inject)

lemma alist_eq_iff: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
by(simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of xs))"
using impl_of[of xs] by simp

lemma Alist_impl_of [code abstype]: "Alist (impl_of xs) = xs"
by(rule impl_of_inverse)

subsection {* Primitive operations *}

(* FIXME: improve quotient_definition so that type annotations on the right hand sides can be removed *) 

quotient_definition lookup :: "('key, 'value) alist \<Rightarrow> 'key \<Rightarrow> 'value option"
where "lookup" is "map_of :: ('key * 'value) list \<Rightarrow> 'key \<Rightarrow> 'value option" ..

quotient_definition empty :: "('key, 'value) alist"
where "empty" is "[] :: ('key * 'value) list" by simp

quotient_definition update :: "'key \<Rightarrow> 'value \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
where "update" is "AList.update :: 'key \<Rightarrow> 'value \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list"
by (simp add: distinct_update)

(* FIXME: we use an unoptimised delete operation. *)
quotient_definition delete :: "'key \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
where "delete" is "AList.delete :: 'key \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list"
by (simp add: distinct_delete)

quotient_definition map_entry :: "'key \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
where "map_entry" is "AList.map_entry :: 'key \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list"
by (simp add: distinct_map_entry)

quotient_definition filter :: "('key \<times> 'value \<Rightarrow> bool) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
where "filter" is "List.filter :: ('key \<times> 'value \<Rightarrow> bool) \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list"
by (simp add: distinct_map_fst_filter)

quotient_definition map_default :: "'key => 'value => ('value => 'value) => ('key, 'value) alist => ('key, 'value) alist"
where "map_default" is "AList.map_default :: 'key => 'value => ('value => 'value) => ('key * 'value) list => ('key * 'value) list"
by (simp add: distinct_map_default)

subsection {* Abstract operation properties *}

(* FIXME: to be completed *)

lemma lookup_empty [simp]: "lookup empty k = None"
by(simp add: empty_def lookup_def Alist_inverse)

lemma lookup_delete [simp]: "lookup (delete k al) = (lookup al)(k := None)"
by (simp add: lookup_def delete_def Alist_inverse distinct_delete delete_conv')

subsection {* Further operations *}

subsubsection {* Equality *}

instantiation alist :: (equal, equal) equal begin

definition "HOL.equal (xs :: ('a, 'b) alist) ys == impl_of xs = impl_of ys"

instance
proof
qed (simp add: equal_alist_def impl_of_inject)

end

subsubsection {* Size *}

instantiation alist :: (type, type) size begin

definition "size (al :: ('a, 'b) alist) = length (impl_of al)"

instance ..

end

subsection {* Quickcheck generators *}

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

definition (in term_syntax)
  valterm_empty :: "('key :: typerep, 'value :: typerep) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)"
where
  "valterm_empty = Code_Evaluation.valtermify empty"

definition (in term_syntax)
  valterm_update :: "'key :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  'value :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "valterm_update k v a = Code_Evaluation.valtermify update {\<cdot>} k {\<cdot>} v {\<cdot>}a"

fun (in term_syntax) random_aux_alist 
where
  "random_aux_alist i j = (if i = 0 then Pair valterm_empty else Quickcheck.collapse (Random.select_weight [(i, Quickcheck.random j \<circ>\<rightarrow> (%k. Quickcheck.random j \<circ>\<rightarrow> (%v. random_aux_alist (i - 1) j \<circ>\<rightarrow> (%a. Pair (valterm_update k v a))))), (1, Pair valterm_empty)]))"

instantiation alist :: (random, random) random
begin

definition random_alist
where
  "random_alist i = random_aux_alist i i"
 
instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation alist :: (exhaustive, exhaustive) exhaustive
begin

fun exhaustive_alist :: "(('a, 'b) alist => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "exhaustive_alist f i = (if i = 0 then None else case f empty of Some ts => Some ts | None =>
     exhaustive_alist (%a. Quickcheck_Exhaustive.exhaustive (%k. Quickcheck_Exhaustive.exhaustive (%v. f (update k v a)) (i - 1)) (i - 1)) (i - 1))"

instance ..

end

instantiation alist :: (full_exhaustive, full_exhaustive) full_exhaustive
begin

fun full_exhaustive_alist :: "(('a, 'b) alist * (unit => term) => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "full_exhaustive_alist f i = (if i = 0 then None else case f valterm_empty of Some ts => Some ts | None =>
     full_exhaustive_alist (%a. Quickcheck_Exhaustive.full_exhaustive (%k. Quickcheck_Exhaustive.full_exhaustive (%v. f (valterm_update k v a)) (i - 1)) (i - 1)) (i - 1))"

instance ..

end

hide_const valterm_empty valterm_update random_aux_alist

hide_fact (open) lookup_def empty_def update_def delete_def map_entry_def filter_def map_default_def
hide_const (open) impl_of lookup empty update delete map_entry filter map_default 

end
