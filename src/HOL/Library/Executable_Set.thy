(*  Title:      HOL/Library/Executable_Set.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of finite sets by lists *}

theory Executable_Set
imports Main
begin

subsection {* Definitional rewrites *}

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset = op \<le>"

declare subset_def [symmetric, code unfold]

lemma [code]: "subset A B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  unfolding subset_def subset_eq ..

definition is_empty :: "'a set \<Rightarrow> bool" where
  "is_empty A \<longleftrightarrow> A = {}"

definition eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [code del]: "eq_set = op ="

lemma [code]: "eq_set A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  unfolding eq_set_def by auto

(* FIXME allow for Stefan's code generator:
declare set_eq_subset[code unfold]
*)

lemma [code]:
  "a \<in> A \<longleftrightarrow> (\<exists>x\<in>A. x = a)"
  unfolding bex_triv_one_point1 ..

definition filter_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "filter_set P xs = {x\<in>xs. P x}"

declare filter_set_def[symmetric, code unfold] 


subsection {* Operations on lists *}

subsubsection {* Basic definitions *}

definition
  flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f a b = f b a"

definition
  member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "member xs x \<longleftrightarrow> x \<in> set xs"

definition
  insertl :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insertl x xs = (if member xs x then xs else x#xs)"

lemma [code target: List]: "member [] y \<longleftrightarrow> False"
  and [code target: List]: "member (x#xs) y \<longleftrightarrow> y = x \<or> member xs y"
  unfolding member_def by (induct xs) simp_all

fun
  drop_first :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_first f [] = []"
| "drop_first f (x#xs) = (if f x then xs else x # drop_first f xs)"
declare drop_first.simps [code del]
declare drop_first.simps [code target: List]

declare remove1.simps [code del]
lemma [code target: List]:
  "remove1 x xs = (if member xs x then drop_first (\<lambda>y. y = x) xs else xs)"
proof (cases "member xs x")
  case False thus ?thesis unfolding member_def by (induct xs) auto
next
  case True
  have "remove1 x xs = drop_first (\<lambda>y. y = x) xs" by (induct xs) simp_all
  with True show ?thesis by simp
qed

lemma member_nil [simp]:
  "member [] = (\<lambda>x. False)"
proof (rule ext)
  fix x
  show "member [] x = False" unfolding member_def by simp
qed

lemma member_insertl [simp]:
  "x \<in> set (insertl x xs)"
  unfolding insertl_def member_def mem_iff by simp

lemma insertl_member [simp]:
  fixes xs x
  assumes member: "member xs x"
  shows "insertl x xs = xs"
  using member unfolding insertl_def by simp

lemma insertl_not_member [simp]:
  fixes xs x
  assumes member: "\<not> (member xs x)"
  shows "insertl x xs = x # xs"
  using member unfolding insertl_def by simp

lemma foldr_remove1_empty [simp]:
  "foldr remove1 xs [] = []"
  by (induct xs) simp_all


subsubsection {* Derived definitions *}

function unionl :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "unionl [] ys = ys"
| "unionl xs ys = foldr insertl xs ys"
by pat_completeness auto
termination by lexicographic_order

lemmas unionl_eq = unionl.simps(2)

function intersect :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersect [] ys = []"
| "intersect xs [] = []"
| "intersect xs ys = filter (member xs) ys"
by pat_completeness auto
termination by lexicographic_order

lemmas intersect_eq = intersect.simps(3)

function subtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "subtract [] ys = ys"
| "subtract xs [] = []"
| "subtract xs ys = foldr remove1 xs ys"
by pat_completeness auto
termination by lexicographic_order

lemmas subtract_eq = subtract.simps(3)

function map_distinct :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_distinct f [] = []"
| "map_distinct f xs = foldr (insertl o f) xs []"
by pat_completeness auto
termination by lexicographic_order

lemmas map_distinct_eq = map_distinct.simps(2)

function unions :: "'a list list \<Rightarrow> 'a list"
where
  "unions [] = []"
| "unions xs = foldr unionl xs []"
by pat_completeness auto
termination by lexicographic_order

lemmas unions_eq = unions.simps(2)

consts intersects :: "'a list list \<Rightarrow> 'a list"
primrec
  "intersects (x#xs) = foldr intersect xs x"

definition
  map_union :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list" where
  "map_union xs f = unions (map f xs)"

definition
  map_inter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list" where
  "map_inter xs f = intersects (map f xs)"


subsection {* Isomorphism proofs *}

lemma iso_member:
  "member xs x \<longleftrightarrow> x \<in> set xs"
  unfolding member_def mem_iff ..

lemma iso_insert:
  "set (insertl x xs) = insert x (set xs)"
  unfolding insertl_def iso_member by (simp add: insert_absorb)

lemma iso_remove1:
  assumes distnct: "distinct xs"
  shows "set (remove1 x xs) = set xs - {x}"
  using distnct set_remove1_eq by auto

lemma iso_union:
  "set (unionl xs ys) = set xs \<union> set ys"
  unfolding unionl_eq
  by (induct xs arbitrary: ys) (simp_all add: iso_insert)

lemma iso_intersect:
  "set (intersect xs ys) = set xs \<inter> set ys"
  unfolding intersect_eq Int_def by (simp add: Int_def iso_member) auto

definition
  subtract' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "subtract' = flip subtract"

lemma iso_subtract:
  fixes ys
  assumes distnct: "distinct ys"
  shows "set (subtract' ys xs) = set ys - set xs"
    and "distinct (subtract' ys xs)"
  unfolding subtract'_def flip_def subtract_eq
  using distnct by (induct xs arbitrary: ys) auto

lemma iso_map_distinct:
  "set (map_distinct f xs) = image f (set xs)"
  unfolding map_distinct_eq by (induct xs) (simp_all add: iso_insert)

lemma iso_unions:
  "set (unions xss) = \<Union> set (map set xss)"
  unfolding unions_eq
proof (induct xss)
  case Nil show ?case by simp
next
  case (Cons xs xss) thus ?case by (induct xs) (simp_all add: iso_insert)
qed

lemma iso_intersects:
  "set (intersects (xs#xss)) = \<Inter> set (map set (xs#xss))"
  by (induct xss) (simp_all add: Int_def iso_member, auto)

lemma iso_UNION:
  "set (map_union xs f) = UNION (set xs) (set o f)"
  unfolding map_union_def iso_unions by simp

lemma iso_INTER:
  "set (map_inter (x#xs) f) = INTER (set (x#xs)) (set o f)"
  unfolding map_inter_def iso_intersects by (induct xs) (simp_all add: iso_member, auto)

definition
  Blall :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Blall = flip list_all"
definition
  Blex :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Blex = flip list_ex"

lemma iso_Ball:
  "Blall xs f = Ball (set xs) f"
  unfolding Blall_def flip_def by (induct xs) simp_all

lemma iso_Bex:
  "Blex xs f = Bex (set xs) f"
  unfolding Blex_def flip_def by (induct xs) simp_all

lemma iso_filter:
  "set (filter P xs) = filter_set P (set xs)"
  unfolding filter_set_def by (induct xs) auto

subsection {* code generator setup *}

ML {*
nonfix inter;
nonfix union;
nonfix subset;
*}

subsubsection {* const serializations *}

consts_code
  "Set.empty" ("{*[]*}")
  insert ("{*insertl*}")
  is_empty ("{*null*}")
  "op \<union>" ("{*unionl*}")
  "op \<inter>" ("{*intersect*}")
  "op - \<Colon> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("{* flip subtract *}")
  image ("{*map_distinct*}")
  Union ("{*unions*}")
  Inter ("{*intersects*}")
  UNION ("{*map_union*}")
  INTER ("{*map_inter*}")
  Ball ("{*Blall*}")
  Bex ("{*Blex*}")
  filter_set ("{*filter*}")
  fold ("{* foldl o flip *}")

end
