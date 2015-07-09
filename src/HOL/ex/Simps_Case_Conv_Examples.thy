theory Simps_Case_Conv_Examples imports
  "~~/src/HOL/Library/Simps_Case_Conv"
begin

section {* Tests for the Simps<->Case conversion tools *}

fun foo where
  "foo (x # xs) Nil = 0" |
  "foo (x # xs) (y # ys) = foo [] []" |
  "foo Nil (y # ys) = 1" |
  "foo Nil Nil = 3"

fun bar where
  "bar x 0 y = 0 + x" |
  "bar x (Suc n) y = n + x"

definition
  split_rule_test :: "((nat => 'a) + ('b * (('b => 'a) option))) => ('a => nat) => nat"
where
 "split_rule_test x f = f (case x of Inl af \<Rightarrow> af 1
    | Inr (b, None) => inv f 0
    | Inr (b, Some g) => g b)"

definition test where "test x y = (case x of None => (case y of [] => 1 | _ # _ => 2) | Some x => x)"

definition nosplit where "nosplit x = x @ (case x of [] \<Rightarrow> [1] | xs \<Rightarrow> xs)"


text {* Function with complete, non-overlapping patterns *}
case_of_simps foo_cases1: foo.simps
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo xs ys = (case (xs, ys) of
    ( [], []) \<Rightarrow> 3
    | ([], y # ys) \<Rightarrow> 1
    | (x # xs, []) \<Rightarrow> 0
    | (x # xs, y # ys) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cases1)

text {* Redundant equations are ignored *}
case_of_simps foo_cases2: foo.simps foo.simps
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo xs ys = (case (xs, ys) of
    ( [], []) \<Rightarrow> 3
    | ([], y # ys) \<Rightarrow> 1
    | (x # xs, []) \<Rightarrow> 0
    | (x # xs, y # ys) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cases2)

text {* Variable patterns *}
case_of_simps bar_cases: bar.simps
print_theorems

text {* Case expression not at top level *}
simps_of_case split_rule_test_simps: split_rule_test_def
lemma
  "split_rule_test (Inl x) f = f (x 1)"
  "split_rule_test (Inr (x, None)) f = f (inv f 0)"
  "split_rule_test (Inr (x, Some y)) f = f (y x)"
  by (fact split_rule_test_simps)+

text {* Argument occurs both as case parameter and seperately*}
simps_of_case nosplit_simps1: nosplit_def
lemma
  "nosplit [] = [] @ [1]"
  "nosplit (x # xs) = (x # xs) @ x # xs"
  by (fact nosplit_simps1)+

text {* Nested case expressions *}
simps_of_case test_simps1: test_def
lemma
  "test None [] = 1"
  "test None (x # xs) = 2"
  "test (Some x) y = x"
  by (fact test_simps1)+

text {* Partial split of case *}
simps_of_case nosplit_simps2: nosplit_def (splits: list.split)
lemma
  "nosplit [] = [] @ [1]"
  "nosplit (x # xs) = (x # xs) @ x # xs"
  by (fact nosplit_simps1)+

simps_of_case test_simps2: test_def (splits: option.split)
lemma
  "test None y = (case y of [] \<Rightarrow> 1 | x # xs \<Rightarrow> 2)"
  "test (Some x) y = x"
  by (fact test_simps2)+

text {* Reversal *}
case_of_simps test_def1: test_simps1
lemma
  "test x y = (case (x,y) of
    (None, []) \<Rightarrow> 1
  | (None, _#_) \<Rightarrow> 2
  | (Some x, _) \<Rightarrow> x)"
  by (fact test_def1)

text {* Case expressions on RHS *}
case_of_simps test_def2: test_simps2
lemma "test xs y = (case (xs, y) of (None, []) \<Rightarrow> 1 | (None, x # xa) \<Rightarrow> 2 | (Some x, y) \<Rightarrow> x)"
  by (fact test_def2)

text {* Partial split of simps *}
case_of_simps foo_cons_def: foo.simps(1,2)
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo (x # xs) ys = (case (x,xs,ys) of
      (_,_,[]) \<Rightarrow> 0
    | (_,_,_ # _) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cons_def)

end
