theory Simps_Case_Conv_Examples imports
  "HOL-Library.Simps_Case_Conv"
begin

section \<open>Tests for the Simps<->Case conversion tools\<close>

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


text \<open>Function with complete, non-overlapping patterns\<close>
case_of_simps foo_cases1: foo.simps
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo xs ys = (case (xs, ys) of
    ( [], []) \<Rightarrow> 3
    | ([], y # ys) \<Rightarrow> 1
    | (x # xs, []) \<Rightarrow> 0
    | (x # xs, y # ys) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cases1)

text \<open>Redundant equations are ignored\<close>
case_of_simps foo_cases2: foo.simps foo.simps
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo xs ys = (case (xs, ys) of
    ( [], []) \<Rightarrow> 3
    | ([], y # ys) \<Rightarrow> 1
    | (x # xs, []) \<Rightarrow> 0
    | (x # xs, y # ys) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cases2)

text \<open>Variable patterns\<close>
case_of_simps bar_cases: bar.simps
print_theorems

text \<open>Case expression not at top level\<close>
simps_of_case split_rule_test_simps: split_rule_test_def
lemma
  "split_rule_test (Inl x) f = f (x 1)"
  "split_rule_test (Inr (x, None)) f = f (inv f 0)"
  "split_rule_test (Inr (x, Some y)) f = f (y x)"
  by (fact split_rule_test_simps)+

text \<open>Argument occurs both as case parameter and seperately\<close>
simps_of_case nosplit_simps1: nosplit_def
lemma
  "nosplit [] = [] @ [1]"
  "nosplit (x # xs) = (x # xs) @ x # xs"
  by (fact nosplit_simps1)+

text \<open>Nested case expressions\<close>
simps_of_case test_simps1: test_def
lemma
  "test None [] = 1"
  "test None (x # xs) = 2"
  "test (Some x) y = x"
  by (fact test_simps1)+

text \<open>Single-constructor patterns\<close>
case_of_simps fst_conv_simps: fst_conv
lemma "fst x = (case x of (a,b) \<Rightarrow> a)"
  by (fact fst_conv_simps)

text \<open>Partial split of case\<close>
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

text \<open>Reversal\<close>
case_of_simps test_def1: test_simps1
lemma
  "test x y = (case (x,y) of
    (None, []) \<Rightarrow> 1
  | (None, _#_) \<Rightarrow> 2
  | (Some x, _) \<Rightarrow> x)"
  by (fact test_def1)

text \<open>Case expressions on RHS\<close>
case_of_simps test_def2: test_simps2
lemma "test xs y = (case (xs, y) of (None, []) \<Rightarrow> 1 | (None, x # xa) \<Rightarrow> 2 | (Some x, y) \<Rightarrow> x)"
  by (fact test_def2)

text \<open>Partial split of simps\<close>
case_of_simps foo_cons_def: foo.simps(1,2)
lemma
  fixes xs :: "'a list" and ys :: "'b list"
  shows "foo (x # xs) ys = (case (x,xs,ys) of
      (_,_,[]) \<Rightarrow> 0
    | (_,_,_ # _) \<Rightarrow> foo ([] :: 'a list) ([] :: 'b list))"
  by (fact foo_cons_def)

end
