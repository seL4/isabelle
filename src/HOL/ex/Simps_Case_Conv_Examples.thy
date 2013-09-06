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

text {* Redundant equations are ignored *}
case_of_simps foo_cases2: foo.simps foo.simps
print_theorems

text {* Variable patterns *}
case_of_simps bar_cases: bar.simps
print_theorems

text {* Case expression not at top level *}
simps_of_case split_rule_test_simps: split_rule_test_def
print_theorems

text {* Argument occurs both as case parameter and seperately*}
simps_of_case nosplit_simps1: nosplit_def
print_theorems

text {* Nested case expressions *}
simps_of_case test_simps1: test_def
print_theorems

text {* Partial split of case *}
simps_of_case nosplit_simps2: nosplit_def (splits: list.split)
print_theorems
simps_of_case test_simps2: test_def (splits: option.split)
print_theorems

text {* Reversal *}
case_of_simps test_def1: test_simps1
print_theorems

text {* Case expressions on RHS *}
case_of_simps test_def2: test_simps2
print_theorems

text {* Partial split of simps *}
case_of_simps foo_cons_def: foo.simps(1,2)
print_theorems


end
