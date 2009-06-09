theory Predicate_Compile_ex
imports Complex_Main Predicate_Compile
begin

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"


(*
code_pred even
  using assms by (rule even.cases)
*)
setup {* Predicate_Compile.add_equations @{const_name even} *}
thm odd.equation
thm even.equation

values "{x. even 2}"
values "{x. odd 2}"
values 10 "{n. even n}"
values 10 "{n. odd n}"


inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    append_Nil: "append [] xs xs"
  | append_Cons: "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

inductive rev
where
"rev [] []"
| "rev xs xs' ==> append xs' [x] ys ==> rev (x#xs) ys"

setup {* Predicate_Compile.add_equations @{const_name rev} *}

thm rev.equation
thm append.equation

(*
code_pred append
  using assms by (rule append.cases)
*)

thm append.equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0,5]}"


inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

setup {* Predicate_Compile.add_equations @{const_name partition} *}
(*
code_pred partition
  using assms by (rule partition.cases)
*)

thm partition.equation

(*FIXME values 10 "{(ys, zs). partition (\<lambda>n. n mod 2 = 0)
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"*)

setup {* Predicate_Compile.add_equations @{const_name tranclp} *}
(*
code_pred tranclp
  using assms by (rule tranclp.cases)
*)

thm tranclp.equation

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

setup {* Predicate_Compile.add_equations @{const_name succ} *} 
(*
code_pred succ
  using assms by (rule succ.cases)
*)
thm succ.equation

(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

end