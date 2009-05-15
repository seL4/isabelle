theory Predicate_Compile_ex
imports Complex_Main Predicate_Compile
begin

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"

code_pred even
  using assms by (rule even.cases)

thm even.equation


inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    append_Nil: "append [] xs xs"
  | append_Cons: "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

code_pred append
  using assms by (rule append.cases)

thm append.equation


inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

code_pred partition
  using assms by (rule partition.cases)

thm partition.equation


code_pred tranclp
  using assms by (rule tranclp.cases)

thm tranclp.equation

end