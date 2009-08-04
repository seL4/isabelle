theory Predicate_Compile_ex
imports Complex_Main Predicate_Compile
begin

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"

code_pred even .

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

code_pred rev .

thm append.equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0,5]}"


inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

code_pred partition .

thm partition.equation

inductive is_even :: "nat \<Rightarrow> bool"
where
  "n mod 2 = 0 \<Longrightarrow> is_even n"

code_pred is_even .

(* TODO: requires to handle abstractions in parameter positions correctly *)
values 10 "{(ys, zs). partition is_even
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"

values 10 "{zs. partition is_even zs [0, 2] [3, 5]}"
values 10 "{zs. partition is_even zs [0, 7] [3, 5]}"

lemma [code_pred_intros]:
"r a b ==> tranclp r a b"
"r a b ==> tranclp r b c ==> tranclp r a c"
by auto

code_pred tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed

thm tranclp.equation

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .

thm succ.equation
(* FIXME: why does this not terminate? -- value chooses mode [] --> [1] and then starts enumerating all successors *)
(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

end