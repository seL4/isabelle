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
    "append [] xs xs"
  | "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

code_pred append .

thm append.equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0,5]}"

inductive rev where
    "rev [] []"
  | "rev xs xs' ==> append xs' [x] ys ==> rev (x#xs) ys"

code_pred rev .

thm rev.equation

values "{xs. rev [0, 1, 2, 3::nat] xs}"
values "Collect (rev [0, 1, 2, 3::nat])"

inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

(* FIXME: correct handling of parameters *)
(*
ML {* reset Predicate_Compile.do_proofs *}
code_pred partition .

thm partition.equation
ML {* set Predicate_Compile.do_proofs *}
*)

(* TODO: requires to handle abstractions in parameter positions correctly *)
(*FIXME values 10 "{(ys, zs). partition (\<lambda>n. n mod 2 = 0)
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}" *)


lemma [code_pred_intros]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
  by auto

(* Setup requires quick and dirty proof *)
(*
code_pred tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed

thm tranclp.equation
*)

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .

thm succ.equation

values 10 "{(m, n). succ n m}"
values "{m. succ 0 m}"
values "{m. succ m 0}"

(* FIXME: why does this not terminate? *)
(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

end