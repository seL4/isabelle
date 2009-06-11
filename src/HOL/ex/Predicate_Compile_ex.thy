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
"r a b ==> tranclp r a b"
"r a b ==> tranclp r b c ==> tranclp r a c" 
by auto


lemma converse_tranclpE:
  assumes "tranclp r x z "
  assumes "r x z ==> P"
  assumes "\<And> y. [| r x y; tranclp r y z |] ==> P"
  shows P
proof -
  from tranclpD[OF assms(1)]
  obtain y where "r x y" and "rtranclp r y z" by iprover
  with assms(2-3) rtranclpD[OF this(2)] this(1)
  show P by iprover
qed  

(* Setup requires quick and dirty proof *)
(*
code_pred tranclp
proof -
  assume tranclp: "tranclp r a1 a2"
     and step: "\<And> a c b. a1 = a ==> a2 = c ==> r a b ==> tranclp r b c ==> thesis"
     and base: "\<And> a b. a1 = a ==> a2 = b ==> r a b ==> thesis"
  show thesis
  proof (cases rule: converse_tranclpE[OF tranclp])
    case 1
    from 1 base show thesis by auto
  next
    case 2
    from 2 step show thesis by auto
  qed
qed

thm tranclp.equation
*)

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .

thm succ.equation
(* FIXME: why does this not terminate? *)
(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

end