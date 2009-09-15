theory Predicate_Compile_ex
imports Main Predicate_Compile
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

values 10 "{(ys, zs). partition is_even
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"
values 10 "{zs. partition is_even zs [0, 2] [3, 5]}"
values 10 "{zs. partition is_even zs [0, 7] [3, 5]}"

lemma [code_pred_intros]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
  by auto

code_pred tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed

thm tranclp.equation
(*
setup {* Predicate_Compile.add_sizelim_equations [@{const_name tranclp}] *}
setup {* fn thy => exception_trace (fn () => Predicate_Compile.add_quickcheck_equations [@{const_name tranclp}] thy)  *}

thm tranclp.rpred_equation
*)

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .

thm succ.equation

values 10 "{(m, n). succ n m}"
values "{m. succ 0 m}"
values "{m. succ m 0}"

(* FIXME: why does this not terminate? -- value chooses mode [] --> [1] and then starts enumerating all successors *)

(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

subsection{* IMP *}

types
  var = nat
  state = "int list"

datatype com =
  Skip |
  Ass var "state => int" |
  Seq com com |
  IF "state => bool" com com |
  While "state => bool" com

inductive exec :: "com => state => state => bool" where
"exec Skip s s" |
"exec (Ass x e) s (s[x := e(s)])" |
"exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
"b s ==> exec c1 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec c2 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec (While b c) s s" |
"b s1 ==> exec c s1 s2 ==> exec (While b c) s2 s3 ==> exec (While b c) s1 s3"

code_pred exec .

values "{t. exec
 (While (%s. s!0 > 0) (Seq (Ass 0 (%s. s!0 - 1)) (Ass 1 (%s. s!1 + 1))))
 [3,5] t}"


subsection{* CCS *}

text{* This example formalizes finite CCS processes without communication or
recursion. For simplicity, labels are natural numbers. *}

datatype proc = nil | pre nat proc | or proc proc | par proc proc

inductive step :: "proc \<Rightarrow> nat \<Rightarrow> proc \<Rightarrow> bool" where
"step (pre n p) n p" |
"step p1 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p2 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p1 a q \<Longrightarrow> step (par p1 p2) a (par q p2)" |
"step p2 a q \<Longrightarrow> step (par p1 p2) a (par p1 q)"

code_pred step .

inductive steps where
"steps p [] p" |
"step p a q \<Longrightarrow> steps q as r \<Longrightarrow> steps p (a#as) r"

code_pred steps .

values 5
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

(* FIXME
values 3 "{(a,q). step (par nil nil) a q}"
*)


inductive divmod_rel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
    "k < l \<Longrightarrow> divmod_rel k l 0 k"
  | "k \<ge> l \<Longrightarrow> divmod_rel (k - l) l q r \<Longrightarrow> divmod_rel k l (Suc q) r"

code_pred divmod_rel ..

value [code] "Predicate.singleton (divmod_rel_1_2 1705 42)"

end