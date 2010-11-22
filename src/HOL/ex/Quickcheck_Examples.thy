(*  Title:      HOL/ex/Quickcheck_Examples.thy
    Author:     Stefan Berghofer, Lukas Bulwahn
    Copyright   2004 - 2010 TU Muenchen
*)

header {* Examples for the 'quickcheck' command *}

theory Quickcheck_Examples
imports Main
begin

text {*
The 'quickcheck' command allows to find counterexamples by evaluating
formulae.
Currently, there are two different exploration schemes:
- random testing: this is incomplete, but explores the search space faster.
- exhaustive testing: this is complete, but increasing the depth leads to
  exponentially many assignments.

quickcheck can handle quantifiers on finite universes.

*}

subsection {* Lists *}

theorem "map g (map f xs) = map (g o f) xs"
  quickcheck[size = 3]
  quickcheck[generator = random, expect = no_counterexample]
  quickcheck[generator = small, size = 3, iterations = 1, report = false, expect = no_counterexample]
  oops

theorem "map g (map f xs) = map (f o g) xs"
  quickcheck[generator = random, expect = counterexample]
  quickcheck[generator = small, report = false]
  oops

theorem "rev (xs @ ys) = rev ys @ rev xs"
  quickcheck[expect = no_counterexample]
  quickcheck[generator = small, expect = no_counterexample, report = false]
  oops

theorem "rev (xs @ ys) = rev xs @ rev ys"
  quickcheck[generator = small, expect = counterexample, report = false]
  quickcheck[generator = random, expect = counterexample]
  oops

theorem "rev (rev xs) = xs"
  quickcheck[expect = no_counterexample]
  oops

theorem "rev xs = xs"
  quickcheck[generator = small, report = false]
  quickcheck[expect = counterexample]
  oops

text {* An example involving functions inside other data structures *}

primrec app :: "('a \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "app [] x = x"
  | "app (f # fs) x = app fs (f x)"

lemma "app (fs @ gs) x = app gs (app fs x)"
  quickcheck[generator = random, expect = no_counterexample]
  quickcheck[generator = small, iterations = 1, size = 4, report = false, expect = no_counterexample]
  by (induct fs arbitrary: x) simp_all

lemma "app (fs @ gs) x = app fs (app gs x)"
  quickcheck[generator = random, expect = counterexample]
  quickcheck[generator = small, report = false, expect = counterexample]
  oops

primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs a [] = 0"
  | "occurs a (x#xs) = (if (x=a) then Suc(occurs a xs) else occurs a xs)"

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 a [] = []"
  | "del1 a (x#xs) = (if (x=a) then xs else (x#del1 a xs))"

text {* A lemma, you'd think to be true from our experience with delAll *}
lemma "Suc (occurs a (del1 a xs)) = occurs a xs"
  -- {* Wrong. Precondition needed.*}
  quickcheck[generator = small, report = false]
  quickcheck[expect = counterexample]
  oops

lemma "xs ~= [] \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[generator = small, report = false]
  quickcheck[expect = counterexample]
    -- {* Also wrong.*}
  oops

lemma "0 < occurs a xs \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[generator = small, report = false]
  quickcheck[expect = no_counterexample]
  by (induct xs) auto

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace a b [] = []"
  | "replace a b (x#xs) = (if (x=a) then (b#(replace a b xs)) 
                            else (x#(replace a b xs)))"

lemma "occurs a xs = occurs b (replace a b xs)"
  quickcheck[generator = small, report = false]
  quickcheck[expect = counterexample]
  -- {* Wrong. Precondition needed.*}
  oops

lemma "occurs b xs = 0 \<or> a=b \<longrightarrow> occurs a xs = occurs b (replace a b xs)"
  quickcheck[expect = no_counterexample, report = false]
  by (induct xs) simp_all


subsection {* Trees *}

datatype 'a tree = Twig |  Leaf 'a | Branch "'a tree" "'a tree"

primrec leaves :: "'a tree \<Rightarrow> 'a list" where
  "leaves Twig = []"
  | "leaves (Leaf a) = [a]"
  | "leaves (Branch l r) = (leaves l) @ (leaves r)"

primrec plant :: "'a list \<Rightarrow> 'a tree" where
  "plant [] = Twig "
  | "plant (x#xs) = Branch (Leaf x) (plant xs)"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Twig) = Twig "
  | "mirror (Leaf a) = Leaf a "
  | "mirror (Branch l r) = Branch (mirror r) (mirror l)"

theorem "plant (rev (leaves xt)) = mirror xt"
  quickcheck[expect = counterexample]
    --{* Wrong! *} 
  oops

theorem "plant((leaves xt) @ (leaves yt)) = Branch xt yt"
  quickcheck[expect = counterexample]
    --{* Wrong! *} 
  oops

datatype 'a ntree = Tip "'a" | Node "'a" "'a ntree" "'a ntree"

primrec inOrder :: "'a ntree \<Rightarrow> 'a list" where
  "inOrder (Tip a)= [a]"
  | "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"

primrec root :: "'a ntree \<Rightarrow> 'a" where
  "root (Tip a) = a"
  | "root (Node f x y) = f"

theorem "hd (inOrder xt) = root xt"
  quickcheck[generator = small, report = false]
  quickcheck[expect = counterexample]
    --{* Wrong! *} 
  oops


subsection {* Exhaustive Testing beats Random Testing *}

text {* Here are some examples from mutants from the List theory
where exhaustive testing beats random testing *}

lemma
  "[] ~= xs ==> hd xs = last (x # xs)"
quickcheck[generator = random, report = false]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
  assumes "!!i. [| i < n; i < length xs |] ==> P (xs ! i)" "n < length xs ==> ~ P (xs ! n)"
  shows "drop n xs = takeWhile P xs"
quickcheck[generator = random, iterations = 10000, report = false, quiet]
quickcheck[generator = small, iterations = 1, report = false, expect = counterexample]
oops

lemma
  "i < length (List.transpose (List.transpose xs)) ==> xs ! i = map (%xs. xs ! i) [ys<-xs. i < length ys]"
quickcheck[generator = random, iterations = 10000, report = false, quiet]
quickcheck[generator = small, iterations = 1, report = false, expect = counterexample]
oops

lemma
  "i < n - m ==> f (lcm m i) = map f [m..<n] ! i"
quickcheck[generator = random, iterations = 10000, report = false, quiet]
quickcheck[generator = small, finite_types = false, report = false, expect = counterexample]
oops

lemma
  "i < n - m ==> f (lcm m i) = map f [m..<n] ! i"
quickcheck[generator = random, iterations = 1000, report = false, quiet]
quickcheck[generator = small, finite_types = false, report = false, expect = counterexample]
oops

lemma
  "ns ! k < length ns ==> k <= listsum ns"
quickcheck[generator = random, iterations = 10000, report = true, quiet]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
  "[| ys = x # xs1; zs = xs1 @ xs |] ==> ys @ zs = x # xs"
quickcheck[generator = random, iterations = 10000, report = true]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
"i < length xs ==> take (Suc i) xs = [] @ xs ! i # take i xs"
quickcheck[generator = random]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
  "i < length xs ==> take (Suc i) xs = (xs ! i # xs) @ take i []"
quickcheck[generator = random]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
  "[| sorted (rev (map length xs)); i < length xs |] ==> xs ! i = map (%ys. ys ! i) [ys<-remdups xs. i < length ys]"
quickcheck[generator = random]
quickcheck[generator = small, report = false]
oops

lemma
  "[| sorted (rev (map length xs)); i < length xs |] ==> xs ! i = map (%ys. ys ! i) [ys<-List.transpose xs. {..<i} (length ys)]"
quickcheck[generator = random]
quickcheck[generator = small, report = false, expect = counterexample]
oops

lemma
  "(ys = zs) = (xs @ ys = splice xs zs)"
quickcheck[generator = random]
quickcheck[generator = small, report = false, expect = counterexample]
oops

section {* Examples with quantifiers *}

text {*
  These examples show that we can handle quantifiers.
*}

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
  quickcheck[expect = counterexample]
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  quickcheck[expect = counterexample]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (EX! x. P x)"
  quickcheck[expect = counterexample]
oops

end
