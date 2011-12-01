(*  Title:      HOL/ex/Quickcheck_Examples.thy
    Author:     Stefan Berghofer, Lukas Bulwahn
    Copyright   2004 - 2010 TU Muenchen
*)

header {* Examples for the 'quickcheck' command *}

theory Quickcheck_Examples
imports Complex_Main
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

declare [[quickcheck_timeout = 3600]]

subsection {* Lists *}

theorem "map g (map f xs) = map (g o f) xs"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, size = 3, expect = no_counterexample]
  oops

theorem "map g (map f xs) = map (f o g) xs"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
  oops

theorem "rev (xs @ ys) = rev ys @ rev xs"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, expect = no_counterexample]
  quickcheck[exhaustive, size = 1000, timeout = 0.1]
  oops

theorem "rev (xs @ ys) = rev xs @ rev ys"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
  oops

theorem "rev (rev xs) = xs"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, expect = no_counterexample]
  oops

theorem "rev xs = xs"
  quickcheck[tester = random, finite_types = true, report = false, expect = counterexample]
  quickcheck[tester = random, finite_types = false, report = false, expect = counterexample]
  quickcheck[tester = random, finite_types = true, report = true, expect = counterexample]
  quickcheck[tester = random, finite_types = false, report = true, expect = counterexample]
  quickcheck[tester = exhaustive, finite_types = true, expect = counterexample]
  quickcheck[tester = exhaustive, finite_types = false, expect = counterexample]
oops


text {* An example involving functions inside other data structures *}

primrec app :: "('a \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "app [] x = x"
  | "app (f # fs) x = app fs (f x)"

lemma "app (fs @ gs) x = app gs (app fs x)"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, size = 4, expect = no_counterexample]
  by (induct fs arbitrary: x) simp_all

lemma "app (fs @ gs) x = app fs (app gs x)"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
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
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
  oops

lemma "xs ~= [] \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
    -- {* Also wrong.*}
  oops

lemma "0 < occurs a xs \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, expect = no_counterexample]
  by (induct xs) auto

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace a b [] = []"
  | "replace a b (x#xs) = (if (x=a) then (b#(replace a b xs)) 
                            else (x#(replace a b xs)))"

lemma "occurs a xs = occurs b (replace a b xs)"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
  -- {* Wrong. Precondition needed.*}
  oops

lemma "occurs b xs = 0 \<or> a=b \<longrightarrow> occurs a xs = occurs b (replace a b xs)"
  quickcheck[random, expect = no_counterexample]
  quickcheck[exhaustive, expect = no_counterexample]
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
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
    --{* Wrong! *} 
  oops

theorem "plant((leaves xt) @ (leaves yt)) = Branch xt yt"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
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
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
  --{* Wrong! *} 
  oops


subsection {* Exhaustive Testing beats Random Testing *}

text {* Here are some examples from mutants from the List theory
where exhaustive testing beats random testing *}

lemma
  "[] ~= xs ==> hd xs = last (x # xs)"
quickcheck[random]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  assumes "!!i. [| i < n; i < length xs |] ==> P (xs ! i)" "n < length xs ==> ~ P (xs ! n)"
  shows "drop n xs = takeWhile P xs"
quickcheck[random, iterations = 10000, quiet]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "i < length (List.transpose (List.transpose xs)) ==> xs ! i = map (%xs. xs ! i) [ys<-xs. i < length ys]"
quickcheck[random, iterations = 10000]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "i < n - m ==> f (lcm m i) = map f [m..<n] ! i"
quickcheck[random, iterations = 10000, finite_types = false]
quickcheck[exhaustive, finite_types = false, expect = counterexample]
oops

lemma
  "i < n - m ==> f (lcm m i) = map f [m..<n] ! i"
quickcheck[random, iterations = 10000, finite_types = false]
quickcheck[exhaustive, finite_types = false, expect = counterexample]
oops

lemma
  "ns ! k < length ns ==> k <= listsum ns"
quickcheck[random, iterations = 10000, finite_types = false, quiet]
quickcheck[exhaustive, finite_types = false, expect = counterexample]
oops

lemma
  "[| ys = x # xs1; zs = xs1 @ xs |] ==> ys @ zs = x # xs"
quickcheck[random, iterations = 10000]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
"i < length xs ==> take (Suc i) xs = [] @ xs ! i # take i xs"
quickcheck[random, iterations = 10000]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "i < length xs ==> take (Suc i) xs = (xs ! i # xs) @ take i []"
quickcheck[random, iterations = 10000]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "[| sorted (rev (map length xs)); i < length xs |] ==> xs ! i = map (%ys. ys ! i) [ys<-remdups xs. i < length ys]"
quickcheck[random]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "[| sorted (rev (map length xs)); i < length xs |] ==> xs ! i = map (%ys. ys ! i) [ys<-List.transpose xs. length ys \<in> {..<i}]"
quickcheck[random]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "(ys = zs) = (xs @ ys = splice xs zs)"
quickcheck[random]
quickcheck[exhaustive, expect = counterexample]
oops

subsection {* Examples with quantifiers *}

text {*
  These examples show that we can handle quantifiers.
*}

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
  quickcheck[random, expect = counterexample]
  quickcheck[exhaustive, expect = counterexample]
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  quickcheck[random, expect = counterexample]
  quickcheck[expect = counterexample]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (EX! x. P x)"
  quickcheck[random, expect = counterexample]
  quickcheck[expect = counterexample]
oops


subsection {* Examples with relations *}

lemma
  "acyclic R ==> acyclic S ==> acyclic (R Un S)"
quickcheck[expect = counterexample]
oops

lemma
  "(x, z) : rtrancl (R Un S) ==> \<exists> y. (x, y) : rtrancl R & (y, z) : rtrancl S"
quickcheck[expect = counterexample]
oops


subsection {* Examples with numerical types *}

text {*
Quickcheck supports the common types nat, int, rat and real.
*}

lemma
  "(x :: nat) > 0 ==> y > 0 ==> z > 0 ==> x * x + y * y \<noteq> z * z"
quickcheck[exhaustive, size = 10, expect = counterexample]
quickcheck[random, size = 10]
oops

lemma
  "(x :: int) > 0 ==> y > 0 ==> z > 0 ==> x * x + y * y \<noteq> z * z"
quickcheck[exhaustive, size = 10, expect = counterexample]
quickcheck[random, size = 10]
oops

lemma
  "(x :: rat) > 0 ==> y > 0 ==> z > 0 ==> x * x + y * y \<noteq> z * z"
quickcheck[exhaustive, size = 10, expect = counterexample]
quickcheck[random, size = 10]
oops

lemma "(x :: rat) >= 0"
quickcheck[random, expect = counterexample]
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "(x :: real) > 0 ==> y > 0 ==> z > 0 ==> x * x + y * y \<noteq> z * z"
quickcheck[exhaustive, size = 10, expect = counterexample]
quickcheck[random, size = 10]
oops

lemma "(x :: real) >= 0"
quickcheck[random, expect = counterexample]
quickcheck[exhaustive, expect = counterexample]
oops

subsubsection {* floor and ceiling functions *}

lemma
  "floor x + floor y = floor (x + y :: rat)"
quickcheck[expect = counterexample]
oops

lemma
  "floor x + floor y = floor (x + y :: real)"
quickcheck[expect = counterexample]
oops

lemma
  "ceiling x + ceiling y = ceiling (x + y :: rat)"
quickcheck[expect = counterexample]
oops

lemma
  "ceiling x + ceiling y = ceiling (x + y :: real)"
quickcheck[expect = counterexample]
oops


subsection {* Examples with Records *}

record point =
  xpos :: nat
  ypos :: nat

lemma
  "xpos r = xpos r' ==> r = r'"
quickcheck[exhaustive, expect = counterexample]
quickcheck[random, expect = counterexample]
oops

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour

lemma
  "xpos r = xpos r' ==> ypos r = ypos r' ==> (r :: cpoint) = r'"
quickcheck[exhaustive, expect = counterexample]
quickcheck[random, expect = counterexample]
oops

subsection {* Examples with locales *}

locale Truth

context Truth
begin

lemma "False"
quickcheck[exhaustive, expect = no_counterexample]
oops

end

interpretation Truth .

context Truth
begin

lemma "False"
quickcheck[exhaustive, expect = counterexample]
oops

end

subsection {* Examples with HOL quantifiers *}

lemma
  "\<forall> xs ys. xs = [] --> xs = ys"
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "ys = [] --> (\<forall>xs. xs = [] --> xs = y # ys)"
quickcheck[exhaustive, expect = counterexample]
oops

lemma
  "\<forall>xs. (\<exists> ys. ys = []) --> xs = ys"
quickcheck[exhaustive, expect = counterexample]
oops

subsection {* Examples with underspecified/partial functions *}

lemma
  "xs = [] ==> hd xs \<noteq> x"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
quickcheck[random, potential = false, report = false, expect = no_counterexample]
quickcheck[random, potential = true, report = false, expect = counterexample]
oops

lemma
  "xs = [] ==> hd xs = x"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
quickcheck[random, potential = false, report = false, expect = no_counterexample]
quickcheck[random, potential = true, report = false, expect = counterexample]
oops

lemma "xs = [] ==> hd xs = x ==> x = y"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
quickcheck[random, potential = false, report = false, expect = no_counterexample]
quickcheck[random, potential = true, report = false, expect = counterexample]
oops

text {* with the simple testing scheme *}

setup {* Exhaustive_Generators.setup_exhaustive_datatype_interpretation *}
declare [[quickcheck_full_support = false]]

lemma
  "xs = [] ==> hd xs \<noteq> x"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
oops

lemma
  "xs = [] ==> hd xs = x"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
oops

lemma "xs = [] ==> hd xs = x ==> x = y"
quickcheck[exhaustive, potential = false, expect = no_counterexample]
quickcheck[exhaustive, potential = true, expect = counterexample]
oops

declare [[quickcheck_full_support = true]]

end
