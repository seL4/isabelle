(*  Title:      HOL/ex/Quickcheck_Examples.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2004 TU Muenchen
*)

header {* Examples for the 'quickcheck' command *}

theory Quickcheck_Examples = Main:

text {*
The 'quickcheck' command allows to find counterexamples by evaluating
formulae under an assignment of free variables to random values.
In contrast to 'refute', it can deal with inductive datatypes,
but cannot handle quantifiers.
*}

subsection {* Lists *}

theorem "map g (map f xs) = map (g o f) xs"
  quickcheck
  oops

theorem "map g (map f xs) = map (f o g) xs"
  quickcheck
  oops

theorem "rev (xs @ ys) = rev ys @ rev xs"
  quickcheck
  oops

theorem "rev (xs @ ys) = rev xs @ rev ys"
  quickcheck
  oops

theorem "rev (rev xs) = xs"
  quickcheck
  oops

theorem "rev xs = xs"
  quickcheck
  oops

consts
  occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
primrec
  "occurs a [] = 0"
  "occurs a (x#xs) = (if (x=a) then Suc(occurs a xs) else occurs a xs)"

consts
  del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
  "del1 a [] = []"
  "del1 a (x#xs) = (if (x=a) then xs else (x#del1 a xs))"

(* A lemma, you'd think to be true from our experience with delAll*)
lemma "Suc (occurs a (del1 a xs)) = occurs a xs"
  -- {* Wrong. Precondition needed.*}
  quickcheck
  oops

lemma "xs ~= [] \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck
    -- {* Also wrong.*}
  oops

lemma "0 < occurs a xs \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck
  apply (induct_tac xs)  
  apply auto
    -- {* Correct! *}
  done

consts
  replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
  "replace a b [] = []"
  "replace a b (x#xs) = (if (x=a) then (b#(replace a b xs)) 
                            else (x#(replace a b xs)))"

lemma "occurs a xs = occurs b (replace a b xs)"
  quickcheck
  -- {* Wrong. Precondition needed.*}
  oops

lemma "occurs b xs = 0 \<or> a=b \<longrightarrow> occurs a xs = occurs b (replace a b xs)"
  quickcheck
  apply (induct_tac xs)  
  apply auto
  done


subsection {* Trees *}

datatype 'a tree = Twig |  Leaf 'a | Branch "'a tree" "'a tree"

consts
  leaves :: "'a tree \<Rightarrow> 'a list"
primrec
  "leaves Twig = []"
  "leaves (Leaf a) = [a]"
  "leaves (Branch l r) = (leaves l) @ (leaves r)"

consts
  plant :: "'a list \<Rightarrow> 'a tree"
primrec
  "plant [] = Twig "
  "plant (x#xs) = Branch (Leaf x) (plant xs)"

consts
  mirror :: "'a tree \<Rightarrow> 'a tree"
primrec
  "mirror (Twig) = Twig "
  "mirror (Leaf a) = Leaf a "
  "mirror (Branch l r) = Branch (mirror r) (mirror l)"

theorem "plant (rev (leaves xt)) = mirror xt"
  quickcheck
    --{* Wrong! *} 
  oops

theorem "plant((leaves xt) @ (leaves yt)) = Branch xt yt"
  quickcheck
    --{* Wrong! *} 
  oops

datatype 'a ntree = Tip "'a" | Node "'a" "'a ntree" "'a ntree"

consts
  inOrder :: "'a ntree \<Rightarrow> 'a list"
primrec
  "inOrder (Tip a)= [a]"
  "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"

consts
  root :: "'a ntree \<Rightarrow> 'a"
primrec
  "root (Tip a) = a"
  "root (Node f x y) = f"

theorem "hd(inOrder xt) = root xt"
  quickcheck
    --{* Wrong! *} 
  oops

end


