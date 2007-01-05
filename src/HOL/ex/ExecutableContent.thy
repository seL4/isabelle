(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
imports
  Main
  "~~/src/HOL/ex/Records"
  AssocList
  Binomial
  Commutative_Ring
  GCD
  List_Prefix
  Nat_Infinity
  NatPair
  Nested_Environment
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  State_Monad
  While_Combinator
  Word
  "~~/src/HOL/ex/CodeEval"
begin

definition
  n :: nat where
  "n = 42"

definition
  k :: "int" where
  "k = -42"

datatype mut1 = Tip | Top mut2
  and mut2 = Tip | Top mut1

consts
  mut1 :: "mut1 \<Rightarrow> mut1"
  mut2 :: "mut2 \<Rightarrow> mut2"

primrec
  "mut1 mut1.Tip = mut1.Tip"
  "mut1 (mut1.Top x) = mut1.Top (mut2 x)"
  "mut2 mut2.Tip = mut2.Tip"
  "mut2 (mut2.Top x) = mut2.Top (mut1 x)"

definition
  "mystring = ''my home is my castle''"

text {* nested lets and such *}

definition
  "abs_let x = (let (y, z) = x in (\<lambda>u. case u of () \<Rightarrow> (y + y)))"

definition
  "nested_let x = (let (y, z) = x in let w = y z in w * w)"

definition
  "case_let x = (let (y, z) = x in case y of () => z)"

definition
  "base_case f = f list_case"

definition
  "apply_tower = (\<lambda>x. x (\<lambda>x. x (\<lambda>x. x)))"

definition
  "keywords fun datatype x instance funa classa =
    Suc fun + datatype * x mod instance - funa - classa"

hide (open) const keywords

definition
  "shadow keywords = keywords @ [ExecutableContent.keywords 0 0 0 0 0 0]"

end
