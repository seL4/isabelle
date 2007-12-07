(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
imports
  Main
  Eval
  "~~/src/HOL/ex/Records"
  AssocList
  Binomial
  Commutative_Ring
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/Real/RealDef"
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
begin

definition
  n :: nat where
  "n = 42"

definition
  k :: "int" where
  "k = -42"

datatype mut1 = Tip | Top mut2
  and mut2 = Tip | Top mut1

primrec
  mut1 :: "mut1 \<Rightarrow> mut1"
  and mut2 :: "mut2 \<Rightarrow> mut2"
where
  "mut1 mut1.Tip = mut1.Tip"
  | "mut1 (mut1.Top x) = mut1.Top (mut2 x)"
  | "mut2 mut2.Tip = mut2.Tip"
  | "mut2 (mut2.Top x) = mut2.Top (mut1 x)"

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

definition
  foo :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "foo r s t = (t + s) / t"

definition
  bar :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
  "bar r s t \<longleftrightarrow> (r - s) \<le> t \<or> (s - t) \<le> r"

definition
  "R1 = Fract 3 7"

definition
  "R2 = Fract (-7) 5"

definition
  "R3 = Fract 11 (-9)"

definition
  "foobar = (foo R1 1 R3, bar R2 0 R3, foo R1 R3 R2)"

definition
  foo' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "foo' r s t = (t + s) / t"

definition
  bar' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "bar' r s t \<longleftrightarrow> (r - s) \<le> t \<or> (s - t) \<le> r"

definition
  "R1' = real_of_rat (Fract 3 7)"

definition
  "R2' = real_of_rat (Fract (-7) 5)"

definition
  "R3' = real_of_rat (Fract 11 (-9))"

definition
  "foobar' = (foo' R1' 1 R3', bar' R2' 0 R3', foo' R1' R3' R2')"

end
