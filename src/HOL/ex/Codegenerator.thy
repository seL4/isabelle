(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and Examples for Code Generator *}

theory Codegenerator
imports Main
begin

subsection {* booleans *}

definition
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  "xor p q = ((p | q) & \<not> (p & q))"

code_generate (ml, haskell) xor

subsection {* natural numbers *}

definition
  one :: nat
  "one = 1"
  n :: nat
  "n = 42"

code_generate (ml, haskell) n

code_generate (ml, haskell)
  "0::nat" "one" n
  "op + :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op - :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op * :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op <= :: nat \<Rightarrow> nat \<Rightarrow> bool"

subsection {* pairs *}

definition
  swap :: "'a * 'b \<Rightarrow> 'b * 'a"
  "swap p = (let (x, y) = p in (y, x))"
  swapp :: "'a * 'b \<Rightarrow> 'c * 'd \<Rightarrow> ('a * 'c) * ('b * 'd)"
  "swapp = (\<lambda>(x, y) (z, w). ((x, z), (y, w)))"
  appl :: "('a \<Rightarrow> 'b) * 'a \<Rightarrow> 'b"
  "appl p = (let (f, x) = p in f x)"

code_generate (ml, haskell) Pair fst snd Let split swap swapp appl

definition
  k :: "int"
  "k = 42"

consts
  fac :: "int => int"

recdef fac "measure nat"
  "fac j = (if j <= 0 then 1 else j * (fac (j - 1)))"

code_generate (ml, haskell)
  "0::int" k
  "op + :: int \<Rightarrow> int \<Rightarrow> int"
  "op - :: int \<Rightarrow> int \<Rightarrow> int"
  "op * :: int \<Rightarrow> int \<Rightarrow> int"
  "op < :: int \<Rightarrow> int \<Rightarrow> bool"
  "op <= :: int \<Rightarrow> int \<Rightarrow> bool"
  fac

subsection {* sums *}

code_generate (ml, haskell) Inl Inr

subsection {* options *}

code_generate (ml, haskell) None Some

subsection {* lists *}

definition
  ps :: "nat list"
  "ps = [2, 3, 5, 7, 11]"
  qs :: "nat list"
  "qs == rev ps"

code_generate (ml, haskell) hd tl "op @" ps qs

subsection {* mutual datatypes *}

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

code_generate (ml, haskell) mut1 mut2

subsection {* equalities *}

code_generate (ml, haskell)
  "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"
  "op = :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op = :: int \<Rightarrow> int \<Rightarrow> bool"
  "op = :: 'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  "op = :: 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  "op = :: 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  "op = :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  "op = :: mut1 \<Rightarrow> mut1 \<Rightarrow> bool"
  "op = :: mut2 \<Rightarrow> mut2 \<Rightarrow> bool"


subsection {* heavy usage of names *}

definition
  f :: nat
  "f = 2"
  g :: nat
  "g = f"
  h :: nat
  "h = g"

code_alias
  "Codegenerator.f" "Mymod.f"
  "Codegenerator.g" "Mymod.A.f"
  "Codegenerator.h" "Mymod.A.B.f"

code_generate (ml, haskell) f g h

code_serialize ml (-)

end