(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and Examples for code generator *}

theory Codegenerator
imports Main "~~/src/HOL/ex/Records"
begin

subsection {* booleans *}

definition
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  "xor p q = ((p | q) & \<not> (p & q))"

subsection {* natural numbers *}

definition
  one :: nat
  "one = 1"
  n :: nat
  "n = 42"

subsection {* pairs *}

definition
  swap :: "'a * 'b \<Rightarrow> 'b * 'a"
  "swap p = (let (x, y) = p in (y, x))"
  swapp :: "'a * 'b \<Rightarrow> 'c * 'd \<Rightarrow> ('a * 'c) * ('b * 'd)"
  "swapp = (\<lambda>(x, y) (z, w). ((x, z), (y, w)))"
  appl :: "('a \<Rightarrow> 'b) * 'a \<Rightarrow> 'b"
  "appl p = (let (f, x) = p in f x)"

subsection {* integers *}

definition
  k :: "int"
  "k = -42"

consts
  fac :: "int => int"

recdef fac "measure nat"
  "fac j = (if j <= 0 then 1 else j * (fac (j - 1)))"

subsection {* sums *}

subsection {* options *}

subsection {* lists *}

definition
  ps :: "nat list"
  "ps = [2, 3, 5, 7, 11]"
  qs :: "nat list"
  "qs == rev ps"

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

subsection {* records *}

subsection {* equalities *}

subsection {* heavy usage of names *}

definition
  f :: nat
  "f = 2"
  g :: nat
  "g = f"
  h :: nat
  "h = g"

code_constname
  f "Mymod.f"
  g "Mymod.A.f"
  h "Mymod.A.B.f"

code_gen xor
code_gen one "0::nat" "1::nat"
code_gen "0::int" "1::int" n fac
  (SML) (Haskell)
code_gen
  "op + :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op - :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op * :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op <= :: nat \<Rightarrow> nat \<Rightarrow> bool"
code_gen
  Pair fst snd Let split swap swapp appl
code_gen
  k
  "op + :: int \<Rightarrow> int \<Rightarrow> int"
  "op - :: int \<Rightarrow> int \<Rightarrow> int"
  "op * :: int \<Rightarrow> int \<Rightarrow> int"
  "op < :: int \<Rightarrow> int \<Rightarrow> bool"
  "op <= :: int \<Rightarrow> int \<Rightarrow> bool"
  fac
  "op div :: int \<Rightarrow> int \<Rightarrow> int"
  "op mod :: int \<Rightarrow> int \<Rightarrow> int"  
  (SML) (Haskell)
code_gen
  Inl Inr
code_gen
  None Some
code_gen
  hd tl "op @" ps qs
code_gen
  mut1 mut2
code_gen
  "op @" filter concat foldl foldr hd tl
  last butlast list_all2
  map 
  nth 
  list_update
  take
  drop
  takeWhile
  dropWhile
  rev
  zip
  upt
  remdups
  remove1
  null
  "distinct"
  replicate
  rotate1
  rotate
  splice
  (SML) (Haskell)
code_gen
  foo1 foo3
code_gen
  "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"
  "op = :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op = :: int \<Rightarrow> int \<Rightarrow> bool"
  "op = :: 'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  "op = :: 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  "op = :: 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  "op = :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  "op = :: point \<Rightarrow> point \<Rightarrow> bool"
  "op = :: mut1 \<Rightarrow> mut1 \<Rightarrow> bool"
  "op = :: mut2 \<Rightarrow> mut2 \<Rightarrow> bool"
code_gen
  f g h

code_gen (SML -)

end