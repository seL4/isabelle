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

subsection {* strings *}

definition
  "mystring = ''my home is my castle''"

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

definition
  "apply_tower = (\<lambda>x. x (\<lambda>x. x (\<lambda>x. x)))"

definition
  "keywords fun datatype class instance funa classa =
    Suc fun + datatype * class mod instance - funa - classa"

hide (open) const keywords

definition
  "shadow keywords = keywords @ [Codegenerator.keywords 0 0 0 0 0 0]"

code_gen xor
code_gen one
code_gen
  Pair fst snd Let split swap
code_gen "0::int" "1::int"
  (SML) (Haskell)
code_gen n
  (SML) (Haskell)
code_gen fac
  (SML) (Haskell)
code_gen
  "op + :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op - :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op * :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op <= :: nat \<Rightarrow> nat \<Rightarrow> bool"
code_gen
  appl
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
  remove1
  null
  replicate
  rotate1
  rotate
  splice
code_gen
  remdups
  "distinct"
code_gen
  foo1 foo3
code_gen
  "OperationalEquality.eq :: bool \<Rightarrow> bool \<Rightarrow> bool"
  "OperationalEquality.eq :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "OperationalEquality.eq :: int \<Rightarrow> int \<Rightarrow> bool"
  "OperationalEquality.eq :: ('a\<Colon>eq) * ('b\<Colon>eq) \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  "OperationalEquality.eq :: ('a\<Colon>eq) + ('b\<Colon>eq) \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  "OperationalEquality.eq :: ('a\<Colon>eq) option \<Rightarrow> 'a option \<Rightarrow> bool"
  "OperationalEquality.eq :: ('a\<Colon>eq) list \<Rightarrow> 'a list \<Rightarrow> bool"
  "OperationalEquality.eq :: mut1 \<Rightarrow> mut1 \<Rightarrow> bool"
  "OperationalEquality.eq :: mut2 \<Rightarrow> mut2 \<Rightarrow> bool"
  "OperationalEquality.eq :: ('a\<Colon>eq) point_scheme \<Rightarrow> 'a point_scheme \<Rightarrow> bool"
code_gen
  mystring
code_gen
  f g h
code_gen
  apply_tower Codegenerator.keywords shadow

code_gen (SML -)

end