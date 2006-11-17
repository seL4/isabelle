(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and Examples for code generator *}

theory Codegenerator
imports Main Records
begin

subsection {* booleans *}

definition
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor p q = ((p | q) & \<not> (p & q))"

subsection {* natural numbers *}

definition
  n :: nat where
  "n = 42"

subsection {* pairs *}

definition
  swap :: "'a * 'b \<Rightarrow> 'b * 'a" where
  "swap p = (let (x, y) = p in (y, x))"

definition
  appl :: "('a \<Rightarrow> 'b) * 'a \<Rightarrow> 'b" where
  "appl p = (let (f, x) = p in f x)"

definition
  snd_three :: "'a * 'b * 'c => 'b" where
  "snd_three a = id (\<lambda>(a, b, c). b) a"

lemma [code]:
  "swap (x, y) = (y, x)"
  unfolding swap_def Let_def by auto

lemma [code]:
  "appl (f, x) = f x"
  unfolding appl_def Let_def by auto

subsection {* integers *}

definition
  k :: "int" where
  "k = -42"

function
  fac :: "int => int" where
  "fac j = (if j <= 0 then 1 else j * (fac (j - 1)))"
  by pat_completeness auto
termination by (relation "measure nat") auto

declare fac.simps [code]

subsection {* sums *}

subsection {* options *}

subsection {* lists *}

definition
  ps :: "nat list" where
  "ps = [2, 3, 5, 7, 11]"

definition
  qs :: "nat list" where
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

subsection {* nested lets and such *}

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
  "keywords fun datatype class instance funa classa =
    Suc fun + datatype * class mod instance - funa - classa"

hide (open) const keywords

definition
  "shadow keywords = keywords @ [Codegenerator.keywords 0 0 0 0 0 0]"

code_gen
  xor
code_gen
  "0::nat" "1::nat"
code_gen
  Pair fst snd Let split swap snd_three
code_gen
  "op + :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op - :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op * :: nat \<Rightarrow> nat \<Rightarrow> nat"
  "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "op <= :: nat \<Rightarrow> nat \<Rightarrow> bool"
code_gen
  appl
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
  filter
code_gen
  foo1 foo3
code_gen
  mystring
code_gen
  apply_tower Codegenerator.keywords shadow base_case
code_gen
  abs_let nested_let case_let
code_gen "0::int" "1::int"
  (SML) (Haskell)
code_gen n
  (SML) (Haskell)
code_gen fac
  (SML) (Haskell)
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
  "Code_Generator.eq :: bool \<Rightarrow> bool \<Rightarrow> bool"
  "Code_Generator.eq :: nat \<Rightarrow> nat \<Rightarrow> bool"
  "Code_Generator.eq :: int \<Rightarrow> int \<Rightarrow> bool"
  "Code_Generator.eq :: ('a\<Colon>eq) * ('b\<Colon>eq) \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  "Code_Generator.eq :: ('a\<Colon>eq) + ('b\<Colon>eq) \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  "Code_Generator.eq :: ('a\<Colon>eq) option \<Rightarrow> 'a option \<Rightarrow> bool"
  "Code_Generator.eq :: ('a\<Colon>eq) list \<Rightarrow> 'a list \<Rightarrow> bool"
  "Code_Generator.eq :: mut1 \<Rightarrow> mut1 \<Rightarrow> bool"
  "Code_Generator.eq :: mut2 \<Rightarrow> mut2 \<Rightarrow> bool"
  "Code_Generator.eq :: ('a\<Colon>eq) point_scheme \<Rightarrow> 'a point_scheme \<Rightarrow> bool"

code_gen (SML *) (Haskell -)

end