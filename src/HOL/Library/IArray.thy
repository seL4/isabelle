header "Immutable Arrays with Code Generation"

theory IArray
imports Main
begin

text{* Immutable arrays are lists wrapped up in an additional constructor.
There are no update operations. Hence code generation can safely implement
this type by efficient target language arrays.  Currently only SML is
provided. Should be extended to other target languages and more operations.

Note that arrays cannot be printed directly but only by turning them into
lists first. Arrays could be converted back into lists for printing if they
were wrapped up in an additional constructor. *}

datatype 'a iarray = IArray "'a list"

primrec list_of :: "'a iarray \<Rightarrow> 'a list" where
"list_of (IArray xs) = xs"
hide_const (open) list_of

definition of_fun :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a iarray" where
[simp]: "of_fun f n = IArray (map f [0..<n])"
hide_const (open) of_fun

definition sub :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
[simp]: "as !! n = IArray.list_of as ! n"
hide_const (open) sub

definition length :: "'a iarray \<Rightarrow> nat" where
[simp]: "length as = List.length (IArray.list_of as)"
hide_const (open) length

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
"all p (IArray as) = (ALL a : set as. p a)"
hide_const (open) all

fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
"exists p (IArray as) = (EX a : set as. p a)"
hide_const (open) exists

lemma list_of_code [code]:
"IArray.list_of as = map (\<lambda>n. as !! n) [0 ..< IArray.length as]"
by (cases as) (simp add: map_nth)


subsection "Code Generation"

code_reserved SML Vector

code_printing
  type_constructor iarray \<rightharpoonup> (SML) "_ Vector.vector"
| constant IArray \<rightharpoonup> (SML) "Vector.fromList"
| constant IArray.all \<rightharpoonup> (SML) "Vector.all"
| constant IArray.exists \<rightharpoonup> (SML) "Vector.exists"

lemma [code]:
  "size (as :: 'a iarray) = Suc (length (IArray.list_of as))"
  by (cases as) simp

lemma [code]:
  "size_iarray f as = Suc (size_list f (IArray.list_of as))"
  by (cases as) simp

lemma [code]:
  "rec_iarray f as = f (IArray.list_of as)"
  by (cases as) simp

lemma [code]:
  "case_iarray f as = f (IArray.list_of as)"
  by (cases as) simp

lemma [code]:
  "set_iarray as = set (IArray.list_of as)"
  by (case_tac as) auto

lemma [code]:
  "map_iarray f as = IArray (map f (IArray.list_of as))"
  by (case_tac as) auto

lemma [code]:
  "rel_iarray r as bs = list_all2 r (IArray.list_of as) (IArray.list_of bs)"
  by (case_tac as) (case_tac bs, auto)

lemma [code]:
  "HOL.equal as bs \<longleftrightarrow> HOL.equal (IArray.list_of as) (IArray.list_of bs)"
  by (cases as, cases bs) (simp add: equal)

primrec tabulate :: "integer \<times> (integer \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
  "tabulate (n, f) = IArray (map (f \<circ> integer_of_nat) [0..<nat_of_integer n])"

hide_const (open) tabulate

lemma [code]:
  "IArray.of_fun f n = IArray.tabulate (integer_of_nat n, f \<circ> nat_of_integer)"
  by simp

code_printing
  constant IArray.tabulate \<rightharpoonup> (SML) "Vector.tabulate"

primrec sub' :: "'a iarray \<times> integer \<Rightarrow> 'a" where
  [code del]: "sub' (as, n) = IArray.list_of as ! nat_of_integer n"

hide_const (open) sub'

lemma [code]:
  "IArray.sub' (IArray as, n) = as ! nat_of_integer n"
  by simp

lemma [code]:
  "as !! n = IArray.sub' (as, integer_of_nat n)"
  by simp

code_printing
  constant IArray.sub' \<rightharpoonup> (SML) "Vector.sub"

definition length' :: "'a iarray \<Rightarrow> integer" where
  [code del, simp]: "length' as = integer_of_nat (List.length (IArray.list_of as))"

hide_const (open) length'

lemma [code]:
  "IArray.length' (IArray as) = integer_of_nat (List.length as)" 
  by simp

lemma [code]:
  "IArray.length as = nat_of_integer (IArray.length' as)"
  by simp

code_printing
  constant IArray.length' \<rightharpoonup> (SML) "Vector.length"

end
