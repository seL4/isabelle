(*  Title:      HOL/Library/IArray.thy
    Author:     Tobias Nipkow, TU Muenchen
*)

section \<open>Immutable Arrays with Code Generation\<close>

theory IArray
imports Main
begin

subsection \<open>Fundamental operations\<close>

text \<open>Immutable arrays are lists wrapped up in an additional constructor.
There are no update operations. Hence code generation can safely implement
this type by efficient target language arrays.  Currently only SML is
provided. Could be extended to other target languages and more operations.\<close>

context
begin

datatype 'a iarray = IArray "'a list"

qualified primrec list_of :: "'a iarray \<Rightarrow> 'a list" where
"list_of (IArray xs) = xs"

qualified definition of_fun :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a iarray" where
[simp]: "of_fun f n = IArray (map f [0..<n])"

qualified definition sub :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
[simp]: "as !! n = IArray.list_of as ! n"

qualified definition length :: "'a iarray \<Rightarrow> nat" where
[simp]: "length as = List.length (IArray.list_of as)"

qualified primrec all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
"all p (IArray as) \<longleftrightarrow> (\<forall>a \<in> set as. p a)"

qualified primrec exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
"exists p (IArray as) \<longleftrightarrow> (\<exists>a \<in> set as. p a)"

lemma list_of_code [code]:
"IArray.list_of as = map (\<lambda>n. as !! n) [0 ..< IArray.length as]"
by (cases as) (simp add: map_nth)

lemma of_fun_nth:
"IArray.of_fun f n !! i = f i" if "i < n"
using that by (simp add: map_nth)

end


subsection \<open>Generic code equations\<close>

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
  by (cases as) auto

lemma [code]:
  "map_iarray f as = IArray (map f (IArray.list_of as))"
  by (cases as) auto

lemma [code]:
  "rel_iarray r as bs = list_all2 r (IArray.list_of as) (IArray.list_of bs)"
  by (cases as, cases bs) auto

lemma [code]:
  "HOL.equal as bs \<longleftrightarrow> HOL.equal (IArray.list_of as) (IArray.list_of bs)"
  by (cases as, cases bs) (simp add: equal)

context term_syntax
begin

lemma [code]:
  "Code_Evaluation.term_of (as :: 'a::typerep iarray) =
    Code_Evaluation.Const (STR ''IArray.iarray.IArray'') (TYPEREP('a list \<Rightarrow> 'a iarray)) <\<cdot>> (Code_Evaluation.term_of (IArray.list_of as))"
  by (subst term_of_anything) rule

end


subsection \<open>Auxiliary operations for code generation\<close>

context
begin

qualified primrec tabulate :: "integer \<times> (integer \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
  "tabulate (n, f) = IArray (map (f \<circ> integer_of_nat) [0..<nat_of_integer n])"

lemma [code]:
  "IArray.of_fun f n = IArray.tabulate (integer_of_nat n, f \<circ> nat_of_integer)"
  by simp

qualified primrec sub' :: "'a iarray \<times> integer \<Rightarrow> 'a" where
  "sub' (as, n) = IArray.list_of as ! nat_of_integer n"

lemma [code]:
  "IArray.sub' (IArray as, n) = as ! nat_of_integer n"
  by simp

lemma [code]:
  "as !! n = IArray.sub' (as, integer_of_nat n)"
  by simp

qualified definition length' :: "'a iarray \<Rightarrow> integer" where
  [simp]: "length' as = integer_of_nat (List.length (IArray.list_of as))"

lemma [code]:
  "IArray.length' (IArray as) = integer_of_nat (List.length as)"
  by simp

lemma [code]:
  "IArray.length as = nat_of_integer (IArray.length' as)"
  by simp

end


subsection \<open>Code Generation for SML\<close>

text \<open>Note that arrays cannot be printed directly but only by turning them into
lists first. Arrays could be converted back into lists for printing if they
were wrapped up in an additional constructor.\<close>

code_reserved SML Vector

code_printing
  type_constructor iarray \<rightharpoonup> (SML) "_ Vector.vector"
| constant IArray \<rightharpoonup> (SML) "Vector.fromList"
| constant IArray.all \<rightharpoonup> (SML) "Vector.all"
| constant IArray.exists \<rightharpoonup> (SML) "Vector.exists"
| constant IArray.tabulate \<rightharpoonup> (SML) "Vector.tabulate"
| constant IArray.sub' \<rightharpoonup> (SML) "Vector.sub"
| constant IArray.length' \<rightharpoonup> (SML) "Vector.length"

end
