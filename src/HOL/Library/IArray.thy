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

lemma list_of_code [code]:
"IArray.list_of as = map (\<lambda>n. as !! n) [0 ..< IArray.length as]"
by (cases as) (simp add: map_nth)


subsection "Code Generation"

code_reserved SML Vector

code_type iarray
  (SML "_ Vector.vector")

code_const IArray
  (SML "Vector.fromList")

primrec tabulate :: "code_numeral \<times> (code_numeral \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
"tabulate (n, f) = IArray (map (f \<circ> Code_Numeral.of_nat) [0..<Code_Numeral.nat_of n])"
hide_const (open) tabulate

lemma [code]:
"IArray.of_fun f n = IArray.tabulate (Code_Numeral.of_nat n, f \<circ> Code_Numeral.nat_of)"
by simp 

code_const IArray.tabulate
  (SML "Vector.tabulate")

primrec sub' :: "'a iarray \<times> code_numeral \<Rightarrow> 'a" where
"sub' (as, n) = IArray.list_of as ! Code_Numeral.nat_of n"
hide_const (open) sub'

lemma [code]:
"as !! n = IArray.sub' (as, Code_Numeral.of_nat n)"
by simp

code_const IArray.sub'
  (SML "Vector.sub")

definition length' :: "'a iarray \<Rightarrow> code_numeral" where
[simp]: "length' as = Code_Numeral.of_nat (List.length (IArray.list_of as))"
hide_const (open) length'

lemma [code]:
"IArray.length as = Code_Numeral.nat_of (IArray.length' as)"
by simp

code_const IArray.length'
  (SML "Vector.length")

end

