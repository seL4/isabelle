header "Immutable Arrays with Code Generation"

theory IArray
imports "~~/src/HOL/Library/Efficient_Nat"
begin

text{* Immutable arrays are lists wrapped up in an additional constructor.
There are no update operations. Hence code generation can safely implement
this type by efficient target language arrays.  Currently only SML is
provided. Should be extended to other target languages and more operations.

Note that arrays cannot be printed directly but only by turning them into
lists first. Arrays could be converted back into lists for printing if they
were wrapped up in an additional constructor. *}

datatype 'a iarray = IArray "'a list"

fun of_fun :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a iarray" where
"of_fun f n = IArray (map f [0..<n])"
hide_const (open) of_fun

fun length :: "'a iarray \<Rightarrow> nat" where
"length (IArray xs) = List.length xs"
hide_const (open) length

fun sub :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
"(IArray as) !! n = as!n"
hide_const (open) sub

fun list_of :: "'a iarray \<Rightarrow> 'a list" where
"list_of (IArray xs) = xs"
hide_const (open) list_of


subsection "Code Generation"

code_type iarray
  (SML "_ Vector.vector")

code_const IArray
  (SML "Vector.fromList")
code_const IArray.sub
  (SML "Vector.sub(_,_)")
code_const IArray.length
  (SML "Vector.length")
code_const IArray.of_fun
  (SML "!(fn f => fn n => Vector.tabulate(n,f))")

lemma list_of_code[code]:
  "IArray.list_of A = map (%n. A!!n) [0..< IArray.length A]"
by (cases A) (simp add: map_nth)

end
