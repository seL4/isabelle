(*  Title:      HOL/Numeral.thy
    ID:         $Id$
    Author:     Larry Paulson and Markus Wenzel

Generic numerals represented as twos-complement bit strings.
*)

theory Numeral = Datatype
files "Tools/numeral_syntax.ML":

datatype
  bin = Pls
      | Min
      | Bit bin bool    (infixl "BIT" 90)

axclass
  number < type  -- {* for numeric types: nat, int, real, \dots *}

consts
  number_of :: "bin => 'a::number"

syntax
  "_Numeral" :: "num_const => 'a"    ("_")
  Numeral0 :: 'a
  Numeral1 :: 'a

translations
  "Numeral0" == "number_of Pls"
  "Numeral1" == "number_of (Pls BIT True)"


setup NumeralSyntax.setup


(*Unfold all "let"s involving constants*)
lemma Let_number_of [simp]: "Let (number_of v) f == f (number_of v)"
  by (simp add: Let_def)

lemma Let_0 [simp]: "Let 0 f == f 0"
  by (simp add: Let_def)

lemma Let_1 [simp]: "Let 1 f == f 1"
  by (simp add: Let_def)

end
