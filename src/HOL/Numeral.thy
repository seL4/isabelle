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
  number < "term"      (*for numeric types: nat, int, real, ...*)

consts
  number_of :: "bin => 'a::number"

nonterminals
  numeral

syntax
  "_constify" :: "num => numeral"    ("_")
  "_Numeral" :: "numeral => 'a"    ("_")
  Numeral0 :: 'a
  Numeral1 :: 'a

translations
  "Numeral0" == "number_of Pls"
  "Numeral1" == "number_of (Pls BIT True)"


setup NumeralSyntax.setup


(*Unfold all "let"s involving constants*)
lemma Let_number_of [simp]: "Let (number_of v) f == f (number_of v)"
  by (simp add: Let_def)

(*The condition "True" is a hack to prevent looping.
  Conditional rewrite rules are tried after unconditional ones, so a rule
  like eq_nat_number_of will be tried first to eliminate #mm=#nn. *)
lemma number_of_reorient [simp]: "True ==> (number_of w = x) = (x = number_of w)"
  by auto

end
