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
  "_constify" :: "xnum => numeral"    ("_")
  "_Numeral" :: "numeral => 'a"    ("_")


setup NumeralSyntax.setup

end
