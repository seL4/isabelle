(*  Title:      HOL/Numeral.thy
    ID:         $Id$
    Author:     Larry Paulson and Markus Wenzel

Generic numerals represented as twos-complement bitstrings.
*)

theory Numeral = Datatype
files "Tools/numeral_syntax.ML":;

datatype
  bin = Pls
      | Min
      | Bit bin bool	(infixl "BIT" 90);

axclass
  numeral < "term";

consts
  number_of :: "bin => 'a::numeral";

syntax
  "_Numeral" :: "xnum => 'a"	("_");

setup NumeralSyntax.setup;


end;
