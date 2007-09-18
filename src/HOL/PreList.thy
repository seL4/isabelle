(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen
*)

header {* A Basis for Building the Theory of Lists *}

theory PreList
imports Presburger Relation_Power SAT Recdef Extraction Record
uses "Tools/function_package/lexicographic_order.ML"
     "Tools/function_package/fundef_datatype.ML"
begin

text {*
  This is defined separately to serve as a basis for
  theory ToyList in the documentation.
*}

(* The lexicographic_order method and the "fun" command *)
setup LexicographicOrder.setup
setup FundefDatatype.setup

end

