(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen
*)

header{*A Basis for Building the Theory of Lists*}

(*Is defined separately to serve as a basis for theory ToyList in the
documentation.*)

theory PreList =
    Wellfounded_Relations + Presburger + Recdef + Relation_Power + Parity:

(*belongs to theory Wellfounded_Recursion*)
lemmas wf_induct_rule = wf_induct [rule_format, case_names less, induct set: wf]

end
