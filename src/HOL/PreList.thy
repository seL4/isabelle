(*  Title:      HOL/PreList.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   2000 TU Muenchen
*)

header{*A Basis for Building the Theory of Lists*}

theory PreList =
    Wellfounded_Relations + Presburger + Recdef + Relation_Power + Parity:

text {*
  Is defined separately to serve as a basis for theory ToyList in the
  documentation. *}

lemmas wf_induct_rule = wf_induct [rule_format, case_names less, induct set: wf]
  -- {* belongs to theory @{text Wellfounded_Recursion} *}

end
