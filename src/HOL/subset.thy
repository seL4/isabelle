(*  Title:      HOL/subset.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

theory subset = Set
files "Tools/typedef_package.ML":

(*belongs to theory Ord*)
theorems linorder_cases [case_names less equal greater] =
  linorder_less_split

(*belongs to theory Set*)
setup Rulify.setup

end
