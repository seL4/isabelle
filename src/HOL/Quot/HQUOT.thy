(*  Title:      HOL/Quot/HQUOT.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

quotient constructor for higher order quotients

*)

HQUOT = PER +      

typedef 'a quot = "{s::'a::per set. ? r.!y.y:s=y===r}" (quotNE)

(* constants for equivalence classes *)
consts
        peclass         :: "'a::per => 'a quot"
        any_in          :: "'a::per quot => 'a"

syntax          "@ecl"  :: "'a::per => 'a quot" ("<[ _ ]>")

translations    "<[x]>" == "peclass x"

defs
        peclass_def     "<[x]> == Abs_quot {y.y===x}"
        any_in_def      "any_in f == @x.<[x]>=f"
end

