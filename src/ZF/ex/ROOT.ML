(*  Title:      ZF/ex/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes miscellaneous examples for Zermelo-Fraenkel Set Theory.
*)

time_use_thy "misc";
time_use_thy "Ring";		(*abstract algebra*)
time_use_thy "Commutation";     (*abstract Church-Rosser theory*)
time_use_thy "Primes";          (*GCD theory*)
time_use_thy "NatSum";          (*Summing integers, squares, cubes, etc.*)
time_use_thy "Ramsey";          (*Simple form of Ramsey's theorem*)
time_use_thy "Limit";           (*Inverse limit construction of domains*)
time_use_thy "BinEx";		(*Binary integer arithmetic*)

(** CoDatatypes **)
time_use_thy "LList";
time_use_thy "CoUnit";
