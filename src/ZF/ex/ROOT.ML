(*  Title:      ZF/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes miscellaneous examples for Zermelo-Fraenkel Set Theory
*)

time_use_thy "misc";
time_use_thy "Commutation";     (*abstract Church-Rosser theory*)
time_use_thy "Primes";          (*GCD theory*)
time_use_thy "NatSum";          (*Summing integers, squares, cubes, etc.*)
time_use_thy "Ramsey";          (*Simple form of Ramsey's theorem*)
time_use_thy "Limit";           (*Inverse limit construction of domains*)
time_use_thy "BinEx";		(*Binary integer arithmetic*)

(** Datatypes **)
time_use_thy "BT";              (*binary trees*)
time_use_thy "Data";            (*Sample datatype*)
time_use_thy "Term";            (*terms: recursion over the list functor*)
time_use_thy "TF";              (*trees/forests: mutual recursion*)
time_use_thy "Ntree";           (*variable-branching trees; function demo*)
time_use_thy "Brouwer";         (*Infinite-branching trees*)
time_use_thy "Enum";            (*Enormous enumeration type*)

(** CoDatatypes **)
time_use_thy "LList";
time_use_thy "CoUnit";
