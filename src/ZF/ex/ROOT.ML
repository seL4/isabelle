(*  Title:      ZF/ex/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes miscellaneous examples for Zermelo-Fraenkel Set Theory
*)

ZF_build_completed;     (*Make examples fail if ZF did*)

writeln"Root file for ZF Set Theory examples";
proof_timing := true;

time_use     "misc.ML";
time_use_thy "Ramsey";
time_use_thy "Limit";

(*Integers & Binary integer arithmetic*)
time_use_thy "Bin";

(** Datatypes **)
time_use_thy "BT";              (*binary trees*)
time_use_thy "Data";            (*Sample datatype*)
time_use_thy "Term";            (*terms: recursion over the list functor*)
time_use_thy "TF";              (*trees/forests: mutual recursion*)
time_use_thy "Ntree";           (*variable-branching trees; function demo*)
time_use_thy "Brouwer";         (*Infinite-branching trees*)
time_use_thy "Enum";            (*Enormous enumeration type*)

(** Inductive definitions **)
time_use_thy "Rmap";            (*mapping a relation over a list*)
time_use_thy "PropLog";         (*completeness of propositional logic*)
(*two Coq examples by Christine Paulin-Mohring*)
time_use_thy "ListN";
time_use_thy "Acc";
time_use_thy "Comb";            (*Combinatory Logic example*)
time_use_thy "Primrec";         (*Primitive recursive functions*)

(** CoDatatypes **)
time_use_thy "LList";
time_use_thy "CoUnit";

writeln"END: Root file for ZF Set Theory examples";
