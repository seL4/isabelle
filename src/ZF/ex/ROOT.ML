(*  Title: 	ZF/ex/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes all examples for Zermelo-Fraenkel Set Theory
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

writeln"Root file for ZF Set Theory examples";
proof_timing := true;

loadpath := [".", "ex"];

time_use     "ex/misc.ML";
time_use_thy "ex/Ramsey";

(*Integers & Binary integer arithmetic*)
use "ex/twos_compl.ML";		(*can delete after autoloader change
				  and addition of "twos_compl" to Bin.thy*)
time_use_thy "ex/Bin";

(** Datatypes **)
time_use_thy "ex/BT";		(*binary trees*)
time_use_thy "ex/Data";		(*Sample datatype*)
time_use_thy "ex/Term";		(*terms: recursion over the list functor*)
time_use_thy "ex/TF";		(*trees/forests: mutual recursion*)
time_use_thy "ex/Ntree";	(*variable-branching trees; function demo*)
time_use_thy "ex/Brouwer";	(*Infinite-branching trees*)
time_use_thy "ex/Enum";		(*Enormous enumeration type*)

(** Inductive definitions **)
time_use_thy "ex/Rmap";		(*mapping a relation over a list*)
time_use_thy "ex/PropLog";	(*completeness of propositional logic*)
(*two Coq examples by Christine Paulin-Mohring*)
time_use_thy "ex/ListN";
time_use_thy "ex/Acc";
time_use_thy "ex/Comb";		(*Combinatory Logic example*)
time_use_thy "ex/Primrec";	(*Primitive recursive functions*)

(** CoDatatypes **)
time_use_thy "ex/LList";
time_use_thy "ex/CoUnit";

maketest"END: Root file for ZF Set Theory examples";
