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

(*Equivalence classes and integers*)
time_use_thy "ex/Equiv";
time_use_thy "ex/Integ";
(*Binary integer arithmetic*)
use          "ex/twos_compl.ML";
time_use_thy "ex/BinFn";

(** Datatypes **)
time_use_thy "ex/BT_Fn";	(*binary trees*)
time_use_thy "ex/TermFn";	(*terms: recursion over the list functor*)
time_use_thy "ex/TF_Fn";	(*trees/forests: mutual recursion*)
time_use_thy "ex/Data";		(*Sample datatype*)
time_use_thy "ex/Enum";		(*Enormous enumeration type*)

(** Inductive definitions **)
time_use_thy "ex/Rmap";		(*mapping a relation over a list*)
time_use_thy "ex/PropLog";	(*completeness of propositional logic*)
(*two Coq examples by Ch. Paulin-Mohring*)
time_use_thy "ex/ListN";
time_use_thy "ex/Acc";
time_use_thy "ex/Contract0";	(*Contraction relation for combinatory logic*)
time_use_thy "ex/ParContract";	(*Diamond property for combinatory logic*)
time_use_thy "ex/Primrec0";

(** CoDatatypes **)
time_use_thy "ex/LList";
time_use_thy "ex/LListFn";
time_use     "ex/counit.ML";

maketest"END: Root file for ZF Set Theory examples";
