(*  Title: 	ZF/ex/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes all examples for Zermelo-Fraenkel Set Theory
*)

ZF_build_completed;	(*Cause examples to fail if ZF did*)

writeln"Root file for ZF Set Theory examples";
proof_timing := true;

time_use     "ex/misc.ML";
time_use_thy "ex/ramsey";

(*Equivalence classes and integers*)
time_use_thy "ex/equiv";
time_use_thy "ex/integ";
(*Binary integer arithmetic*)
use          "ex/twos-compl.ML";
time_use     "ex/bin.ML";
time_use_thy "ex/bin-fn";

(** Datatypes **)
(*binary trees*)
time_use     "ex/bt.ML";
time_use_thy "ex/bt-fn";
(*terms: recursion over the list functor*)
time_use     "ex/term.ML";
time_use_thy "ex/term-fn";
(*trees/forests: mutual recursion*)
time_use     "ex/tf.ML";
time_use_thy "ex/tf-fn";
(*Enormous enumeration type -- could be even bigger?*)
time_use     "ex/enum.ML";

(** Inductive definitions **)
(*completeness of propositional logic*)
time_use     "ex/prop.ML";
time_use_thy "ex/prop-log";
(*two Coq examples by Ch. Paulin-Mohring*)
time_use     "ex/listn.ML";
time_use     "ex/acc.ML";
(*Diamond property for combinatory logic*)
time_use     "ex/comb.ML";
time_use_thy "ex/contract";
time_use     "ex/parcontract.ML";

(** Co-Datatypes **)
time_use     "ex/llist.ML";
time_use_thy "ex/llist-fn";


maketest"END: Root file for ZF Set Theory examples";
