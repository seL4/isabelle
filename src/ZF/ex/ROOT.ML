(*  Title: 	ZF/ex/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Executes all examples for Zermelo-Fraenkel Set Theory
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

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
time_use_thy "ex/binfn";

(** Datatypes **)
(*binary trees*)
time_use     "ex/bt.ML";
time_use_thy "ex/bt_fn";
(*terms: recursion over the list functor*)
time_use     "ex/term.ML";
time_use_thy "ex/termfn";
(*trees/forests: mutual recursion*)
time_use     "ex/tf.ML";
time_use_thy "ex/tf_fn";
(*Sample datatype; enormous enumeration type*)
time_use     "ex/data.ML";
time_use     "ex/enum.ML";

(** Inductive definitions **)
(*mapping a relation over a list*)
time_use     "ex/rmap.ML";
(*completeness of propositional logic*)
time_use     "ex/prop.ML";
time_use_thy "ex/propthms";
(*two Coq examples by Ch. Paulin-Mohring*)
time_use     "ex/listn.ML";
time_use     "ex/acc.ML";
(*Diamond property for combinatory logic*)
time_use     "ex/comb.ML";
time_use_thy "ex/contract";
time_use     "ex/parcontract.ML";
time_use_thy "ex/primrec";

(** Co-Datatypes **)
time_use     "ex/llist.ML";
time_use     "ex/llist_eq.ML";
time_use_thy "ex/llistfn";


maketest"END: Root file for ZF Set Theory examples";
