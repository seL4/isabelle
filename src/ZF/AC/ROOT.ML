(*  Title: 	ZF/AC/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Executes the proofs of the AC-equivalences, by Krzysztof Gr`abczewski
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

writeln"Root file for ZF/AC";
proof_timing := true;

loadpath := [".", "AC"];

time_use_thy "WO6_WO1";

(*New ones pending on ~kg10006/isabelle
time_use     "AC10_AC11.ML";
time_use     "AC11_AC12.ML";
time_use     "AC1_AC13.ML";
time_use     "AC13_AC1.ML";
time_use     "AC13_AC13.ML";
time_use     "AC13_AC14.ML";
time_use     "AC14_AC15.ML";
time_use_thy "lemmas_AC13_AC15";
time_use_thy "AC10_AC13";
time_use_thy "AC11_AC14";
time_use_thy "AC12_AC15";
time_use     "AC14_AC15.ML";
*)

writeln"END: Root file for ZF/AC";
