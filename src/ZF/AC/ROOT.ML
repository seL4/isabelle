(*  Title: 	ZF/ex/ROOT
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

writeln"END: Root file for ZF/AC";
