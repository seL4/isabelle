(*  Title: 	ZF/AC/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Executes the proofs of the AC-equivalences, due to Krzysztof Gr`abczewski
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

writeln"Root file for ZF/AC";
proof_timing := true;

loadpath := [".", "AC"];

time_use_thy "AC/AC_Equiv";

time_use     "AC/WO1_WO6.ML";
time_use_thy "AC/WO6_WO1";
time_use     "AC/WO1_WO7.ML";
time_use     "AC/WO1_WO8.ML";

time_use     "AC/AC0_AC1.ML";
time_use     "AC/AC2_AC6.ML";
time_use     "AC/AC7_AC9.ML";

time_use_thy "AC/WO1_AC1";
time_use_thy "AC/AC1_WO2";

time_use     "AC/AC10_AC15.ML";
time_use_thy "AC/AC15_WO6";

(* AC16 to add *)

time_use     "AC/AC1_AC17.ML";
time_use_thy "AC/AC17_AC1";

time_use_thy "AC/AC18_AC19";

writeln"END: Root file for ZF/AC";
