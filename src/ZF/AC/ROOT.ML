(*  Title: 	ZF/AC/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Executes the proofs of the AC-equivalences, due to Krzysztof Grabczewski
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

writeln"Root file for ZF/AC";
proof_timing := true;

time_use_thy "AC_Equiv";

time_use     "WO1_WO6.ML";
time_use_thy "WO6_WO1";
time_use     "WO1_WO7.ML";
time_use     "WO1_WO8.ML";

time_use     "AC0_AC1.ML";
time_use     "AC2_AC6.ML";
time_use     "AC7_AC9.ML";

time_use_thy "WO1_AC";
time_use_thy "AC1_WO2";

time_use     "AC10_AC15.ML";
time_use_thy "AC15_WO6";

time_use_thy "WO2_AC16";
time_use_thy "AC16_WO4";

time_use     "AC1_AC17.ML";
time_use_thy "AC17_AC1";

time_use_thy "AC18_AC19";

time_use_thy "DC";

writeln"END: Root file for ZF/AC";
