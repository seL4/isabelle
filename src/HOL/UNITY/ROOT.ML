(*  Title:      HOL/UNITY/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Root file for UNITY proofs.
*)

writeln"Root file for HOL/UNITY";

set proof_timing;

time_use_thy "UNITY";
time_use_thy "Deadlock";
time_use_thy "WFair";
time_use_thy "Common";
time_use_thy "Network";
time_use_thy "Token";
time_use_thy "Channel";
time_use_thy "Mutex";
time_use_thy "FP";
time_use_thy "Reach";
time_use_thy "Handshake";
time_use_thy "Lift";
time_use_thy "Comp";
(*Allocator example*)
time_use_thy "Client";
time_use_thy "Extend";
time_use_thy "PPROD";
time_use_thy "TimerArray";
time_use_thy "Follows";

add_path "../Auth";	(*to find Public.thy*)
use_thy"NSP_Bad";

reset_path ();
