(*  Title:      HOL/UNITY/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Root file for UNITY proofs.
*)

(*Basic meta-theory*)
time_use_thy "FP";
time_use_thy "WFair";

(*Simple examples: no composition*)
time_use_thy "Simple/Deadlock";
time_use_thy "Simple/Common";
time_use_thy "Simple/Network";
time_use_thy "Simple/Token";
time_use_thy "Simple/Channel";
time_use_thy "Simple/Lift";
time_use_thy "Simple/Mutex";
time_use_thy "Simple/Reach";
time_use_thy "Simple/Reachability";

with_path "../Auth"  (*to find Public.thy*)
  time_use_thy"Simple/NSP_Bad";

(*Example of composition*)
time_use_thy "Comp";
time_use_thy "Comp/Handshake";

(*Universal properties examples*)
time_use_thy "Comp/Counter";
time_use_thy "Comp/Counterc";
time_use_thy "Comp/Priority";

(*Allocator example*)
time_use_thy "PPROD";
time_use_thy "Comp/TimerArray";

time_use_thy "Comp/Alloc";
time_use_thy "Comp/AllocImpl";
time_use_thy "Comp/Client";

time_use_thy "ELT";  (*obsolete*)
