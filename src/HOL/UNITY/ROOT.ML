(*  Title:      HOL/UNITY/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Root file for UNITY proofs.
*)

(*Verifying security protocols using UNITY*)
no_document use_thy "../Auth/Public";

use_thys [
  (*Basic meta-theory*)
  "UNITY_Main",

  (*Simple examples: no composition*)
  "Simple/Deadlock",
  "Simple/Common",
  "Simple/Network",
  "Simple/Token",
  "Simple/Channel",
  "Simple/Lift",
  "Simple/Mutex",
  "Simple/Reach",
  "Simple/Reachability",

  (*Verifying security protocols using UNITY*)
  "Simple/NSP_Bad",

  (*Example of composition*)
  "Comp/Handshake",

  (*Universal properties examples*)
  "Comp/Counter",
  "Comp/Counterc",
  "Comp/Priority",

  "Comp/TimerArray",

  (*obsolete*)
  "ELT"
];

(*Allocator example*)
(* FIXME some parts no longer work -- had been commented out for a long time *)
setmp quick_and_dirty true
  use_thy "Comp/Alloc";

use_thys ["Comp/AllocImpl", "Comp/Client"];
