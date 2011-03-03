(*  Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

(*Verifying security protocols using UNITY*)
no_document use_thys ["../Auth/Public"];

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
  "Comp/Progress",

  "Comp/Alloc",
  "Comp/AllocImpl",
  "Comp/Client",

  (*obsolete*)
  "ELT"
];
