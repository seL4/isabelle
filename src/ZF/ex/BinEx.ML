(*  Title:      ZF/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Examples of performing binary arithmetic by simplification
*)

context Bin.thy;

set proof_timing;
(*All runtimes below are on a 300MHz Pentium*)

Goal "#13  $+  #19 = #32";
by (Simp_tac 1);    (*0 secs*)
result();

Goal "#1234  $+  #5678 = #6912";
by (Simp_tac 1);    (*190 msec*)
result();

Goal "#1359  $+  #-2468 = #-1109";
by (Simp_tac 1);    (*160 msec*)
result();

Goal "#93746  $+  #-46375 = #47371";
by (Simp_tac 1);    (*300 msec*)
result();

Goal "$~ #65745 = #-65745";
by (Simp_tac 1);    (*80 msec*)
result();

(* negation of ~54321 *)
Goal "$~ #-54321 = #54321";
by (Simp_tac 1);    (*90 msec*)
result();

Goal "#13  $*  #19 = #247";
by (Simp_tac 1);    (*110 msec*)
result();

Goal "#-84  $*  #51 = #-4284";
by (Simp_tac 1);    (*210 msec*)
result();

(*The worst case for 8-bit operands *)
Goal "#255  $*  #255 = #65025";
by (Simp_tac 1);    (*730 msec*)
result();

Goal "#1359  $*  #-2468 = #-3354012";
by (Simp_tac 1);    (*1.04 secs*)
result();
