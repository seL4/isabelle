(*  Title:      ZF/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Examples of performing binary arithmetic by simplification
*)

context Main.thy;

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

Goal "$- #65745 = #-65745";
by (Simp_tac 1);    (*80 msec*)
result();

(* negation of ~54321 *)
Goal "$- #-54321 = #54321";
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


(** Comparisons **)

Goal "(#89) $* #10 \\<noteq> #889";  
by (Simp_tac 1); 
result();

Goal "(#13) $< #18 $- #4";  
by (Simp_tac 1); 
result();

Goal "(#-345) $< #-242 $+ #-100";  
by (Simp_tac 1); 
result();

Goal "(#13557456) $< #18678654";  
by (Simp_tac 1); 
result();

Goal "(#999999) $<= (#1000001 $+ #1) $- #2";  
by (Simp_tac 1); 
result();

Goal "(#1234567) $<= #1234567";  
by (Simp_tac 1); 
result();


(*** Quotient and remainder!! [they could be faster] ***)

Goal "#23 zdiv #3 = #7";
by (Simp_tac 1); 
result();

Goal "#23 zmod #3 = #2";
by (Simp_tac 1); 
result();

(** negative dividend **)

Goal "#-23 zdiv #3 = #-8";
by (Simp_tac 1); 
result();

Goal "#-23 zmod #3 = #1";
by (Simp_tac 1); 
result();

(** negative divisor **)

Goal "#23 zdiv #-3 = #-8";
by (Simp_tac 1); 
result();

Goal "#23 zmod #-3 = #-1";
by (Simp_tac 1); 
result();

(** Negative dividend and divisor **)

Goal "#-23 zdiv #-3 = #7";
by (Simp_tac 1); 
result();

Goal "#-23 zmod #-3 = #-2";
by (Simp_tac 1); 
result();

