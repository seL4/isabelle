(*  Title:      ZF/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Examples of performing binary arithmetic by simplification
*)

theory BinEx = Main:
(*All runtimes below are on a 300MHz Pentium*)

lemma "#13  $+  #19 = #32"
by simp (*0 secs*)

lemma "#1234  $+  #5678 = #6912"
by simp (*190 msec*)

lemma "#1359  $+  #-2468 = #-1109"
by simp (*160 msec*)

lemma "#93746  $+  #-46375 = #47371"
by simp (*300 msec*)

lemma "$- #65745 = #-65745"
by simp (*80 msec*)

(* negation of ~54321 *)
lemma "$- #-54321 = #54321"
by simp (*90 msec*)

lemma "#13  $*  #19 = #247"
by simp (*110 msec*)

lemma "#-84  $*  #51 = #-4284"
by simp (*210 msec*)

(*The worst case for 8-bit operands *)
lemma "#255  $*  #255 = #65025"
by simp (*730 msec*)

lemma "#1359  $*  #-2468 = #-3354012"
by simp (*1.04 secs*)


(** Comparisons **)

lemma "(#89) $* #10 \<noteq> #889"
by simp

lemma "(#13) $< #18 $- #4"
by simp

lemma "(#-345) $< #-242 $+ #-100"
by simp

lemma "(#13557456) $< #18678654"
by simp

lemma "(#999999) $<= (#1000001 $+ #1) $- #2"
by simp

lemma "(#1234567) $<= #1234567"
by simp


(*** Quotient and remainder!! [they could be faster] ***)

lemma "#23 zdiv #3 = #7"
by simp

lemma "#23 zmod #3 = #2"
by simp

(** negative dividend **)

lemma "#-23 zdiv #3 = #-8"
by simp

lemma "#-23 zmod #3 = #1"
by simp

(** negative divisor **)

lemma "#23 zdiv #-3 = #-8"
by simp

lemma "#23 zmod #-3 = #-1"
by simp

(** Negative dividend and divisor **)

lemma "#-23 zdiv #-3 = #7"
by simp

lemma "#-23 zmod #-3 = #-2"
by simp

end

