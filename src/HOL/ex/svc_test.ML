(*  Title:      HOL/ex/svc_test.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Demonstrating svc_tac: the interface to the Stanford Validity Checker

SVC is assumed to be present if the environment variable SVC_HOME is non-empty.

set Svc.trace;
*)

(** Propositional Logic **)

(*Blast_tac's runtime for this type of problem appears to be exponential
  in its length, though Fast_tac manages*)
Goal "P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P";
by (svc_tac 1);
qed "";

(** Some big tautologies supplied by John Harrison **)

(*Tautology name: puz013_1.  Auto_tac manages; Blast_tac and Fast_tac take
  a minute or more.*)
Goal "~(~v12 & \
\  v0 & \
\  v10 & \
\  (v4 | v5) & \
\  (v9 | v2) & \
\  (v8 | v1) & \
\  (v7 | v0) & \
\  (v3 | v12) & \
\  (v11 | v10) & \
\  (~v12 | ~v6 | v7) & \
\  (~v10 | ~v3 | v1) & \
\  (~v10 | ~v0 | ~v4 | v11) & \
\  (~v5 | ~v2 | ~v8) & \
\  (~v12 | ~v9 | ~v7) & \
\  (~v0 | ~v1 | v4) & \
\  (~v4 | v7 | v2) & \
\  (~v12 | ~v3 | v8) & \
\  (~v4 | v5 | v6) & \
\  (~v7 | ~v8 | v9) & \
\  (~v10 | ~v11 | v12))";
by (svc_tac 1);
qed "";

(*Tautology name: dk17_be*)
Goal "(GE17 <-> ~IN4 & ~IN3 & ~IN2 & ~IN1) & \
\   (GE0 <-> GE17 & ~IN5) & \
\   (GE22 <-> ~IN9 & ~IN7 & ~IN6 & IN0) & \
\   (GE19 <-> ~IN5 & ~IN4 & ~IN3 & ~IN0) & \
\   (GE20 <-> ~IN7 & ~IN6) & \
\   (GE18 <-> ~IN6 & ~IN2 & ~IN1 & ~IN0) & \
\   (GE21 <-> IN9 & ~IN7 & IN6 & ~IN0) & \
\   (GE23 <-> GE22 & GE0) & \
\   (GE25 <-> ~IN9 & ~IN7 & IN6 & ~IN0) & \
\   (GE26 <-> IN9 & ~IN7 & ~IN6 & IN0) & \
\   (GE2 <-> GE20 & GE19) & \
\   (GE1 <-> GE18 & ~IN7) & \
\   (GE24 <-> GE23 | GE21 & GE0) & \
\   (GE5 <-> ~IN5 & IN4 | IN5 & ~IN4) & \
\   (GE6 <-> GE0 & IN7 & ~IN6 & ~IN0) & \
\   (GE12 <-> GE26 & GE0 | GE25 & GE0) & \
\   (GE14 <-> GE2 & IN8 & ~IN2 & IN1) & \
\   (GE27 <-> ~IN8 & IN5 & ~IN4 & ~IN3) & \
\   (GE9 <-> GE1 & ~IN5 & ~IN4 & IN3) & \
\   (GE7 <-> GE24 | GE2 & IN2 & ~IN1) & \
\   (GE10 <-> GE6 | GE5 & GE1 & ~IN3) & \
\   (GE15 <-> ~IN8 | IN9) & \
\   (GE16 <-> GE12 | GE14 & ~IN9) & \
\   (GE4 <-> \
\    GE5 & GE1 & IN8 & ~IN3 | \
\    GE0 & ~IN7 & IN6 & ~IN0 | \
\    GE2 & IN2 & ~IN1) & \
\   (GE13 <-> GE27 & GE1) & \
\   (GE11 <-> GE9 | GE6 & ~IN8) & \
\   (GE8 <-> GE1 & ~IN5 & IN4 & ~IN3 | GE2 & ~IN2 & IN1) & \
\   (OUT0 <-> GE7 & ~IN8) & \
\   (OUT1 <-> GE7 & IN8) & \
\   (OUT2 <-> GE8 & ~IN9 | GE10 & IN8) & \
\   (OUT3 <-> GE8 & IN9 & ~IN8 | GE11 & ~IN9 | GE12 & ~IN8) & \
\   (OUT4 <-> GE11 & IN9 | GE12 & IN8) & \
\   (OUT5 <-> GE14 & IN9) & \
\   (OUT6 <-> GE13 & ~IN9) & \
\   (OUT7 <-> GE13 & IN9) & \
\   (OUT8 <-> GE9 & ~IN8 | GE15 & GE6 | GE4 & IN9) & \
\   (OUT9 <-> GE9 & IN8 | ~GE15 & GE10 | GE16) & \
\   (OUT10 <-> GE7) & \
\   (WRES0 <-> ~IN5 & ~IN4 & ~IN3 & ~IN2 & ~IN1) & \
\   (WRES1 <-> ~IN7 & ~IN6 & ~IN2 & ~IN1 & ~IN0) & \
\   (WRES2 <-> ~IN7 & ~IN6 & ~IN5 & ~IN4 & ~IN3 & ~IN0) & \
\   (WRES5 <-> ~IN5 & IN4 | IN5 & ~IN4) & \
\   (WRES6 <-> WRES0 & IN7 & ~IN6 & ~IN0) & \
\   (WRES9 <-> WRES1 & ~IN5 & ~IN4 & IN3) & \
\   (WRES7 <-> \
\    WRES0 & ~IN9 & ~IN7 & ~IN6 & IN0 | \
\    WRES0 & IN9 & ~IN7 & IN6 & ~IN0 | \
\    WRES2 & IN2 & ~IN1) & \
\   (WRES10 <-> WRES6 | WRES5 & WRES1 & ~IN3) & \
\   (WRES12 <-> \
\    WRES0 & IN9 & ~IN7 & ~IN6 & IN0 | \
\    WRES0 & ~IN9 & ~IN7 & IN6 & ~IN0) & \
\   (WRES14 <-> WRES2 & IN8 & ~IN2 & IN1) & \
\   (WRES15 <-> ~IN8 | IN9) & \
\   (WRES4 <-> \
\    WRES5 & WRES1 & IN8 & ~IN3 | \
\    WRES2 & IN2 & ~IN1 | \
\    WRES0 & ~IN7 & IN6 & ~IN0) & \
\   (WRES13 <-> WRES1 & ~IN8 & IN5 & ~IN4 & ~IN3) & \
\   (WRES11 <-> WRES9 | WRES6 & ~IN8) & \
\   (WRES8 <-> WRES1 & ~IN5 & IN4 & ~IN3 | WRES2 & ~IN2 & IN1) \
\   --> (OUT10 <-> WRES7) & \
\       (OUT9 <-> WRES9 & IN8 | WRES12 | WRES14 & ~IN9 | ~WRES15 & WRES10) & \
\       (OUT8 <-> WRES9 & ~IN8 | WRES15 & WRES6 | WRES4 & IN9) & \
\       (OUT7 <-> WRES13 & IN9) & \
\       (OUT6 <-> WRES13 & ~IN9) & \
\       (OUT5 <-> WRES14 & IN9) & \
\       (OUT4 <-> WRES11 & IN9 | WRES12 & IN8) & \
\       (OUT3 <-> WRES8 & IN9 & ~IN8 | WRES11 & ~IN9 | WRES12 & ~IN8) & \
\       (OUT2 <-> WRES8 & ~IN9 | WRES10 & IN8) & \
\       (OUT1 <-> WRES7 & IN8) & \
\       (OUT0 <-> WRES7 & ~IN8)";
by (svc_tac 1);
qed "";

(*Tautology name: sqn_be.  Fast_tac only takes a couple of seconds.*)
Goal "(GE0 <-> IN6 & IN1 | ~IN6 & ~IN1) & \
\  (GE8 <-> ~IN3 & ~IN1) & \
\  (GE5 <-> IN6 | IN5) & \
\  (GE9 <-> ~GE0 | IN2 | ~IN5) & \
\  (GE1 <-> IN3 | ~IN0) & \
\  (GE11 <-> GE8 & IN4) & \
\  (GE3 <-> ~IN4 | ~IN2) & \
\  (GE34 <-> ~GE5 & IN4 | ~GE9) & \
\  (GE2 <-> ~IN4 & IN1) & \
\  (GE14 <-> ~GE1 & ~IN4) & \
\  (GE19 <-> GE11 & ~GE5) & \
\  (GE13 <-> GE8 & ~GE3 & ~IN0) & \
\  (GE20 <-> ~IN5 & IN2 | GE34) & \
\  (GE12 <-> GE2 & ~IN3) & \
\  (GE27 <-> GE14 & IN6 | GE19) & \
\  (GE10 <-> ~IN6 | IN5) & \
\  (GE28 <-> GE13 | GE20 & ~GE1) & \
\  (GE6 <-> ~IN5 | IN6) & \
\  (GE15 <-> GE2 & IN2) & \
\  (GE29 <-> GE27 | GE12 & GE5) & \
\  (GE4 <-> IN3 & ~IN0) & \
\  (GE21 <-> ~GE10 & ~IN1 | ~IN5 & ~IN2) & \
\  (GE30 <-> GE28 | GE14 & IN2) & \
\  (GE31 <-> GE29 | GE15 & ~GE6) & \
\  (GE7 <-> ~IN6 | ~IN5) & \
\  (GE17 <-> ~GE3 & ~IN1) & \
\  (GE18 <-> GE4 & IN2) & \
\  (GE16 <-> GE2 & IN0) & \
\  (GE23 <-> GE19 | GE9 & ~GE1) & \
\  (GE32 <-> GE15 & ~IN6 & ~IN0 | GE21 & GE4 & ~IN4 | GE30 | GE31) & \
\  (GE33 <-> \
\   GE18 & ~GE6 & ~IN4 | \
\   GE17 & ~GE7 & IN3 | \
\   ~GE7 & GE4 & ~GE3 | \
\   GE11 & IN5 & ~IN0) & \
\  (GE25 <-> GE14 & ~GE6 | GE13 & ~GE5 | GE16 & ~IN5 | GE15 & GE1) & \
\  (GE26 <-> \
\   GE12 & IN5 & ~IN2 | \
\   GE10 & GE4 & IN1 | \
\   GE17 & ~GE6 & IN0 | \
\   GE2 & ~IN6) & \
\  (GE24 <-> GE23 | GE16 & GE7) & \
\  (OUT0 <-> \
\   GE6 & IN4 & ~IN1 & IN0 | GE18 & GE0 & ~IN5 | GE12 & ~GE10 | GE24) & \
\  (OUT1 <-> GE26 | GE25 | ~GE5 & GE4 & GE3 | GE7 & ~GE1 & IN1) & \
\  (OUT2 <-> GE33 | GE32) & \
\  (WRES8 <-> ~IN3 & ~IN1) & \
\  (WRES0 <-> IN6 & IN1 | ~IN6 & ~IN1) & \
\  (WRES2 <-> ~IN4 & IN1) & \
\  (WRES3 <-> ~IN4 | ~IN2) & \
\  (WRES1 <-> IN3 | ~IN0) & \
\  (WRES4 <-> IN3 & ~IN0) & \
\  (WRES5 <-> IN6 | IN5) & \
\  (WRES11 <-> WRES8 & IN4) & \
\  (WRES9 <-> ~WRES0 | IN2 | ~IN5) & \
\  (WRES10 <-> ~IN6 | IN5) & \
\  (WRES6 <-> ~IN5 | IN6) & \
\  (WRES7 <-> ~IN6 | ~IN5) & \
\  (WRES12 <-> WRES2 & ~IN3) & \
\  (WRES13 <-> WRES8 & ~WRES3 & ~IN0) & \
\  (WRES14 <-> ~WRES1 & ~IN4) & \
\  (WRES15 <-> WRES2 & IN2) & \
\  (WRES17 <-> ~WRES3 & ~IN1) & \
\  (WRES18 <-> WRES4 & IN2) & \
\  (WRES19 <-> WRES11 & ~WRES5) & \
\  (WRES20 <-> ~IN5 & IN2 | ~WRES5 & IN4 | ~WRES9) & \
\  (WRES21 <-> ~WRES10 & ~IN1 | ~IN5 & ~IN2) & \
\  (WRES16 <-> WRES2 & IN0) \
\  --> (OUT2 <-> \
\       WRES11 & IN5 & ~IN0 | \
\       ~WRES7 & WRES4 & ~WRES3 | \
\       WRES12 & WRES5 | \
\       WRES13 | \
\       WRES14 & IN2 | \
\       WRES14 & IN6 | \
\       WRES15 & ~WRES6 | \
\       WRES15 & ~IN6 & ~IN0 | \
\       WRES17 & ~WRES7 & IN3 | \
\       WRES18 & ~WRES6 & ~IN4 | \
\       WRES20 & ~WRES1 | \
\       WRES21 & WRES4 & ~IN4 | \
\       WRES19) & \
\      (OUT1 <-> \
\       ~WRES5 & WRES4 & WRES3 | \
\       WRES7 & ~WRES1 & IN1 | \
\       WRES2 & ~IN6 | \
\       WRES10 & WRES4 & IN1 | \
\       WRES12 & IN5 & ~IN2 | \
\       WRES13 & ~WRES5 | \
\       WRES14 & ~WRES6 | \
\       WRES15 & WRES1 | \
\       WRES16 & ~IN5 | \
\       WRES17 & ~WRES6 & IN0) & \
\      (OUT0 <-> \
\       WRES6 & IN4 & ~IN1 & IN0 | \
\       WRES9 & ~WRES1 | \
\       WRES12 & ~WRES10 | \
\       WRES16 & WRES7 | \
\       WRES18 & WRES0 & ~IN5 | \
\       WRES19)";
by (svc_tac 1);
qed "";


(** Linear arithmetic **)

Goal "x ~= #14 & x ~= #13 & x ~= #12 & x ~= #11 & x ~= #10 & x ~= #9 & \
\     x ~= #8 & x ~= #7 & x ~= #6 & x ~= #5 & x ~= #4 & x ~= #3 & \
\     x ~= #2 & x ~= #1 & #0 < x & x < #16 --> #15 = (x::int)";
by (svc_tac 1);
qed "";

(*merely to test polarity handling in the presence of biconditionals*)
Goal "(x < (y::int)) = (x+#1 <= y)";
by (svc_tac 1);
qed "";

(** Natural number examples requiring implicit "non-negative" assumptions*)

Goal "(#3::nat)*a <= #2 + #4*b + #6*c  & #11 <= #2*a + b + #2*c & \
\     a + #3*b <= #5 + #2*c  --> #2 + #3*b <= #2*a + #6*c";
by (svc_tac 1);
qed "";

Goal "(n::nat) < #2 ==> (n = #0) | (n = #1)";
by (svc_tac 1);
qed "";
