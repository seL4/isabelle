(*  Title:      HOL/ex/svc_test.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Demonstrating svc_tac: the interface to the Stanford Validity Checker

SVC is assumed to be present if the environment variable SVC_HOME is non-empty.

set Svc.trace;
*)

val svc_enabled = getenv "SVC_HOME" <> "";

if svc_enabled then
 (
  (** Propositional Logic **)
  Goal "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))";
  by (svc_tac 1);
  result();

  (*Blast_tac's runtime for this type of problem appears to be exponential
    in its length*)
  Goal "P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P";
  by (svc_tac 1);
  result();

  (** Linear arithmetic **)
  
  Goal "x ~= #14 & x ~= #13 & x ~= #12 & x ~= #11 & x ~= #10 & x ~= #9 & \
  \     x ~= #8 & x ~= #7 & x ~= #6 & x ~= #5 & x ~= #4 & x ~= #3 & \
  \     x ~= #2 & x ~= #1 & #0 < x & x < #16 --> #15 = (x::int)";
  by (svc_tac 1);
  result();

  (*merely to test polarity handling in the presence of biconditionals*)
  Goal "(x < (y::int)) = (x+#1 <= y)";
  by (svc_tac 1);
  result();

  (** Natural number examples requiring implicit "non-negative" assumptions*)

  Goal "(#3::nat)*a <= #2 + #4*b + #6*c  & #11 <= #2*a + b + #2*c & \
  \     a + #3*b <= #5 + #2*c  --> #2 + #3*b <= #2*a + #6*c";
  by (svc_tac 1);
  result();

  Goal "(n::nat) < #2 ==> (n = #0) | (n = #1)";
  by (svc_tac 1);
  result();

  ()
)
else ();
