(*  Title:      HOL/LessThan/LessThan
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

*)


(*** Finally, a few set-theoretic laws...
     CAN BOOLEAN SIMPLIFICATION BE AUTOMATED? ***)

(** Rewrite rules to eliminate A.  Conditions can be satisfied by letting B
    be any set including A Int C and contained in A Un C, such as B=A or B=C.
**)

Goal "[| A Int C <= B; B <= A Un C |] \
\     ==> (A Int B) Un (-A Int C) = B Un C";
by (Blast_tac 1);
qed "set_cancel1";

Goal "[| A Int C <= B; B <= A Un C |] \
\     ==> (A Un B) Int (-A Un C) = B Int C";
by (Blast_tac 1);
qed "set_cancel2";

(*The base B=A*)
Goal "A Un (-A Int C) = A Un C";
by (Blast_tac 1);
qed "set_cancel3";

Goal "A Int (-A Un C) = A Int C";
by (Blast_tac 1);
qed "set_cancel4";

(*The base B=C*)
Goal "(A Int C) Un (-A Int C) = C";
by (Blast_tac 1);
qed "set_cancel5";

Goal "(A Un C) Int (-A Un C) = C";
by (Blast_tac 1);
qed "set_cancel6";

Addsimps [set_cancel1, set_cancel2, set_cancel3,
	  set_cancel4, set_cancel5, set_cancel6];


