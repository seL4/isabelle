(*  Title:      ZF/ex/Enum
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Example of a BIG enumeration type

Can go up to at least 100 constructors, but it takes nearly 7 minutes...
*)

open Enum;

goal Enum.thy "C00 ~= C01";
by (simp_tac (ZF_ss addsimps enum.free_iffs) 1);
result();

